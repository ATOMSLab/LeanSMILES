"""
canon_ref.py -- pure-Python reference of RDKit's canonical SMILES writer
              Chem.MolToSmiles(mol, isomericSmiles=False)   (RDKit 2026.09.1)

Intended as a porting spec for Lean 4: only ints / bools / plain lists, no
dicts-as-maps semantics that matter, no Python sort with key tricks on the
critical path (all sorts are explicit insertion sorts or a literal port of
RDKit's hanoi merge sort).

File references are to Code/GraphMol/ in the RDKit Release_2026_09_1 source:
  new_canon.h / new_canon.cpp   -- atom ranking (rankMolAtoms)
  RDGeneral/hanoiSort.h          -- the partition sort
  Canon.cpp / Canon.h            -- DFS traversal (dfsFindCycles, dfsBuildStack)
  SmilesParse/SmilesWrite.cpp    -- fragments, atom/bond tokens, ring digits

INPUT
  atoms : list of dicts, SMILES input order, with keys
            Z          atomic number (0 = '*')
            charge     formal charge
            aromatic   bool
            totalHs    RDKit getTotalNumHs() (explicit + implicit, NOT H neighbours)
            radicals   number of radical electrons (normally 0)
            explicitHs RDKit getNumExplicitHs()  (only used for bracket rules)
  bonds : list of (a, b, t) with t in {"SINGLE","DOUBLE","TRIPLE","AROMATIC"}
          (or the RDKit enum ints 1,2,3,12).  Bond index order and the
          direction a->b do NOT influence the output (see notes at bottom).

OUTPUT
  canonical SMILES string, identical to RDKit's MolToSmiles(m, isomericSmiles=False)
"""

# ---------------------------------------------------------------------------
# constants
# ---------------------------------------------------------------------------
# RDKit Bond::BondType enum values (Bond.h).  The numeric values matter:
# they are compared in bondholder::compare (new_canon.h:92) and used in the
# DFS neighbour-ordering formula (Canon.cpp:911,921,1080).
SINGLE, DOUBLE, TRIPLE, AROMATIC = 1, 2, 3, 12
BT_FROM_NAME = {"SINGLE": SINGLE, "DOUBLE": DOUBLE, "TRIPLE": TRIPLE,
                "AROMATIC": AROMATIC}

MAX_NATOMS = 5000     # Canon.h:22
MAX_BONDTYPE = 32     # Canon.h:24

SYMBOLS = ['*', 'H', 'He', 'Li', 'Be', 'B', 'C', 'N', 'O', 'F', 'Ne', 'Na',
           'Mg', 'Al', 'Si', 'P', 'S', 'Cl', 'Ar', 'K', 'Ca', 'Sc', 'Ti', 'V',
           'Cr', 'Mn', 'Fe', 'Co', 'Ni', 'Cu', 'Zn', 'Ga', 'Ge', 'As', 'Se',
           'Br', 'Kr', 'Rb', 'Sr', 'Y', 'Zr', 'Nb', 'Mo', 'Tc', 'Ru', 'Rh',
           'Pd', 'Ag', 'Cd', 'In', 'Sn', 'Sb', 'Te', 'I', 'Xe', 'Cs', 'Ba',
           'La', 'Ce', 'Pr', 'Nd', 'Pm', 'Sm', 'Eu', 'Gd', 'Tb', 'Dy', 'Ho',
           'Er', 'Tm', 'Yb', 'Lu', 'Hf', 'Ta', 'W', 'Re', 'Os', 'Ir', 'Pt',
           'Au', 'Hg', 'Tl', 'Pb', 'Bi', 'Po', 'At', 'Rn', 'Fr', 'Ra', 'Ac',
           'Th', 'Pa', 'U', 'Np', 'Pu', 'Am', 'Cm', 'Bk', 'Cf', 'Es', 'Fm',
           'Md', 'No', 'Lr', 'Rf', 'Db', 'Sg', 'Bh', 'Hs', 'Mt', 'Ds', 'Rg',
           'Cn', 'Nh', 'Fl', 'Mc', 'Lv', 'Ts', 'Og']

# SmilesWrite.cpp:32 inOrganicSubset
ORGANIC_SUBSET = [0, 5, 6, 7, 8, 9, 15, 16, 17, 35, 53]
# SmilesWrite.cpp:196-206: elements written lower-case when aromatic
AROMATIC_LOWER = [5, 6, 7, 8, 14, 15, 16, 33, 34, 52]
# QueryOps.cpp:434-470 makeMAtomQuery: "metal" = NOT one of these
NON_METALS = [0, 1, 2, 5, 6, 7, 8, 9, 10, 14, 15, 16, 17, 18, 33, 34, 35, 36,
              52, 53, 54, 85, 86]
# PeriodicTable valence lists for the organic subset (only consulted for
# neutral organic-subset atoms; all others are bracketed anyway)
VALENCE_LIST = {0: [-1], 5: [3], 6: [4], 7: [3], 8: [2], 9: [1], 15: [3, 5],
                16: [2, 4, 6], 17: [1], 35: [1], 53: [1, 3, 5]}


def member(x, xs):
    for y in xs:
        if y == x:
            return True
    return False


# ---------------------------------------------------------------------------
# graph helpers
# ---------------------------------------------------------------------------
def build_adj(n, bonds):
    """adj[i] = list of (nbr, bondType, bondIdx).  Order = bond index order,
    as RDKit's atomBonds()/getAtomNeighbors iterate.  Nothing downstream
    depends on this order (all uses are sorted or set-like)."""
    adj = [[] for _ in range(n)]
    for k in range(len(bonds)):
        a, b, t = bonds[k]
        adj[a].append((b, t, k))
        adj[b].append((a, t, k))
    return adj


def ring_bonds(n, bonds, adj):
    """inRing[k] for bond k: bond is in a ring iff it is not a bridge.
    RDKit uses RingInfo::numBondRings(b) != 0 (Canon.cpp:918,1077); every
    non-bridge bond lies in at least one SSSR / fastFindRings ring."""
    m = len(bonds)
    inRing = [False] * m
    for k in range(m):
        a, b, _ = bonds[k]
        # is b reachable from a without using bond k ?
        seen = [False] * n
        stack = [a]
        seen[a] = True
        found = False
        while stack:
            x = stack.pop()
            if x == b:
                found = True
                break
            for (y, _, kk) in adj[x]:
                if kk != k and not seen[y]:
                    seen[y] = True
                    stack.append(y)
        inRing[k] = found
    return inRing


def components(n, adj):
    """connected components, each a list of atom indices in ascending order
    (MolOps.cpp getMolFrags: fragment atoms keep original relative order)."""
    comp = [-1] * n
    frags = []
    for s in range(n):
        if comp[s] != -1:
            continue
        c = len(frags)
        comp[s] = c
        stack = [s]
        members = []
        while stack:
            x = stack.pop()
            members.append(x)
            for (y, _, _) in adj[x]:
                if comp[y] == -1:
                    comp[y] = c
                    stack.append(y)
        frags.append(sorted(members))
    return frags


# ---------------------------------------------------------------------------
# ranking: Canon::rankMolAtoms with includeChirality=false,
# includeIsotopes=false, includeAtomMaps=true (no maps present),
# includeChiralPresence=false, includeStereoGroups=false   (SmilesWrite.cpp:632-647)
# ---------------------------------------------------------------------------
class Ranker:
    def __init__(self, Z, charge, nH, adj, atomInRing, atomMultiRing):
        self.n = len(Z)
        self.Z = Z
        self.charge = charge
        self.nH = nH
        self.adj = adj
        self.deg = [len(adj[i]) for i in range(self.n)]
        self.inRing = atomInRing           # numAtomRings(i) > 0
        self.multiRing = atomMultiRing     # numAtomRings(i) > 1
        self.index = [0] * self.n          # canon_atom::index (current class)
        # canon_atom::bonds : list of [bondType, nbrIdx]; nbrSymClass is looked
        # up live as self.index[nbr] (new_canon.cpp:719-725)
        self.nbrlist = [[(t, j) for (j, t, _) in adj[i]] for i in range(self.n)]
        self.neighborNum = [[] for _ in range(self.n)]
        self.revisited = [[] for _ in range(self.n)]

    # --- neighbour list of i as (bondType, nbrClass), sorted DESCENDING ----
    # new_canon.cpp:500 (std::sort greater) and 718-741 (insertion sort after
    # refreshing nbrSymClass).  bondholder::compare (new_canon.h:84-113) with
    # includeChirality=false compares: bondType, bondStereo(=0 always),
    # nbrSymClass.  Ties within the list are irrelevant since the compared
    # keys are equal.
    def bondholders(self, i):
        lst = [(t, self.index[j]) for (t, j) in self.nbrlist[i]]
        # insertion sort, descending lexicographic on (bondType, class)
        for a in range(1, len(lst)):
            v = lst[a]
            b = a
            while b > 0 and (v[0] > lst[b - 1][0] or
                             (v[0] == lst[b - 1][0] and v[1] > lst[b - 1][1])):
                lst[b] = lst[b - 1]
                b -= 1
            lst[b] = v
        return lst

    def cmp_bonds(self, i, j):
        bi = self.bondholders(i)
        bj = self.bondholders(j)
        k = 0
        while k < len(bi) and k < len(bj):
            if bi[k][0] != bj[k][0]:
                return -1 if bi[k][0] < bj[k][0] else 1
            if bi[k][1] != bj[k][1]:
                return -1 if bi[k][1] < bj[k][1] else 1
            k += 1
        if len(bi) != len(bj):
            return -1 if len(bi) < len(bj) else 1
        return 0

    # --- AtomCompareFunctor::operator() with df_useNbrs=true ---------------
    # new_canon.h:547-593 -> basecomp new_canon.h:323-518.  With the flags
    # MolToSmiles(isomeric=False) uses, basecomp reduces to:
    #   index, [atom map number: all 0], degree, atomic number,
    #   total H count, formal charge (compared as UNSIGNED, see charge_key)
    # (isotope, chirality, chiral presence, ring stereo all disabled).
    def cmp_atom(self, i, j):
        for (a, b) in ((self.index[i], self.index[j]),
                       (self.deg[i], self.deg[j]),
                       (self.Z[i], self.Z[j]),
                       (self.nH[i], self.nH[j]),
                       (charge_key(self.charge[i]), charge_key(self.charge[j]))):
            if a != b:
                return -1 if a < b else 1
        return self.cmp_bonds(i, j)

    # --- SpecialSymmetryAtomCompareFunctor (new_canon.h:216-274) ----------
    # NB: no basecomp; only called within one partition, so index is equal.
    def cmp_special(self, i, j):
        c = cmp_int_lists(self.neighborNum[i], self.neighborNum[j])
        if c != 0:
            return c
        c = cmp_int_lists(self.revisited[i], self.revisited[j])
        if c != 0:
            return c
        return self.cmp_bonds(i, j)

    # --- compareRingAtomsConcerningNumNeighbors (new_canon.cpp:149-272) ---
    # BFS shells from each ring atom; non-ring atoms are counted but not
    # expanded.  neighborNum = [n1,-1,n2,-1,...]; revisited = per level the
    # sorted multiset of "revisit counts", each level terminated by -1.
    def ring_bfs_invariants(self):
        n = self.n
        for idx in range(n):
            if not self.inRing[idx]:
                continue
            visited = [False] * n
            lastLevel = [False] * n
            curLevel = [False] * n
            neighborNum = []
            revisited = []
            queue = [idx]
            while len(queue) > 0:
                numLevelNbrs = 0
                nextLevel = []
                for nidx in queue:
                    if not self.inRing[nidx]:
                        continue
                    lastLevel[nidx] = True
                    visited[nidx] = True
                    for (j, _, _) in self.adj[nidx]:
                        if not visited[j]:
                            curLevel[j] = True
                            numLevelNbrs += 1
                            visited[j] = True
                            nextLevel.append(j)
                # count, for every atom j in current or last level, how many
                # times it is a neighbour of an atom of nextLevel
                revCount = [0] * n
                touched = []
                for i in nextLevel:
                    for (j, _, _) in self.adj[i]:
                        if curLevel[j] or lastLevel[j]:
                            if revCount[j] == 0:
                                touched.append(j)
                            revCount[j] += 1
                lastLevel = [False] * n
                for i in nextLevel:
                    lastLevel[i] = True
                for i in nextLevel:
                    curLevel[i] = False
                tmp = insertion_sort_ints([revCount[j] for j in touched])
                tmp.append(-1)
                revisited.extend(tmp)
                neighborNum.append(numLevelNbrs)
                neighborNum.append(-1)
                queue = nextLevel
            self.neighborNum[idx] = neighborNum
            self.revisited[idx] = revisited


def charge_key(c):
    """basecomp compares the formal charge through an `unsigned int`
    (new_canon.h:324,410-416), so -1 becomes 2^32-1: the order is
    0 < 1 < 2 < ... < -3 < -2 < -1.  Return that unsigned value."""
    return c if c >= 0 else 4294967296 + c


def cmp_int_lists(a, b):
    """std::vector<int> lexicographic operator< (shorter prefix is smaller)."""
    k = 0
    while k < len(a) and k < len(b):
        if a[k] != b[k]:
            return -1 if a[k] < b[k] else 1
        k += 1
    if len(a) != len(b):
        return -1 if len(a) < len(b) else 1
    return 0


def insertion_sort_ints(xs):
    xs = list(xs)
    for a in range(1, len(xs)):
        v = xs[a]
        b = a
        while b > 0 and xs[b - 1] > v:
            xs[b] = xs[b - 1]
            b -= 1
        xs[b] = v
    return xs


# ---------------------------------------------------------------------------
# hanoi sort (RDGeneral/hanoiSort.h:28-150), literal port.
# A stable merge sort that also groups equal elements: after sorting,
# count[first of a run of equal elements] = run length, count[others] = 0.
# The `changed` shortcut (both unchanged => treat as equal) is semantically
# neutral (see report) but kept for fidelity.
# Buffers are python lists; a "pointer" is (buffer, offset).
# ---------------------------------------------------------------------------
def hanoi(base, b0, nel, temp, t0, count, changed, compar):
    if nel == 1:
        count[base[b0]] = 1
        return False
    if nel == 2:
        n1 = base[b0]
        n2 = base[b0 + 1]
        stat = compar(n1, n2) if (changed[n1] or changed[n2]) else 0
        if stat == 0:
            count[n1] = 2
            count[n2] = 0
        elif stat < 0:
            count[n1] = 1
            count[n2] = 1
        else:
            count[n1] = 1
            count[n2] = 1
            base[b0] = n2
            base[b0 + 1] = n1
        return False

    n1 = nel // 2
    n2 = nel - n1
    # sub-results land either in base or temp
    if hanoi(base, b0, n1, temp, t0, count, changed, compar):
        if hanoi(base, b0 + n1, n2, temp, t0 + n1, count, changed, compar):
            s2 = (temp, t0 + n1)
        else:
            s2 = (base, b0 + n1)
        result = False
        ptr = (base, b0)
        s1 = (temp, t0)
    else:
        if hanoi(base, b0 + n1, n2, temp, t0 + n1, count, changed, compar):
            s2 = (temp, t0 + n1)
        else:
            s2 = (base, b0 + n1)
        result = True
        ptr = (temp, t0)
        s1 = (base, b0)

    def move(dst, src, k):  # memmove
        dbuf, di = dst
        sbuf, si = src
        chunk = sbuf[si:si + k]
        dbuf[di:di + k] = chunk
        return (dbuf, di + k)

    while True:
        e1 = s1[0][s1[1]]
        e2 = s2[0][s2[1]]
        stat = compar(e1, e2) if (changed[e1] or changed[e2]) else 0
        len1 = count[e1]
        len2 = count[e2]
        if stat == 0:
            count[e1] = len1 + len2
            count[e2] = 0
            ptr = move(ptr, s1, len1)
            n1 -= len1
            if n1 == 0:
                if ptr != s2:
                    move(ptr, s2, n2)
                return result
            s1 = (s1[0], s1[1] + len1)
            ptr = move(ptr, s2, len2)
            n2 -= len2
            if n2 == 0:
                move(ptr, s1, n1)
                return result
            s2 = (s2[0], s2[1] + len2)
        elif stat < 0:
            ptr = move(ptr, s1, len1)
            n1 -= len1
            if n1 == 0:
                if ptr != s2:
                    move(ptr, s2, n2)
                return result
            s1 = (s1[0], s1[1] + len1)
        else:
            ptr = move(ptr, s2, len2)
            n2 -= len2
            if n2 == 0:
                move(ptr, s1, n1)
                return result
            s2 = (s2[0], s2[1] + len2)


def simple_group_sort(seg, count, compar):
    """Equivalent simpler alternative to hanoi (for Lean): stable insertion
    sort by compar, then mark runs of equal elements in `count`."""
    seg = list(seg)
    for a in range(1, len(seg)):
        v = seg[a]
        b = a
        while b > 0 and compar(seg[b - 1], v) > 0:
            seg[b] = seg[b - 1]
            b -= 1
        seg[b] = v
    s = 0
    while s < len(seg):
        e = s + 1
        while e < len(seg) and compar(seg[s], seg[e]) == 0:
            e += 1
        count[seg[s]] = e - s
        for q in range(s + 1, e):
            count[seg[q]] = 0
        s = e
    return seg


USE_HANOI = True


class Partitioner:
    """order / count / next / changed / activeset machinery
    (new_canon.cpp:96-147, new_canon.h:727-887)."""

    def __init__(self, R):
        self.R = R
        n = R.n
        self.n = n
        # CreateSinglePartition (new_canon.cpp:96-108)
        for i in range(n):
            R.index[i] = 0
        self.order = list(range(n))
        self.count = [0] * n
        self.count[0] = n
        self.next = [-2] * n
        self.changed = [1] * n
        self.touched = [0] * n
        self.activeset = -1

    def activate(self):
        # ActivatePartitions (new_canon.cpp:110-147)
        n = self.n
        self.activeset = -1
        for i in range(n):
            self.next[i] = -2
        i = 0
        while i < n:
            j = self.order[i]
            if self.count[j] > 1:
                self.next[j] = self.activeset
                self.activeset = j
                i += self.count[j]
            else:
                i += 1
        for i in range(n):
            self.changed[self.order[i]] = 1

    def refine(self, compar):
        # RefinePartitions (new_canon.h:727-833), mode = true
        R = self.R
        order, count, nxt, changed = self.order, self.count, self.next, self.changed
        symclass = 0
        while self.activeset != -1:
            partition = self.activeset
            self.activeset = nxt[partition]
            nxt[partition] = -2
            ln = count[partition]
            offset = R.index[partition]
            if USE_HANOI:
                temp = [0] * ln
                if hanoi(order, offset, ln, temp, 0, count, changed, compar):
                    for k in range(ln):
                        order[offset + k] = temp[k]
            else:
                seg = simple_group_sort(order[offset:offset + ln], count, compar)
                for k in range(ln):
                    order[offset + k] = seg[k]
            for k in range(ln):
                changed[order[offset + k]] = 0
            first = order[offset]
            for i in range(count[first], ln):
                idx = order[offset + i]
                if count[idx]:
                    symclass = offset + i
                R.index[idx] = symclass
                for (j, _, _) in R.adj[idx]:
                    changed[j] = 1
            # mode == true
            for i in range(count[first], ln):
                idx = order[offset + i]
                for (j, _, _) in R.adj[idx]:
                    self.touched[R.index[j]] = 1
            for ii in range(self.n):
                if self.touched[ii]:
                    p = order[ii]
                    if count[p] > 1 and nxt[p] == -2:
                        nxt[p] = self.activeset
                        self.activeset = p
                    self.touched[ii] = 0

    def break_ties(self, compar):
        # BreakTies (new_canon.h:835-887)
        R = self.R
        order, count, nxt, changed = self.order, self.count, self.next, self.changed
        i = 0
        while i < self.n:
            partition = order[i]
            oldPart = R.index[partition]
            while count[partition] > 1:
                ln = count[partition]
                offset = R.index[partition] + ln - 1
                idx = order[offset]
                R.index[idx] = offset
                count[partition] = ln - 1
                count[idx] = 1
                if R.deg[idx] < 1:
                    continue
                for (j, _, _) in R.adj[idx]:
                    self.touched[R.index[j]] = 1
                    changed[j] = 1
                for ii in range(self.n):
                    if self.touched[ii]:
                        p = order[ii]
                        if count[p] > 1 and nxt[p] == -2:
                            nxt[p] = self.activeset
                            self.activeset = p
                        self.touched[ii] = 0
                self.refine(compar)
            if R.index[partition] != oldPart:
                i -= 1
            i += 1


def rank_atoms(Z, charge, nH, adj, atomInRing, atomMultiRing, use_special=True):
    """Canon::rankMolAtoms -> detail::rankWithFunctor (new_canon.cpp:274-387,
    835-874).  Returns rank[i] in 0..n-1 (all distinct)."""
    R = Ranker(Z, charge, nH, adj, atomInRing, atomMultiRing)
    n = R.n
    if n == 0:
        return []
    P = Partitioner(R)
    P.activate()
    P.refine(R.cmp_atom)
    # (SpecialChiralityAtomCompareFunctor pass skipped: useChirality=false,
    #  new_canon.cpp:325)
    # SpecialSymmetry gate (new_canon.cpp:339-375)
    ties = False
    symRingAtoms = 0
    ringAtoms = 0
    branchingRingAtom = False
    for i in range(n):
        o = P.order[i]
        if R.inRing[o]:
            if P.count[o] > 2:
                symRingAtoms += P.count[o]
            ringAtoms += 1
            if R.multiRing[o] and P.count[o] > 1:
                branchingRingAtom = True
        if P.count[i] == 0:
            ties = True
    # float(sym)/ring > 0.5  <=>  2*sym > ring
    if (use_special and ties and ringAtoms > 0 and 2 * symRingAtoms > ringAtoms
            and branchingRingAtom):
        R.ring_bfs_invariants()
        P.activate()
        P.refine(R.cmp_special)
    P.break_ties(R.cmp_atom)
    rank = [0] * n
    for i in range(n):
        rank[P.order[i]] = R.index[P.order[i]]
    return rank


# ---------------------------------------------------------------------------
# SMILES writing
# ---------------------------------------------------------------------------
def total_valence(atom, bondTypes):
    """Atom::getTotalValence for a NEUTRAL organic-subset atom
    (Atom.cpp:337-415).  Only used by the 'non-standard valence' bracket
    rule.  Works in half-units to stay integral."""
    Z = atom["Z"]
    acc2 = 2 * atom["explicitHs"]
    for t in bondTypes:
        acc2 += 3 if t == AROMATIC else 2 * t
    vl = VALENCE_LIST[Z]
    dv = vl[0]
    if atom["aromatic"] and acc2 > 2 * dv:
        pval = dv
        for v in vl:
            if v == -1 or 2 * v > acc2:
                break
            pval = v
        if acc2 - 2 * pval <= 3:
            acc2 = 2 * pval
    explicitVal = (acc2 + 1) // 2          # round(accum + 0.1)
    implicitHs = atom["totalHs"] - atom["explicitHs"]
    return explicitVal + implicitHs


def atom_needs_bracket(atom, nbrZs, bondTypes):
    # SmilesWrite.cpp:107-153 atomNeedsBracket (isomeric=false)
    Z = atom["Z"]
    if not member(Z, ORGANIC_SUBSET):
        return True
    if atom["charge"] != 0:
        return True
    # (isotope / chirality only when isomeric; no atom maps)
    if atom["radicals"] > 0:
        return True
    if (Z == 7 or Z == 15) and atom["aromatic"] and atom["explicitHs"] > 0:
        return True
    if atom["totalHs"] > 0 and total_valence(atom, bondTypes) != VALENCE_LIST[Z][0]:
        return True
    for z in nbrZs:                       # bonded to a metal
        if not member(z, NON_METALS):
            return True
    return False


def atom_smiles(atom, nbrZs, bondTypes):
    # SmilesWrite.cpp:157-252 GetAtomSmiles
    Z = atom["Z"]
    symb = SYMBOLS[Z]
    br = atom_needs_bracket(atom, nbrZs, bondTypes)
    if atom["aromatic"] and member(Z, AROMATIC_LOWER):
        symb = symb[0].lower() + symb[1:]
    s = "[" if br else ""
    s += symb
    if br:
        h = atom["totalHs"]
        if h > 0:
            s += "H"
            if h > 1:
                s += str(h)
        fc = atom["charge"]
        if fc > 0:
            s += "+"
            if fc > 1:
                s += str(fc)
        elif fc < 0:
            if fc < -1:
                s += str(fc)        # e.g. "-2"
            else:
                s += "-"
        s += "]"
    return s


def bond_smiles(t, a1, a2):
    # SmilesWrite.cpp:254-364 GetBondSmiles (no kekule, no explicit bonds,
    # no bond directions in non-isomeric output).
    aromatic = a1["aromatic"] and a2["aromatic"] and (a1["Z"] != 0 or a2["Z"] != 0)
    if t == SINGLE:
        return "-" if aromatic else ""      # single bond is never isAromatic here
    if t == DOUBLE:
        return "="
    if t == TRIPLE:
        return "#"
    if t == AROMATIC:
        return "" if aromatic else ":"
    return "~"


def fragment_smiles(atoms, bonds, adj, inRingBond, rank, start):
    """Canon.cpp:1146-1174 canonicalDFSTraversal + 1382-1442 canonicalizeFragment
    + SmilesWrite.cpp:366-488 FragmentSmilesConstruct.
    Atoms/adj here are indexed by fragment-local indices."""
    n = len(atoms)
    WHITE, GREY, BLACK = 0, 1, 2

    # ---- pass 1: dfsFindCycles (Canon.cpp:860-984) ----
    colors = [WHITE] * n
    ringClosures = [[] for _ in range(n)]   # list of bond indices per atom

    def possibles_sorted(lst):
        # std::sort on the int key (Canon.cpp:357,948,1102); keys are unique
        for a in range(1, len(lst)):
            v = lst[a]
            b = a
            while b > 0 and lst[b - 1][0] > v[0]:
                lst[b] = lst[b - 1]
                b -= 1
            lst[b] = v
        return lst

    def find_cycles(a, inBond):
        colors[a] = GREY
        poss = []
        for (o, t, k) in adj[a]:
            if k == inBond:
                continue
            r = rank[o]
            if colors[o] == GREY:
                r = r - (MAX_BONDTYPE + 1) * MAX_NATOMS * MAX_NATOMS
                r = r + (MAX_BONDTYPE - t) * MAX_NATOMS
            elif inRingBond[k]:
                r = r + (MAX_BONDTYPE - t) * MAX_NATOMS * MAX_NATOMS
            poss.append((r, o, k))
        poss = possibles_sorted(poss)
        for (_, o, k) in poss:
            if colors[o] == WHITE:
                find_cycles(o, k)
            elif colors[o] == GREY:
                ringClosures[o].append(k)
                ringClosures[a].append(k)
        colors[a] = BLACK

    find_cycles(start, -1)

    # ---- pass 2: dfsBuildStack (Canon.cpp:986-1144) ----
    colors = [WHITE] * n
    cyclesAvailable = [True] * 1024           # MAX_CYCLES
    bondRingIdx = [0] * len(bonds)            # _TraversalRingClosureBond prop (0 = unset)
    stack = []                                # ("A",atom) ("B",bondType,leftAtom,otherAtom) ("R",idx) ("(",) (")",)

    def build(a, inBond):
        seenFromHere = [False] * n
        seenFromHere[a] = True
        stack.append(("A", a))
        colors[a] = GREY
        ringsClosed = []
        for k in ringClosures[a]:
            o = bond_other(k, a)
            seenFromHere[o] = True
            if bondRingIdx[k] != 0:
                # closing: bond symbol then digit
                stack.append(("B", bond_type(k), a, o))
                stack.append(("R", bondRingIdx[k]))
                ringsClosed.append(bondRingIdx[k] - 1)
            else:
                low = 0
                while not cyclesAvailable[low]:
                    low += 1
                cyclesAvailable[low] = False
                bondRingIdx[k] = low + 1
                stack.append(("R", low + 1))
        for r in ringsClosed:
            cyclesAvailable[r] = True
        poss = []
        for (o, t, k) in adj[a]:
            if k == inBond:
                continue
            if colors[o] != WHITE or seenFromHere[o]:
                continue
            r = rank[o]
            if inRingBond[k]:
                r = r + (MAX_BONDTYPE - t) * MAX_NATOMS * MAX_NATOMS
            poss.append((r, o, k))
        poss = possibles_sorted(poss)
        for p in range(len(poss)):
            _, o, k = poss[p]
            if colors[o] != WHITE:
                continue
            last = (p + 1 == len(poss))
            if not last:
                stack.append(("(",))
            stack.append(("B", bond_type(k), a, o))
            build(o, k)
            if not last:
                stack.append((")",))
        colors[a] = BLACK

    def bond_other(k, x):
        return bonds[k][1] if bonds[k][0] == x else bonds[k][0]

    def bond_type(k):
        return bonds[k][2]

    build(start, -1)

    # ---- token emission (SmilesWrite.cpp:409-487) ----
    out = ""
    ringMapKeys = []      # ringClosureMap: parallel lists key -> value
    ringMapVals = []
    toErase = []
    for e in stack:
        if e[0] == "A":
            for r in toErase:
                p = ringMapKeys.index(r)
                del ringMapKeys[p]
                del ringMapVals[p]
            toErase = []
            a = e[1]
            nbrZs = [atoms[o]["Z"] for (o, _, _) in adj[a]]
            bts = [t for (_, t, _) in adj[a]]
            out += atom_smiles(atoms[a], nbrZs, bts)
        elif e[0] == "B":
            out += bond_smiles(e[1], atoms[e[2]], atoms[e[3]])
        elif e[0] == "R":
            ridx = e[1]
            if member(ridx, ringMapKeys):
                val = ringMapVals[ringMapKeys.index(ridx)]
                toErase.append(ridx)
            else:
                val = 1
                while member(val, ringMapVals):
                    val += 1
                ringMapKeys.append(ridx)
                ringMapVals.append(val)
            if val < 10:
                out += str(val)
            elif val < 100:
                out += "%" + str(val)
            else:
                out += "%(" + str(val) + ")"
        elif e[0] == "(":
            out += "("
        else:
            out += ")"
    return out


def canonical_smiles(atoms, bonds, multi_ring=None, use_special=True):
    """Chem.MolToSmiles(mol, isomericSmiles=False).

    multi_ring: optional list[bool], RDKit RingInfo numAtomRings(i) > 1 for
    the ring info the fragment carries (see report: symmetrized SSSR for a
    single-fragment molecule, fastFindRings for multi-fragment ones).  If
    None, the proxy 'atom has >= 3 ring bonds' is used."""
    bonds = [(a, b, BT_FROM_NAME[t] if isinstance(t, str) else t) for (a, b, t) in bonds]
    n = len(atoms)
    if n == 0:
        return ""
    adj = build_adj(n, bonds)
    frags = components(n, adj)
    smis = []
    for fr in frags:
        # fragment-local renumbering (ascending original index) and bonds in
        # original bond order (SmilesWrite.cpp:507-534)
        loc = [-1] * n
        for i in range(len(fr)):
            loc[fr[i]] = i
        fatoms = [atoms[i] for i in fr]
        fbonds = []
        for (a, b, t) in bonds:
            if loc[a] >= 0 and loc[b] >= 0:
                fbonds.append((loc[a], loc[b], t))
        m = len(fr)
        fadj = build_adj(m, fbonds)
        inRingBond = ring_bonds(m, fbonds, fadj)
        atomInRing = [False] * m
        nRingBonds = [0] * m
        for k in range(len(fbonds)):
            if inRingBond[k]:
                a, b, _ = fbonds[k]
                atomInRing[a] = True
                atomInRing[b] = True
                nRingBonds[a] += 1
                nRingBonds[b] += 1
        if multi_ring is None:
            fmulti = [nRingBonds[i] >= 3 for i in range(m)]
        else:
            fmulti = [multi_ring[i] for i in fr]
        rank = rank_atoms([x["Z"] for x in fatoms], [x["charge"] for x in fatoms],
                          [x["totalHs"] for x in fatoms], fadj, atomInRing,
                          fmulti, use_special)
        # start atom = lowest rank (SmilesWrite.cpp:671-678)
        start = 0
        for i in range(m):
            if rank[i] < rank[start]:
                start = i
        smis.append(fragment_smiles(fatoms, fbonds, fadj, inRingBond, rank, start))
    # sort fragment strings bytewise, join with '.' (SmilesWrite.cpp:700-730)
    smis = insertion_sort_strs(smis)
    return ".".join(smis)


def insertion_sort_strs(xs):
    xs = list(xs)
    for a in range(1, len(xs)):
        v = xs[a]
        b = a
        while b > 0 and xs[b - 1] > v:
            xs[b] = xs[b - 1]
            b -= 1
        xs[b] = v
    return xs


# ---------------------------------------------------------------------------
# NOTES ON ORDER DEPENDENCE (verified empirically, see report)
#  * Bond index order / bond direction: no influence.  Neighbour lists are
#    only used (a) as sets (changed/touched flags, BFS shells), (b) sorted by
#    (bondType, class) where equal keys are indistinguishable, (c) sorted by
#    the DFS key whose values are unique per neighbour.  The ring-closure
#    order at an atom (ringClosures[a]) is produced by the DFS, i.e. by ranks.
#    GetBondSmiles only looks at whether BOTH ends are aromatic (symmetric).
#  * Atom index order: influences only which of several still-tied atoms
#    BreakTies promotes (the last one in the partition's `order` slice, whose
#    order descends from the initial identity order through stable sorts).
#    For automorphic atoms this cannot change the string.  Feed atoms in
#    SMILES input order (= RDKit's order) to match RDKit exactly.
# ---------------------------------------------------------------------------
