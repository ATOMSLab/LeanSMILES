"""
aromaticity_ref.py -- pure-Python reference for the part of RDKit's
sanitizeMol (Release_2026_09_1) that turns an *as-parsed* SMILES graph
(Chem.MolFromSmiles(s, sanitize=False)) into RDKit's final graph:
bond types, atom aromatic flags, formal charges, total H counts.

Pipeline (MolOps.cpp:604-716, sanitizeMol):
  1. cleanUp                 MolOps.cpp:315  (nitrogens / P / halogens)
  2. updatePropertyCache     MolOps.cpp:627  -> total H frozen (input)
  3. Kekulize                Kekulize.cpp     (kekulizeForSanitize, MolOps.cpp:597;
                                               canonical=false -> atom ranks = indices)
  4. symmetrizeSSSR          MolOps.cpp:646 -> FindRings.cpp:1085
                             (non-legacy default = RDL "relevant cycles")
  5. assignRadicals          MolOps.cpp:437
  6. setAromaticity DEFAULT  Aromaticity.cpp:1143 -> aromaticityHelper :839
  (conjugation/hybridization/chirality do not change our outputs.)

Note: the Lean port (LeanSMILES/Canonical/Sanitize.lean) goes further than this reference
in three places found by fuzzing with broken SMILES: the strict valence checks
(after cleanUp and at the very end), H counts as RDKit's aromaticity sees them
(explicit + cached implicit, refreshed for GitHub #141 atoms), and the final H
recount with adjustHs. On normal molecules (all test sets in verify.py) the
results are identical; they differ only for odd inputs such as `C=oC` or
`[nH]=C`.

Everything is small-integer / boolean logic.  Valences are kept in
*half units* (SINGLE=2, DOUBLE=4, TRIPLE=6, AROMATIC=3) so that RDKit's
double arithmetic (aromatic bond = 1.5) is exact.

Data model (plain lists, index = RDKit atom/bond index):
  atom: dict Z, chg, arom (bool), nexpH (bracket H count), noImpl (bool),
             totH (frozen total H), nrad
  bond: dict a, b, t ('S','D','T','A'), arom (bool)
Neighbour order of an atom = order of its bonds by bond index (this is
RDKit's adjacency order; checked in the verification script).
"""

S, D, T, A = 'S', 'D', 'T', 'A'
HALF = {S: 2, D: 4, T: 6, A: 3}           # Bond::getValenceContrib * 2

# ---------------------------------------------------------------------------
# Periodic table subset (atomic_data.cpp): Z -> (defaultValence, valenceList, nOuterElecs)
# ---------------------------------------------------------------------------
PT = {
    1: (1, [1], 1), 2: (0, [0], 2), 3: (1, [1, -1], 1), 4: (2, [2], 2),
    5: (3, [3], 3), 6: (4, [4], 4), 7: (3, [3], 5), 8: (2, [2], 6),
    9: (1, [1], 7), 10: (0, [0], 8), 11: (1, [1, -1], 1), 12: (2, [2, -1], 2),
    13: (3, [3], 3), 14: (4, [4], 4), 15: (3, [3, 5], 5), 16: (2, [2, 4, 6], 6),
    17: (1, [1], 7), 18: (0, [0], 8), 19: (1, [1, -1], 1), 20: (2, [2, -1], 2),
    31: (3, [3], 3), 32: (4, [4], 4), 33: (3, [3, 5], 5), 34: (2, [2, 4, 6], 6),
    35: (1, [1], 7), 36: (0, [0], 8), 49: (3, [3], 3), 50: (2, [2, 4], 4),
    51: (3, [3, 5], 5), 52: (2, [2, 4, 6], 6), 53: (1, [1, 3, 5], 7),
    54: (0, [0, 2, 4, 6], 8),
}
def dval(z): return PT[z][0]
def vlist(z): return PT[z][1]
def nouter(z): return PT[z][2]

# Atom.cpp:58 isEarlyAtom (subset of the table that matters here)
EARLY = {3, 4, 5, 11, 12, 13, 19, 20, 21, 22, 30, 31, 32, 37, 38, 39, 40, 41,
         48, 49, 50, 51, 55, 56, 80, 81, 82, 83}

def more_electronegative(z1, z2):          # PeriodicTable.h:304
    n1, n2 = nouter(z1), nouter(z2)
    if n1 > n2:
        return True
    return n1 == n2 and z1 < z2

# ---------------------------------------------------------------------------
# small graph helpers
# ---------------------------------------------------------------------------
def atom_bonds(bonds, i):
    """bond indices incident to atom i, in bond-index (= RDKit adjacency) order"""
    return [k for k in range(len(bonds)) if bonds[k]['a'] == i or bonds[k]['b'] == i]

def other(bd, i):
    return bd['b'] if bd['a'] == i else bd['a']

def degree(bonds, i):                      # Atom::getDegree (explicit graph nbrs)
    return len(atom_bonds(bonds, i))

def bond_between(bonds, i, j):
    for k in range(len(bonds)):
        if (bonds[k]['a'] == i and bonds[k]['b'] == j) or (bonds[k]['a'] == j and bonds[k]['b'] == i):
            return k
    return -1

def calc_explicit_valence(atoms, bonds, i):
    """Atom.cpp:350 calculateExplicitValence(strict=false). Returns an int."""
    at = atoms[i]
    acc2 = sum(HALF[bonds[k]['t']] for k in atom_bonds(bonds, i)) + 2 * at['nexpH']
    eff = at['Z'] - at['chg']                         # getEffectiveAtomicNum
    if eff < 0: eff = 0
    dv = dval(eff); vals = vlist(eff)
    if acc2 > 2 * dv and at['arom']:                  # Atom.cpp:369
        pval = dv
        for v in vals:
            if v == -1: break
            if 2 * v > acc2: break
            pval = v
        if acc2 - 2 * pval <= 3:                      # "within 1.5"
            acc2 = 2 * pval
    return (acc2 + 1) // 2                            # round(accum + 0.1)

# ---------------------------------------------------------------------------
# 1. cleanUp  (MolOps.cpp:315)
# ---------------------------------------------------------------------------
def clean_up(atoms, bonds):
    # nitrogensCleanup  MolOps.cpp:51-136
    consider = []
    for i in range(len(atoms)):
        at = atoms[i]
        if at['Z'] != 7 or at['chg'] != 0:            # :63-72 neutral N only
            continue
        if calc_explicit_valence(atoms, bonds, i) != 5:   # :78
            continue
        consider.append(i)
        for k in atom_bonds(bonds, i):                # :88-100 first =O (neutral)
            j = other(bonds[k], i)
            if atoms[j]['Z'] == 8 and atoms[j]['chg'] == 0 and bonds[k]['t'] == D:
                bonds[k]['t'] = S
                at['chg'] = 1
                atoms[j]['chg'] = -1
                break
    for i in consider:                                # :111-135  N#N -> N=[N+]=[N-]
        for k in atom_bonds(bonds, i):
            j = other(bonds[k], i)
            if atoms[j]['Z'] == 7 and atoms[j]['chg'] == 0 and bonds[k]['t'] == T:
                bonds[k]['t'] = D
                atoms[i]['chg'] = 1
                atoms[j]['chg'] = -1
                break
    for i in range(len(atoms)):                       # :317-329
        z = atoms[i]['Z']
        if z == 15:
            _phosphorus_cleanup(atoms, bonds, i)
        elif z in (17, 35, 53):
            _halogen_cleanup(atoms, bonds, i)

def _phosphorus_cleanup(atoms, bonds, i):             # MolOps.cpp:138
    at = atoms[i]
    if at['chg'] != 0:
        return
    if calc_explicit_valence(atoms, bonds, i) == 5 and degree(bonds, i) == 3:
        dbl_o = -1; o_atom = -1; dbl_cn = False
        for k in atom_bonds(bonds, i):
            j = other(bonds[k], i)
            if atoms[j]['Z'] == 8 and atoms[j]['chg'] == 0 and bonds[k]['t'] == D:
                dbl_o = k; o_atom = j
            elif atoms[j]['Z'] in (6, 7) and degree(bonds, j) >= 2 and bonds[k]['t'] == D:
                dbl_cn = True
        if dbl_cn and dbl_o >= 0:
            atoms[o_atom]['chg'] = -1
            bonds[dbl_o]['t'] = S
            at['chg'] = 1

def _halogen_cleanup(atoms, bonds, i):                # MolOps.cpp:182
    at = atoms[i]
    ev = calc_explicit_valence(atoms, bonds, i)
    if at['chg'] == 0 and ev in (3, 5, 7):
        if all(atoms[other(bonds[k], i)]['Z'] == 8 for k in atom_bonds(bonds, i)):
            fc = 0
            for k in atom_bonds(bonds, i):
                if bonds[k]['t'] == D:
                    bonds[k]['t'] = S
                    fc += 1
                    atoms[other(bonds[k], i)]['chg'] = -1
            at['chg'] = fc

# ---------------------------------------------------------------------------
# 4. Ring perception: RDL relevant cycles (FindRings.cpp:1099-1108)
#    A cycle is relevant iff it is not a GF(2) sum of strictly shorter cycles.
#    Relevant cycles are geodesic, so every one is found as
#    root r + two vertex-disjoint shortest paths closed by an edge (odd)
#    or by a common vertex (even)   (Vismara 1997).
# ---------------------------------------------------------------------------
def _bfs(adj, n, r):
    d = [-1] * n; d[r] = 0; q = [r]; h = 0
    while h < len(q):
        u = q[h]; h += 1
        for v in adj[u]:
            if d[v] < 0:
                d[v] = d[u] + 1; q.append(v)
    return d

def _all_shortest_paths(adj, d, r, v, memo):
    if v in memo: return memo[v]
    if v == r:
        res = [[r]]
    else:
        res = []
        for u in adj[v]:                             # predecessors
            if d[u] >= 0 and d[u] == d[v] - 1:
                for p in _all_shortest_paths(adj, d, r, u, memo):
                    res.append(p + [v])
    memo[v] = res
    return res

def relevant_cycles(n, bonds):
    adj = [[] for _ in range(n)]
    for bd in bonds:
        adj[bd['a']].append(bd['b']); adj[bd['b']].append(bd['a'])
    cands = {}                                       # bondmask -> atom cycle
    def add(cyc):
        mask = 0
        for t in range(len(cyc)):
            mask |= 1 << bond_between(bonds, cyc[t], cyc[(t + 1) % len(cyc)])
        if mask not in cands:
            cands[mask] = cyc
    for r in range(n):
        d = _bfs(adj, n, r); memo = {}
        for x in range(n):
            if d[x] <= 0: continue
            # odd cycles: edge (x,y), d(x)=d(y)
            for y in adj[x]:
                if y > x and d[y] == d[x]:
                    for P in _all_shortest_paths(adj, d, r, x, memo):
                        for Q in _all_shortest_paths(adj, d, r, y, memo):
                            if len(set(P[1:]) & set(Q[1:])) == 0:
                                add(P + Q[::-1][:-1])
            # even cycles: vertex p=x with two predecessors q1<q2
            preds = [u for u in adj[x] if d[u] == d[x] - 1]
            for a in range(len(preds)):
                for b in range(a + 1, len(preds)):
                    if d[x] - 1 == 0: continue        # would be a 2-cycle
                    for P in _all_shortest_paths(adj, d, r, preds[a], memo):
                        for Q in _all_shortest_paths(adj, d, r, preds[b], memo):
                            if len(set(P[1:]) & set(Q[1:])) == 0:
                                add(P + [x] + Q[::-1][:-1])
    # GF(2) relevance test, strictly-shorter basis
    order = sorted(cands.keys(), key=lambda m: (bin(m).count('1'), sorted(cands[m])))
    basis = []                                       # list of (pivotbit, vec)
    def reduce(v):
        for (p, b) in basis:
            if v >> p & 1: v ^= b
        return v
    res = []; i = 0
    while i < len(order):
        L = bin(order[i]).count('1'); j = i
        group = []
        while j < len(order) and bin(order[j]).count('1') == L:
            group.append(order[j]); j += 1
        newvecs = []
        for m in group:
            if reduce(m) != 0:
                res.append(cands[m]); newvecs.append(m)
        for m in newvecs:                            # extend basis after the group
            v = reduce(m)
            if v:
                p = v.bit_length() - 1
                basis.append((p, v))
                basis.sort(key=lambda pb: -pb[0])
        i = j
    return res          # atom cycles, sorted by (size, sorted atoms)

def ring_bonds(bonds, ring):                         # RingUtils::convertToBonds
    return [bond_between(bonds, ring[t], ring[(t + 1) % len(ring)]) for t in range(len(ring))]

def _components(nr, neigh):                          # RingUtils::pickFusedRings
    seen = [False] * nr; comps = []
    for s in range(nr):
        if seen[s]: continue
        comp = []; stack = [s]; seen[s] = True
        while stack:
            u = stack.pop(); comp.append(u)
            for v in neigh[u]:
                if not seen[v]:
                    seen[v] = True; stack.append(v)
        comps.append(sorted(comp))
    return comps

def _neighbor_map(brings, max_size, max_overlap):    # Aromaticity.cpp:117
    nr = len(brings); neigh = [[] for _ in range(nr)]
    for i in range(nr):
        if max_size and len(brings[i]) > max_size: continue
        for j in range(i + 1, nr):
            if max_size and len(brings[j]) > max_size: continue
            inter = len(set(brings[i]) & set(brings[j]))
            if inter > 0 and (not max_overlap or inter <= max_overlap):
                neigh[i].append(j); neigh[j].append(i)
    return neigh

# ---------------------------------------------------------------------------
# 3. Kekulize  (Kekulize.cpp)
# ---------------------------------------------------------------------------
class KekulizeError(Exception):
    pass

def _mark_dbond_cands(atoms, bonds, all_atms, ev0, cands, done):
    """Kekulize.cpp:63 markDbondCands (no dummy atoms supported)"""
    if not any(atoms[i]['arom'] for i in all_atms):  # :73-84
        return
    in_all = set(all_atms)
    make_single = []
    for i in all_atms:
        at = atoms[i]
        if not at['arom']:                           # :105-108
            done.append(i)
            continue
        sbo = 0; n_ignore = 0
        for k in atom_bonds(bonds, i):               # :113-135
            bd = bonds[k]
            if bd['arom'] and bd['t'] in (S, D, A):
                sbo += 1; make_single.append(k)
            else:
                c = (HALF[bd['t']] + 1) // 2         # lround(contrib)
                sbo += c
                if c == 0: n_ignore += 1
        z = at['Z']
        impl = at['totH'] - at['nexpH']
        sbo += at['totH']                            # :151
        dv = dval(z); chrg = at['chg']
        if z in EARLY: chrg = -chrg                  # :154
        if z == 6 and chrg > 0: chrg = -chrg         # :158
        dv += chrg
        tbo = ev0[i] + impl                          # getTotalValence (cached)
        nrad = at['nrad']
        tdeg = degree(bonds, i) + impl - n_ignore
        vl = vlist(z); vi = 1
        while tbo > dv and vi < len(vl) and vl[vi] > 0:   # :169
            dv = vl[vi] + chrg; vi += 1
        if (tbo == 5 and sbo == 4 and dv == 3 and tdeg == 3 and nrad == 0
                and chrg == 0 and at['totH'] == 0 and z in (7, 15, 33)):
            dv = 5                                   # :176 aromatic N-oxide
        if tdeg + nrad >= dv:                        # :191
            continue
        if dv == sbo + 1 + nrad:                     # :199
            cands[i] = True
        elif nrad == 0 and at['noImpl'] and dv == sbo + 2:
            cands[i] = True
    for k in make_single:                            # :213
        bonds[k]['t'] = S

def _back_track(bonds, last_opt, done, astack, cands, adds):
    """Kekulize.cpp:24 backTrack"""
    pos = done.index(last_opt)
    tdone = done[:pos]
    for a in reversed(done[pos:]):                   # push back, lastOpt ends at front
        astack.insert(0, a)
    for k in range(len(bonds)):
        if adds[k]:
            a1, a2 = bonds[k]['a'], bonds[k]['b']
            if a1 not in tdone and a2 not in tdone:
                adds[k] = False
                bonds[k]['t'] = S
                cands[a1] = True; cands[a2] = True
    done[:] = tdone

def _kekulize_worker(atoms, bonds, all_atms, cands, done, max_bt=100):
    """Kekulize.cpp:217 kekulizeWorker, canonical=false => rank = index,
    no wedge bonds."""
    adds = [False] * len(bonds)
    local_added = [False] * len(bonds)
    in_all = set(all_atms)
    sorted_atms = sorted(all_atms)
    astack = []; options = {}; last_opt = -1; btmoves = []; num_bt = 0
    while len(done) < len(sorted_atms) or astack:
        if astack:
            curr = astack.pop(0)
        else:
            curr = -1
            for a in sorted_atms:
                if a not in done:
                    curr = a; break
        assert curr >= 0
        done.append(curr)
        ccand = cands[curr]
        if curr in options:                          # :319
            opts = list(options[curr])
        else:
            opts = []
            nbrs = []
            for k in atom_bonds(bonds, curr):
                j = other(bonds[k], curr)
                if j not in in_all or j in done: continue
                nbrs.append(j)
            nbrs.sort()                              # lessByRank
            lstack = []
            for j in nbrs:
                k = bond_between(bonds, curr, j)
                if j not in astack:
                    lstack.append(j)
                if ccand and cands[j] and bonds[k]['arom']:   # :355
                    opts.append(j)
            astack.extend(lstack)
        if ccand:
            if opts:
                n = opts.pop(0)
                k = bond_between(bonds, curr, n)
                bonds[k]['t'] = D
                cands[curr] = False; cands[n] = False
                adds[k] = True; local_added[k] = True
                if curr in options:                  # :398
                    if not opts:
                        del options[curr]
                        btmoves.pop()
                        last_opt = btmoves[-1] if btmoves else -1
                    else:
                        options[curr] = opts
                else:
                    if opts:
                        last_opt = curr; btmoves.append(curr); options[curr] = opts
            else:                                    # :425 need to backtrack
                if last_opt >= 0 and num_bt < max_bt:
                    _back_track(bonds, last_opt, done, astack, cands, adds)
                    num_bt += 1
                else:
                    for k in range(len(bonds)):
                        if local_added[k]: bonds[k]['t'] = S
                    return False
    return True

def kekulize(atoms, bonds, rings):
    """Kekulize.cpp:563 KekulizeFragment(markAtomsBonds=true, canonical=false)."""
    # cached explicit valence (updatePropertyCache before kekulize). RDKit keeps
    # using this cached value in setAromaticity (getValence / getTotalValence),
    # it is NOT recomputed on the Kekule graph (matters e.g. for arynes c#c).
    ev0 = [calc_explicit_valence(atoms, bonds, i) for i in range(len(atoms))]
    for i in range(len(atoms)):
        atoms[i]['ev'] = ev0[i]
    if not any(bd['arom'] for bd in bonds) and not any(a['arom'] for a in atoms):
        return
    brings = [ring_bonds(bonds, r) for r in rings]
    neigh = _neighbor_map(brings, 0, 0)              # any shared bond
    for comp in _components(len(rings), neigh):      # :727-746 fused systems
        all_atms = []
        for ri in comp:
            for a in rings[ri]:
                if a not in all_atms: all_atms.append(a)
        cands = [False] * len(atoms); done = []
        _mark_dbond_cands(atoms, bonds, all_atms, ev0, cands, done)
        if not _kekulize_worker(atoms, bonds, all_atms, cands, done):
            raise KekulizeError("Can't kekulize mol")
    # markAtomsBonds  :748-777
    ring_atoms = set(a for r in rings for a in r)
    for bd in bonds:
        bd['arom'] = False
    for i in range(len(atoms)):
        at = atoms[i]
        if at['arom']:
            if i not in ring_atoms:
                raise KekulizeError("non-ring atom marked aromatic")
            at['arom'] = False
            if at['Z'] in (7, 15) and at['chg'] == 0 and at['nexpH'] == 1:  # Github #141
                at['noImpl'] = False
                at['nexpH'] = 0          # totH is unchanged (H becomes implicit)
                # updatePropertyCache(false) (Kekulize.cpp:789) on the Kekule graph
                at['ev'] = sum(HALF[bonds[k]['t']] for k in atom_bonds(bonds, i)) // 2
    for bd in bonds:
        if bd['t'] == A:                 # aromatic bond outside every ring system
            raise KekulizeError("aromatic bond left after kekulization")

# ---------------------------------------------------------------------------
# 5. assignRadicals  (MolOps.cpp:437)
# ---------------------------------------------------------------------------
def assign_radicals(atoms, bonds):
    for i in range(len(atoms)):
        at = atoms[i]
        if not at['noImpl'] or at['Z'] == 0:
            continue
        z = at['Z']; chg = at['chg']; no = nouter(z); vals = vlist(z)
        acc2 = sum(HALF[bonds[k]['t']] for k in atom_bonds(bonds, i)) + 2 * at['nexpH']
        tv = acc2 // 2                                # int(accum + 0.1)
        base = 2 if z in (1, 2) else 8
        nr = base - no - tv + chg
        if nr < 0:
            nr = 0
            if len(vals) > 1:
                for v in vals:
                    if v - tv + chg >= 0:
                        nr = v - tv + chg; break
        nr2 = no - tv - chg
        if nr2 >= 0:
            nr = min(nr, nr2)
        at['nrad'] = nr

# ---------------------------------------------------------------------------
# 6. setAromaticity, AROMATICITY_DEFAULT  (Aromaticity.cpp)
# ---------------------------------------------------------------------------
VACANT, ONE, TWO, ONE_OR_TWO, ANY, NONE = 0, 1, 2, 3, 4, 5
MIN_MAX = {ANY: (1, 2), ONE_OR_TWO: (1, 2), ONE: (1, 1), TWO: (2, 2),
           NONE: (0, 0), VACANT: (0, 0)}          # getMinMaxAtomElecs :207
MAX_FUSED_RING_SIZE = 24                          # :23

def _ev(atoms, bonds, i):
    """RDKit's cached explicit valence (Atom::getValence(EXPLICIT)), set in
    kekulize(): computed before kekulization, refreshed only for GitHub #141 atoms."""
    return atoms[i]['ev']

def _non_cyclic_multiple(atoms, bonds, ring_bond_set, i):   # :234
    for k in atom_bonds(bonds, i):
        if k not in ring_bond_set and HALF[bonds[k]['t']] >= 4:
            return other(bonds[k], i)
    return -1

def _cyclic_multiple(atoms, bonds, ring_bond_set, i):       # :251
    for k in atom_bonds(bonds, i):
        if k in ring_bond_set and HALF[bonds[k]['t']] >= 4:
            return True
    return False

def _incident_multiple(atoms, bonds, i):                    # :263
    deg = degree(bonds, i) + atoms[i]['nexpH']
    return _ev(atoms, bonds, i) != deg

def count_atom_elec(atoms, bonds, i):                       # :656 countAtomElec
    at = atoms[i]; z = at['Z']
    dv = dval(z)
    if dv <= 1:
        return -1
    deg = degree(bonds, i) + at['totH']
    if deg > 3:
        return -1
    nlp = nouter(z) - dv
    nlp = max(nlp - at['chg'], 0)
    res = (dv - deg) + nlp - at['nrad']
    if res > 1:
        if _ev(atoms, bonds, i) - degree(bonds, i) > 1:
            res = 1
    return res

def donor_type(atoms, bonds, ring_bond_set, i):             # :581 getAtomDonorTypeArom
    at = atoms[i]
    nelec = count_atom_elec(atoms, bonds, i)
    who = _non_cyclic_multiple(atoms, bonds, ring_bond_set, i)
    if nelec < 0:
        return NONE
    if nelec == 0:
        if who >= 0: return VACANT
        if _cyclic_multiple(atoms, bonds, ring_bond_set, i): return ONE
        return NONE
    if nelec == 1:
        if who >= 0:
            return VACANT if more_electronegative(atoms[who]['Z'], at['Z']) else ONE
        if _incident_multiple(atoms, bonds, i): return ONE
        if at['chg'] == 1: return VACANT
        return NONE
    if who >= 0 and more_electronegative(atoms[who]['Z'], at['Z']):
        nelec -= 1
    return ONE if nelec % 2 == 1 else TWO

def is_atom_cand(atoms, bonds, i, edon):                    # :440 isAtomCandForArom (defaults)
    at = atoms[i]; z = at['Z']
    if z > 18 and z not in (34, 52):
        return False
    if edon == NONE:
        return False
    impl = at['totH'] - at['nexpH']
    if dval(z) > 0 and _ev(atoms, bonds, i) + impl > dval(z - at['chg']):
        return False
    if at['nrad'] and (z != 6 or at['chg']):
        return False
    if _ev(atoms, bonds, i) - degree(bonds, i) > 1:
        nmult = 0
        for k in atom_bonds(bonds, i):
            if bonds[k]['t'] in (D, T): nmult += 1
        if nmult > 1:
            return False
    return True

def _apply_huckel(ring_atoms, edon):                        # :278 applyHuckel
    rlw = 0; rup = 0; nany = 0
    for a in ring_atoms:
        if edon[a] == ANY:
            nany += 1
            if nany > 1: return False
        lo, hi = MIN_MAX[edon[a]]
        rlw += lo; rup += hi
    if rup >= 6:
        for rie in range(rlw, rup + 1):
            if (rie - 2) % 4 == 0:
                return True
        return False
    return rup == 2

def _check_fused(rids, neigh):                              # :97 checkFused
    rset = set(rids); seen = {rids[0]}; stack = [rids[0]]
    while stack:
        u = stack.pop()
        for v in neigh[u]:
            if v in rset and v not in seen:
                seen.add(v); stack.append(v)
    return len(seen) == len(rids)

def _combinations(n, k):            # lexicographic k-subsets of range(n) (nextCombination)
    if k == 0: return [[]]
    out = []
    def rec(start, cur):
        if len(cur) == k:
            out.append(list(cur)); return
        for x in range(start, n):
            cur.append(x); rec(x + 1, cur); cur.pop()
    rec(0, [])
    return out

def _huckel_fused(atoms, bonds, crings, brings, fused, edon, neigh, max_fused=6):
    """Aromaticity.cpp:334 applyHuckelToFused (minRingSize=0)"""
    nrings = len(fused)
    n_ring_bonds = len(set(b for r in fused for b in brings[r]))
    done_bonds = set()
    cur_size = 0
    while True:
        if cur_size == 2 and nrings > 300:
            break
        cur_size += 1
        if cur_size > min(nrings, max_fused) or len(done_bonds) >= n_ring_bonds:
            break
        for comb in _combinations(nrings, cur_size):
            cur = [fused[c] for c in comb]
            if not _check_fused(cur, neigh):
                continue
            cnt = [0] * len(atoms)
            for r in cur:
                for a in crings[r]: cnt[a] += 1
            unon = [a for a in range(len(atoms)) if cnt[a] == 1 or cnt[a] == 2]  # :418 (#2895)
            if _apply_huckel(unon, edon):
                # markAtomsBondsArom :183 - only bonds seen once in the subsystem
                bc = {}
                for r in cur:
                    for b in brings[r]: bc[b] = bc.get(b, 0) + 1
                for b in sorted(bc):
                    if bc[b] == 1:
                        bd = bonds[b]; bd['arom'] = True
                        if bd['t'] in (S, D):
                            bd['t'] = A
                            atoms[bd['a']]['arom'] = True; atoms[bd['b']]['arom'] = True
                        done_bonds.add(b)

def set_aromaticity(atoms, bonds, rings):
    """Aromaticity.cpp:839 aromaticityHelper(minRingSize=0,maxRingSize=0,includeFused=true)"""
    ring_bond_set = set(b for r in rings for b in ring_bonds(bonds, r))
    n = len(atoms)
    acand = [False] * n; seen = [False] * n; edon = [NONE] * n
    crings = []
    for ring in rings:
        sz = len(ring); all_arom = True; all_dummy = True
        for a in ring:
            if atoms[a]['Z'] != 0: all_dummy = False
            if seen[a]:
                if not acand[a]: all_arom = False
                continue
            seen[a] = True
            dt = donor_type(atoms, bonds, ring_bond_set, a)
            # macrocycle ether/thioether rule :871-887
            if dt == TWO and sz >= 9 and atoms[a]['Z'] in (8, 16) and \
               degree(bonds, a) == 2 and atoms[a]['chg'] == 0 and \
               not any(bonds[k]['t'] in (D, T) for k in atom_bonds(bonds, a)):
                dt = NONE
            edon[a] = dt
            acand[a] = is_atom_cand(atoms, bonds, a, dt)
            if not acand[a]: all_arom = False
        if all_arom and not all_dummy:
            crings.append(ring)
    brings = [ring_bonds(bonds, r) for r in crings]
    neigh = _neighbor_map(brings, MAX_FUSED_RING_SIZE, 1)   # :929 share exactly 1 bond
    for fused in _components(len(crings), neigh):
        _huckel_fused(atoms, bonds, crings, brings, fused, edon, neigh, 6)

# ---------------------------------------------------------------------------
# driver
# ---------------------------------------------------------------------------
def sanitize(atoms, bonds):
    """atoms/bonds as described in the module docstring (modified in place).
    Returns (bond types, atom aromatic flags, charges, total H)."""
    clean_up(atoms, bonds)                         # 1
    # 2. totH already frozen in input
    rings = relevant_cycles(len(atoms), bonds)     # ring set (used by 3 and 6)
    kekulize(atoms, bonds, rings)                  # 3
    assign_radicals(atoms, bonds)                  # 5
    set_aromaticity(atoms, bonds, rings)           # 6
    return ([bd['t'] for bd in bonds], [a['arom'] for a in atoms],
            [a['chg'] for a in atoms], [a['totH'] for a in atoms])

def from_rdkit_unsanitized(smiles):
    """The ONLY RDKit use: parse with sanitize=False + UpdatePropertyCache(strict=False)."""
    from rdkit import Chem
    m = Chem.MolFromSmiles(smiles, sanitize=False)
    m.UpdatePropertyCache(strict=False)
    tmap = {Chem.BondType.SINGLE: S, Chem.BondType.DOUBLE: D,
            Chem.BondType.TRIPLE: T, Chem.BondType.AROMATIC: A}
    atoms = [dict(Z=a.GetAtomicNum(), chg=a.GetFormalCharge(), arom=a.GetIsAromatic(),
                  nexpH=a.GetNumExplicitHs(), noImpl=a.GetNoImplicit(),
                  totH=a.GetTotalNumHs(), nrad=a.GetNumRadicalElectrons())
             for a in m.GetAtoms()]
    bonds = [dict(a=b.GetBeginAtomIdx(), b=b.GetEndAtomIdx(), t=tmap[b.GetBondType()],
                  arom=b.GetIsAromatic()) for b in m.GetBonds()]
    return m, atoms, bonds
