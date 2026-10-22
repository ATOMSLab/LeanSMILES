"""Pure-Python reference of RDKit's default Morgan generator (radius R, fpSize).
RDKit used ONLY to read the graph / per-atom properties."""
M = 0xFFFFFFFF

def hc(seed, h):                      # gboost::hash_combine, 32-bit (hash.hpp:218)
    return (seed ^ ((h + 0x9e3779b9 + ((seed << 6) & M) + (seed >> 2)) & M)) & M

def hash_vec(vals):                   # gboost::hash<vector<uint32>> = hash_range, seed 0
    s = 0
    for v in vals:
        s = hc(s, v & M)              # hash_value(uint) = identity; negatives wrap mod 2^32
    return s

def hash_pair(a, b):                  # hash_value(std::pair) (hash.hpp:286)
    return hc(hc(0, a & M), b & M)

def atom_invariants(atoms):
    """atoms: list of dicts with Z, total_degree, total_hs, charge, delta_mass, in_ring"""
    out = []
    for a in atoms:
        comp = [a['Z'], a['total_degree'], a['total_hs'], a['charge'], a['delta_mass']]
        if a['in_ring']:
            comp.append(1)
        out.append(hash_vec(comp))
    return out

def morgan_envs(n_atoms, bonds, inv0, radius):
    """bonds: list of (i, j, bond_type_enum) indexed by bond idx.
    Returns list of (id, atom, layer) in RDKit's env semantics."""
    nbrs = [[] for _ in range(n_atoms)]          # (bond idx, other atom)
    for b, (i, j, _) in enumerate(bonds):
        nbrs[i].append((b, j)); nbrs[j].append((b, i))
    cur = list(inv0)
    res = [(cur[i], i, 0) for i in range(n_atoms)]            # radius-0 ids always included
    atom_nb = [frozenset() for _ in range(n_atoms)]           # bond sets, previous round
    round_nb = list(atom_nb)                                  # persists for dead atoms
    seen = set()
    dead = [False] * n_atoms
    for layer in range(radius):
        nxt = [0] * n_atoms                                    # dead atoms -> 0 next round
        this_round = []
        for a in range(n_atoms):
            if dead[a]:
                continue
            if not nbrs[a]:
                dead[a] = True; continue
            env = set(round_nb[a]); pairs = []
            for b, o in nbrs[a]:
                env.add(b); env |= atom_nb[o]
                pairs.append((bonds[b][2], cur[o]))
            round_nb[a] = frozenset(env)
            pairs.sort()                                        # (int32 bondtype, uint32 id)
            h = hc(layer, cur[a])                               # seed = layer index!
            for p in pairs:
                h = hc(h, hash_pair(*p))
            nxt[a] = h
            this_round.append((round_nb[a], h, a))
        # dedup: among identical bond sets keep smallest (id, atomIdx); drop sets seen earlier
        this_round.sort(key=lambda t: (t[1], t[2]))
        for env, h, a in this_round:
            if env not in seen:
                res.append((h, a, layer + 1)); seen.add(env)
            else:
                dead[a] = True
        cur = nxt
        atom_nb = list(round_nb)
    return res

def from_rdkit(mol):
    from rdkit.Chem import GetPeriodicTable
    pt = GetPeriodicTable()
    ri = mol.GetRingInfo()
    atoms = [dict(Z=a.GetAtomicNum(), total_degree=a.GetTotalDegree(),
                  total_hs=a.GetTotalNumHs(includeNeighbors=True),
                  charge=a.GetFormalCharge(),
                  delta_mass=int(a.GetMass() - pt.GetAtomicWeight(a.GetAtomicNum())),
                  in_ring=ri.NumAtomRings(a.GetIdx()) > 0) for a in mol.GetAtoms()]
    bonds = [(b.GetBeginAtomIdx(), b.GetEndAtomIdx(), int(b.GetBondType())) for b in mol.GetBonds()]
    return atoms, bonds

def morgan(mol, radius=2, fpSize=2048):
    atoms, bonds = from_rdkit(mol)
    envs = morgan_envs(len(atoms), bonds, atom_invariants(atoms), radius)
    sparse = {}
    for h, _, _ in envs:
        sparse[h] = sparse.get(h, 0) + 1
    bits = sorted({h % fpSize for h in sparse})
    return sparse, bits
