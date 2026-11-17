"""How do InChI and LeanSMILES cope with highly symmetric graphs?

Each graph becomes a saturated hydrocarbon (every vertex a carbon, every edge a single
bond). For N random atom renumberings: time InChI (via RDKit) and count distinct InChIs;
then, if a LeanSMILES worker is given, time it on the same renumberings.

    symmetry_inchi.py [worker] [N] [lean_timeout_s]
"""
import json, random, subprocess, sys, time
import networkx as nx
from rdkit import Chem, RDLogger
from rdkit.Chem import inchi
RDLogger.DisableLog("rdApp.*")
worker = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] != "-" else None
N = int(sys.argv[2]) if len(sys.argv) > 2 else 50
LEAN_T = int(sys.argv[3]) if len(sys.argv) > 3 else 120
random.seed(0)

def mol_of(g):
    g = nx.convert_node_labels_to_integers(g)
    m = Chem.RWMol()
    for _ in g.nodes: m.AddAtom(Chem.Atom(6))
    for a, b in g.edges: m.AddBond(a, b, Chem.BondType.SINGLE)
    m = m.GetMol(); Chem.SanitizeMol(m); return m

C60 = "c12c3c4c5c1c1c6c7c2c2c8c3c3c9c4c4c%10c5c5c1c1c6c6c%11c7c2c2c7c8c3c3c8c9c4c4c9c%10c5c5c1c1c6c6c%11c2c2c7c3c3c8c4c4c9c5c1c1c6c2c3c41"

def tert_butyl(generations):
    """Neopentane (1), tetra-tert-butylmethane (2), and so on: every methyl becomes a tert-butyl."""
    def arm(g): return "C" if g == 0 else "C(%s)(%s)%s" % ((arm(g - 1),) * 3)
    return Chem.MolFromSmiles("C(%s)(%s)(%s)%s" % ((arm(generations - 1),) * 4))

cases = [
    ("neopentane",                     tert_butyl(1)),
    ("tetra-tert-butylmethane",        tert_butyl(2)),
    ("tert-butyl dendrimer C53",       tert_butyl(3)),
    ("cubane (cube graph)",            mol_of(nx.cubical_graph())),
    ("Petersen (CH)10",                mol_of(nx.petersen_graph())),
    ("Heawood (CH)14",                 mol_of(nx.heawood_graph())),
    ("Pappus (CH)18",                  mol_of(nx.pappus_graph())),
    ("dodecahedrane",                  mol_of(nx.dodecahedral_graph())),
    ("Desargues (CH)20",               mol_of(nx.desargues_graph())),
    ("Tutte-Coxeter (CH)30",           mol_of(nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5))),
    ("K5 as C5",                       mol_of(nx.complete_graph(5))),
    ("K4,4 as C8",                     mol_of(nx.complete_bipartite_graph(4, 4))),
    ("hypercube Q4 as C16",            mol_of(nx.hypercube_graph(4))),
    ("30-prism (CH)60",                mol_of(nx.circular_ladder_graph(30))),
    ("cyclohexacontane C60H120",       mol_of(nx.cycle_graph(60))),
    ("C60 fullerene",                  Chem.MolFromSmiles(C60)),
    ("8 x cubane (disconnected)",      Chem.MolFromSmiles(".".join(["C12C3C4C1C5C2C3C45"] * 8))),
    ("20 x neopentane (disconnected)", Chem.MolFromSmiles(".".join(["CC(C)(C)C"] * 20))),
]

def lean(smiles):
    t = time.time()
    try:
        p = subprocess.run([worker], input="".join(f"parse\t{s}\n" for s in smiles), capture_output=True, text=True, timeout=LEAN_T)
    except subprocess.TimeoutExpired:
        return None, None
    out = [json.loads(c.split("__JSON_END__")[0]) for c in p.stdout.split("__JSON_START__")[1:]]
    return (time.time() - t) / max(len(smiles), 1), {o.get("canonicalSmiles") or o.get("error") for o in out}

print(f"{'graph':<32}{'atoms':>6}{'|Aut|':>12}{'InChI ms':>10}{'InChIs':>8}{'Lean s':>9}{'Lean strs':>10}")
for name, m in cases:
    n = m.GetNumAtoms()
    g = nx.Graph([(b.GetBeginAtomIdx(), b.GetEndAtomIdx()) for b in m.GetBonds()]); g.add_nodes_from(range(n))
    aut = "-"
    if n <= 30 and nx.is_connected(g):      # brute-force count is only cheap for the small ones
        aut = sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(g, g).isomorphisms_iter())
    perms = []
    for _ in range(N):
        p = list(range(n)); random.shuffle(p); perms.append(Chem.RenumberAtoms(m, p))
    t = time.time(); keys = {inchi.MolToInchi(x) for x in perms}; ms = 1000 * (time.time() - t) / N
    ls, lstr = ("", "")
    if worker:
        sec, strs = lean([Chem.MolToSmiles(x, canonical=False) for x in perms[:3]])
        ls, lstr = (f">{LEAN_T}", "timeout") if sec is None else (f"{sec:.2f}", len(strs))
    print(f"{name:<32}{n:>6}{aut:>12}{ms:>10.1f}{len(keys):>8}{ls:>9}{lstr:>10}", flush=True)
