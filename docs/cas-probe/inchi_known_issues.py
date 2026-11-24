"""InChI's own published failures, tried on today's InChI and on LeanSMILES.

The CIDs are a sample of the 547 "Renumbering issues" InChI v1.06 lists in
INCHI-1-DOC/KNOWNISSUES.pdf (the InChI repository), plus the one CANON_ERR structure.
Structures come from PubChem (PUG REST). For each: R random atom renumberings ->
how many distinct InChIs (RDKit's bundled InChI) and how many distinct LeanSMILES
canonical strings, with stereo as given and with stereo stripped.

    inchi_known_issues.py <worker> [R] [lean_timeout_s]
"""
import json, random, subprocess, sys, urllib.request
from rdkit import Chem, RDLogger
from rdkit.Chem import inchi
RDLogger.DisableLog("rdApp.*")
worker = sys.argv[1]; R = int(sys.argv[2]) if len(sys.argv) > 2 else 40
LEAN_T = int(sys.argv[3]) if len(sys.argv) > 3 else 40   # seconds for each batch of LeanSMILES orderings
LEAN_N = 4
random.seed(0)
RENUMBER = [5150642, 6337844, 10771998, 10899850, 10953242, 10985980, 11378274, 11521032, 16007017,
            16153846, 16720756, 18711062, 20615544, 20764540, 20829425, 21024640, 21028630, 21044212,
            21361215, 22835673, 22979380, 23382747, 23596680, 25014394, 25035003, 25045269, 44147122,
            53290019, 53878088, 54721371, 57082975, 57225931, 58594422, 59106996, 60015145, 67011034,
            71475856, 72370542, 76184772, 88370203, 89291042, 90268683, 91287324, 100918399, 101455837]
CANON_ERR = [92178689]
cids = RENUMBER + CANON_ERR
# POST keeps the CID list out of the URL; curl because urllib gets disconnected by PubChem here
raw = subprocess.run(["curl", "-s", "-m", "90", "-X", "POST", "-d", "cid=" + ",".join(map(str, cids)),
                      "https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/cid/property/SMILES/JSON"],
                     capture_output=True, text=True).stdout
props = {p["CID"]: p["SMILES"] for p in json.loads(raw)["PropertyTable"]["Properties"]}

def lean(smiles):
    try:
        p = subprocess.run([worker], input="".join(f"parse\t{s}\n" for s in smiles), capture_output=True, text=True, timeout=LEAN_T)
    except subprocess.TimeoutExpired:
        return "timeout"
    out = [json.loads(c.split("__JSON_END__")[0]) for c in p.stdout.split("__JSON_START__")[1:]]
    errs = [o.get("error") for o in out if o.get("error")]
    return f"rejects: {errs[0][:40]}" if errs else len({o.get("canonicalSmiles") for o in out})

print(f"InChI {inchi.GetInchiVersion()}, {R} renumberings each")
print(f"{'CID':>10} {'atoms':>5} {'charge':>6} {'stereo':>6} {'InChIs':>7} {'layer that varies':<18} {'Lean':>5} {'Lean, no stereo':>16}  SMILES")
tally = {"inchi_unstable": 0, "lean_unstable": 0, "lean_flat_unstable": 0, "n": 0}
for cid in cids:
    s = props.get(cid); m = Chem.MolFromSmiles(s) if s else None
    if m is None: print(f"{cid:>10}  RDKit cannot read PubChem's SMILES: {s}"); continue
    n = m.GetNumAtoms()
    perms = []
    for _ in range(R):
        p = list(range(n)); random.shuffle(p); perms.append(Chem.RenumberAtoms(m, p))
    ins = {inchi.MolToInchi(x) for x in perms}
    varies = ""
    if len(ins) > 1:   # which InChI layers differ between the variants?
        layers = [dict((seg[0], seg) for seg in i.split("/")[2:]) for i in ins]
        keys = set().union(*layers)
        varies = ",".join(sorted("/" + k for k in keys if len({l.get(k) for l in layers}) > 1))
    flat = Chem.Mol(m); Chem.RemoveStereochemistry(flat)
    fperms = []
    for _ in range(LEAN_N):
        p = list(range(n)); random.shuffle(p); fperms.append(Chem.RenumberAtoms(flat, p))
    l1 = lean([Chem.MolToSmiles(x, canonical=False) for x in perms[:LEAN_N]])
    l2 = lean([Chem.MolToSmiles(x, canonical=False) for x in fperms])
    stereo = len(Chem.FindMolChiralCenters(m, includeUnassigned=False)) + sum(b.GetStereo() != Chem.BondStereo.STEREONONE for b in m.GetBonds())
    tally["n"] += 1; tally["inchi_unstable"] += len(ins) > 1
    tally["lean_unstable"] += l1 != 1; tally["lean_flat_unstable"] += l2 != 1
    tag = "CANON_ERR case" if cid in CANON_ERR else ""
    print(f"{cid:>10} {n:>5} {Chem.GetFormalCharge(m):>+6} {stereo:>6} {len(ins):>7} {varies:<18} {str(l1):>5} {str(l2):>16}  {s[:60]} {tag}", flush=True)
print(tally)
