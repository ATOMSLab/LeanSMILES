"""What the published CAS Common Chemistry strings can and cannot do.

For every record in cas.tsv (transcribed from commonchemistry.cas.org):
  1. coverage    - is there a structure string at all?
  2. parse       - does RDKit accept the string?  (OpenBabel: see --ob)
  3. self-check  - does the string reproduce the InChIKey printed on the same record?
                   skeleton = first 14 characters, stereo/isotope = next 8
  4. injectivity - which different substances get the same string?
"""
import csv, sys, collections
from rdkit import Chem, RDLogger
from rdkit.Chem import inchi
from rdkit.Chem.rdMolDescriptors import CalcMolFormula
RDLogger.DisableLog("rdApp.*")
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
n = len(rows)

def why(s):
    try: Chem.SanitizeMol(Chem.MolFromSmiles(s, sanitize=False)); return ""
    except Exception as e: return str(e).split("\n")[0][:70]

print(f"== 1. coverage ({n} records)")
for r in rows:
    if r["canonical_smiles"] == "NONE":
        print(f"   no structure string: {r['rn']:<12} {r['cas_name']}")

print("\n== 2+3. parse and self-check")
stats = collections.Counter()
for r in rows:
    for col in ("canonical_smiles", "isomeric_smiles"):
        s = r[col]
        if not s or s == "NONE": continue
        stats[col] += 1
        m = Chem.MolFromSmiles(s)
        if m is None:
            stats["rdkit rejects"] += 1
            print(f"   RDKit rejects   {r['rn']:<12} {r['cas_name'][:26]:<26} {s[:44]:<44} {why(s)}"); continue
        if r["inchikey"] == "NONE":
            print(f"   no InChI on record {r['rn']:<10} {r['cas_name'][:26]:<26} string '{s}' reads as {CalcMolFormula(m)}, CAS formula {r['formula']}")
            stats["formula mismatch"] += CalcMolFormula(m) != r["formula"]; continue
        # records printed with a non-standard InChI (prefix "InChI=1/") carry relative stereo
        k = (inchi.InchiToInchiKey(inchi.MolToInchi(m, options="/SRel")) if r["inchi_flavor"] == "1" and col == "isomeric_smiles"
             else inchi.MolToInchiKey(m))
        if not k:
            stats["no InChI can be computed from the string"] += 1
            fe = [a.GetDegree() for a in m.GetAtoms() if a.GetSymbol() == "Fe"]
            print(f"   GRAPH differs    {r['rn']:<12} {r['cas_name'][:26]:<26} string bonds Fe to {fe[0] if fe else '?'} atoms; the InChI on the record has no metal bonds")
        elif k[:14] != r["inchikey"][:14]:
            stats["skeleton mismatch"] += 1
            print(f"   SKELETON differs {r['rn']:<12} {r['cas_name'][:26]:<26} string -> {k}  record {r['inchikey']}")
        elif k[15:23] != r["inchikey"][15:23]:
            if col == "isomeric_smiles":
                stats["isomeric string loses stereo"] += 1
                print(f"   STEREO lost      {r['rn']:<12} {r['cas_name'][:26]:<26} isomeric string -> {k[15:23]}  record {r['inchikey'][15:23]}")
            elif not r["isomeric_smiles"]:
                stats["record has stereo/isotope layer but no string carries it"] += 1
                print(f"   layer unwritten  {r['rn']:<12} {r['cas_name'][:26]:<26} record key block {r['inchikey'][15:23]}, only string is '{s[:40]}'")
for k, v in stats.items(): print(f"   -- {k}: {v}")

print("\n== 4. different substances, same strings")
g = collections.defaultdict(list)
for r in rows:
    if r["canonical_smiles"] != "NONE":
        g[(r["canonical_smiles"], r["isomeric_smiles"])].append(r)
for (c, i), rs in g.items():
    if len(rs) > 1:
        keys = {r["inchikey"] for r in rs}
        print(f"   {len(rs)} RNs share '{(i or c)[:50]}': " + "; ".join(f"{r['cas_name']} [{r['rn']}]" for r in rs)
              + ("   (InChIKey identical too)" if len(keys) == 1 else ""))

print("\n== non-standard InChI (prefix 'InChI=1/'), keys that end in NA-N")
print("   " + ", ".join(f"{r['cas_name']} [{r['rn']}]" for r in rows if r["inchi_flavor"] == "1"))
