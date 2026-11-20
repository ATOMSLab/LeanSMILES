"""RDKit vs OpenBabel on the panel: canonical strings, aromatic-atom counts, and
whether each toolkit's canonical SMILES survives random atom reordering.

RDKit and OpenBabel segfault when imported into one process here, so this runs
in three passes over a JSON work file:
    toolkits.py rd1 panel.tsv work.json [N]   # RDKit: canonical + N random SMILES
    toolkits.py ob  work.json                 # OpenBabel: canonicalize all of them
    toolkits.py rd2 work.json > toolkits.tsv  # RDKit: cross-check, write the table
"""
import csv, json, re, sys, random
mode = sys.argv[1]

if mode == "rd1":
    from rdkit import Chem, RDLogger; RDLogger.DisableLog("rdApp.*")
    N = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    random.seed(0); work = []
    for r in csv.DictReader(open(sys.argv[2]), delimiter="\t"):
        s = r["ref_smiles"]
        if not s: continue
        m = Chem.MolFromSmiles(s)
        e = {"name": r["name"], "ref": s, "rd_can": None, "rand": []}
        if m is not None:
            e["rd_can"] = Chem.MolToSmiles(m)
            e["rd_arom"] = sum(a.GetIsAromatic() for a in m.GetAtoms())
            e["rand"] = [Chem.MolToSmiles(m, doRandom=True) for _ in range(N)]
            e["rd_variants"] = len({Chem.MolToSmiles(Chem.MolFromSmiles(x)) for x in e["rand"]})
        work.append(e)
    json.dump(work, open(sys.argv[3], "w"))

elif mode == "ob":
    # one obabel process per molecule, so a crash in OpenBabel costs one row
    import os, subprocess, tempfile
    OBABEL = os.path.join(os.path.dirname(sys.executable), "obabel")
    def can_all(smiles):
        with tempfile.NamedTemporaryFile("w", suffix=".smi", delete=False) as f:
            f.write("\n".join(smiles) + "\n")
        p = subprocess.run([OBABEL, f.name, "-ocan"], capture_output=True, text=True)
        os.unlink(f.name)
        if p.returncode != 0: return None
        return [l.split("\t")[0].strip() for l in p.stdout.splitlines()]
    work = json.load(open(sys.argv[2]))
    for e in work:
        r = can_all([e["ref"]] + e["rand"])
        if r is None or len(r) != 1 + len(e["rand"]):
            e["ob_can"], e["ob_arom"], e["ob_variants"] = "OPENBABEL_CRASHES" if r is None else "OPENBABEL_DROPS", None, None
            continue
        e["ob_can"] = r[0]
        # aromatic atoms: lowercase b c n o p s outside brackets, or a bracket atom with a lowercase symbol
        outside = re.sub(r"\[[^\]]*\]", "", r[0])
        e["ob_arom"] = sum(ch in "bcnops" for ch in outside) + len(re.findall(r"\[\d*[a-z]", r[0]))
        e["ob_variants"] = len(set(r[1:]))
    json.dump(work, open(sys.argv[2], "w"))

elif mode == "rd2":
    from rdkit import Chem, RDLogger; from rdkit.Chem import inchi; RDLogger.DisableLog("rdApp.*")
    out = csv.writer(sys.stdout, delimiter="\t")
    out.writerow("name rd_can ob_can rd_arom ob_arom rd_variants ob_variants rd_reads_ob".split())
    for e in json.load(open(sys.argv[2])):
        if e["rd_can"] is None:
            out.writerow([e["name"], "RDKIT_REJECTS", e.get("ob_can"), "", e.get("ob_arom"), "", "", ""]); continue
        k0 = inchi.MolToInchiKey(Chem.MolFromSmiles(e["rd_can"]))
        mo = Chem.MolFromSmiles(e["ob_can"]) if e.get("ob_can") and not e["ob_can"].startswith("OPENBABEL") else None
        cross = "same" if (mo is not None and inchi.MolToInchiKey(mo) == k0) else ("REJECTED" if mo is None else "DIFFERENT")
        out.writerow([e["name"], e["rd_can"], e["ob_can"], e["rd_arom"], e["ob_arom"], e["rd_variants"], e["ob_variants"], cross])
