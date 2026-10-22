"""Broken-SMILES test set: does Lean accept exactly the SMILES RDKit accepts?

Takes real SMILES (Delaney + RDKit's bundled NCI sample), applies one or two
random single-character edits (insert / delete / replace with a SMILES token),
and records whether RDKit's MolFromSmiles accepts each result. The Lean side
(`lake exe validity-test`) must agree on every line, apart from elements that
are not in Chem/Element.lean (it reports those separately).

Usage:
    python tools/rdkit_fuzz.py [output.tsv] [count] [seed]
Defaults: datasets/fuzz-validity.tsv, 10000, 470
Each line: 1 or 0 (RDKit accepts?) <TAB> SMILES
"""
import csv
import os
import random
import sys

from rdkit import Chem, RDConfig, RDLogger

RDLogger.DisableLog("rdApp.*")

TOKENS = list("CNOSPFIcnosp()=#12345[]H+-./\\%") + [
    "Cl", "Br", "[nH]", "[N+]", "[O-]", "%10", "c1", "1c", "[C@H]", "[13C]",
    "[S-]", "[n+]", "[se]"]


def mutate(s, rng):
    i = rng.randrange(len(s) + 1)
    op = rng.choice("idr")
    if op == "i":
        return s[:i] + rng.choice(TOKENS) + s[i:]
    if op == "d":
        return s[:i] + s[i + 1:]
    return s[:i] + rng.choice(TOKENS) + s[i + 1:]


def main(dst="datasets/fuzz-validity.tsv", count=10000, seed=470):
    rng = random.Random(int(seed))
    with open("datasets/delaney-processed.csv", newline="") as f:
        base = [row["smiles"].strip() for row in csv.DictReader(f)]
    with open(os.path.join(RDConfig.RDDataDir, "NCI", "first_5K.smi")) as f:
        base += [line.split()[0] for line in f if line.strip()]

    out = set()
    while len(out) < int(count):
        s = rng.choice(base)
        for _ in range(rng.choice([1, 1, 2])):
            if s:
                s = mutate(s, rng)
        if s and "\t" not in s:
            out.add(s)

    accepted = 0
    with open(dst, "w") as f:
        for s in sorted(out):
            ok = Chem.MolFromSmiles(s) is not None
            accepted += ok
            f.write(f"{int(ok)}\t{s}\n")
    print(f"wrote {len(out)} broken SMILES to {dst} ({accepted} accepted by RDKit)")


if __name__ == "__main__":
    main(*sys.argv[1:4])
