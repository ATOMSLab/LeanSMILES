"""RDKit reference answers for testing the Lean implementation.

For every molecule in the Delaney CSV, writes RDKit's canonical SMILES, its
Morgan fingerprint (radius 2, 2048 bits), and per-atom data the Lean parser
should reproduce. Read by `lake exe oracle-test` and `lake exe morgan-test`.

Optionally also writes a second file with the same molecules re-written in
Kekulé form (no lowercase aromatic atoms), to test aromaticity perception.

Usage:
    python tools/rdkit_oracle.py [input.csv] [output.csv] [kekule-output.csv]
Defaults: datasets/delaney-processed.csv -> datasets/delaney-oracle.csv
"""
import csv
import sys

import rdkit
from rdkit import Chem, RDLogger
from rdkit.Chem import rdFingerprintGenerator

RDLogger.DisableLog("rdApp.*")

RADIUS = 2
FP_SIZE = 2048

COLUMNS = [
    "index",              # 0-based row in the input CSV (same as records[i] in Lean)
    "smiles",             # input SMILES, whitespace-trimmed
    "canonical_smiles",   # Chem.MolToSmiles(Chem.MolFromSmiles(smiles))
    "morgan_bits",        # on-bits, ascending, space-separated
    "morgan_ids",         # unfolded id:count pairs, ascending by id, space-separated
    "num_atoms",          # heavy atoms
    "num_bonds",
    "atom_symbols",       # per atom, in input SMILES order (RDKit keeps that order)
    "atom_total_hs",      # per atom total H count after sanitization
    "atom_charges",       # per atom formal charge after sanitization
    "atom_in_ring",       # per atom 1/0
    "bonds",              # per bond "i-j:t" (i < j), sorted; t = RDKit bond type 1/2/3/12(aromatic)
    "needs_aromaticity",  # 1 if the as-written graph + cleanup rules 1-2 still differ from RDKit
    "canonical_smiles_nostereo",  # MolToSmiles(mol, isomericSmiles=False)
]


def cleaned_graph(smiles):
    """The graph a Lean v1 parser would build: aromatic bonds as written,
    no aromaticity perception, plus scope-doc cleanup rules 1 and 2."""
    m = Chem.RWMol(Chem.MolFromSmiles(smiles, sanitize=False))
    Chem.FastFindRings(m)
    ring_info = m.GetRingInfo()
    # Rule 1: an aromatic bond that is not in a ring becomes single
    for b in m.GetBonds():
        if b.GetBondType() == Chem.BondType.AROMATIC and not ring_info.NumBondRings(b.GetIdx()):
            b.SetBondType(Chem.BondType.SINGLE)
            b.SetIsAromatic(False)
    # Rule 2: nitro N(=O)=O  ->  [N+](=O)[O-]
    for a in m.GetAtoms():
        if a.GetSymbol() != "N" or a.GetFormalCharge() != 0:
            continue
        double_o = [b for b in a.GetBonds()
                    if b.GetBondType() == Chem.BondType.DOUBLE
                    and b.GetOtherAtom(a).GetSymbol() == "O"
                    and b.GetOtherAtom(a).GetDegree() == 1]
        if len(double_o) == 2:  # RDKit charges the first =O
            a.SetFormalCharge(1)
            double_o[0].SetBondType(Chem.BondType.SINGLE)
            double_o[0].GetOtherAtom(a).SetFormalCharge(-1)
    m.UpdatePropertyCache(strict=False)
    return m


def row_for(index, smiles, gen):
    mol = Chem.MolFromSmiles(smiles)
    if mol is None:
        raise ValueError(f"row {index}: RDKit cannot parse {smiles!r}")
    ring_info = mol.GetRingInfo()
    atoms = list(mol.GetAtoms())

    bits = list(gen.GetFingerprint(mol).GetOnBits())
    ids = sorted(gen.GetSparseCountFingerprint(mol).GetNonzeroElements().items())

    cleaned = cleaned_graph(smiles)
    same = (Chem.MolToSmiles(cleaned) == Chem.MolToSmiles(mol)
            and list(gen.GetFingerprint(cleaned).GetOnBits()) == bits)

    return {
        "index": index,
        "smiles": smiles,
        "canonical_smiles": Chem.MolToSmiles(mol),
        "morgan_bits": " ".join(map(str, bits)),
        "morgan_ids": " ".join(f"{i}:{c}" for i, c in ids),
        "num_atoms": mol.GetNumAtoms(),
        "num_bonds": mol.GetNumBonds(),
        "atom_symbols": " ".join(a.GetSymbol() for a in atoms),
        "atom_total_hs": " ".join(str(a.GetTotalNumHs()) for a in atoms),
        "atom_charges": " ".join(str(a.GetFormalCharge()) for a in atoms),
        "atom_in_ring": " ".join("1" if ring_info.NumAtomRings(a.GetIdx()) else "0" for a in atoms),
        "bonds": " ".join(sorted(
            f"{min(i, j)}-{max(i, j)}:{int(b.GetBondType())}"
            for b in mol.GetBonds()
            for i, j in [(b.GetBeginAtomIdx(), b.GetEndAtomIdx())])),
        "needs_aromaticity": 0 if same else 1,
        "canonical_smiles_nostereo": Chem.MolToSmiles(mol, isomericSmiles=False),
    }


def write_oracle(smiles_list, dst, gen):
    rows = [row_for(i, s, gen) for i, s in enumerate(smiles_list)]
    with open(dst, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS, lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    hard = sum(r["needs_aromaticity"] for r in rows)
    print(f"RDKit {rdkit.__version__}: wrote {len(rows)} molecules to {dst} "
          f"({hard} need aromaticity perception)")


def main(src="datasets/delaney-processed.csv", dst="datasets/delaney-oracle.csv",
         kekule_dst=None):
    with open(src, newline="") as f:
        smiles_list = [row["smiles"].strip() for row in csv.DictReader(f)]

    gen = rdFingerprintGenerator.GetMorganGenerator(radius=RADIUS, fpSize=FP_SIZE)
    write_oracle(smiles_list, dst, gen)

    # Same molecules written without lowercase aromatic atoms (C1=CC=CC=C1 style),
    # to test that aromaticity is perceived rather than read from the input.
    # Atom order follows these new strings, so rows line up by index only.
    if kekule_dst:
        kekule = [kekule_smiles(s) for s in smiles_list]
        write_oracle(kekule, kekule_dst, gen)


def kekule_smiles(s):
    """Kekulé form of s; s itself if RDKit cannot write one (rare: some aromatic
    systems RDKit accepts but cannot kekulize for output)."""
    try:
        k = Chem.MolToSmiles(Chem.MolFromSmiles(s), kekuleSmiles=True)
        return k if Chem.MolFromSmiles(k) is not None else s
    except Exception:
        return s


if __name__ == "__main__":
    main(*sys.argv[1:4])
