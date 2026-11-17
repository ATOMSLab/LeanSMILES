#!/usr/bin/env python3
"""Hard cases for `lake exe invariance-test` (`LeanSMILES/Aromaticity/Invariance.lean`).

    python3 tools/rdkit_invariance_cases.py > datasets/aromatize-invariance.smi

Two parts. `HAND` is written as it is, RDKit not involved: lowercase rings that stay
non-aromatic (where relabeling does not commute with `aromatize`), fused systems with one
aromatic and one non-aromatic ring, charged rings, exocyclic double bonds, annulenes,
cyclophanes, and the inputs RDKit's `cleanUp` rewrites (where relisting the bonds, or for
`CN(C)#N(C)CC` renumbering the atoms, changes the output).  `BASE` is written by RDKit:
its canonical SMILES and four random atom orders, in lowercase and in Kekulé form.

Needs RDKit (`pip install rdkit`).  The random orders depend on the RDKit version.
"""
import random

from rdkit import Chem, RDLogger

RDLogger.DisableLog("rdApp.*")

HAND = [
    'Cc1cc2cccc2c1', 'c1cc2cccc2c1', 'c1ccc2cccc-2cc1', 'Cc1ccc2cccc-2cc1', 'Cc1cccc2ncc12',
    'c1ccc1', 'Cc1ccc1', 'c1ccccccc1', 'Cc1ccccccc1', 'c1ccc2cccccc2cc1', 'c1ccc2C=Cc2c1',
    'C1C=Cc2ccccc12', 'C1=CC2=CC=CC=C2C1', 'c1ccc2c(c1)Cc1ccccc12', 'c1ccc2c(c1)-c1ccccc1-2',
    'C1=CC=C2C(=C1)C1=CC=CC=C21', 'C1=Cc2cccc3cccc1c23', 'C1=CC2=CC=CC3=CC=CC1=C23',
    'C1=CC2=CC=CC=CC2=C1', 'CC1=CC2=CC=CC=CC2=C1', 'O=c1cccccc1', 'O=C1C=CC=CC=C1',
    'O=c1cc[nH]cc1', 'O=C1C=CNC=C1', 'O=C1C=CC(=O)C=C1', 'O=c1ccc2ccccc2o1',
    'O=C1C=CC2=CC=CC=C2O1', 'O=c1ccoc2ccccc12', 'C=C1C=CC=C1', '[cH-]1cccc1', 'C1=CC=C[CH-]1',
    'c1ccc[cH+]cc1', 'C1=CC=C[CH+]C=C1', 'C[n+]1ccccc1', 'C[N+]1=CC=CC=C1', 'c1cc[o+]cc1',
    'C1=CC=[O+]C=C1', '[O-][n+]1ccccc1', '[O-][N+]1=CC=CC=C1', 'O=S1(=O)C=CC=C1',
    'C=S1(=O)C=CC=C1', 'O=S1(=C)C=CC=C1', 'C=S1(=O)c2ccccc2C=C1', 'O=S1(=C)c2ccccc2C=C1',
    'O=P1(=S)C=CC=CC1', 'S=P1(=O)C=CC=CC1', 'C=C1C=CC(=O)C=C1', 'O=C1C=CC(=C)C=C1',
    'S=c1cccc[nH]1', 'S=C1C=CC=CN1', 'C[n+]1cc[nH]c1', 'c1nnn[nH]1', 'C1=NN=NN1',
    'c1ccccc1N(=O)=O', '[O-][N+](=O)C1=CC=CC=C1', 'O=N(=O)c1ccc2ccccc2c1',
    'c1cc2ccc1CCc1ccc(cc1)CC2', 'C1=CC=CC=CC=CC=CC=CC=CC=CC=C1', 'C1=CC=CC=CC=CC=CC=CC=C1',
    'C1=CC=CC=CC=CC=C1', 'C1=CC=CC=CC=CC=CC=C1', 'c1ccc2c(c1)oc1ccccc12',
    'C1=CC=C2C(=C1)OC1=CC=CC=C21', '[CH]1C=CC=C1', 'c1cc2ccc3ccc4ccc5ccc6ccc1c1c2c3c4c5c61',
    'c1cc2ccc3cccc4ccc(c1)c2c34', 'c1cc2cccc3c4cccc5cccc(c(c1)c23)c54',
    'c1cc2ccc3ccc4ccc5ccc1c1c2c3c4c51', 'C1=CC2=C3C(=C1)C=CC1=CC=CC(C=C2)=C13',
    'c1ccc2cc3ccccc3cc2c1', 'C1=CC=C2C=C3C=CC=CC3=CC2=C1',
    'c1cc2cc3ccc(cc4nc(cc5ccc(cc1n2)[nH]5)C=C4)[nH]3',
    'C1=CC2=CC3=CC=C(N3)C=C3C=CC(C=C4C=CC(=N4)C=C1N2)=N3', 'Cn1cnc2c1c(=O)n(C)c(=O)n2C',
    'CN1C=NC2=C1C(=O)N(C)C(=O)N2C', 'O=c1[nH]c(=O)c2[nH]cnc2[nH]1', 'c1ccc2[nH]ccc2c1',
    'C1=CC=C2NC=CC2=C1', 'c1ccc2nonc2c1', 'C1=CC2=NON=C2C=C1', 'c1ccsc1', 'C1=CSC=C1',
    'c1cnc2ncnn2c1', 'o1cccc1C=Cc1ccco1', 'C1=CC2=C(C=C1)C1=C(C=CC=C1)C2=O',
    'O=C1c2ccccc2-c2ccccc21', 'c1ccc2c(c1)C(=O)c1ccccc1C2=O',
    'C1=CC=C2C(=C1)C(=O)C1=CC=CC=C1C2=O', 'c1ccc2c(c1)ccc1ccccc12',
    'C1=CC2=C(C=C1)C1=C(C=CC=C1)C=C2', 'c1ccc2c(c1)[nH]c1ccccc12', 'B1C=CC=CC=C1',
    'c1cc[se]c1', 'C1=C[Se]C=C1', 'c1ccc2[se]ccc2c1', 'c1cc[te]c1', '[nH]1cccc1[N+](=O)[O-]',
    'O=[N+]([O-])c1ccc[nH]1', 'CN(C)#N(C)CC', 'CCN(C)#N(C)C', 'O=N#N=O', 'CN(C)#N', 'CN(=O)=O',
    'O=N(=O)C', 'OCl(=O)(=O)=O', 'CP(=O)(=C)C', 'C=P(C)(C)=O', 'C1=CC=CC=C1N(C)#N(C)CC',
    'O=N(=O)C1=CC=CC=C1', 'C1=CC=CC=C1N(=O)=O', 'O=N(=O)C1=CC=C2C=CC=CC2=C1',
    'O=N(=O)c1ccccc1', 'CN(C)(=O)C',
]

BASE = """c1ccc2c(c1)Cc1ccccc12 C1=Cc2ccccc2C1 c1ccc2c(c1)C=Cc1ccccc1-2 O=C1C=Cc2ccccc21 O=C1c2ccccc2C(=O)c2ccccc12
C1=Cc2cccc3cccc1c23 c1ccc2c(c1)-c1cccc3cccc-2c13 O=c1ccc2ccccc2o1 O=c1cc(-c2ccccc2)oc2ccccc12 O=c1c2ccccc2[nH]c2ccccc12
O=C1C=CC(=O)c2ccccc21 C=C1C=Cc2ccccc21 c1ccc2c(c1)CCc1ccccc1-2 O=c1cccc[nH]1 O=c1[nH]cnc2[nH]cnc12 S=c1[nH]c2ccccc2[nH]1
C[n+]1ccccc1 C[n+]1ccc2ccccc2c1 c1cc[n+]2ccccc2c1 [O-][n+]1ccccc1 [O-][n+]1ccc2ccccc2c1 c1ccc2[o+]cccc2c1 c1ccc2[s+]cccc2c1
[cH-]1cccc1 c1ccc2c(c1)[cH-]c1ccccc12 c1cc[cH+]ccc1 C[N+]1=CC=CC=C1 Cc1cc[n+](C)cc1 c1c[nH+]c[nH]1 C[n+]1ccn(C)c1
O=[N+]([O-])c1ccccc1 O=[N+]([O-])c1ccc2ccccc2c1 Cn1cnc2c1c(=O)n(C)c(=O)n2C O=c1[nH]c(=O)c2[nH]c(=O)[nH]c2[nH]1
c1ccc2cc3ccccc3cc2c1 c1ccc2c(c1)ccc1ccccc12 c1cc2ccc3cccc4ccc(c1)c2c34 c1ccc2cc3cc4ccccc4cc3cc2c1 c1ccc2c(c1)c1cccc3c4ccccc4c2c31
c1cc2ccc3ccc4ccc5ccc6ccc1c1c2c3c4c5c61 c1ccc2c(c1)c1ccccc1c1ccccc21 c1ccc2cc3c(ccc4ccccc43)cc2c1 c1cc2cccc3c4cccc5cccc(c(c1)c23)c54
c1ccc2cc3cc4cc5ccccc5cc4cc3cc2c1 c1cc2ccc3ccc4ccc5ccc1c1c2c3c4c51 c1cc2cc3ccc4cc5ccc6cc1c1c2c2c3c4c3c5c6c1c23
c1cc2ccc3ccc4ccc5ccc6ccc7ccc1c1c2c3c2c4c5c6c7c12 c1ccc2c(c1)c1cccc3c1c2cc1ccccc13
c1ccc2c(c1)[nH]c1ccccc12 c1ccc2c(c1)oc1ccccc12 c1ccc2c(c1)sc1ccccc12 c1ccc2nc3ccccc3cc2c1 c1ccc2nc3ccccc3nc2c1 c1cnc2c(c1)ccc1cccnc12
c1cc2cc3ccc(cc4nc(cc5ccc(cc1n2)[nH]5)C=C4)[nH]3 c1cc2cc3ccc(cc4ccc(cc5ccc(cc1n2)[nH]5)n4)[nH]3
c1ccc2cccc-2cc1 Cc1ccc2cccc-2cc1 c1ccc2c(c1)ccc1cccc-1c2 O=c1cccccc1 Oc1cccccc1=O c1ccc2ccccc2c1 C1=CC=CC=CC=CC=CC=CC=CC=CC=C1
c1ccc(-c2ccccc2)cc1 c1ccc(cc1)-c1ccc(cc1)-c1ccccc1 C(=Cc1ccccc1)c1ccccc1 c1ccc(cc1)N=Nc1ccccc1 c1ccoc1 c1ccsc1 c1cc[nH]c1 c1cnoc1 c1cscn1
c1ccc2[se]ccc2c1 c1cc2ccc1CCc1ccc(CC2)cc1 c1ccc2c(c1)C1c3ccccc3C2c2ccccc21 O=C1NC(=O)c2ccccc21 O=c1oc2ccccc2c2ccccc12
C1=CC2=CC=C1C=C2 c1cc2cc(c1)CCc1cccc(c1)CC2 c1cc2ccc3cc4ccc5cc6ccc7cc1c1c2c3c2c4c5c3c6c7c1c23""".split()


def generated():
    random.seed(7)
    out = []
    for s in BASE:
        m = Chem.MolFromSmiles(s)
        if m is None:
            continue
        out.append(Chem.MolToSmiles(m))
        out += [Chem.MolToSmiles(m, doRandom=True) for _ in range(4)]
        k = Chem.Mol(m)
        try:
            Chem.Kekulize(k, clearAromaticFlags=True)
        except Exception:
            continue
        out.append(Chem.MolToSmiles(k, kekuleSmiles=True))
        out += [Chem.MolToSmiles(k, kekuleSmiles=True, doRandom=True) for _ in range(4)]
    return list(dict.fromkeys(out))


if __name__ == "__main__":
    print("# Hard cases for lake exe invariance-test (LeanSMILES/Aromaticity/Invariance.lean),")
    print("# written by tools/rdkit_invariance_cases.py.")
    print("# Hand-picked: lowercase rings that stay non-aromatic, fused aromatic/non-aromatic")
    print("# systems, charged rings, exocyclic double bonds, annulenes, cyclophanes, clean-up cases.")
    print("\n".join(HAND))
    print("# Generated with RDKit: lowercase and Kekulé writings in random atom orders.")
    print("\n".join(generated()))
