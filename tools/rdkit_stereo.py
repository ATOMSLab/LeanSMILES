"""RDKit reference answers for the stereochemistry tests (`lake exe stereo-test`).

Two files, both tab-separated with a header row:

1. `datasets/stereo-canon.tsv`: is the canonical SMILES a function of the
   stereoisomer?  Molecules come in *families*: one constitution, several
   stereoisomers (*variants*), each written several ways.  Columns:

       family  variant  smiles  rdkit_key  inchi

   `rdkit_key` is RDKit's canonical isomeric SMILES of `smiles` and `inchi` its
   standard InChI.  Within a family, two rows are the same molecule iff their
   keys are equal; the Lean test asks that its own canonical SMILES draw the
   same line.  A pair on which RDKit and InChI disagree is reported, not
   judged.  RDKit's string itself is never compared with ours: the walk and the
   tie-breaking differ.

   Variants: the molecule as given, its mirror image (every tetrahedral centre
   inverted), and up to two other stereoisomers from RDKit's enumerator
   (centres *and* double bonds flipped).  Each variant is written once
   canonically and `--rewrites` more times in random atom orders.  The
   hand-picked hard cases (`HARD` below) add their own strings, as written, as
   variants too.

   Both files leave out every string in which a tetrahedral centre with a
   lone pair as its fourth ligand carries a ring-closure digit: RDKit reads
   some of those against OpenSMILES (see `lone_pair_ring_digit`), and its
   answers would then be about the mirror image of what the string says.
   The canonical file also leaves out a string RDKit writes from a variant but
   reads back as a different molecule, by InChI (it happens with `/` `\\` in
   some conjugated macrocycles): RDKit's answers about it would be about that
   other molecule.

2. `datasets/stereo-parity.tsv`: does the parser read each mark the way
   RDKit does?  Columns:

       smiles  centres  alkenes

   `centres` lists, for every tetrahedral centre RDKit keeps, `i:@` or `i:@@`:
   the mark the centre would carry if its neighbors were listed in ascending
   atom index, an implicit hydrogen or lone pair last.  `alkenes` lists, for
   every stereo double bond RDKit keeps outside a ring, `a-c:c` or `a-c:t` for
   each pair of heavy substituents (`a` on the bond's first atom).

   The answers are read off RDKit's chiral tags (relative to the order of the
   atom's bonds, with `AddHs` appending the hydrogen last; a lone pair also
   counts last) and off `SetBondStereoFromDirections`.  Because that is a
   convention of RDKit's, every input string is also checked against a 3D
   embedding, which shares no convention with either side: `@` is the negative
   signed volume `det(b - a, c - a, d - a) < 0` (looking from `a`, `b c d`
   anticlockwise), a lone pair sits opposite the other three neighbors, and
   cis is a dihedral under 90°.  The embedding must reproduce RDKit's tags atom
   by atom.  A row where the two disagree is dropped and listed; a molecule
   that cannot be embedded within the time limit keeps its tag answers.

Usage:
    python tools/rdkit_stereo.py [--rewrites K] [--seed S] [--embed-timeout SECONDS] [--max-atoms N]
Inputs: datasets/stereo.smi (molecules of at most `--max-atoms` heavy atoms,
default 100: the 34 larger ones, up to 346 atoms, cost the Lean canonicalizer
minutes each and add no stereo situations the smaller ones lack) plus HARD.  Atom indices are the order atoms appear
in the string, which RDKit (with explicit hydrogens kept) and LeanSMILES share.
"""
import argparse
import itertools
import random
import re

import numpy as np
import rdkit
from rdkit import Chem, RDLogger
from rdkit.Chem import AllChem, rdMolTransforms
from rdkit.Chem.EnumerateStereoisomers import EnumerateStereoisomers, StereoEnumerationOptions

RDLogger.DisableLog("rdApp.*")

CANON_OUT = "datasets/stereo-canon.tsv"
PARITY_OUT = "datasets/stereo-parity.tsv"
SOURCE = "datasets/stereo.smi"


def combos(template, k):
    """Every way of filling the k `{}` slots of template with `@` or `@@`."""
    return [template.format(*marks) for marks in itertools.product(["@", "@@"], repeat=k)]


# Hand-picked hard cases: each family is one constitution; the strings are its
# stereoisomers written in deliberately awkward ways.  Which strings are the
# same molecule is left to RDKit and InChI.
HARD = {
    # the alanine bug: same enantiomer, marks flipped by neighbor order;
    # centre as the first atom (implicit H first in the neighbor order)
    "alanine": ["N[C@@H](C)C(=O)O", "N[C@H](C(=O)O)C", "C[C@H](N)C(=O)O",
                "N[C@H](C)C(=O)O", "N[C@@H](C(=O)O)C", "[C@@H](N)(C)C(=O)O",
                "[C@H](C)(N)C(=O)O", "C[C@@H](C(=O)O)N", "OC(=O)[C@@H](C)N"],
    # four explicit neighbors
    "bromochlorofluoroiodomethane": ["F[C@](Cl)(Br)I", "F[C@@](Cl)(Br)I", "Cl[C@](F)(Br)I",
                                     "[C@](F)(Cl)(Br)I", "I[C@@](Br)(Cl)F", "Br[C@](I)(F)Cl"],
    # meso: two of the four mark patterns are one achiral molecule
    "tartaric": combos("OC(=O)[C{}H](O)[C{}H](O)C(=O)O", 2),
    # pseudoasymmetric middle centre (r/s): 8 patterns, 4 stereoisomers
    "trihydroxyglutaric": combos("OC(=O)[C{}H](O)[C{}H](O)[C{}H](O)C(=O)O", 3),
    # para-stereocentres: not CIP-chiral, still cis or trans
    "dimethylcyclohexane-1,4": combos("C[C{}H]1CC[C{}H](C)CC1", 2),
    "dimethylcyclohexane-1,2": combos("C[C{}H]1CCCC[C{}H]1C", 2),
    "decalin": combos("C1CC[C{}H]2CCCC[C{}H]2C1", 2),
    # six centres on a ring with a 12-element symmetry group: 64 patterns, 9
    # stereoisomers.  Stresses that pruning by automorphisms respects stereo.
    "inositol": combos("O[C{}H]1[C{}H](O)[C{}H](O)[C{}H](O)[C{}H](O)[C{}H]1O", 6),
    # ring-closure digits on the centre, including digits in the "wrong" order
    # (ring 2 opened first but ring 1 closed first)
    "halodecalin": ["F[C@]12CCCC[C@]1(Cl)CCCC2", "F[C@@]12CCCC[C@]1(Cl)CCCC2",
                    "[C@]12(F)CCCC[C@]1(Cl)CCCC2", "[C@@]21(F)CCCC[C@]1(Cl)CCCC2",
                    "[C@]21(F)CCCC[C@@]1(Cl)CCCC2", "Cl[C@@]12CCCC[C@]1(F)CCCC2"],
    "halocyclohexane": ["F[C@@H]1CCCC[C@H]1Cl", "[C@@H]1(F)CCCC[C@H]1Cl", "Cl[C@@H]1CCCC[C@@H]1F",
                        "F[C@H]1CCCC[C@H]1Cl", "C1CC[C@@H](Cl)[C@@H](F)C1"],
    # marks on atoms that are not stereocentres
    "isobutane": ["C[C@H](C)C", "C[C@@H](C)C", "CC(C)C", "[C@H](C)(C)C"],
    "chlorofluoropropane": ["C[C@](C)(F)Cl", "C[C@@](C)(F)Cl", "CC(C)(F)Cl"],
    # lone pair as the fourth neighbor, including the centre as the first atom
    "sulfoxide": ["C[S@](=O)CC", "C[S@@](=O)CC", "[S@](C)(=O)CC", "[S@@](C)(=O)CC",
                  "O=[S@](C)CC", "O=[S@@](CC)C", "CC[S@](C)=O"],
    "phosphine": ["C[P@](CC)c1ccccc1", "C[P@@](CC)c1ccccc1", "[P@](C)(CC)c1ccccc1",
                  "c1ccccc1[P@](C)CC"],
    "ammonium": ["C[N@@+](CC)(CCC)c1ccccc1", "C[N@+](CC)(CCC)c1ccccc1", "CC[N@+](C)(CCC)c1ccccc1"],
    # cis/trans
    "difluoroethene": ["F/C=C/F", "F/C=C\\F", "F\\C=C\\F", "F\\C=C/F", "C(/F)=C/F",
                       "C(\\F)=C/F", "FC=CF"],
    "crotonic": ["C/C=C/C(=O)O", "C/C=C\\C(=O)O", "OC(=O)/C=C/C", "C(/C)=C/C(=O)O"],
    "methylfluoropropene": ["C/C(C)=C/F", "CC(C)=CF", "C/C(C)=C\\F"],
    "hexadiene": ["C/C=C/C=C/C", "C/C=C\\C=C/C", "C/C=C/C=C\\C", "C/C=C\\C=C\\C"],
    "cyclooctene": ["C1CCC/C=C\\CC1", "C1CCC/C=C/CC1"],
    # both kinds at once
    "chlorofluoropentene": ["C/C=C/[C@H](F)Cl", "C/C=C\\[C@H](F)Cl", "C/C=C/[C@@H](F)Cl",
                            "Cl[C@H](F)/C=C/C"],
}

KEEP_H = Chem.SmilesParserParams()
KEEP_H.removeHs = False


def tetrahedral_centres(mol):
    return [a.GetIdx() for a in mol.GetAtoms()
            if a.GetChiralTag() in (Chem.ChiralType.CHI_TETRAHEDRAL_CW,
                                    Chem.ChiralType.CHI_TETRAHEDRAL_CCW)]


# RDKit (2025.09) reads `@`/`@@` on a centre whose fourth ligand is a lone
# pair, and which carries a ring-closure digit, against OpenSMILES for amines,
# phosphines and sulfonium (C[N@]1CC1C, F[P@]1CC1C, C[S@+]1CC1C: its own 3D
# embedding is the mirror image of the OpenSMILES reading) though not for
# sulfoxides (O=[S@]1CC1C), nor without the digit (CC1[N@](C)C1).  Its writer
# shares the convention, so its writings stay self-consistent, but such a
# string means the other hand to an OpenSMILES reader.  Strings with a
# lone-pair centre carrying a ring digit are therefore left out of both
# files, all elements alike.
ATOM_TOKEN = re.compile(r"\[[^\]]*\]|Br|Cl|[BCNOPSFIbcnops*]")


def ring_digit_atoms(smiles):
    """Indices (order of appearance) of the atoms that carry a ring-closure digit."""
    out, k, i = set(), -1, 0
    while i < len(smiles):
        m = ATOM_TOKEN.match(smiles, i)
        if m:
            k, i = k + 1, m.end()
        elif smiles[i].isdigit():
            out.add(k)
            i += 1
        elif smiles[i] == "%":
            out.add(k)
            i += 3
        else:
            i += 1
    return out


def lone_pair_ring_digit(smiles):
    """Whether a tetrahedral centre with three neighbors and no hydrogen (a
    lone pair as the fourth ligand) carries a ring-closure digit in smiles."""
    m = Chem.MolFromSmiles(smiles, KEEP_H)
    if m is None:
        return False
    lone = {k for k in tetrahedral_centres(m)
            if m.GetAtomWithIdx(k).GetDegree() == 3 and m.GetAtomWithIdx(k).GetTotalNumHs() == 0}
    return bool(lone & ring_digit_atoms(smiles))


def has_stereo(mol):
    return bool(tetrahedral_centres(mol)) or any(
        b.GetStereo() != Chem.BondStereo.STEREONONE for b in mol.GetBonds())


def random_writing(mol, rng):
    """mol written from a random atom order (non-canonical walk), and for each
    written atom its index in mol."""
    perm = list(range(mol.GetNumAtoms()))
    rng.shuffle(perm)
    renum = Chem.RenumberAtoms(mol, perm)
    s = Chem.MolToSmiles(renum, canonical=False)
    order = list(renum.GetPropsAsDict(True, True)["_smilesAtomOutputOrder"])
    return s, [perm[k] for k in order]


def inchi(smiles):
    m = Chem.MolFromSmiles(smiles)
    return Chem.MolToInchi(m) if m is not None else ""


def rdkit_key(smiles):
    m = Chem.MolFromSmiles(smiles)
    return Chem.MolToSmiles(m) if m is not None else ""


# --------------------------------------------------------------------------
# 1. canonical-form families


def variants_of(mol, rng):
    """(name, mol) stereoisomers of mol: itself, its mirror image, and up to
    two more from the enumerator."""
    out = [("orig", mol)]
    centres = tetrahedral_centres(mol)
    if centres:
        mirror = Chem.Mol(mol)
        for i in centres:
            mirror.GetAtomWithIdx(i).InvertChirality()
        out.append(("mirror", mirror))
    opts = StereoEnumerationOptions(onlyUnassigned=False, maxIsomers=3, unique=True,
                                    rand=rng.randrange(1 << 30))
    others = [m for m in EnumerateStereoisomers(mol, options=opts)
              if Chem.MolToSmiles(m) != Chem.MolToSmiles(mol)]
    out += [(f"iso{k + 1}", m) for k, m in enumerate(others[:2])]
    return out


def canon_rows(family, mol, extra, rewrites, rng, unread):
    """Rows for every variant of mol and every hand string.  A string RDKit
    writes from a variant but reads back as another molecule — its InChI is not
    the variant's — is left out and listed in `unread`: RDKit's answers about
    it would be about that other molecule.  (RDKit's own key is no test: its
    canonical SMILES of one molecule can differ with the atom order.)"""
    rows = []
    for name, v in variants_of(mol, rng):
        strings = [Chem.MolToSmiles(v)]
        strings += [random_writing(v, rng)[0] for _ in range(rewrites)]
        rows += [(family, name, s, Chem.MolToInchi(v)) for s in strings]
    for k, s in enumerate(extra):
        v = Chem.MolFromSmiles(s)
        rows.append((family, f"hand{k + 1}", s, inchi(s)))
        rows += [(family, f"hand{k + 1}", random_writing(v, rng)[0], inchi(s))
                 for _ in range(rewrites)]
    out = []
    for f, v, s, ref in rows:
        i = inchi(s)
        if i != ref:
            unread.append(f"{f} {v}: {s} reads back as {i}, written from {ref}")
            continue
        out.append((f, v, s, rdkit_key(s), i))
    return out


def without_lone_pair_ring_digits(rows, excluded):
    """rows without the strings `lone_pair_ring_digit` excludes (string first)."""
    kept = []
    for r in rows:
        if lone_pair_ring_digit(r[0] if len(r) == 3 else r[2]):
            excluded.append(r[0] if len(r) == 3 else r[2])
        else:
            kept.append(r)
    return kept


# --------------------------------------------------------------------------
# 2. parser parity: RDKit's tags, checked against a 3D embedding


def inversions(keys):
    return sum(1 for i in range(len(keys)) for j in range(i + 1, len(keys)) if keys[i] > keys[j])


def tag_answers(m):
    """`centres` and `alkenes` from RDKit's tags; m parsed with hydrogens kept."""
    n = m.GetNumAtoms()
    mh = Chem.AddHs(m)  # implicit hydrogens become atoms n, n+1, ..., bonded last
    centres = []
    for k in tetrahedral_centres(m):
        a = mh.GetAtomWithIdx(k)
        keys = [min(b.GetOtherAtomIdx(k), n) for b in a.GetBonds()]  # bond order
        if len(keys) == 3:
            keys.append(n)  # lone pair, last
        if len(keys) != 4:
            continue
        ccw = a.GetChiralTag() == Chem.ChiralType.CHI_TETRAHEDRAL_CCW  # @ in bond order
        centres.append(f"{k}:{'@' if ccw != (inversions(keys) % 2 == 1) else '@@'}")
    d = Chem.Mol(m)
    Chem.SetBondStereoFromDirections(d)
    alkenes = []
    for bond in d.GetBonds():
        if bond.GetBondType() != Chem.BondType.DOUBLE or bond.IsInRing():
            continue
        if bond.GetStereo() not in (Chem.BondStereo.STEREOCIS, Chem.BondStereo.STEREOTRANS):
            continue
        u, v = bond.GetBeginAtomIdx(), bond.GetEndAtomIdx()
        ref_a, ref_c = bond.GetStereoAtoms()
        if ref_a not in [x.GetIdx() for x in d.GetAtomWithIdx(u).GetNeighbors()]:
            ref_a, ref_c = ref_c, ref_a
        ref_cis = bond.GetStereo() == Chem.BondStereo.STEREOCIS
        for ia, ic in substituent_pairs(d, u, v):
            cis = ref_cis != ((ia != ref_a) != (ic != ref_c))
            alkenes.append(f"{ia}-{ic}:{'c' if cis else 't'}")
    return " ".join(centres), " ".join(alkenes)


def substituent_pairs(m, u, v):
    """Pairs of heavy substituents across the double bond u=v."""
    return [(a.GetIdx(), c.GetIdx())
            for a in m.GetAtomWithIdx(u).GetNeighbors()
            for c in m.GetAtomWithIdx(v).GetNeighbors()
            if a.GetIdx() != v and c.GetIdx() != u
            and a.GetAtomicNum() != 1 and c.GetAtomicNum() != 1]


def embed(m, timeout):
    """m with hydrogens added and a conformer that reproduces every tetrahedral
    tag atom by atom, or None."""
    mh = Chem.AddHs(m)
    centres = tetrahedral_centres(mh)
    for seed in (0xf00d, 7, 42):
        params = AllChem.ETKDGv3()
        params.randomSeed = seed
        params.timeout = timeout
        if AllChem.EmbedMolecule(mh, params) != 0:
            continue
        check = Chem.Mol(mh)
        Chem.AssignStereochemistryFrom3D(check)
        if all(check.GetAtomWithIdx(k).GetChiralTag() == mh.GetAtomWithIdx(k).GetChiralTag()
               for k in centres):
            return mh
    return None


def geometry_answers(m, centre_atoms, alkene_bonds, timeout):
    """The same answers read off a 3D embedding, or None if there is none."""
    mh = embed(m, timeout)
    if mh is None:
        return None
    n = m.GetNumAtoms()
    pos = mh.GetConformer().GetPositions()
    centres = []
    for k in centre_atoms:
        nbrs = sorted(a.GetIdx() for a in mh.GetAtomWithIdx(k).GetNeighbors())  # added H last
        pts = [pos[j] for j in nbrs]
        if len(pts) == 3:  # lone pair opposite the three neighbors
            pts.append(pos[k] - sum(p - pos[k] for p in pts))
        a, b, c, d = (np.array(p) for p in pts)
        vol = np.linalg.det(np.array([b - a, c - a, d - a]))
        centres.append(f"{k}:{'@' if vol < 0 else '@@'}")
    alkenes = []
    conf = mh.GetConformer()
    for u, v in alkene_bonds:
        for ia, ic in substituent_pairs(m, u, v):
            dih = rdMolTransforms.GetDihedralDeg(conf, ia, u, v, ic)
            alkenes.append(f"{ia}-{ic}:{'c' if abs(dih) < 90 else 't'}")
    return " ".join(centres), " ".join(alkenes)


def parity_rows(s, rewrites, rng, timeout, dropped):
    """Rows for s and `rewrites` random writings of it.  s itself is checked
    against an embedding; its rewrites are the same molecule read by the same
    rules."""
    src = Chem.MolFromSmiles(s, KEEP_H)
    tags = tag_answers(src)
    centre_atoms = [int(e.split(":")[0]) for e in tags[0].split()]
    alkene_bonds = []
    for e in tags[1].split():
        ia, ic = (int(x) for x in e.split(":")[0].split("-"))
        bond = next(b for b in src.GetBonds() if b.GetBondType() == Chem.BondType.DOUBLE
                    and {b.GetBeginAtomIdx(), b.GetEndAtomIdx()} & {x.GetIdx() for x in src.GetAtomWithIdx(ia).GetNeighbors()}
                    and {b.GetBeginAtomIdx(), b.GetEndAtomIdx()} & {x.GetIdx() for x in src.GetAtomWithIdx(ic).GetNeighbors()})
        alkene_bonds.append((bond.GetBeginAtomIdx(), bond.GetEndAtomIdx()))
    geo = geometry_answers(src, centre_atoms, list(dict.fromkeys(alkene_bonds)), timeout)
    status = "unchecked" if geo is None else ("agrees" if geo == tags else "disagrees")
    if status == "disagrees":
        dropped.append(f"{s}: tags {tags}, geometry {geo}")
        return [], status
    rows = [(s, *tags)]
    for _ in range(rewrites):
        w = random_writing(src, rng)[0]
        rows.append((w, *tag_answers(Chem.MolFromSmiles(w, KEEP_H))))
    return rows, status


# --------------------------------------------------------------------------


def read_smi(path):
    with open(path) as f:
        return [line.split()[0] for line in f if line.strip() and not line.startswith("#")]


def write_tsv(path, header, rows):
    with open(path, "w") as f:
        f.write("\t".join(header) + "\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rewrites", type=int, default=2)
    ap.add_argument("--seed", type=int, default=470)
    ap.add_argument("--embed-timeout", type=int, default=2)
    ap.add_argument("--max-atoms", type=int, default=100)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    canon, parity, dropped, skipped, excluded, unread = [], [], [], [], [], []
    checks = {"agrees": 0, "disagrees": 0, "unchecked": 0}
    sources = [(f"stereo:{k}", s, []) for k, s in enumerate(read_smi(SOURCE))]
    sources += [(f"hard:{name}", strings[0], strings) for name, strings in HARD.items()]
    for done, (family, s, extra) in enumerate(sources):
        if done % 50 == 0:
            print(f"  {done}/{len(sources)}", flush=True)
        mol = Chem.MolFromSmiles(s)
        # a hard family whose marks RDKit drops is kept: all its strings are
        # then one molecule, which is the point
        if mol is None or (not extra and not has_stereo(mol)):
            skipped.append(f"{family} (no stereo after RDKit's cleanup)")
            continue
        if mol.GetNumAtoms() > args.max_atoms:
            skipped.append(f"{family} ({mol.GetNumAtoms()} heavy atoms)")
            continue
        canon += canon_rows(family, mol, extra, args.rewrites, rng, unread)
        for w in (extra or [s]):
            rows, status = parity_rows(w, args.rewrites, rng, args.embed_timeout, dropped)
            parity += rows
            checks[status] += 1

    canon = without_lone_pair_ring_digits(canon, excluded)
    parity = without_lone_pair_ring_digits(parity, excluded)
    write_tsv(CANON_OUT, ["family", "variant", "smiles", "rdkit_key", "inchi"], canon)
    write_tsv(PARITY_OUT, ["smiles", "centres", "alkenes"], parity)
    print(f"RDKit {rdkit.__version__}: {len(canon)} rows in "
          f"{len({r[0] for r in canon})} families -> {CANON_OUT}; "
          f"{len(parity)} rows -> {PARITY_OUT}")
    print(f"parity inputs checked against a 3D embedding: {checks['agrees']} agree, "
          f"{checks['disagrees']} disagree (dropped), {checks['unchecked']} not embedded in time")
    print(f"strings left out for a lone-pair centre with a ring digit "
          f"(RDKit reads some against OpenSMILES): {len(excluded)}")
    print(f"strings RDKit wrote but does not read back as the molecule written: {len(unread)}")
    for d in (skipped + dropped + [f"lone pair + ring digit: {e}" for e in excluded]
              + [f"not read back: {e}" for e in unread]):
        print(f"  {d}")


if __name__ == "__main__":
    main()
