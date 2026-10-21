# LeanSMILES
Formalizing molecular representations in Lean


1. Download the project's dependencies and Mathlib's precompiled cache, then
   check the project:

   ```bash
   lake exe cache get
   lake build
   ```


## SMILES → typed molecular graph → canonical SMILES

`LeanSMILES.SMILES.Canon` is the one import for the SMILES toolkit:

```lean
import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph            -- the Mathlib views
open LeanSMILES LeanSMILES.SMILES

#eval parse "c1cc[nH]c1"                                  -- Except.ok (Molecule 5 ["c","c","c","[nH]","c"] [0:1, 1:2, 2:3, 3:4, 0:4])
#eval (Mol.ofSmiles! "C(O)C").canonicalSmiles             -- "CCO"
#eval (Mol.ofSmiles! "C=CO").mol.adjMatrix                -- !![0, 2, 0; 2, 0, 1; 0, 1, 0]  (over ℚ)
#eval (Mol.ofSmiles! "C=CO").mol.graph.adjMatrix ℚ        -- Mathlib's 0/1 matrix
```

A `Molecule n` is a `Vector Atom n` and a list of `Bond n` between distinct
atoms with no duplicate bonds — the invariants are the type, so
`Molecule.graph : SimpleGraph (Fin n)` and `Molecule.adjMatrix : Matrix (Fin n) (Fin n) ℚ`
come with Mathlib's theorems (`sum_degrees`, `card_edgeFinset`, `relabelIso`,
`canonicalize_iso`).  The parser checks syntax, not valence; the only chemistry
applied is the OpenSMILES implicit-hydrogen rule.  Canonical SMILES is
colour refinement plus exhaustive tie-breaking (lexicographically smallest
string), so it is canonical by construction rather than by matching RDKit.

Open `LeanSMILES/Examples/smiles.lean` for more; design and comparison with
the `canonical-smiles` branch in `docs/design-molecular-representation.md`.

Tests against RDKit's answers (oracle files from the `canonical-smiles` branch):

```bash
lake exe validity-test   # 10 000 broken SMILES: accepts everything RDKit accepts (0 parser bugs)
lake exe oracle-test     # 1 128 Delaney molecules: graph = RDKit's, canonical SMILES round-trips and is relabelling-invariant, 1128/1128
lake exe morgan-test     # Morgan fingerprints: ring membership = RDKit's, bits = RDKit's wherever the graph is, relabelling-invariant
```

### Morgan fingerprints

`LeanSMILES.Fingerprint.Morgan` ports RDKit's `GetMorganGenerator(radius=2, fpSize=2048)`
(from the `canonical-smiles` branch's port) onto `Molecule n`: `morganIds` (unfolded
identifiers with counts), `morganBits` (sorted on-bits), `morganVector : Vector Bool 2048`,
`inRingVector`, and an exact `tanimoto : … → ℚ`.  It hashes the graph *as written*, so the
bits equal RDKit's exactly where the as-written bond types and hydrogen counts equal RDKit's
sanitized ones (no aromaticity perception here, by design), and they are always invariant
under relabelling of the atoms.

```lean
#eval (Mol.ofSmiles! "CCO").morganBits        -- [80, 222, 294, 807, 1057, 1410, ...]
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
```
