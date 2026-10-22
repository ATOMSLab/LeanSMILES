# LeanSMILES
Formalizing molecular representations in Lean

## Installation

No Lean experience needed. Setup is a one-time job, and most of it is download
time. Two tools do the work: **elan** installs the right Lean version (much as
conda manages Python environments), and **lake** fetches dependencies and builds
the project.

1. **Install the editor and Lean.** Install [Git](https://git-scm.com/downloads)
   and [VS Code](https://code.visualstudio.com/), then add VS Code's **Lean 4**
   extension (search "Lean 4" in the Extensions panel). The first time you open
   a Lean file, the extension offers to install Lean (elan) for you. Accept.

   Prefer the terminal? On macOS or Linux, install elan directly:

   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Download this project:**

   ```bash
   git clone https://github.com/ATOMSLab/LeanSMILES.git
   cd LeanSMILES
   ```

3. **Download the project's dependencies and Mathlib's precompiled cache, then
   check the project:**

   ```bash
   lake exe cache get
   lake build
   ```

   Mathlib is Lean's mathematics library, and it is large. `lake exe cache get`
   downloads it already compiled (several GB of disk). Without it, `lake build`
   compiles Mathlib from scratch, which takes hours. The Lean version this
   project needs (pinned in `lean-toolchain`) installs itself the first time you
   run `lake`.

4. **Try it.** In VS Code, use **File → Open Folder…** and open the whole
   `LeanSMILES` folder, not a single file, so the dataset paths resolve. Then
   open `LeanSMILES/Examples/parsercsv.lean`. The **Lean Infoview** panel on the
   right shows each `#eval` result: the solubility dataset in `datasets/`, read
   in as SMILES strings with their numeric features.

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
`canonicalizeIso`).  The matrices also exist as subtypes that say they come
from a molecule — `BondMatrix n` (bond orders, O(1) lookups) and `FlatMatrix n`
(0/1, Mathlib's `IsAdjMatrix`) — with `normalEquiv : {m // m.IsNormal} ≃ Vector Atom n × BondMatrix n`
proving that nothing but bond orientation is lost.  The parser checks syntax, not valence; the only chemistry
applied is the OpenSMILES implicit-hydrogen rule.  Canonical SMILES is
color refinement plus exhaustive tie-breaking (lexicographically smallest
string), and it is canonical by theorem (`Molecule.canonicalSmiles_relabel`)
rather than by matching RDKit.

Open `LeanSMILES/Examples/caffeine.lean` for one molecule walked through every
representation — tokens, atoms, bonds, graph, matrices, normal form, canonical
ranks, fingerprint — and `LeanSMILES/Examples/smiles.lean` for more; design and
comparison with the `canonical-smiles` branch in
`docs/design-molecular-representation.md`.

Tests against RDKit's answers (oracle files from the `canonical-smiles` branch):

```bash
lake exe validity-test   # 10 000 broken SMILES: accepts everything RDKit accepts (0 parser bugs)
lake exe oracle-test     # 1 128 Delaney molecules: graph = RDKit's, canonical SMILES round-trips and is relabeling-invariant, 1128/1128
lake exe morgan-test     # Morgan fingerprints: ring membership = RDKit's, bits = RDKit's wherever the graph is, relabeling-invariant
```

### Morgan fingerprints

`LeanSMILES.Fingerprint.Morgan` ports RDKit's `GetMorganGenerator(radius=2, fpSize=2048)`
(from the `canonical-smiles` branch's port) onto `Molecule n`: `morganIds` (unfolded
identifiers with counts), `morganBits` (sorted on-bits), `morganVector : Vector Bool 2048`,
`inRingVector`, and an exact `tanimoto : … → ℚ`.  It hashes the graph *as written*, so the
bits equal RDKit's exactly where the as-written bond types and hydrogen counts equal RDKit's
sanitized ones (no aromaticity perception here, by design), and they are always invariant
under relabeling of the atoms.

```lean
#eval (Mol.ofSmiles! "CCO").morganBits        -- [80, 222, 294, 807, 1057, 1410, ...]
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
```

## Classification with Morgan fingerprints

`LeanSMILES.ML.Logistic` trains L2-regularized logistic regression (scikit-learn's
`LogisticRegression()` objective) on Morgan fingerprint bits from
`LeanSMILES.Fingerprint.Morgan`. It is written over `ScalarLike`
(`LeanSMILES/Scalar.lean`), so it runs on `Float`.
`LeanSMILES/Examples/classification.lean` redoes ENCH 470 Lecture 21: EGFR
actives vs. inactives (`ench470-content/`), test accuracy 0.925, then the five
FDA-approved EGFR drugs.

```bash
lake exe logistic-test   # EGFR classification vs scikit-learn (tools/sklearn_egfr.py)
```

The test trains twice: on RDKit's fingerprint bits (stored in
`datasets/egfr-classification.csv`), where every probability matches
scikit-learn's to 10⁻⁶, and on Lean's own `morganFeatures`, which differ from
RDKit's sanitized fingerprints on 30 of the 205 molecules (no aromaticity
perception yet) but give the same predicted class for every molecule.

## References

LeanSMILES builds on prior work in Lean, cheminformatics, and chemistry
education. [`REFERENCES.md`](REFERENCES.md) credits each source and says what
it is credited for; [`references.bib`](references.bib) has the BibTeX.

## Findings about external tools

Things the formalization turned up in the tools and specifications it is
checked against.

* **RDKit canonical SMILES is not always canonical.** Its tie-breaking
  individualizes one atom of the lowest tied class and never backtracks, which
  is only canonical when the tied atoms are symmetry-equivalent. On a 12-carbon
  cubic graph where they are not, RDKit 2026.09.1 returns eight different
  canonical SMILES depending on input atom order
  (`LeanSMILES/Examples/smiles.lean`). Found by searching random cubic graphs;
  20 of 1 989 showed it. LeanSMILES tries every tied atom and keeps the
  lexicographically smallest string, and its canonical SMILES is proved
  independent of input order for every molecule, with no budget:
  `Mol.canonicalSmiles_relabel` (`LeanSMILES/SMILES/Canonicity.lean`).
  nauty-style automorphism pruning, checked at every use, keeps symmetric
  molecules tractable — a 53-atom *tert*-butyl dendrimer with about 7 × 10¹³
  tie-breaking leaves canonicalizes in seconds.
* **OpenSMILES underdetermines implicit hydrogens on aromatic atoms.** §3.1.5
  computes the count from a sum of bond orders but never says what an
  aromatic bond contributes; §3.5 only requires that electrons be assignable
  without violating valence. Read literally with aromatic bonds at `3/2`, the
  nitrogen of `Cn1cccc1` and the sulfur of thiophene get a hydrogen they
  cannot have. Toolkits agree on a fix the spec does not state
  (`Molecule.implicitHydrogens`).
