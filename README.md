# LeanSMILES
Formalizing molecular representations in Lean — and, downstream of them, the
learning algorithms that consume them.

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
   in as SMILES strings with their numeric features. `lake build` builds and
   checks all three libraries below; on a laptop, `LEAN_NUM_THREADS=4 lake build`
   keeps memory in check (the editor is capped the same way by
   `.vscode/settings.json`).

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

Because the parser checks syntax only, `[C+123]` parses, round-trips and
canonicalizes like any other atom (RDKit accepts it too).  The chemistry check
available after parsing is `Molecule.checkCharges` (`LeanSMILES.Chem.Charge`):
a decidable predicate, `Molecule.chargesConsistent`, saying every formal charge
is one its element can physically carry — no more electrons lost than it has
(`charge ≤ Z`), no more gained than complete its valence shell
(`-shellVacancy ≤ charge`, the distance to the next noble gas: `C` −4, `O` −2,
`Fe` −10), and OpenSMILES's ±15 for the wildcard `*` — with a message naming
the offending atom.  It is deliberately not an invariant of `Molecule`, so the
canonicalization theorems carry no chemistry; relabeling and canonicalization
preserve it (`chargesConsistent_relabel`, `chargesConsistent_canonicalize`).

```lean
#eval (Mol.ofSmiles! "[NH4+].[Cl-]").checkCharges  -- Except.ok ()
#eval (Mol.ofSmiles! "C[C+123]").checkCharges      -- Except.error "atom 1 (C) has formal charge +123; C can carry -4 to +6"
```

Open `LeanSMILES/Examples/caffeine.lean` for one molecule walked through every
representation — tokens, atoms, bonds, graph, matrices, normal form, canonical
ranks, fingerprint — and `LeanSMILES/Examples/smiles.lean` for more; design and
comparison with the `canonical-smiles` branch in
`docs/design-molecular-representation.md`.

### What the parser accepts

The grammar is OpenSMILES's ([opensmiles.org](http://opensmiles.org/opensmiles.html),
§2.2).  RDKit and the specification disagree on a handful of strings; where
they do, LeanSMILES follows the specification, with the decided exceptions
below.  Every row is pinned by `lake exe parse-errors-test`.

| String | RDKit | OpenSMILES | LeanSMILES |
|---|---|---|---|
| `C(C)1CC1` — ring-closure label after a branch | accepts | rejects: `atom ringbond* branch*` | rejects (`ringAfterBranch`).  Chlorothalonil in the Delaney set is written `…c(Cl)1` and is skipped by `oracle-test`. |
| `C(.O)`, `C.(O)`, `C(C.)`, `C.1CC1` — dots next to branches and labels | rejects | allows only the first | rejects all four |
| `" C"` — leading whitespace | methane | empty molecule, then a title | methane |
| `[Fe+++]`, `[C+123]` — charge forms | rejects, accepts | rejects both: `++`/`--` only, two digits | accepts both; whether the element has the electrons is `Molecule.checkCharges`, a post-parse chemistry check, not a lexical one |
| `[CH10]`, `[C:]` — two-digit H count, empty class | accepts, rejects | rejects both | rejects both |
| `[C@TH1]` … `[Fe@OH30]` — named chirality classes | accepts | accepts | accepts, recorded as written (`@` is not rewritten to `@TH1`) |
| `C=1CC-1` — different bond symbols on one ring closure | accepts, opening symbol wins | rejects | rejects (`conflictingRingBond`) |
| `C%(123)CC%(123)` — RDKit's long ring labels | accepts | rejects | rejects |
| `[02H]` — isotope with a leading zero | rejects | accepts | accepts |

Tests against RDKit's answers (oracle files from the `canonical-smiles` branch):

```bash
lake exe parse-errors-test  # every ParseError with its exact message, plus the accept/reject decisions above
lake exe validity-test      # 10 000 broken SMILES: accepts everything RDKit accepts, bar the OpenSMILES rules above (0 parser bugs)
lake exe oracle-test        # 1 128 Delaney molecules: graph = RDKit's, canonical SMILES round-trips and is relabeling-invariant (1 skipped, see above)
lake exe morgan-test        # Morgan fingerprints: ring membership = RDKit's, bits = RDKit's wherever the graph is, relabeling-invariant
lake exe charge-test        # formal charges: [C+123], [H+++], [C-123] parse but fail checkCharges; [Na+], [O-2], [Fe+3], [NH4+] pass
```

### Morgan fingerprints

`LeanSMILES.Fingerprint.Morgan` ports RDKit's `GetMorganGenerator(radius=2, fpSize=2048)`
(from the `canonical-smiles` branch's port) onto `Molecule n`: `morganIds` (unfolded
identifiers with counts), `morganBits` (sorted on-bits), `morganVector : Vector Bool 2048`,
`inRingVector`, and an exact `tanimoto : … → ℚ`.  It hashes the graph *as written*, so the
bits equal RDKit's exactly where the as-written bond types and hydrogen counts equal RDKit's
sanitized ones; run `Molecule.aromatize` first (below) to get RDKit's bits.  Up to radius 2 the
fingerprint is proved independent of the atom order: `Molecule.morganBits_relabel`
(`LeanSMILES/Fingerprint/MorganInvariance.lean`).  From radius 3 it is not, here or in
RDKit, and that is a theorem too: `Molecule.not_forall_morganBits_relabel_three`
(`LeanSMILES/Fingerprint/MorganRadius3.lean`), checked by the kernel on the molecule below
(see "Findings about external tools").

```lean
#eval (Mol.ofSmiles! "CCO").morganBits        -- [80, 222, 294, 807, 1057, 1410, ...]
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
```

`LeanSMILES.Fingerprint.Tanimoto` answers *is Tanimoto a metric?* (Surendran et al. 2025).
On bit sets, the Tanimoto distance `|A ∆ B| / |A ∪ B|` is a metric
(`Finset.tanimotoMetricSpace`, the Marczewski–Steinhaus / Lipkus theorem), and `tanimoto` on
Morgan on-bits computes the bit-set similarity (`Molecule.tanimoto_morganBits`). On
real-valued vectors the same formula, `⟨x,y⟩ / (⟨x,x⟩ + ⟨y,y⟩ − ⟨x,y⟩)`, fails the triangle
inequality already for the scalars `1/3, 2/3, 1` (`not_tanimotoVec_dist_triangle`), so there
is no such metric space (`not_exists_metricSpace_tanimotoVec`).

### Aromaticity: RDKit's view of the bonds

The parser reads bonds as written. `Molecule.aromatize` (`LeanSMILES/Aromaticity/`)
gives a molecule RDKit's view of them, as a separate step after parsing: RDKit's
ring set (relevant cycles), kekulization, aromaticity perception (default model:
donor types, Hückel 4n + 2, fused systems) and final hydrogen counts. So
`C1=CC=CC=C1` becomes aromatic benzene, the bond between the rings of
`c1ccccc1c1ccccc1` becomes single, and `c1cccc1` fails as it does in RDKit
("Can't kekulize mol"). RDKit's `cleanUp` (nitro and similar rewrites), valence
rejection and removal of `[H]` atoms are not included yet.

```lean
#eval (SMILES.parseAromatized "C1=CC=CC=C1").map (·.morganBits)   -- RDKit's benzene bits
```

```bash
lake exe aromaticity-test   # bond types, hydrogens and Morgan bits = RDKit's on every oracle file
```

On every oracle file, as written and in Kekulé form (Delaney, 56 hand-picked
aromaticity cases, isotope cases, hydrogen cases), every molecule that `cleanUp`
and `[H]` removal do not touch gets RDKit's bond types, hydrogen counts and
Morgan fingerprint: 3 368 of 3 368 (chlorothalonil, which the parser rejects, is not counted). On 10 000 fuzzed strings it never fails on
one RDKit accepts. The code is ported from the `canonical-smiles` branch's
array-based sanitization (commit `5b5fe9e`) and still runs on an index-based
working copy inside; its interface is `Molecule n → Except String (Molecule n)`.
RDKit's remaining sanitization steps were ported on that earlier representation;
`docs/scope-canonical-smiles-morgan.md` records the port, the commit that holds
its code, the oracle datasets and the Python references.

### Drawing molecules

`LeanSMILES.Depict` draws any `Molecule n` the parser accepts — chains,
fused rings, cages, sugars, stereocentres, cis/trans alkenes, charges and
isotopes — with no dependency beyond Lean itself. In the editor:

```lean
import LeanSMILES.Depict.Widget
meta import LeanSMILES.Depict.Widget

#draw "OC[C@H]1O[C@@H](O)[C@H](O)[C@@H](O)[C@@H]1O"   -- β-D-glucose, wedges and hashes
#draw "C1C2CC3CC1CC(C2)C3"                              -- adamantane, in perspective
#draw "F/C=C\\F"                                        -- cis-difluoroethene
```

and from the command line, `lake exe depict "<smiles>" [out.svg]` writes the
SVG, `lake exe depict --mol "<smiles>"` an MDL mol block with wedge/hash flags
that any other toolkit reads back, and `lake exe depict --html in.smi out.html`
a gallery. `LeanSMILES/Examples/depict.lean` shows the range.

The layout is deterministic: classical multidimensional scaling on the graph
distances (chains zigzag at 120°, rings become regular polygons), refined by
stress majorisation; a component with three or more rings that cannot lie flat
is laid out in three dimensions and projected obliquely, which is how chemists
draw cubane or norbornane. The stereochemistry is read back from what the
parser *recorded*: `Atom.chirality` is `@`/`@@` (or `@TH1`/`@TH2`) relative
to the SMILES neighbor order, which `Depict.Graph.stereoNeighbors`
reconstructs from the bond list (ring-closure bonds belong at the *opening*
digit, not where the parser created them), and one bond per centre becomes a
wedge or a hash so that the signed volume of the drawn neighbors has the
written sign; `Bond.dir` gives the cis/trans arrangement, enforced by target
distances and, if the layout still came out the other way, by reflecting one
side of the double bond. Bonds are drawn as written; to draw RDKit's view of
an aromatic system, `aromatize` first.

Tests:

```bash
lake exe depict-test                        # datasets/stereo.smi: every centre wedged, every
                                            # marked double bond cis/trans as written, sane geometry
python3 tools/check_depiction.py out/stereo.sdf   # RDKit reads the mol blocks back: same isomeric SMILES
```

The Lean check passes 552 of the 557 drawings (the five misses are crowded
tri- and tetrasubstituted alkenes); RDKit recovers the written
stereochemistry exactly from 481 of them (86 %), the rest being mostly
bridged bicyclics, where one wedge per centre is not always enough for a
reader to settle the configuration, and double bonds in large rings, for
which RDKit assigns an E/Z the SMILES did not specify.
`datasets/stereo.smi` is drawn from RDKit's example data (ESOL, WEHI, CDK2,
ChEMBL document CHEMBL2321810 — CC BY-SA 3.0 — and the NIBR PubChem examples)
plus seven textbook cases.

## Three libraries

The repository builds three Lean libraries, with one direction of dependency:

| Library | What it is | Imports |
|---|---|---|
| [`LeanSMILES/`](LeanSMILES) | SMILES → typed molecular graph → canonical SMILES, Morgan fingerprints, matrices | Mathlib |
| [`LeanLearn/`](LeanLearn) | learning algorithms on tabular data (`X`, `y`) and their proofs: linear regression in closed form and by certified iterative solvers, logistic regression, and the theorems over `ℝ` | Mathlib only — no chemistry |
| [`Pipelines/`](Pipelines) | molecules as tabular data: representations `Mol → ℚᵈ`, labelled molecules, certified pipelines, the Delaney and EGFR walkthroughs, the tests against scikit-learn | both |

`LeanLearn` does not know what a molecule is — as scikit-learn does not import RDKit —
and `LeanSMILES` does not know what a model is. `Pipelines` is the only code that imports
both, and the join is thin: [`Pipelines/Representation.lean`](Pipelines/Representation.lean)
is the one place the toolkit's fingerprints are read. *This split, and the name `Pipelines`,
are provisional: architecture to review now that the code is in one place.*

## Learning algorithms: `LeanLearn`

Everything executable is written once over `ScalarLike`
([`LeanLearn/Scalar.lean`](LeanLearn/Scalar.lean)): `Float` is what runs, `ℝ` is what the
theorems are about, and the polynomial fragment also runs exactly over `ℚ`.

### Linear regression

Two formulations of the same problem, by two authors, side by side:

* **Closed form, over `ℝ`** ([`Proofs/LeastSquares/OLS.lean`](LeanLearn/Proofs/LeastSquares/OLS.lean),
  [`Ridge.lean`](LeanLearn/Proofs/LeastSquares/Ridge.lean); Hao Liu). `X : Matrix (Fin n) (Fin p) ℝ`,
  loss `‖Xw − y‖²`, plus `Σⱼ ρⱼ wⱼ²` for ridge. Any solution of the normal equations is a
  global minimizer, with no rank assumption; `fit = (XᵀX)⁻¹ Xᵀy` satisfies them and is the
  unique minimizer when `det(XᵀX) ≠ 0`; positive ridge has a unique minimizer for every
  design, even underdetermined ones. [`RidgeOLS.lean`](LeanLearn/Proofs/LeastSquares/RidgeOLS.lean)
  relates the two: a ridge minimizer trades squared error for a smaller penalized norm than
  any OLS minimizer, `wρ = (XᵀX + diag ρ)⁻¹ XᵀX w₀`, and the ridge path is continuous with
  `wλ → w₀` as `λ → 0` and `‖wλ‖² → 0` as `λ → ∞`.
  [`Regression/LinearModel.lean`](LeanLearn/Regression/LinearModel.lean) writes the same
  objectives over `PolynomialLike`, so they run at `Float`, and
  [`Proofs/Regression/LinearModel.lean`](LeanLearn/Proofs/Regression/LinearModel.lean) proves
  that their `ℝ` reading is the specification. [`OLSFloat.lean`](LeanLearn/Regression/OLSFloat.lean)
  and [`RidgeFloat.lean`](LeanLearn/Regression/RidgeFloat.lean) are executable Householder-QR
  solvers on `Float` arrays, with input validation and no formal rounding bound. Worked proofs
  in [`Examples/ols.lean`](LeanLearn/Examples/ols.lean) and
  [`ridge.lean`](LeanLearn/Examples/ridge.lean); details in
  [`LeanLearn/README.md`](LeanLearn/README.md).
* **Iterative, over any scalar** ([`Regression/Problem.lean`](LeanLearn/Regression/Problem.lean),
  [`Solvers.lean`](LeanLearn/Regression/Solvers.lean); DeMarko Fulcher). The ridge problem
  `(1/m) Σᵣ (⟪xᵣ, θ⟫ − yᵣ)² + λ‖θ‖²` with an intercept, its normal equations `Aθ = b`, and
  gradient descent, Jacobi and Gauss–Seidel on them, started from `0`; `Algorithm` is the
  solver with its hyperparameters, as data. [`Certificates.lean`](LeanLearn/Regression/Certificates.lean)
  is the exact `ℚ` check (`SolverWitness`: weighted diagonal dominance) that certifies
  Jacobi and Gauss–Seidel before running them.
  [`Proofs/Regression/MatrixBridge.lean`](LeanLearn/Proofs/Regression/MatrixBridge.lean) proves
  the two formulations are one problem up to the factor `m` — `‖Xθ − y‖² + mλ‖θ‖² = m·L(θ)`,
  `XᵀX + mλI = m·A`, `Xᵀy = m·b` — so for `m > 0` they share normal equations and minimizers,
  and the closed form `(XᵀX + mλI)⁻¹Xᵀy` with its uniqueness for `λ > 0` transfers to
  `Problem`, which also gets the ridge-vs-OLS shrinkage trade-off.
* **Sparse, for fingerprints** ([`Regression/SparseRidge.lean`](LeanLearn/Regression/SparseRidge.lean);
  Samiha Sharlin). scikit-learn's `Ridge(alpha)` objective, intercept not penalized, on
  sparse `0/1` features: conjugate gradients on the centered normal equations, using only
  products with the on-bits, so 2048 fingerprint bits never form a dense matrix.
  [`Metrics.lean`](LeanLearn/Regression/Metrics.lean) has `r2`, `rmse` and `mae`, and
  [`Plot/Parity.lean`](LeanLearn/Plot/Parity.lean) writes parity plots as SVG.

```bash
lake exe ols-float-test      # Householder-QR OLS: known solutions, extreme scales, every rejected input
lake exe ridge-float-test    # the same for ridge, with an exempt intercept column
lake exe linear-model-test   # the shared Float definitions on supplied coefficients
```

### Classification

[`Classification/Logistic.lean`](LeanLearn/Classification/Logistic.lean): L2-regularized
logistic regression — scikit-learn's `LogisticRegression()` objective, intercept not
penalized — on sparse `0/1` features, trained by Nesterov-accelerated gradient descent with
gradient-based restarts to a (nearly) zero gradient. It runs at `Float`; `Pipelines` checks it
against scikit-learn molecule by molecule (`lake exe logistic-test`, below).

### Proofs over `ℝ`

[`Proofs/`](LeanLearn/Proofs): `LeastSquares/` is the closed form on Mathlib matrices (the bullets
above); `Regression/` reads the executable code in `ℝ`:

* **The loss is an exact quadratic**: `L(θ + v) = L(θ) + 2⟪Aθ − b, v⟫ + vᵀAv`; so solutions
  of the normal equations are global minimizers.
* **The two formulations are one problem** (`MatrixBridge.lean`): the averaged `Vec` loss is
  the matrix ridge loss with weights `mλ`, divided by `m`, entry for entry (`m·A = XᵀX + mλI`,
  `m·b = Xᵀy`); so `Problem` inherits the closed form and its uniqueness for `λ > 0` from
  `Ridge.lean`, and the shrinkage trade-off — `‖θ‖²` falls and the mean squared error rises
  with `λ` — holds for it directly.
* **Gradient descent**: sufficient decrease, monotone loss, and the `O(1/k)` rate
  `L(θₖ) ≤ L(u) + ‖u‖²/(2ηk)` for every `u`, when `2η((1/m)Σ‖xᵣ‖² + λ) ≤ 1`.
* **Jacobi and Gauss–Seidel**, for any linear system with weighted diagonal dominance
  (`∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ`, `ρ < 1`): a solution exists (Gershgorin), both iterations
  contract by `ρ` per step in the weighted max-norm, and on the normal equations
  `L(θₖ) ≤ L(u) + Γβ²ρ²ᵏ`.
* **Gauss–Seidel is coordinate descent**: it never increases the loss, for any data. A fixed
  point of Jacobi is optimal.
* **The certificate is sound** (`SolverWitness.check_sound`): a passing exact `ℚ` check
  gives the hypotheses above in `ℝ`.

## Molecules as tabular data: `Pipelines`

### Certifying a regression pipeline

Open [`Pipelines/Examples/delaney.lean`](Pipelines/Examples/delaney.lean): like
`caffeine.lean`, it walks through the pipeline one `#eval` at a time, on the Delaney table.

**1. Data and pipeline.** Molecules come from SMILES (`LabelledMolecules.ofSmiles!`) or from
a table in `datasets/` (`ofRecords`, through the toolkit's `CSVparser`), with exact rational
targets. A pipeline adds a representation (`Mol → ℚᵈ`: Morgan bits, bond-order matrices,
counts, read through canonical SMILES or not), a ridge penalty `λ` (default `0`) and a
solver:

```lean
def delaney := CSVparser.load "datasets/delaney-processed.csv"
def train : LabelledMolecules 40 := .ofRecords delaney 0 40

def gd : Pipeline 40 32 :=
  { data := train, representation := .morgan 2 32, algorithm := .gradientDescent (1 / 66) 3000 }

#eval gd.trainMSE Float                       -- train it, on Float
#eval gd.predictSmiles (gd.model Float) "CCCO"
```

**2. Gradient descent.** Morgan bits are `0/1`, so `‖φ(M)‖² ≤ 32` for every molecule
(`morgan_bounded`). With that bound the certificate is arithmetic on the hyperparameters, so
it holds for every dataset:

```lean
#eval gd.maxStepSize 32          -- 1/66: the largest step size the certificate accepts
#eval gd.gdTolerance 4           -- 11/250: within 0.044 of every model with ‖θ‖² ≤ 4
#eval gd.checkGD 32 4 (1 / 20)   -- true

theorem gd_certified (u : Vec ℝ 33) (hu : ∑ i : Fin 33, u[i] ^ 2 ≤ 4) :
    gd.trainLoss ℝ ≤ (gd.problem ℝ).loss u + 1 / 20 := by
  have := gd.checkGD_sound (R2 := (32 : ℕ)) (B := 4) (ε := 1 / 20)
    (Representation.morgan_bounded 2 32) (by decide +kernel) u (by exact_mod_cast hu)
  simpa using this
```

**3. Jacobi and Gauss–Seidel.** The condition is about the data: the normal equations must
be diagonally dominant with respect to some weights. `suggestWitness` proposes a witness,
`certifiedSolverExcess` is how close to the optimum the solver is then guaranteed to end
(`none` if the check fails), and for representations the kernel can evaluate (bond orders)
the whole check is a proof:

```lean
def gs : Pipeline 40 16 :=
  { data := train, representation := .bondOrders 4, ridge := 16, algorithm := .gaussSeidel 30 }

#eval gs.suggestWitness                                   -- weights, ρ < 1, β
#eval gs.certifiedSolverExcess.map fun e ↦ decide (e < 1 / 10 ^ 9)   -- some true

theorem smallJacobi_certified (u : Vec ℝ 10) :           -- within 0.001 of the optimum
    smallJacobi.trainLoss ℝ ≤ (smallJacobi.problem ℝ).loss u + 1 / 1000 := by
  have := smallJacobi.checkSolver_sound (W := smallJacobi.suggestWitness) (ε := 1 / 1000)
    (by decide +kernel) u
  simpa using this
```

When a condition fails there is no certificate: `checkGD` returns `false` for a step size
too large for the representation, and `certifiedSolverExcess` is `none` for Jacobi without
enough ridge penalty — a pipeline that, run on `Float`, diverges.

What is proved ([`Pipelines/Proofs/Certificates.lean`](Pipelines/Proofs/Certificates.lean),
[`Representation.lean`](Pipelines/Proofs/Representation.lean)); `L` is the training loss:

| Solver | Conditions (checked without training) | Guarantee |
|---|---|---|
| Gradient descent | `‖φ(M)‖² ≤ R²` for the representation, `λ ≥ 0`, `η > 0`, `2η(R² + 1 + λ) ≤ 1`, `B ≤ 2ηkε` | `L(θ) ≤ L(u) + ε` for every `u` with `‖u‖² ≤ B`, for **every dataset** (`GDCertificate.sound`) |
| Jacobi, Gauss–Seidel | the exact `ℚ` check of weighted diagonal dominance (`checkSolver`) | `L(θ) ≤ L(u) + ε` for **every** `u`: `θ` is `ε`-optimal (`checkSolver_sound`) |
| Gauss–Seidel | none (`λ ≥ 0`) | the loss never increases with more sweeps (`gaussSeidel_antitone`) |

and about representations: `bondOrder_eq_adjMatrix` (the kernel-evaluable bond-order
features are the toolkit's `adjMatrix`), `canonical_relabel` (a representation read through
canonical SMILES gives every atom numbering of a molecule the same features, from the
toolkit's `canonicalSmiles_relabel`), and feature bounds for every molecule: Morgan
`≤ fpSize`, bond orders `≤ 16k²`, `clip c` of anything `≤ dc²`, and through `canonical` and
`++`. Every theorem depends only on Lean's standard axioms; kernel checks use
`decide +kernel`, never `native_decide`.

**What the guarantees do not cover.** Floating-point rounding (the theorems are about the
solvers at `ℝ`; the `Float` run is the same code, up to rounding). Kernel-checked data
conditions need a kernel-evaluable representation: `bondOrders` is one, Morgan fingerprints
are not (their hashing uses `UInt32` and `mergeSort`), so a Jacobi/Gauss–Seidel certificate on
Morgan features can be computed with `#eval` but not yet proved by `decide +kernel`; the
gradient-descent certificate needs no evaluation and works for Morgan. Diagonal dominance
needs ridge: with an intercept, the normal equations of typical molecular data are not
diagonally dominant unless `λ` is large enough. And generalization: the guarantees bound the
training loss.

### Classification with Morgan fingerprints

[`Pipelines/Examples/egfr.lean`](Pipelines/Examples/egfr.lean) redoes ENCH 470 Lecture 21 in
Lean: EGFR actives vs. inactives (`ench470-content/`), featurized by `morganFeatures`
(parse, `Molecule.aromatize`, the toolkit's Morgan on-bits, 2048 bits), classified by
`LeanLearn.Classification.fitLogistic`,
test accuracy 0.925, then the five FDA-approved EGFR drugs.

```bash
lake exe logistic-test   # EGFR classification vs scikit-learn (tools/sklearn_egfr.py)
```

The test trains twice, on RDKit's fingerprint bits (stored in
`datasets/egfr-classification.csv`) and on Lean's own `morganFeatures`, which equal RDKit's
on all 205 molecules; both match scikit-learn's probabilities to 10⁻⁶.

### Regression with Morgan fingerprints

Delaney's measured log solubility from the same 2048 Morgan bits, with
`LeanLearn.Regression.SparseRidge` (α = 1) and the lecture's 80/20 split. `lake exe
ridge-test` checks it against scikit-learn's `Ridge` (`tools/sklearn_delaney.py`,
`datasets/delaney-ridge.csv`) and computes R², RMSE and MAE in Lean:

| | R² | RMSE | MAE |
|---|---|---|---|
| on RDKit's bits (= scikit-learn, predictions within 10⁻⁶), test | 0.671 | 1.26 | 0.94 |
| on Lean's own features, test | 0.662 | 1.27 | 0.96 |

Lean's own features equal RDKit's on 1 068 of the 1 127 molecules the parser accepts
(chlorothalonil's ring label after a branch is rejected); the rest need RDKit's `cleanUp`,
which `aromatize` does not do yet. The training fit is much closer (R² 0.96), the usual
sign of more features than molecules.

```bash
lake exe ridge-test --svg docs/figures/delaney-ridge-parity.svg   # also writes the parity plot
```

[`docs/figures/delaney-ridge-parity.svg`](docs/figures/delaney-ridge-parity.svg) is that plot,
written by `LeanLearn.Plot.paritySvg`, with R², RMSE and MAE for each split.

## Project layout

```
LeanSMILES/           the typed SMILES toolkit (imports Mathlib)
  Chem/               Element, Atom, Bond, Molecule n, Mathlib graph and matrix views, charges
  SMILES/             tokenizer, parser, writer, canonical SMILES and its canonicity proof
  Fingerprint/        RDKit-compatible Morgan fingerprints on Molecule n; order-invariance proof
  Aromaticity/        Molecule.aromatize: RDKit's ring set, kekulization, aromaticity perception
  Depict/             2D depiction: layout, SVG, mol blocks, #draw for the Infoview, lake exe depict
  Data/               CSV parser (columns by header name) for the Delaney dataset
  Tests/              validity, oracle, Morgan, aromaticity, charge, parse-error and depiction tests (lake exe …-test)
  Examples/           caffeine.lean, smiles.lean, parsercsv.lean, depict.lean
LeanLearn/            learning algorithms on tabular data (imports Mathlib only); see its README.md
  Scalar.lean         ScalarLike: the scalar interface, Float to run and ℝ to prove (from LeanCatalyst)
  Regression/         executable, over any scalar: Problem, Solvers, Certificates (iterative);
                      LinearModel (the objectives on a matrix); OLSFloat, RidgeFloat (QR, Float);
                      SparseRidge (conjugate gradients, sparse 0/1); Metrics (R², RMSE, MAE)
  Classification/     Logistic
  Plot/               parity plots as SVG
  Proofs/             over ℝ. LeastSquares/: OLS, Ridge, RidgeOLS — the closed form on Mathlib
                      matrices. Regression/: the executable code read in ℝ — the quadratic loss,
                      gradient descent, Jacobi and Gauss–Seidel, certificate soundness, and the
                      bridges to the closed form (MatrixBridge, LinearModel)
  Examples/           ols.lean, ridge.lean (worked proofs), olsFloat.lean, ridgeFloat.lean (runs)
  Tests/              OLSFloat, RidgeFloat, LinearModel (lake exe …-test)
Pipelines/            molecules as tabular data (imports both)
  Representation.lean morgan, bondOrders, counts, canonical, clip, ++; morganFeatures (aromatized)
  Pipeline.lean       LabelledMolecules (from SMILES), Pipeline, model, losses, predictions
  Data.lean           LabelledMolecules from the CSV tables in datasets/ (via CSVparser)
  Certificates.lean   the exact checks on a pipeline: checkGD, checkSolver, certifiedSolverExcess
  Proofs/             representations (bounds, canonicity), certificate soundness
  Examples/           delaney.lean (certified solubility regression), egfr.lean (classification)
  Tests/              Logistic, Ridge (lake exe logistic-test, ridge-test)
datasets/             Delaney (ESOL) data, RDKit oracle files (as written and Kekulé), the EGFR and
                      Delaney-ridge answer files
tools/                RDKit oracle and fuzz generators; sklearn_egfr.py and sklearn_delaney.py write
                      the scikit-learn answer files; check_depiction.py reads the drawings back with
                      RDKit; rdkit_reference/ holds the pure-Python references the RDKit ports follow
docs/                 design notes, REFERENCES.md and references.bib; figures/ holds plots written by Lean
ench470-content/      ENCH 470 course notebooks and data
```

### Module system

Every file is a Lean `module`, so what a file exports is a decision, not an accident:

* `public import` re-exports a dependency to whoever imports the file; a plain `import` is
  private to the file. Project modules and the Mathlib modules whose types appear in
  signatures are public; tactic-only imports (`Mathlib.Tactic.*`, `Std`, `Lean`) are private.
  So `import LeanSMILES.SMILES.Canon` still brings the whole toolkit, and
  `import LeanLearn.Regression.Solvers` the scalar interface and the regression problem.
* Library files open `@[expose] public section`: their declarations are public and their
  definition bodies can be unfolded downstream — which `decide +kernel`, `rfl` and
  `simp [f]` need (the Delaney certificates reduce the SMILES parser in the kernel).
  Theorem-only files open `public section`.
* Examples and tests open `public section` too, so their theorems can be cited. A file
  whose `#eval`s run code from another module also `meta import`s that module: under the
  module system, code that runs at elaboration time is a separate phase, and a `meta
  import` is what loads it there. The one file that proves certificates by `decide +kernel`
  (`Pipelines/Examples/delaney.lean`) also `import all`s the three core modules whose array
  loops the kernel has to run — core does not expose their bodies.

Merging this branch into `main`: see [`MERGE-NOTES.md`](MERGE-NOTES.md).

## References

LeanSMILES builds on prior work in Lean, cheminformatics, and chemistry
education. [`docs/REFERENCES.md`](docs/REFERENCES.md) credits each source and says
what it is credited for; [`docs/references.bib`](docs/references.bib) has the BibTeX.

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
* **RDKit Morgan fingerprints depend on atom order from radius 3.** When two
  atoms' environments cover the same bonds, RDKit keeps the one with the
  smaller (identifier, atom index) and the other stops growing. If the
  identifiers are equal too, the atom index decides, and the survivor's
  identifiers at the next radius can differ from the loser's. In
  `C1=C(CO)C=C1CC`, a cyclobutadiene with ethyl and hydroxymethyl groups, the
  two ring CH carbons tie at radius 2 without being symmetric (one is
  single-bonded to the ethyl-bearing carbon and double-bonded to the other,
  the second the reverse). Over all 8! atom orders, RDKit 2026.09.1 gives one
  fingerprint at radii 1 and 2 and two at radii 3 and 4; the spelling
  `C1(CC)=CC(CO)=C1` has a different radius-3 identifier (58732580 instead of
  837408524) and different folded bits. So ECFP6 is not a function of the
  molecule. LeanSMILES reproduces RDKit's fingerprint bit for bit, including
  this, and proves the fingerprint independent of atom order up to radius 2,
  the default: `Molecule.morganBits_relabel`
  (`LeanSMILES/Fingerprint/MorganInvariance.lean`). A tie at radius 1 can only
  be a two-atom fragment, which emits nothing more whichever atom survives; a
  tie at radius 2, as here, first shows at radius 3. The bound is sharp:
  `Molecule.not_forall_morganBits_relabel_three`
  (`LeanSMILES/Fingerprint/MorganRadius3.lean`) proves, by kernel computation on
  this molecule, that swapping its two ring CH carbons changes the radius-3
  fingerprint and leaves the radius-2 one alone.
