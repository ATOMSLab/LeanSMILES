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
sanitized ones (no aromaticity perception here, by design), and they are always invariant
under relabeling of the atoms.

```lean
#eval (Mol.ofSmiles! "CCO").morganBits        -- [80, 222, 294, 807, 1057, 1410, ...]
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
```

## Three libraries

The repository builds three Lean libraries, with one direction of dependency:

| Library | What it is | Imports |
|---|---|---|
| [`LeanSMILES/`](LeanSMILES) | SMILES → typed molecular graph → canonical SMILES, Morgan fingerprints, matrices | Mathlib |
| [`LeanLearn/`](LeanLearn) | learning algorithms on tabular data (`X`, `y`) and their proofs: linear regression, logistic regression, iterative solvers and their certificates, optimization, learning theory | Mathlib only — no chemistry |
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

* **Closed form, over `ℝ`** ([`Regression/OLS.lean`](LeanLearn/Regression/OLS.lean),
  [`Ridge.lean`](LeanLearn/Regression/Ridge.lean); Hao Liu). `X : Matrix (Fin n) (Fin p) ℝ`,
  loss `‖Xw − y‖²`, plus `Σⱼ ρⱼ wⱼ²` for ridge. Any solution of the normal equations is a
  global minimizer, with no rank assumption; `fit = (XᵀX)⁻¹ Xᵀy` satisfies them and is the
  unique minimizer when `det(XᵀX) ≠ 0`; positive ridge has a unique minimizer for every
  design, even underdetermined ones. [`LinearModel.lean`](LeanLearn/Regression/LinearModel.lean)
  writes the same objectives over `PolynomialLike`, so they run at `Float`, and proves that
  their `ℝ` reading is the specification. [`OLSFloat.lean`](LeanLearn/Regression/OLSFloat.lean)
  and [`RidgeFloat.lean`](LeanLearn/Regression/RidgeFloat.lean) are executable Householder-QR
  solvers on `Float` arrays, with input validation and no formal rounding bound. Worked proofs
  in [`Examples/ols.lean`](LeanLearn/Examples/ols.lean) and
  [`ridge.lean`](LeanLearn/Examples/ridge.lean); details in
  [`LeanLearn/Regression/README.md`](LeanLearn/Regression/README.md).
* **Iterative, over any scalar** ([`Regression/Problem.lean`](LeanLearn/Regression/Problem.lean),
  [`Solvers.lean`](LeanLearn/Regression/Solvers.lean); DeMarko Fulcher). The ridge problem
  `(1/m) Σᵣ (⟪xᵣ, θ⟫ − yᵣ)² + λ‖θ‖²` with an intercept, its normal equations `Aθ = b`, and
  gradient descent, Jacobi and Gauss–Seidel on them, started from `0`; `Algorithm` is the
  solver with its hyperparameters, as data. [`Certificates.lean`](LeanLearn/Regression/Certificates.lean)
  is the exact `ℚ` check (`SolverWitness`: weighted diagonal dominance) that certifies
  Jacobi and Gauss–Seidel before running them.

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

[`Proofs/Regression/`](LeanLearn/Proofs/Regression):

* **The loss is an exact quadratic**: `L(θ + v) = L(θ) + 2⟪Aθ − b, v⟫ + vᵀAv`; so solutions
  of the normal equations are global minimizers.
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

### Optimization and learning theory (from TorchLean)

[`Optimization/`](LeanLearn/Optimization) and
[`LearningTheory/`](LeanLearn/LearningTheory) are proofs over `ℝ` that import only Mathlib;
nothing executable depends on them.

- `Optimization/StronglyConvexGD.lean`: for a μ-strongly monotone, L-Lipschitz `g` on a real
  inner product space, each step of `x ↦ x − η g(x)` shrinks the squared distance to the
  root of `g` by the factor `1 − 2ημ + η²L²`, which is below 1 when `0 < η` and `ηL² < 2μ`;
  the iterates converge to the root. `SmoothStrongConvexBridge.lean` derives strong
  monotonicity of `∇f` from `StrongConvexOn`; the Lipschitz constant of `∇f` stays a
  hypothesis.
- `LearningTheory/Stability/RidgeRegression1D/Real.lean`: replace-one uniform stability of
  the closed-form 1D ridge fit, with `β = 4X²Y²(λ+X²)²/(λ³N)`.
- `LearningTheory/Stability/RidgeRegression1D/Minimizer.lean` (written here, not from
  TorchLean): for `λ > 0` the closed form is the unique minimizer of
  `(1/N) Σ (w xᵢ − yᵢ)² + λ w²`.

To apply the gradient-descent theorems to `LeanLearn.Regression.gradientDescent`,
instantiate them on `EuclideanSpace ℝ (Fin n)` (Mathlib's `Fin n → ℝ` carries the sup norm,
not an inner product). The files are copied from
[TorchLean](https://github.com/lean-dojo/TorchLean) (MIT; `LICENSES/TorchLean-MIT.txt`), and
each file's header records the source commit and every change made here.

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
(the toolkit's Morgan on-bits, 2048 bits), classified by `LeanLearn.Classification.fitLogistic`,
test accuracy 0.925, then the five FDA-approved EGFR drugs.

```bash
lake exe logistic-test   # EGFR classification vs scikit-learn (tools/sklearn_egfr.py)
```

The test trains twice: on RDKit's fingerprint bits (stored in
`datasets/egfr-classification.csv`), where every probability matches scikit-learn's to 10⁻⁶,
and on Lean's own `morganFeatures`, which differ from RDKit's sanitized fingerprints on some
molecules (no aromaticity perception yet) but give the same predicted class for every
molecule.

## Project layout

```
LeanSMILES/           the typed SMILES toolkit (imports Mathlib)
  Chem/               Element, Atom, Bond, Molecule n, Mathlib graph and matrix views, charges
  SMILES/             tokenizer, parser, writer, canonical SMILES and its canonicity proof
  Fingerprint/        RDKit-compatible Morgan fingerprints on Molecule n
  Data/               CSV parser for the Delaney dataset
  Tests/              validity, oracle, Morgan, charge and parse-error tests (lake exe …-test)
  Examples/           caffeine.lean, smiles.lean, parsercsv.lean
LeanLearn/            learning algorithms on tabular data (imports Mathlib only)
  Scalar.lean         ScalarLike: the scalar interface, Float to run and ℝ to prove (from LeanCatalyst)
  Regression/         Problem, Solvers, Certificates (iterative, any scalar);
                      OLS, Ridge, LinearModel (closed form, ℝ); OLSFloat, RidgeFloat (QR, Float)
  Classification/     Logistic
  Proofs/Regression/  the quadratic loss, gradient descent, Jacobi and Gauss–Seidel, certificate soundness
  Optimization/       gradient-descent convergence over ℝ (from TorchLean)
  LearningTheory/     algorithmic stability; 1D ridge regression (from TorchLean)
  Examples/           ols.lean, ridge.lean (worked proofs), olsFloat.lean, ridgeFloat.lean (runs)
  Tests/              OLSFloat, RidgeFloat, LinearModel (lake exe …-test)
Pipelines/            molecules as tabular data (imports both)
  Representation.lean morgan, bondOrders, counts, canonical, clip, ++; morganFeatures
  Pipeline.lean       LabelledMolecules (from SMILES), Pipeline, model, losses, predictions
  Data.lean           LabelledMolecules from the CSV tables in datasets/ (via CSVparser)
  Certificates.lean   the exact checks on a pipeline: checkGD, checkSolver, certifiedSolverExcess
  Proofs/             representations (bounds, canonicity), certificate soundness
  Examples/           delaney.lean (certified solubility regression), egfr.lean (classification)
  Tests/              Logistic (lake exe logistic-test)
datasets/             Delaney (ESOL) data, RDKit oracle files, the EGFR answer file
tools/                sklearn_egfr.py: writes the EGFR answer file
docs/                 design notes
ench470-content/      ENCH 470 course notebooks and data
LICENSES/             TorchLean's MIT license
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
