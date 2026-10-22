# LeanSMILES
Formalizing molecular representations in Lean

The repository has two parts that build together:

* **A typed SMILES toolkit**: SMILES → `Molecule n` → canonical SMILES, Morgan fingerprints
  and bond-order matrices, with Mathlib graph and matrix views, canonical SMILES proved
  canonical, and tests against RDKit.
* **Certified linear-regression pipelines** (`Regression/`, `Pipeline/`, `Proofs/`), built on
  the toolkit: describe a pipeline — molecules from SMILES with exact targets, a molecular
  representation, a ridge penalty, and an iterative solver (gradient descent, Jacobi or
  Gauss–Seidel) with its hyperparameters — and prove what the trained model is guaranteed to
  satisfy, without training it. The solvers are written once over the toolkit's scalar
  interface (`LeanSMILES.Scalar`): they compute exactly over `ℚ` for certificates, run on
  `Float`, and are proved correct over `ℝ`.

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

   `lake build` also checks every proof and runs the examples, including
   `LeanSMILES/Examples/pipeline.lean`
   (`lake build LeanSMILES.Examples.pipeline` checks it alone).

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

## Certifying a pipeline

Open [`LeanSMILES/Examples/pipeline.lean`](LeanSMILES/Examples/pipeline.lean): like
`caffeine.lean`, it walks through the pipeline one `#eval` at a time, on the Delaney table.

**1. Data and pipeline.** Molecules come from SMILES (`LabelledMolecules.ofSmiles!`) or from
a table in `datasets/` (`ofRecords`, through the toolkit's `CSVparser`), with exact rational
targets. A pipeline adds a representation, a ridge penalty `λ` (default `0`) and a solver:

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

## What is proved

### Certificates ([`Proofs/Pipeline/Certificates.lean`](LeanSMILES/Proofs/Pipeline/Certificates.lean))

Write `L` for the training loss `(1/m) ∑ᵣ (⟪xᵣ, θ⟫ - yᵣ)² + λ ‖θ‖²` (`λ = 0`: least squares).

| Solver | Conditions (checked without training) | Guarantee |
|---|---|---|
| Gradient descent | `‖φ(M)‖² ≤ R²` for the representation, `λ ≥ 0`, `η > 0`, `2η(R² + 1 + λ) ≤ 1`, `B ≤ 2ηkε` | `L(θ) ≤ L(u) + ε` for every `u` with `‖u‖² ≤ B`, for **every dataset** (`GDCertificate.sound`) |
| Jacobi, Gauss–Seidel | the exact `ℚ` check of weighted diagonal dominance (`checkSolver`) | `L(θ) ≤ L(u) + ε` for **every** `u`: `θ` is `ε`-optimal (`checkSolver_sound`) |
| Gauss–Seidel | none (`λ ≥ 0`) | the loss never increases with more sweeps (`gaussSeidel_antitone`) |

### Linear regression ([`Proofs/Regression/`](LeanSMILES/Proofs/Regression))

* **The loss is an exact quadratic**: `L(θ + v) = L(θ) + 2⟪Aθ - b, v⟫ + vᵀAv` for the normal
  equations `Aθ = b`; so solutions of the normal equations are global minimisers.
* **Gradient descent**: sufficient decrease, monotone loss, and the `O(1/k)` rate
  `L(θₖ) ≤ L(u) + ‖u‖²/(2ηk)` for every `u`, when `2η((1/m)∑‖xᵣ‖² + λ) ≤ 1`.
* **Jacobi and Gauss–Seidel**, for any linear system with weighted diagonal dominance
  (`∑_{j≠i} |Aᵢⱼ| wⱼ ≤ ρ Aᵢᵢ wᵢ`, `ρ < 1`): a solution exists (Gershgorin), both iterations
  contract by `ρ` per step in the weighted max-norm, and the solution is bounded from `b`.
  On the normal equations this gives `L(θₖ) ≤ L(u) + Γβ²ρ²ᵏ`.
* **Gauss–Seidel is coordinate descent**: every update minimises the loss exactly along one
  coordinate, so it never increases the loss, for any data. A fixed point of Jacobi is
  optimal.

### Representations ([`Proofs/Pipeline/Representation.lean`](LeanSMILES/Proofs/Pipeline/Representation.lean))

* `bondOrder_eq_adjMatrix`: the kernel-evaluable bond-order features are the toolkit's
  `adjMatrix`.
* `canonical_relabel`: a representation read through canonical SMILES gives every atom
  numbering of a molecule the same features (from the toolkit's `canonicalSmiles_relabel`).
* Feature bounds for every molecule: Morgan `≤ fpSize`, bond orders `≤ 16k²`, `clip c` of
  anything `≤ d c²`, and through `canonical` and `++`.

Every theorem depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); kernel checks use `decide +kernel`, never `native_decide`.

## What the guarantees do not cover

* **Floating-point rounding.** Theorems are about the solvers at `ℝ`; the `Float` run is the
  same code, and agrees up to rounding, which is not modelled.
* **Kernel-checked data conditions need a kernel-evaluable representation.** `bondOrders` is
  one; the toolkit's Morgan fingerprints are not (their hashing uses `UInt32` and
  `mergeSort`, which the kernel cannot reduce). So a Jacobi/Gauss–Seidel certificate on
  Morgan features can be computed (`#eval p.checkSolver …`) but not yet proved by
  `decide +kernel`. Gradient-descent certificates need no evaluation and work for Morgan.
* **Diagonal dominance needs ridge.** With an intercept, the normal equations of typical
  molecular data are not diagonally dominant unless `λ` is large enough; the guarantee is
  then about the ridge loss. Gauss–Seidel's monotonicity needs no condition.
* **Generalization.** The guarantees bound the training loss.

## Project layout

```
LeanSMILES/
  Scalar.lean         ScalarLike scalar interface (from LeanCatalyst)
  Chem/               the typed SMILES toolkit: Element, Atom, Bond, Molecule n, Mathlib
                      graph and matrix views, BondMatrix / FlatMatrix
  SMILES/             tokenizer, parser, writer, canonical SMILES and its canonicity proof
  Fingerprint/        RDKit-compatible Morgan fingerprints on Molecule n
  Data/               CSV parser for the Delaney dataset
  Tests/              validity, oracle and Morgan tests against RDKit (lake exe …-test)
  Regression/         ridge regression and its solvers, over the scalar interface:
    Basic.lean          vectors, the problem, normal equations, loss
    Solvers.lean        gradient descent, Jacobi, Gauss–Seidel; Algorithm (the solver as data)
  Pipeline/           certified pipelines on the toolkit's molecules:
    Representation.lean morgan, bondOrders, counts, canonical, clip, ++
    Pipeline.lean       LabelledMolecules (from SMILES), Pipeline, model, losses, predictions
    Data.lean           LabelledMolecules from the CSV tables in datasets/ (via CSVparser)
    Certificates.lean   the exact checks: checkGD, SolverWitness, certifiedSolverExcess
  Proofs/             all theorems, over ℝ
    Regression/         the quadratic loss, gradient descent, Jacobi and Gauss–Seidel
    Pipeline/           representations, certificate soundness
  Optimization/       gradient-descent convergence theorems over ℝ (from TorchLean)
  LearningTheory/     algorithmic stability; 1D ridge regression: closed form, uniform
                      stability, unique minimizer (over ℝ)
  Examples/           caffeine.lean, smiles.lean, parsercsv.lean, pipeline.lean
datasets/             Delaney (ESOL) data and RDKit oracle files for the tests
docs/                 design notes and the build memory report
ench470-content/      ENCH 470 course notebooks and data
notebooks/            the original Python (RDKit + scikit-learn) project notebook
```

## Theorems ported from TorchLean

`Optimization/` and `LearningTheory/` are proofs over `ℝ` that import only Mathlib. Nothing
executable depends on them; `lake build` builds them, but the root module does not import
them.

- `Optimization/StronglyConvexGD.lean`: for a μ-strongly monotone, L-Lipschitz `g` on a real
  inner product space, each step of `x ↦ x - η g(x)` shrinks the squared distance to the
  root of `g` by the factor `1 - 2ημ + η²L²`, which is below 1 when `0 < η` and `ηL² < 2μ`;
  the iterates converge to the root. `SmoothStrongConvexBridge.lean` derives strong
  monotonicity of `∇f` from `StrongConvexOn`; the Lipschitz constant of `∇f` stays a
  hypothesis.
- `LearningTheory/Stability/RidgeRegression1D/Real.lean`: replace-one uniform stability of
  the closed-form 1D ridge fit, with `β = 4X²Y²(λ+X²)²/(λ³N)`.
- `LearningTheory/Stability/RidgeRegression1D/Minimizer.lean` (written here, not from
  TorchLean): for `λ > 0` the closed form is the unique minimizer of
  `(1/N) Σ (w xᵢ - yᵢ)² + λ w²`.

To apply the gradient-descent theorems to `ML.gradientDescent`, instantiate them on
`EuclideanSpace ℝ (Fin n)` (Mathlib's `Fin n → ℝ` carries the sup norm, not an inner
product) and rewrite with `Primitives.iterate_eq_iterate`. The files are copied from
[TorchLean](https://github.com/lean-dojo/TorchLean) (MIT; `LICENSES/TorchLean-MIT.txt`), and
each file's header records the source commit and every change made here.

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
