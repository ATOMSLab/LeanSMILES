# LeanSMILES
Formalizing molecular representations in Lean

The repository has two parts that build together:

* **A typed SMILES toolkit** (`LeanSMILES.*`): SMILES → `Molecule n` → canonical SMILES and
  Morgan fingerprints, with Mathlib graph and matrix views, canonical SMILES proved
  canonical, and tests against RDKit.
* **Certified cheminformatics pipelines** (`Polymorphic/`, `Float/`, `Real/`, `Proofs/`):
  describe a pipeline — labelled molecules, a molecular representation, a learning algorithm
  and its hyperparameters — and prove what the trained model is guaranteed to satisfy,
  without training it. Every definition is written once, polymorphic over a scalar type `α`;
  theorems are proved at `α := ℝ` and the same code runs at `α := Float`.

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

   `lake build` also checks every proof and the worked example
   `LeanSMILES/Examples/CertifiedPipeline.lean`
   (`lake build LeanSMILES.Examples.CertifiedPipeline` checks it alone).

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

**1. Write the pipeline**, once, for any scalar type:

```lean
def esolPipeline (α : Type) [Scalar α] : Pipeline α 6 1024 where
  data := esolData α                                  -- molecules + targets
  representation := .morgan 2 1024                    -- radius-2, 1024-bit fingerprints
  algorithm := .gradientDescent ⟨1 / Scalar.fromNat 2050, 41000⟩   -- step size, iterations
```

**2. Fill in its certificate.** Each field is a condition on the parameters. The feature bound
comes from a lemma about the representation, and the rest is arithmetic that `norm_num` closes:

```lean
noncomputable def esolCertificate :
    Pipeline.GDCertificate (esolPipeline ℝ).representation ⟨1 / Scalar.fromNat 2050, 41000⟩ where
  R2 := (1024 : ℕ)                                    -- ‖φ(mol)‖² ≤ 1024 for every molecule
  B := 1                                              -- compare with models of norm² ≤ 1
  ε := 1 / 20                                         -- tolerated excess training error
  bounded := Representation.morgan_bounded 2 1024
  stepSize_pos := by norm_num
  stepSize_small := by norm_num                       -- 2η(R² + 1) ≤ 1
  iters_pos := by norm_num
  iters_enough := by norm_num                         -- B ≤ 2ηkε
```

If a condition fails, for example a step size too large for the representation, `norm_num`
proves its negation and there is no certificate.

**3. Use the guarantee:**

```lean
theorem esol_guarantee (u : LinearModel ℝ 1024) (hu : normSq u.toParams ≤ 1) :
    (esolPipeline ℝ).trainMSE ≤ mse u (esolPipeline ℝ).dataset + 1 / 20 :=
  esolCertificate.sound (esolPipeline ℝ) rfl u hu
```

The certificate never mentions the data, so the guarantee holds for every dataset.

**Perceptron pipelines** need a separator with a positive margin on the training molecules.
For bit representations (such as Morgan fingerprints) you can give it as an integer
`PerceptronWitness`. The kernel then parses the SMILES, computes the fingerprints and checks the
witness:

```lean
theorem hydroxylWitness_check :
    hydroxylWitness.check (fun m => (m.morganFingerprint 0 64).bits)
      solubilityClassifier.data.molecules solubleLabels 45 = true := by
  decide +kernel

theorem solubility_guarantee (i : Fin 8) :   -- every training molecule classified correctly
    solubilityClassifier.model.classify (solubilityClassifier.representation.featurize
      solubilityClassifier.data.molecules[i]) = solubilityClassifier.data.targets[i] :=
  (hydroxylWitness.certificate solubilityClassifier rfl rfl (by norm_num)
    hydroxylWitness_check).sound rfl i
```

## What is proved

### Pipelines ([`Proofs/Pipeline.lean`](LeanSMILES/Proofs/Pipeline.lean), [`Proofs/Certificates.lean`](LeanSMILES/Proofs/Certificates.lean))

| Algorithm | Conditions (checked without training) | Guarantee |
|---|---|---|
| Gradient descent | `‖φ‖² ≤ R²` for the representation, `η > 0`, `2η(R² + 1) ≤ 1`, `B ≤ 2ηkε` | training MSE ≤ MSE of any model with `‖(w, b)‖² ≤ B`, plus `ε`, for **every dataset** (`GDCertificate.sound`); MSE non-increasing in `k` (`gd_antitone`); the `O(1/k)` rate (`gd_rate`) |
| Perceptron | `±1` labels, a separator with `‖u‖ ≤ 1` and margin `γ`, `‖φ‖² ≤ R²` on the data, `(R² + 1)/γ² ≤ epochs` | every training molecule classified correctly, training accuracy 1 (`PerceptronCertificate.sound`) |
| OLS | the augmented features of the training molecules are linearly independent | no linear model has a smaller training MSE (`ols_optimal_of_fullColumnRank`) |

### Machine learning ([`Proofs/ML/`](LeanSMILES/Proofs/ML))

* **Gradient descent converges at rate `O(1/k)`** (`mse_linRegGD_le`): with `2η ∑ᵢ‖xᵢ‖² ≤ m`, after `k` steps
  `mse(θₖ) ≤ mse(u) + ‖u‖² / (2ηk)` for every linear model `u`. Proved through convexity,
  sufficient decrease, and a telescoping distance argument.
* **Gauss–Jordan elimination is correct** ([`Proofs/LinSolve.lean`](LeanSMILES/Proofs/LinSolve.lean)):
  if `A` is invertible, `linSolve A b` (with partial pivoting) solves `A x = b`, and it is the
  only solution (`linSolve_spec`, `linSolve_unique`, `linSolve_spec_of_det_ne_zero`).
* Least squares: the loss is an exact quadratic; zero gradient ⟺ global minimum; normal equations,
  solved by `linSolve` whenever the features have full column rank; a fixed point of gradient
  descent is optimal; the sparse solver computes the same iterates.
* Perceptron: Novikoff's mistake bound `mistakes ≤ (R/γ)²` (for any separator with `‖u‖ ≤ 1`),
  convergence within `⌊(R/γ)²⌋` epochs, and stability afterwards.
* Lipschitz predictions: `(score x − score x')² ≤ ‖w‖² ‖x − x'‖²`.

### Molecular representations ([`Proofs/Chem/`](LeanSMILES/Proofs/Chem))

* **Matrices** (`Matrices.lean`), for well-formed molecules:
  * the adjacency, bond-order and weighted adjacency matrices are symmetric with zero diagonal;
  * row sums are the degrees (or total bond orders), and `∑ deg = 2 · #bonds` (handshake lemma);
  * for every Laplacian `L = D − W`: `L𝟙 = 0`, `tr L = 2∑w_b`, and
    `xᵀLx = ∑_bonds w_b (x_s − x_d)²`, so `L` is positive semidefinite, and `xᵀLx = 0` forces
    `x` to be constant along bonds;
  * Zagreb indices: `M₁ = ∑ deg²` and `M₂ = ∑_bonds deg(s)·deg(d)`.
* **Topological distance** (`Distance.lean`): breadth-first distance is a metric (zero exactly on
  the diagonal, symmetric, triangle inequality), and bonded atoms are at distance 1. The distance
  and topological Coulomb matrices are symmetric, and the Wiener index is non-negative.
* **Fingerprints** (`Fingerprint.lean`): the squared feature distance between two fingerprints
  equals their Hamming distance. So, for any linear model,
  `(pred a − pred b)² ≤ ‖w‖² · hamming(a, b)`: molecules with similar fingerprints get similar
  predictions.
* **Feature bounds** (`Representation.lean`), for every molecule: `morgan` ≤ `nBits`,
  `adjacency k` ≤ `k²`, `clip c r` ≤ `n c²`, `normalize r` ≤ 1, `scale c r` ≤ `c² R²`, and
  `r₁ ++ r₂` ≤ `R₁² + R₂²`.

All of these depend only on Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
Kernel checks use `decide +kernel`, never `native_decide`.

## What the guarantees do not cover

* **Floating-point rounding.** Theorems are about the definitions at `α := ℝ`, and the `Float`
  code is the same definitions at `α := Float`. They agree up to rounding, which is not modelled.
* **OLS on rank-deficient data.** When the features are linearly dependent, the normal equations
  have many solutions and Gauss–Jordan hits a zero pivot. No guarantee is given then.
* **Generalization.** The guarantees bound the training error. For unseen molecules, the
  available bound is the Lipschitz one: predictions move by at most `‖w‖ · √hamming`.
* **The pipeline's canonical SMILES** (`Polymorphic/Chem/SMILES.lean`) is proved to be a function
  of the molecule only; that it does not depend on atom order is not proved. The toolkit's
  canonical SMILES (`LeanSMILES.SMILES.Canon`) is: `Mol.canonicalSmiles_relabel`.

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
  Polymorphic/        definitions, written once for any [Scalar α]; no Mathlib
    Scalar.lean         the scalar interface
    LinAlg.lean         vectors, matrices, sparse products, Laplacians, linear solves
    Chem/               molecules: SMILES parsing and canonical form, graph, Morgan fingerprints,
                        descriptors, matrix representations, topological distance,
                        Representation (feature maps and combinators)
    ML/                 linear models, gradient descent, least squares, perceptron, metrics,
                        Algorithm (the learner as data)
    Pipeline.lean       Pipeline = labelled molecules + representation + algorithm
    Certificates.lean   integer witnesses that the kernel checks
  Float/              the Float instance and precompiled specializations (runs the code)
  Real/               the ℝ instance (used by the proofs)
  Proofs/             all theorems, mirroring Polymorphic/
  Optimization/       gradient-descent convergence theorems over ℝ (from TorchLean)
  LearningTheory/     algorithmic stability; 1D ridge regression: closed form, uniform
                      stability, unique minimizer (over ℝ)
  Examples/           CertifiedPipeline.lean, caffeine.lean, smiles.lean, parsercsv.lean
datasets/             Delaney (ESOL) data and RDKit oracle files for the tests
docs/                 design notes and the build memory report
ench470-content/      ENCH 470 course notebooks and data
notebooks/            the original Python (RDKit + scikit-learn) project notebook
```

The two parts use different molecule types: the toolkit's `LeanSMILES.Molecule n` and the
pipeline's `Chem.Molecule` (`Polymorphic/Chem/`). They do not depend on each other yet.

`Polymorphic/` and `Float/` form the `LeanSMILESExec` library. It imports no Mathlib and is
precompiled to native code, so `#eval` runs at compiled speed (use `lake lean`, not
`lake env lean`, to load the native code). Everything else forms the `LeanSMILES`
library.

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
