# LeanSMILES
Formalizing molecular representations in Lean: a SMILES → features → machine-learning
pipeline whose algorithms are written once, run on `Float`, and are proved correct over `ℝ`.

## Getting started

1. Download the project's dependencies and Mathlib's precompiled cache, then
   check the project:

   ```bash
   lake exe cache get
   lake build
   ```

2. `lake build` also runs the test suite. Each file in `LeanSMILES/Tests/` tests one part
   of the system with `#test` checks, and a failing check fails the build. To run a single
   test file:

   ```bash
   lake build LeanSMILES.Tests.CanonicalSMILES
   ```

3. Run the example: load the Delaney (ESOL) solubility dataset, clean and validate the
   SMILES, train a linear model on Morgan fingerprints, and predict the log solubility of
   new SMILES strings with `predictSolubilityMessage`:

   ```bash
   lake lean LeanSMILES/Examples/PredictSolubility.lean
   ```

   Use `lake lean`, not `lake env lean`: only `lake lean` (and the editor) load the
   precompiled native code, which is about 100× faster.

## Project layout

```
LeanSMILES/
  Primitives/       Scalar interface, Float instance, exact decimals, dense and sparse
                    linear algebra, algorithm parameters; Real.lean is the ℝ instance
  SMILES/           molecules: parsing, canonical SMILES, Morgan fingerprints, descriptors
  MachineLearning/  linear regression (closed form, dense and sparse gradient descent),
                    perceptron
  Optimization/     gradient-descent convergence theorems over ℝ (from TorchLean)
  LearningTheory/   algorithmic stability; 1D ridge regression: closed form, uniform
                    stability, unique minimizer (over ℝ)
  API/              the pipeline: CSV loading, validation, features, train/test split,
                    metrics, SMILES → prediction
  MetaPrograms/     `#test` and `cached def` (notebook-style values computed once)
  Tests/            one test file per component, run by `lake build`
  Examples/         PredictSolubility.lean
  Data/             delaney-processed.csv
notebooks/          the original Python (RDKit + scikit-learn) project notebook
```

`SMILES/` and `MachineLearning/` each split into four layers:

| File | Contents | Library |
|---|---|---|
| `Types.lean` | data types | `LeanSMILESExec` |
| `Definitions.lean` | algorithms, generic over `[Scalar α]` | `LeanSMILESExec` |
| `Executables.lean` | the definitions at `α := Float`; `*_eq` lemmas hold by `rfl` | `LeanSMILESExec` |
| `Proofs.lean` | theorems at `α := ℝ`, with Mathlib | `LeanSMILES` |

`LeanSMILESExec` imports no Mathlib and is precompiled to native code. Because the code
that runs is the generic definition, a theorem about it over `ℝ` describes the `Float`
code up to rounding. Where the compiled code uses a faster implementation, the two are
proved equal: `Molecule.morganFingerprint_eq_fast` (a `@[csimp]` lemma) and
`ML.linRegGDSparse_eq` (sparse gradient descent = dense gradient descent).

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
product) and rewrite with `iterate_eq_iterate`. The files are copied from
[TorchLean](https://github.com/lean-dojo/TorchLean) (MIT; `LICENSES/TorchLean-MIT.txt`), and
each file's header records the source commit and every change made here.
