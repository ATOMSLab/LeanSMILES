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
