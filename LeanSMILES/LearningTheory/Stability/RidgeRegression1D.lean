/-
Copyright (c) 2026 TorchLean
Released under MIT license as described in the file LICENSES/TorchLean-MIT.txt.
Authors: TorchLean Team
-/

module

public import LeanSMILES.LearningTheory.Stability.RidgeRegression1D.Real
public import LeanSMILES.LearningTheory.Stability.RidgeRegression1D.Minimizer

/-!
# 1D ridge regression (stability): umbrella import

- `LeanSMILES.LearningTheory.Stability.RidgeRegression1D.Real`: the closed-form estimator over `ℝ`
  and its replace-one uniform stability theorem.
- `LeanSMILES.LearningTheory.Stability.RidgeRegression1D.Minimizer`: for `λ > 0`, that closed form
  is the unique minimizer of the ridge objective (LeanSMILES addition, not from TorchLean).

This short umbrella module lets downstream code write
`import LeanSMILES.LearningTheory.Stability.RidgeRegression1D`
without needing to remember the internal file split.

## Provenance

Adapted from TorchLean (`NN/MLTheory/LearningTheory/Stability/RidgeRegression1D.lean`, `main` at
`772b6b8`), MIT-licensed; see `LICENSES/TorchLean-MIT.txt`. TorchLean keeps an executable float32
version of the fit (on its own IEEE-754 kernel) in a separate module; that version is not ported
here.
-/

@[expose] public section
