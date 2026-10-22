/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanLearn.Scalar

/-!
# Regression metrics

How close predictions are to measured values, as scikit-learn reports them:
`r2` (coefficient of determination, `r2_score`), `rmse` (root mean squared
error) and `mae` (mean absolute error, `mean_absolute_error`), the last two in
the units of the target. Each takes (measured, predicted) pairs and is written
over `ScalarLike`.
-/

@[expose] public section

namespace LeanLearn.Regression

variable {K : Type} [ScalarLike K]

/-- Coefficient of determination `1 − SS_res / SS_tot` of predictions against
measured values (scikit-learn's `r2_score`). -/
def r2 (pairs : Array (K × K)) : K :=
  let count : K := pairs.foldl (fun s _ ↦ s + 1) 0
  let mean := pairs.foldl (fun s (y, _) ↦ s + y) 0 / count
  let ssRes := pairs.foldl (fun s (y, p) ↦ s + (y - p) * (y - p)) 0
  let ssTot := pairs.foldl (fun s (y, _) ↦ s + (y - mean) * (y - mean)) 0
  1 - ssRes / ssTot

/-- Root mean squared error of predictions against measured values. -/
def rmse (pairs : Array (K × K)) : K :=
  let count : K := pairs.foldl (fun s _ ↦ s + 1) 0
  ScalarLike.sqrt (pairs.foldl (fun s (y, p) ↦ s + (y - p) * (y - p)) 0 / count)

/-- Mean absolute error of predictions against measured values. -/
def mae (pairs : Array (K × K)) : K :=
  let count : K := pairs.foldl (fun s _ ↦ s + 1) 0
  pairs.foldl (fun s (y, p) ↦ s + ScalarLike.abs (y - p)) 0 / count

end LeanLearn.Regression
