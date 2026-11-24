/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.LinearModel
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Executable Float checks for the shared regression definitions

These are small numerical checks of predictions and objectives, not a training
or evaluation pipeline. The coefficients are supplied explicitly. The general
optimality proofs are in `Proofs/LeastSquares/` and `Proofs/Regression/LinearModel.lean`.

Run: `lake exe linear-model-test`
-/

namespace LeanLearn.Tests.LinearModel

open Matrix
open scoped Matrix
open LeanLearn.Regression.LinearModel

/-- The design `[1, xᵢ]` for `xᵢ = 0, 1, 2`: an intercept column and one feature, three rows. -/
def design : Design Float 3 2 := !![1, 0; 1, 1; 1, 2]

/-- The targets `1, 3, 5`, exactly `1 + 2 xᵢ` on the rows of `design`, so the coefficients
`![1, 2]` reproduce them with zero squared error. -/
def targets : Fin 3 → Float := ![1, 3, 5]

private def near (actual expected : Float) : IO Unit :=
  unless actual.isFinite && (actual - expected).abs ≤ 1e-10 * (1 + expected.abs) do
    throw (IO.userError s!"expected {expected}, received {actual}")

/-- Eight hand-computed checks of the Float objectives on `design` and `targets`: `![1, 2]` fits
`targets` exactly and `![2, 1]` solves the ridge normal equations for weights `![0, 2]`. Throws
at a mismatch. -/
def run : IO Unit := do
  let ols : Fin 2 → Float := ![1, 2]
  let ridge : Fin 2 → Float := ![2, 1]
  let weights : Fin 2 → Float := ![0, 2]
  near (predictRow ![1, 3] ols) 7
  near (predictRow ![1, 3] ridge) 5
  near (squaredError design targets ols) 0
  near (squaredError design targets ridge) 2
  near (penalty weights ridge) 2
  near (ridgeLoss design targets weights ridge) 4
  let g := normalResidual design targets weights ridge
  near (g 0) 0
  near (g 1) 0
  IO.println s!"OLS predictions: {Array.ofFn (predict design ols)}"
  IO.println s!"Ridge predictions: {Array.ofFn (predict design ridge)}"
  IO.println s!"Ridge squared error: {squaredError design targets ridge}"
  IO.println s!"Ridge objective: {ridgeLoss design targets weights ridge}"
  IO.println "8/8 Float definition checks passed"

end LeanLearn.Tests.LinearModel

/-- Entry point of the `linear-model-test` executable: runs every LinearModel Float check and
exits nonzero at the first failure. -/
public def main : IO Unit := LeanLearn.Tests.LinearModel.run
