/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
import LeanSMILES.Algorithms.RidgeFloat

/-!
# Running ridge regression on Float data

From the repository root:
`lake env lean --run LeanSMILES/Algorithms/RidgeFloatExamples.lean`

The first column of ones is an explicit intercept. The example exempts it
from the ridge penalty, then fits a singular design with all columns penalized.
-/

open LeanSMILES.Algorithms.RidgeFloat

private def getResult {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e.toString)

def main : IO Unit := do
  let X : Design := #[#[1.0, 0.0], #[1.0, 1.0], #[1.0, 2.0]]
  let y : Array Float := #[1.0, 3.0, 5.0]
  let cfg : Config := { penalty := 2.0, unpenalizedColumn := some 0 }
  let model ← getResult (fit X y cfg)
  IO.println s!"Ridge coefficients [intercept, slope] = {model.coefficients}"
  IO.println s!"Predictions on the input rows = {← getResult (model.predictAll X)}"
  IO.println s!"Prediction at x = 3 = {← getResult (model.predict #[1.0, 3.0])}"
  IO.println s!"Sum of squared errors = {← getResult (model.sumSquaredError X y)}"
  IO.println s!"Penalized loss = {← getResult (model.penalizedLoss X y)}"

  let singularX : Design := #[#[1.0, 1.0], #[1.0, 1.0]]
  let singular ← getResult (fit singularX #[1.0, 3.0])
  IO.println s!"Regularized duplicate columns = {singular.coefficients}"
