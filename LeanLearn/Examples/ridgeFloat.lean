/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.RidgeFloat
-- The same modules again as `meta` imports: the `#eval`s run their code at elaboration time.
meta import LeanLearn.Regression.RidgeFloat

/-!
# Running ridge regression on Float data

Open this file in the editor: the Infoview shows the output of `#eval run` (and so does
`lake build`).

The first column of ones is an explicit intercept. The example exempts it
from the ridge penalty, then fits a singular design with all columns penalized.
-/

public section

namespace LeanLearn.Examples.RidgeFloat

open LeanLearn.Regression.RidgeFloat

private def getResult {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e.toString)

def run : IO Unit := do
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

#eval run

end LeanLearn.Examples.RidgeFloat
