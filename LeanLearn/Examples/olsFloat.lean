/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.OLSFloat
-- The same modules again as `meta` imports: the `#eval`s run their code at elaboration time.
meta import LeanLearn.Regression.OLSFloat

/-!
# Running OLS on Float data

Open this file in the editor: the Infoview shows the output of `#eval run` (and so does
`lake build`).

These are executable computations. The exact-real proofs and worked proof
examples are in `OLS.lean` and `OLSExamples.lean` respectively.
-/

public section

namespace LeanLearn.Examples.OLSFloat

open LeanLearn.Regression.OLSFloat

private def getResult {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError e.toString)

def run : IO Unit := do
  -- Column 0 is the intercept; column 1 contains x = 0, 1, 2.
  let X : Design := #[#[1.0, 0.0], #[1.0, 1.0], #[1.0, 2.0]]
  let y : Array Float := #[1.0, 3.0, 5.0]
  let model ← getResult (fit X y)
  IO.println s!"Exact line: coefficients [intercept, slope] = {model.coefficients}"
  IO.println s!"Predictions on the input rows = {← getResult (model.predictAll X)}"
  IO.println s!"Prediction at x = 3 = {← getResult (model.predict #[1.0, 3.0])}"
  IO.println s!"Sum of squared errors = {← getResult (model.sumSquaredError X y)}"

  let noisyY : Array Float := #[1.0, 2.0, 4.0]
  let noisy ← getResult (fit X noisyY)
  IO.println s!"Noisy line: coefficients = {noisy.coefficients} (expected [5/6, 3/2])"
  IO.println s!"Sum of squared errors = {← getResult (noisy.sumSquaredError X noisyY)}"

  -- Repeated columns cannot determine a unique pair of coefficients.
  match fit #[#[1.0, 1.0], #[1.0, 1.0]] #[1.0, 3.0] with
  | .error e => IO.println s!"Singular design: {e}"
  | .ok _ => throw (IO.userError "expected rejection of the singular design")

#eval run

end LeanLearn.Examples.OLSFloat
