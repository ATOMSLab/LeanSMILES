/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.OLSFloat

/-!
# Numerical and input-validation checks for OLSFloat

Run from the repository root:
`lake exe ols-float-test`

Expected coefficients come from small independent algebraic examples.
Numerical tolerances accommodate rounding; these tests are not formal error bounds.
-/

namespace LeanLearn.Tests.OLSFloat

open LeanLearn.Regression.OLSFloat

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def near (actual expected : Float) : IO Unit :=
  require (actual.isFinite && (actual - expected).abs ≤ 1e-9 * (1 + expected.abs))
    s!"expected approximately {expected}, got {actual}"

private def getResult {α : Type} (result : Except Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error e => throw (IO.userError s!"unexpected error: {e}")

private def expectError {α : Type} (result : Except Error α) (expected : Error) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"expected {expected}, got success")
  | .error actual => require (actual == expected) s!"expected {expected}, got {actual}"

private def lineX : Design := #[#[1, 0], #[1, 1], #[1, 2]]

private def cases : Array (String × IO Unit) := #[
  ("exact line and prediction", do
    let m ← getResult (fit lineX #[1, 3, 5])
    require (m.coefficients.size == 2) "wrong coefficient count"
    near m.coefficients[0]! 1
    near m.coefficients[1]! 2
    near (← getResult (m.predict #[1, 3])) 7
    let predicted ← getResult (m.predictAll lineX)
    require (predicted.size == 3) "wrong prediction count"
    for i in [0:3] do near predicted[i]! (#[1.0, 3.0, 5.0][i]!)
    near (← getResult (m.sumSquaredError lineX #[1, 3, 5])) 0),
  ("noisy line and nonzero minimum loss", do
    let m ← getResult (fit lineX #[1, 2, 4])
    near m.coefficients[0]! (5 / 6)
    near m.coefficients[1]! (3 / 2)
    near (← getResult (m.sumSquaredError lineX #[1, 2, 4])) (1 / 6)),
  ("multiple features", do
    let X : Design := #[#[1, 0, 0], #[1, 1, 0], #[1, 0, 1], #[1, 1, 1], #[1, 2, -1]]
    let y : Array Float := #[3, 5, -1, 1, 11]
    let m ← getResult (fit X y)
    near m.coefficients[0]! 3
    near m.coefficients[1]! 2
    near m.coefficients[2]! (-4)
    near (← getResult (m.sumSquaredError X y)) 0),
  ("one observation and one coefficient", do
    let m ← getResult (fit #[#[2]] #[6])
    near m.coefficients[0]! 3),
  ("no implicit intercept", do
    let m ← getResult (fit #[#[1], #[2], #[3]] #[1, 2, 4])
    require (m.coefficients.size == 1) "unexpected intercept"
    near m.coefficients[0]! (17 / 14)),
  ("intercept only", do
    let m ← getResult (fit #[#[1], #[1], #[1]] #[1, 2, 4])
    near m.coefficients[0]! (7 / 3)),
  ("zero targets", do
    let m ← getResult (fit lineX #[0, 0, 0])
    for w in m.coefficients do near w 0),
  ("large feature scale", do
    let X : Design := #[#[1, 0], #[1, 1e150], #[1, 2e150]]
    let m ← getResult (fit X #[1, 3, 5])
    near m.coefficients[0]! 1
    near (m.coefficients[1]! * 1e150) 2
    near (← getResult (m.predict #[1, 3e150])) 7),
  ("small feature scale", do
    let X : Design := #[#[1, 0], #[1, 1e-150], #[1, 2e-150]]
    let m ← getResult (fit X #[1, 3, 5])
    near m.coefficients[0]! 1
    near (m.coefficients[1]! * 1e-150) 2
    near (← getResult (m.predict #[1, 3e-150])) 7),
  ("large targets", do
    let m ← getResult (fit lineX #[1e150, 3e150, 5e150])
    near (m.coefficients[0]! / 1e150) 1
    near (m.coefficients[1]! / 1e150) 2),
  ("small targets", do
    let m ← getResult (fit lineX #[1e-150, 3e-150, 5e-150])
    near (m.coefficients[0]! * 1e150) 1
    near (m.coefficients[1]! * 1e150) 2),
  ("rescaling avoids an overflowing scale ratio", do
    let m ← getResult (fit #[#[1e-200], #[0]] #[1e100, 1e200])
    near (m.coefficients[0]! / 1e300) 1),
  ("empty data", expectError (fit #[] #[]) .emptyData),
  ("no feature columns", expectError (fit #[#[]] #[1]) .noFeatures),
  ("target count mismatch", expectError (fit lineX #[1]) (.targetCount 3 1)),
  ("ragged rows", expectError (fit #[#[1, 2], #[3]] #[1, 2]) (.rowWidth 1 2 1)),
  ("more coefficients than observations",
    expectError (fit #[#[1, 2]] #[3]) (.underdetermined 1 2)),
  ("NaN feature", expectError (fit #[#[0.0 / 0.0]] #[1]) (.nonFiniteFeature 0 0)),
  ("infinite target", expectError (fit #[#[1]] #[1.0 / 0.0]) (.nonFiniteTarget 0)),
  ("invalid negative tolerance",
    expectError (fit lineX #[1, 3, 5] { rankTolerance := -1 }) .invalidTolerance),
  ("invalid zero tolerance",
    expectError (fit lineX #[1, 3, 5] { rankTolerance := 0 }) .invalidTolerance),
  ("invalid large tolerance",
    expectError (fit lineX #[1, 3, 5] { rankTolerance := 1 }) .invalidTolerance),
  ("invalid NaN tolerance",
    expectError (fit lineX #[1, 3, 5] { rankTolerance := 0.0 / 0.0 }) .invalidTolerance),
  ("zero column", expectError (fit #[#[0], #[0]] #[1, 2]) (.rankDeficient 0)),
  ("duplicate columns",
    expectError (fit #[#[1, 1], #[1, 1]] #[1, 3]) (.rankDeficient 1)),
  ("near-dependent columns", do
    let X : Design := #[#[1, 1], #[1, 1 + 1e-12], #[1, 1 - 1e-12]]
    expectError (fit X #[1, 2, 3]) (.rankDeficient 1)),
  ("prediction width check", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.predict #[3]) (.rowWidth 0 2 1)),
  ("batch prediction preserves row index", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.predictAll #[#[1, 0], #[1, 0.0 / 0.0]]) (.nonFiniteFeature 1 1)),
  ("loss target count check", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.sumSquaredError lineX #[1]) (.targetCount 3 1)),
  ("loss target finiteness check", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.sumSquaredError lineX #[1, 1.0 / 0.0, 5]) (.nonFiniteTarget 1)),
  ("prediction overflow is an error", do
    let m : Model := { coefficients := #[1e308] }
    expectError (m.predict #[2]) (.numericalFailure "prediction at row 0")),
  ("loss overflow is an error", do
    let m : Model := { coefficients := #[0] }
    expectError (m.sumSquaredError #[#[1]] #[1e308])
      (.numericalFailure "sum of squared errors"))
]

def run : IO Unit := do
  for (name, action) in cases do
    try
      action
      IO.println s!"PASS {name}"
    catch e => throw (IO.userError s!"FAIL {name}: {e}")
  IO.println s!"{cases.size}/{cases.size} OLS Float checks passed"

end LeanLearn.Tests.OLSFloat

public def main : IO Unit := LeanLearn.Tests.OLSFloat.run
