/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
import LeanLearn.Regression.RidgeFloat

/-!
# Numerical and input-validation checks for RidgeFloat

Run from the repository root:
`lake exe ridge-float-test`

The expected coefficients follow from small ridge normal equations. These
checks are numerical examples, not formal floating-point error bounds.
-/

namespace LeanLearn.Tests.RidgeFloat

open LeanLearn.Regression.RidgeFloat

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
  ("one coefficient shrinks", do
    let X : Design := #[#[1], #[2]]
    let m ← getResult (fit X #[1, 2])
    near m.coefficients[0]! (5 / 6)
    near (← getResult (m.predict #[3])) (5 / 2)
    near (← getResult (m.sumSquaredError X #[1, 2])) (5 / 36)
    near (← getResult (m.penalizedLoss X #[1, 2])) (5 / 6)),
  ("all supplied coefficients are penalized by default", do
    let m ← getResult (fit lineX #[1, 3, 5])
    near m.coefficients[0]! 1
    near m.coefficients[1]! (5 / 3)
    require (m.unpenalizedColumn == none) "unexpected exempt column"
    near m.penalty 1),
  ("explicit intercept exemption", do
    let cfg : Config := { penalty := 2, unpenalizedColumn := some 0 }
    let m ← getResult (fit lineX #[1, 3, 5] cfg)
    near m.coefficients[0]! 2
    near m.coefficients[1]! 1
    near (← getResult (m.predict #[1, 3])) 5
    let predictions ← getResult (m.predictAll lineX)
    require (predictions.size == 3) "wrong prediction count"
    for i in [0:3] do near predictions[i]! (#[2.0, 3.0, 4.0][i]!)
    near (← getResult (m.sumSquaredError lineX #[1, 3, 5])) 2
    near (← getResult (m.penalizedLoss lineX #[1, 3, 5])) 4),
  ("duplicate columns become identifiable", do
    let X : Design := #[#[1, 1], #[1, 1]]
    let m ← getResult (fit X #[1, 3])
    near m.coefficients[0]! (4 / 5)
    near m.coefficients[1]! (4 / 5)
    near (← getResult (m.penalizedLoss X #[1, 3])) (18 / 5)),
  ("underdetermined design", do
    let m ← getResult (fit #[#[1, 2]] #[3])
    near m.coefficients[0]! (1 / 2)
    near m.coefficients[1]! 1),
  ("zero feature column is regularized", do
    let m ← getResult (fit #[#[0], #[0]] #[1, 2])
    near m.coefficients[0]! 0),
  ("exempt intercept stays identifiable with a duplicate feature", do
    let X : Design := #[#[1, 1], #[1, 1]]
    let m ← getResult (fit X #[1, 3] { unpenalizedColumn := some 0 })
    near m.coefficients[0]! 2
    near m.coefficients[1]! 0),
  ("zero penalty recovers ordinary least squares", do
    let m ← getResult (fit lineX #[1, 3, 5] { penalty := 0 })
    near m.coefficients[0]! 1
    near m.coefficients[1]! 2
    near (← getResult (m.penalizedLoss lineX #[1, 3, 5])) 0),
  ("large feature and target scales", do
    let m ← getResult (fit #[#[1e150]] #[1e150])
    near m.coefficients[0]! 1),
  ("large penalty", do
    let m ← getResult (fit #[#[1]] #[1] { penalty := 1e300 })
    near (m.coefficients[0]! * 1e300) 1),
  ("empty data", expectError (fit #[] #[]) .emptyData),
  ("no features", expectError (fit #[#[]] #[1]) .noFeatures),
  ("target count", expectError (fit lineX #[1]) (.targetCount 3 1)),
  ("ragged rows", expectError (fit #[#[1, 2], #[3]] #[1, 2]) (.rowWidth 1 2 1)),
  ("NaN feature", expectError (fit #[#[0.0 / 0.0]] #[1]) (.nonFiniteFeature 0 0)),
  ("infinite target", expectError (fit #[#[1]] #[1.0 / 0.0]) (.nonFiniteTarget 0)),
  ("negative penalty", expectError (fit lineX #[1, 3, 5] { penalty := -1 }) .invalidPenalty),
  ("NaN penalty", expectError (fit lineX #[1, 3, 5] { penalty := 0.0 / 0.0 }) .invalidPenalty),
  ("infinite penalty", expectError (fit lineX #[1, 3, 5] { penalty := 1.0 / 0.0 }) .invalidPenalty),
  ("invalid exempt column", expectError (fit lineX #[1, 3, 5]
    { unpenalizedColumn := some 2 }) (.invalidUnpenalizedColumn 2 2)),
  ("invalid tolerance", expectError (fit lineX #[1, 3, 5]
    { rankTolerance := 0 }) .invalidTolerance),
  ("zero penalty underdetermined", expectError (fit #[#[1, 2]] #[3]
    { penalty := 0 }) (.underdetermined 1 2)),
  ("zero penalty duplicate columns", expectError (fit #[#[1, 1], #[1, 1]] #[1, 3]
    { penalty := 0 }) (.rankDeficient 1)),
  ("unpenalized zero column", expectError (fit #[#[0, 1], #[0, 2]] #[1, 2]
    { unpenalizedColumn := some 0 }) (.rankDeficient 0)),
  ("prediction width", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.predict #[1]) (.rowWidth 0 2 1)),
  ("prediction row index", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.predictAll #[#[1, 0], #[1, 0.0 / 0.0]]) (.nonFiniteFeature 1 1)),
  ("loss target count", do
    let m ← getResult (fit lineX #[1, 3, 5])
    expectError (m.penalizedLoss lineX #[1]) (.targetCount 3 1)),
  ("loss overflow", do
    let m ← getResult (fit #[#[1]] #[1])
    expectError (m.sumSquaredError #[#[1]] #[1e308])
      (.numericalFailure "sum of squared errors"))
]

def run : IO Unit := do
  for (name, action) in cases do
    try
      action
      IO.println s!"PASS {name}"
    catch e => throw (IO.userError s!"FAIL {name}: {e}")
  IO.println s!"{cases.size}/{cases.size} Ridge Float checks passed"

end LeanLearn.Tests.RidgeFloat

def main : IO Unit := LeanLearn.Tests.RidgeFloat.run
