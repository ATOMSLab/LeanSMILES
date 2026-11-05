/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

import Std

/-!
# Executable ordinary least squares with floating-point arrays

`fit X y` accepts rows of numerical features and one target per row. Include
a column of ones in `X` to fit an intercept. The output coefficients follow
the input column order. No intercept or regularization is added implicitly.

The solver scales columns and targets, performs Householder QR, and solves
the resulting triangular system. It does not form or invert `XᵀX`.
It requires at least as many observations as coefficients and rejects
numerical rank deficiency using a configurable relative tolerance.

This implements the OLS objective specified in `Proofs/LeastSquares/OLS.lean`, but the exact-real
proofs there do not certify this program's floating-point rounding errors.
-/

public section

namespace LeanLearn.Regression.OLSFloat

/-- Rows of a floating-point design matrix. -/
abbrev Design := Array (Array Float)

/-- Invalid inputs or a failure to obtain a finite, numerically full-rank solution. -/
inductive Error where
  /-- The design has no rows. -/
  | emptyData
  /-- The first design row has no columns. -/
  | noFeatures
  /-- The target vector has `actual` entries but the design has `expected` rows. -/
  | targetCount (expected actual : Nat)
  /-- Zero-based `row` has `actual` entries instead of `expected`. -/
  | rowWidth (row expected actual : Nat)
  /-- A NaN or infinite design entry at the zero-based position. -/
  | nonFiniteFeature (row column : Nat)
  /-- A NaN or infinite target at the zero-based row. -/
  | nonFiniteTarget (row : Nat)
  /-- Fewer observations than coefficients, so no unique solution exists. -/
  | underdetermined (observations features : Nat)
  /-- `Config.rankTolerance` is not finite or not strictly between 0 and 1. -/
  | invalidTolerance
  /-- The zero-based column is zero or numerically dependent on earlier columns. -/
  | rankDeficient (column : Nat)
  /-- A non-finite intermediate value; `context` names the stage that produced it. -/
  | numericalFailure (context : String)
  deriving Repr, BEq, DecidableEq

/-- Human-readable errors; all row and column indices are zero-based. -/
def Error.toString : Error → String
  | .emptyData => "OLS needs at least one observation"
  | .noFeatures => "OLS needs at least one feature column"
  | .targetCount expected actual => s!"expected {expected} targets, received {actual}"
  | .rowWidth row expected actual => s!"row {row}: expected {expected} features, received {actual}"
  | .nonFiniteFeature row column => s!"non-finite feature at row {row}, column {column}"
  | .nonFiniteTarget row => s!"non-finite target at row {row}"
  | .underdetermined observations features =>
    s!"{observations} observations cannot determine {features} coefficients uniquely"
  | .invalidTolerance => "rankTolerance must be finite and strictly between 0 and 1"
  | .rankDeficient column =>
    s!"feature column {column} is zero or numerically dependent on earlier columns"
  | .numericalFailure context => s!"non-finite numerical result: {context}"

instance : ToString Error := ⟨Error.toString⟩

/-- Numerical options for `fit`. -/
structure Config where
  /-- A column is rank-deficient when its remaining norm at its QR step is at most this fraction
  of its original scaled Euclidean norm; must be finite and strictly between 0 and 1. -/
  rankTolerance : Float := 1e-10
  deriving Repr

/-- A fitted linear model; apply it with `Model.predict` or `Model.predictAll`. -/
structure Model where
  /-- One coefficient per training column, in column order, including the intercept column if
  one was supplied. -/
  coefficients : Array Float
  deriving Repr

-- Check that the row has `expected` entries and that every entry is finite.
private def checkRow (row : Array Float) (expected index : Nat) : Except Error Unit := do
  if row.size != expected then throw (.rowWidth index expected row.size)
  for j in [0:row.size] do
    if !row[j]!.isFinite then throw (.nonFiniteFeature index j)

-- Dot the row with the coefficients after checking dimensions and finiteness.
private def predictRow (model : Model) (row : Array Float) (index : Nat) : Except Error Float := do
  checkRow row model.coefficients.size index
  let mut value := 0.0
  for j in [0:model.coefficients.size] do
    if !model.coefficients[j]!.isFinite then throw (.numericalFailure s!"coefficient {j}")
    value := value + row[j]! * model.coefficients[j]!
  if !value.isFinite then throw (.numericalFailure s!"prediction at row {index}")
  return value

/-- Predict a single row; its feature order must match the training design. -/
def Model.predict (model : Model) (row : Array Float) : Except Error Float :=
  predictRow model row 0

/-- Predict all supplied rows. An empty input produces an empty output. -/
def Model.predictAll (model : Model) (X : Design) : Except Error (Array Float) := do
  let mut result := #[]
  for i in [0:X.size] do
    result := result.push (← predictRow model X[i]! i)
  return result

/-- Sum of squared errors on the supplied observations, without averaging or a penalty. -/
def Model.sumSquaredError (model : Model) (X : Design) (y : Array Float) : Except Error Float := do
  if y.size != X.size then throw (.targetCount X.size y.size)
  let mut total := 0.0
  for i in [0:X.size] do
    if !y[i]!.isFinite then throw (.nonFiniteTarget i)
    let r := (← predictRow model X[i]! i) - y[i]!
    total := total + r * r
    if !total.isFinite then throw (.numericalFailure "sum of squared errors")
  return total

-- Undo scaling without first forming an overflowing or underflowing scale ratio.
private def unscale (value targetScale columnScale : Float) : Float :=
  let (v, ev) := value.frExp
  let (t, et) := targetScale.frExp
  let (c, ec) := columnScale.frExp
  ((v * t) / c).scaleB (ev + et - ec)

/-- Fit unweighted, unregularized OLS to a dense design by Householder QR after scaling each
column by its largest absolute entry. At QR step `k` the remaining column norm must exceed
`cfg.rankTolerance` times the column's original scaled norm; this is a numerical threshold, not a
proof of rank, so near-dependent designs may be rejected and column order can affect the decision.
Singular or underdetermined designs are errors; no pseudoinverse solution is returned. -/
def fit (X : Design) (y : Array Float) (cfg : Config := {}) : Except Error Model := do
  if !cfg.rankTolerance.isFinite || cfg.rankTolerance ≤ 0 || 1 ≤ cfg.rankTolerance then
    throw .invalidTolerance
  let m := X.size
  if m == 0 then throw .emptyData
  let p := X[0]!.size
  if p == 0 then throw .noFeatures
  if y.size != m then throw (.targetCount m y.size)
  for i in [0:m] do
    checkRow X[i]! p i
    if !y[i]!.isFinite then throw (.nonFiniteTarget i)
  if m < p then throw (.underdetermined m p)
  -- Scale the inputs before QR; this does not change the least-squares problem.
  let mut scales := Array.replicate p 0.0
  for j in [0:p] do
    for i in [0:m] do
      scales := scales.set! j (max scales[j]! X[i]![j]!.abs)
    if scales[j]! == 0 then throw (.rankDeficient j)
  let targetMax := y.foldl (fun s v ↦ max s v.abs) 0.0
  let targetScale := if targetMax == 0 then 1.0 else targetMax
  let mut a := X.map fun row ↦ row.mapIdx fun j v ↦ v / scales[j]!
  let mut b := y.map (· / targetScale)
  let mut originalNorms := Array.replicate p 0.0
  for j in [0:p] do
    let mut ss := 0.0
    for i in [0:m] do
      ss := ss + a[i]![j]! * a[i]![j]!
    originalNorms := originalNorms.set! j ss.sqrt
  -- Householder reflections turn A into R and apply the same transformations to y.
  for k in [0:p] do
    let mut ss := 0.0
    for i in [k:m] do
      ss := ss + a[i]![k]! * a[i]![k]!
    let norm := ss.sqrt
    if !norm.isFinite then throw (.numericalFailure s!"column norm {k}")
    if norm ≤ cfg.rankTolerance * originalNorms[k]! then throw (.rankDeficient k)
    let alpha := if 0 ≤ a[k]![k]! then -norm else norm
    let mut v := Array.replicate m 0.0
    for i in [k:m] do
      v := v.set! i a[i]![k]!
    v := v.set! k (v[k]! - alpha)
    let vnormSq := v.foldl (fun s vi ↦ s + vi * vi) 0.0
    if !vnormSq.isFinite || vnormSq == 0 then
      throw (.numericalFailure s!"Householder reflection {k}")
    for j in [k:p] do
      let mut dot := 0.0
      for i in [k:m] do
        dot := dot + v[i]! * a[i]![j]!
      let factor := 2 * (dot / vnormSq)
      for i in [k:m] do
        let entry := a[i]![j]! - factor * v[i]!
        if !entry.isFinite then throw (.numericalFailure "QR matrix update")
        a := a.set! i (a[i]!.set! j entry)
    let mut dot := 0.0
    for i in [k:m] do
      dot := dot + v[i]! * b[i]!
    let factor := 2 * (dot / vnormSq)
    for i in [k:m] do
      let entry := b[i]! - factor * v[i]!
      if !entry.isFinite then throw (.numericalFailure "QR target update")
      b := b.set! i entry
    a := a.set! k (a[k]!.set! k alpha)
    for i in [k + 1:m] do
      a := a.set! i (a[i]!.set! k 0)
  -- Back substitution: solve R z = Qᵀ y for the scaled coefficients.
  let mut z := Array.replicate p 0.0
  for offset in [0:p] do
    let k := p - 1 - offset
    let mut rhs := b[k]!
    for j in [k + 1:p] do
      rhs := rhs - a[k]![j]! * z[j]!
    let value := rhs / a[k]![k]!
    if !value.isFinite then throw (.numericalFailure s!"back substitution {k}")
    z := z.set! k value
  let mut coefficients := Array.replicate p 0.0
  for j in [0:p] do
    let value := unscale z[j]! targetScale scales[j]!
    if !value.isFinite then throw (.numericalFailure s!"rescaling coefficient {j}")
    coefficients := coefficients.set! j value
  return { coefficients }

end LeanLearn.Regression.OLSFloat
