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

This implements the OLS objective specified in `OLS.lean`, but the exact-real
proofs there do not certify this program's floating-point rounding errors.
-/

public section

namespace LeanLearn.Regression.OLSFloat

/-- Rows of a floating-point design matrix. -/
abbrev Design := Array (Array Float)

/-- Invalid inputs or a failure to obtain a finite, numerically full-rank solution. -/
inductive Error where
  | emptyData
  | noFeatures
  | targetCount (expected actual : Nat)
  | rowWidth (row expected actual : Nat)
  | nonFiniteFeature (row column : Nat)
  | nonFiniteTarget (row : Nat)
  | underdetermined (observations features : Nat)
  | invalidTolerance
  | rankDeficient (column : Nat)
  | numericalFailure (context : String)
  deriving Repr, BEq, DecidableEq

/-- Human-readable errors; all row and column indices are zero-based. -/
def Error.toString : Error → String
  | .emptyData => "OLS needs at least one observation"
  | .noFeatures => "OLS needs at least one feature column"
  | .targetCount expected actual =>
    s!"expected {expected} targets, received {actual}"
  | .rowWidth row expected actual =>
    s!"row {row}: expected {expected} features, received {actual}"
  | .nonFiniteFeature row column => s!"non-finite feature at row {row}, column {column}"
  | .nonFiniteTarget row => s!"non-finite target at row {row}"
  | .underdetermined observations features =>
    s!"{observations} observations cannot determine {features} coefficients uniquely"
  | .invalidTolerance => "rankTolerance must be finite and strictly between 0 and 1"
  | .rankDeficient column =>
    s!"feature column {column} is zero or numerically dependent on earlier columns"
  | .numericalFailure context => s!"non-finite numerical result: {context}"

instance : ToString Error := ⟨Error.toString⟩

/-- The rank threshold is relative to each scaled column's original Euclidean norm. -/
structure Config where
  rankTolerance : Float := 1e-10
  deriving Repr

/-- One coefficient for each input column, including an intercept column if supplied. -/
structure Model where
  coefficients : Array Float
  deriving Repr

/-- Validate one feature row. -/
private def checkRow (row : Array Float) (expected index : Nat) : Except Error Unit := do
  if row.size != expected then throw (.rowWidth index expected row.size)
  for j in [0:row.size] do
    if !row[j]!.isFinite then throw (.nonFiniteFeature index j)

/-- Compute one prediction after checking the row and coefficient dimensions/values. -/
private def predictRow (model : Model) (row : Array Float) (index : Nat) :
    Except Error Float := do
  checkRow row model.coefficients.size index
  let mut value := 0.0
  for j in [0:model.coefficients.size] do
    if !model.coefficients[j]!.isFinite then
      throw (.numericalFailure s!"coefficient {j}")
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
def Model.sumSquaredError (model : Model) (X : Design) (y : Array Float) :
    Except Error Float := do
  if y.size != X.size then throw (.targetCount X.size y.size)
  let mut total := 0.0
  for i in [0:X.size] do
    if !y[i]!.isFinite then throw (.nonFiniteTarget i)
    let r := (← predictRow model X[i]! i) - y[i]!
    total := total + r * r
    if !total.isFinite then throw (.numericalFailure "sum of squared errors")
  return total

/-- Undo scaling without first forming an overflowing or underflowing scale ratio. -/
private def unscale (value targetScale columnScale : Float) : Float :=
  let (v, ev) := value.frExp
  let (t, et) := targetScale.frExp
  let (c, ec) := columnScale.frExp
  ((v * t) / c).scaleB (ev + et - ec)

/--
Fit unweighted, unregularized OLS to a dense numerical design matrix.

Columns are scaled by their largest absolute entry. At QR step `k`, the
remaining column norm must exceed `rankTolerance` times its original scaled
norm. This is a numerical threshold, not a proof of mathematical rank;
near-dependent designs may be rejected, and column order can affect the decision.

No pseudoinverse solution is returned for singular or underdetermined designs.
-/
def fit (X : Design) (y : Array Float) (cfg : Config := {}) : Except Error Model := do
  if !cfg.rankTolerance.isFinite || cfg.rankTolerance ≤ 0 || cfg.rankTolerance ≥ 1 then
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
  let targetMax := y.foldl (fun s v => max s v.abs) 0.0
  let targetScale := if targetMax == 0 then 1.0 else targetMax
  let mut a := X.map fun row => row.mapIdx fun j v => v / scales[j]!
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
    let alpha := if a[k]![k]! ≥ 0 then -norm else norm
    let mut v := Array.replicate m 0.0
    for i in [k:m] do
      v := v.set! i a[i]![k]!
    v := v.set! k (v[k]! - alpha)
    let vnormSq := v.foldl (fun s vi => s + vi * vi) 0.0
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
