/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

import Std

/-!
# Executable ridge regression with floating-point arrays

`fit X y` minimizes `Σᵢ ((Xw)ᵢ - yᵢ)² + penalty * Σⱼ wⱼ²`.
Include a column of ones in `X` to fit an intercept; set `unpenalizedColumn`
to its zero-based index if the intercept should be exempt from the penalty.
No column is added implicitly. The coefficients follow the input column order.

The solver augments the design with `sqrt penalty` times the identity on
penalized coefficients, scales columns and targets, and performs Householder
QR. It does not form or invert `XᵀX`. A positive penalty permits singular or
underdetermined designs when the augmented design is numerically full rank.
With zero penalty, this solves the ordinary least-squares problem.

The exact-real OLS proofs in `OLS.lean` do not certify this program's
floating-point rounding errors or its regularized objective.
-/

public section

namespace LeanLearn.Regression.RidgeFloat

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
  | invalidPenalty
  | invalidUnpenalizedColumn (column features : Nat)
  | invalidTolerance
  | rankDeficient (column : Nat)
  | numericalFailure (context : String)
  deriving Repr, BEq, DecidableEq

/-- Human-readable errors; all row and column indices are zero-based. -/
def Error.toString : Error → String
  | .emptyData => "ridge regression needs at least one observation"
  | .noFeatures => "ridge regression needs at least one feature column"
  | .targetCount expected actual =>
    s!"expected {expected} targets, received {actual}"
  | .rowWidth row expected actual =>
    s!"row {row}: expected {expected} features, received {actual}"
  | .nonFiniteFeature row column => s!"non-finite feature at row {row}, column {column}"
  | .nonFiniteTarget row => s!"non-finite target at row {row}"
  | .underdetermined observations features =>
    s!"{observations} observations cannot determine {features} coefficients uniquely without a penalty"
  | .invalidPenalty => "penalty must be finite and nonnegative"
  | .invalidUnpenalizedColumn column features =>
    s!"unpenalized column {column} is outside {features} feature columns"
  | .invalidTolerance => "rankTolerance must be finite and strictly between 0 and 1"
  | .rankDeficient column =>
    s!"augmented column {column} is zero or numerically dependent on earlier columns"
  | .numericalFailure context => s!"non-finite numerical result: {context}"

instance : ToString Error := ⟨Error.toString⟩

/-- Ridge settings. By default every coefficient, including any intercept, is penalized. -/
structure Config where
  penalty : Float := 1.0
  unpenalizedColumn : Option Nat := none
  rankTolerance : Float := 1e-10
  deriving Repr

/-- Fitted coefficients and the settings that determine their penalty. -/
structure Model where
  coefficients : Array Float
  penalty : Float
  unpenalizedColumn : Option Nat
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

/-- Ridge objective: squared error plus the configured coefficient penalty. -/
def Model.penalizedLoss (model : Model) (X : Design) (y : Array Float) :
    Except Error Float := do
  let mut total ← model.sumSquaredError X y
  let rootPenalty := model.penalty.sqrt
  for j in [0:model.coefficients.size] do
    if some j != model.unpenalizedColumn then
      let weighted := rootPenalty * model.coefficients[j]!
      total := total + weighted * weighted
      if !total.isFinite then throw (.numericalFailure "penalized loss")
  return total

/-- Undo scaling without first forming an overflowing or underflowing scale ratio. -/
private def unscale (value targetScale columnScale : Float) : Float :=
  let (v, ev) := value.frExp
  let (t, et) := targetScale.frExp
  let (c, ec) := columnScale.frExp
  ((v * t) / c).scaleB (ev + et - ec)

/--
Fit unweighted ridge regression to a dense numerical design matrix.

The penalty applies to every supplied coefficient except `unpenalizedColumn`.
At QR step `k`, the remaining augmented-column norm must exceed
`rankTolerance` times its original scaled norm. This is a numerical threshold,
not a proof of mathematical rank. Near-dependent designs may be rejected.

At zero penalty, an underdetermined design is rejected and rank deficiency
is handled like in `OLSFloat.fit`.
-/
def fit (X : Design) (y : Array Float) (cfg : Config := {}) : Except Error Model := do
  if !cfg.penalty.isFinite || cfg.penalty < 0 then throw .invalidPenalty
  if !cfg.rankTolerance.isFinite || cfg.rankTolerance ≤ 0 || cfg.rankTolerance ≥ 1 then
    throw .invalidTolerance
  let m := X.size
  if m == 0 then throw .emptyData
  let p := X[0]!.size
  if p == 0 then throw .noFeatures
  if let some j := cfg.unpenalizedColumn then
    if j ≥ p then throw (.invalidUnpenalizedColumn j p)
  if y.size != m then throw (.targetCount m y.size)
  for i in [0:m] do
    checkRow X[i]! p i
    if !y[i]!.isFinite then throw (.nonFiniteTarget i)
  if cfg.penalty == 0 && m < p then throw (.underdetermined m p)

  -- Augment with sqrt(penalty) * I, omitting the exempt diagonal entry.
  let rootPenalty := cfg.penalty.sqrt
  let mut scales := Array.replicate p 0.0
  for j in [0:p] do
    for i in [0:m] do
      scales := scales.set! j (max scales[j]! X[i]![j]!.abs)
    if some j != cfg.unpenalizedColumn then
      scales := scales.set! j (max scales[j]! rootPenalty)
    if scales[j]! == 0 then throw (.rankDeficient j)
  let targetMax := y.foldl (fun s v => max s v.abs) 0.0
  let targetScale := if targetMax == 0 then 1.0 else targetMax
  -- Put penalty rows first so a dominant penalty does not erase a small
  -- data contribution when the first Householder reflection updates the target.
  let mut a : Design := #[]
  let mut b : Array Float := #[]
  if cfg.penalty > 0 then
    for j in [0:p] do
      let mut row := Array.replicate p 0.0
      if some j != cfg.unpenalizedColumn then
        row := row.set! j (rootPenalty / scales[j]!)
      a := a.push row
      b := b.push 0.0
  for i in [0:m] do
    a := a.push (X[i]!.mapIdx fun j v => v / scales[j]!)
    b := b.push (y[i]! / targetScale)
  let rows := a.size
  let mut originalNorms := Array.replicate p 0.0
  for j in [0:p] do
    let mut ss := 0.0
    for i in [0:rows] do
      ss := ss + a[i]![j]! * a[i]![j]!
    let norm := ss.sqrt
    if !norm.isFinite then throw (.numericalFailure s!"original column norm {j}")
    originalNorms := originalNorms.set! j norm

  -- Householder reflections turn A into R and apply the same transformations to y.
  for k in [0:p] do
    let mut ss := 0.0
    for i in [k:rows] do
      ss := ss + a[i]![k]! * a[i]![k]!
    let norm := ss.sqrt
    if !norm.isFinite then throw (.numericalFailure s!"column norm {k}")
    if norm ≤ cfg.rankTolerance * originalNorms[k]! then throw (.rankDeficient k)
    let alpha := if a[k]![k]! ≥ 0 then -norm else norm
    let mut v := Array.replicate rows 0.0
    for i in [k:rows] do
      v := v.set! i a[i]![k]!
    v := v.set! k (v[k]! - alpha)
    let vnormSq := v.foldl (fun s vi => s + vi * vi) 0.0
    if !vnormSq.isFinite || vnormSq == 0 then
      throw (.numericalFailure s!"Householder reflection {k}")
    for j in [k:p] do
      let mut dot := 0.0
      for i in [k:rows] do
        dot := dot + v[i]! * a[i]![j]!
      let factor := 2 * (dot / vnormSq)
      for i in [k:rows] do
        let entry := a[i]![j]! - factor * v[i]!
        if !entry.isFinite then throw (.numericalFailure "QR matrix update")
        a := a.set! i (a[i]!.set! j entry)
    let mut dot := 0.0
    for i in [k:rows] do
      dot := dot + v[i]! * b[i]!
    let factor := 2 * (dot / vnormSq)
    for i in [k:rows] do
      let entry := b[i]! - factor * v[i]!
      if !entry.isFinite then throw (.numericalFailure "QR target update")
      b := b.set! i entry
    a := a.set! k (a[k]!.set! k alpha)
    for i in [k + 1:rows] do
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
  return { coefficients, penalty := cfg.penalty, unpenalizedColumn := cfg.unpenalizedColumn }

end LeanLearn.Regression.RidgeFloat
