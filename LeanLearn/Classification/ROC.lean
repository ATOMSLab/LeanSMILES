/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

/-!
# ROC curves and AUC

How well a classifier's scores rank class 1 above class 0, at every threshold
at once. `rocCurve` lowers the threshold through the distinct scores, from the
highest down, and records after each step the false-positive rate (class-0
samples at or above the threshold, as a fraction of all class-0 samples) and
the true-positive rate (the same for class 1). Samples with equal scores enter
together, so ties give a diagonal step, as in scikit-learn's `roc_curve`.

`auc` is the area under that curve by the trapezoidal rule (scikit-learn's
`roc_auc_score`): the probability that a random class-1 sample scores above a
random class-0 sample, ties counting one half. 1 is a perfect ranking, 0.5 a
random one.
-/

@[expose] public section

namespace LeanLearn.Classification

/-- The ROC curve of (score, class) pairs as (false-positive rate, true-positive
rate) points, from (0, 0) to (1, 1). Empty if either class is missing. -/
def rocCurve (pairs : Array (Float × Bool)) : Array (Float × Float) := Id.run do
  let pos := (pairs.filter (·.2)).size.toFloat
  let neg := (pairs.filter (!·.2)).size.toFloat
  if pos == 0 || neg == 0 then return #[]
  let sorted := pairs.toList.mergeSort fun a b ↦ a.1 ≥ b.1
  let mut points : Array (Float × Float) := #[(0, 0)]
  let mut tp : Float := 0
  let mut fp : Float := 0
  let mut rest := sorted
  -- one point per distinct score: everything scoring at least that much is called class 1
  for _ in [0:sorted.length] do
    match rest with
    | [] => break
    | (s, _) :: _ =>
      let group := rest.takeWhile (·.1 == s)
      tp := tp + (group.filter (·.2)).length.toFloat
      fp := fp + (group.filter (!·.2)).length.toFloat
      points := points.push (fp / neg, tp / pos)
      rest := rest.drop group.length
  return points

/-- Area under a curve given as points in order of increasing `x`, by the
trapezoidal rule. -/
def auc (curve : Array (Float × Float)) : Float :=
  ((curve.toList.zip curve.toList.tail).map fun ((x₁, y₁), (x₂, y₂)) ↦
    (x₂ - x₁) * (y₁ + y₂) / 2).foldl (· + ·) 0

/-- The ROC AUC of (score, class) pairs. -/
def rocAuc (pairs : Array (Float × Bool)) : Float := auc (rocCurve pairs)

end LeanLearn.Classification
