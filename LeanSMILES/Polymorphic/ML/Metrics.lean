module

public import LeanSMILES.Polymorphic.ML.LinearModel

/-!
# Machine Learning — Metrics

The metrics in `sklearn.metrics`, for any `Scalar`: `meanSquaredError`,
`rootMeanSquaredError`, `meanAbsoluteError` and `r2Score`, plus `accuracy` for `±1`
labels. `evaluate` computes all of them for a linear model on a dataset.
-/

@[expose] public section

namespace ML

open Primitives

variable {α : Type} [Scalar α] {m n : Nat}

@[specialize] def meanSquaredError (yTrue yPred : Vec α m) : α :=
  (sumFin fun (i : Fin m) => (yTrue[i] - yPred[i]) * (yTrue[i] - yPred[i])) / Scalar.fromNat m

@[specialize] def rootMeanSquaredError (yTrue yPred : Vec α m) : α :=
  Scalar.sqrt (meanSquaredError yTrue yPred)

@[specialize] def meanAbsoluteError (yTrue yPred : Vec α m) : α :=
  (sumFin fun (i : Fin m) => Scalar.abs (yTrue[i] - yPred[i])) / Scalar.fromNat m

/-- Coefficient of determination `1 - SS_res / SS_tot`. Like sklearn, a constant target
(`SS_tot = 0`) scores `1` if the predictions are perfect and `0` otherwise. -/
@[specialize] def r2Score (yTrue yPred : Vec α m) : α :=
  let μ := vsum yTrue / Scalar.fromNat m
  let ssRes := sumFin fun (i : Fin m) => (yTrue[i] - yPred[i]) * (yTrue[i] - yPred[i])
  let ssTot := sumFin fun (i : Fin m) => (yTrue[i] - μ) * (yTrue[i] - μ)
  if ssTot ≤ 0 then (if ssRes ≤ 0 then 1 else 0) else 1 - ssRes / ssTot

/-- Fraction of `±1` labels predicted with the right sign. -/
@[specialize] def accuracy (yTrue yPred : Vec α m) : α :=
  (sumFin fun (i : Fin m) => if 0 < yTrue[i] * yPred[i] then (1 : α) else 0) / Scalar.fromNat m

structure RegressionMetrics (α : Type) where
  mse : α
  rmse : α
  mae : α
  r2 : α

@[specialize] def regressionMetrics (yTrue yPred : Vec α m) : RegressionMetrics α :=
  { mse := meanSquaredError yTrue yPred, rmse := rootMeanSquaredError yTrue yPred
    mae := meanAbsoluteError yTrue yPred, r2 := r2Score yTrue yPred }

/-- All metrics of `model` on `d`. -/
@[specialize] def evaluate (model : LinearModel α n) (d : Dataset α m n) : RegressionMetrics α :=
  regressionMetrics d.y (model.predictAll d.X)

end ML

end
