module

public import LeanSMILES.Polymorphic.LinAlg

/-!
# Machine Learning — Types

Data, model and hyperparameter types shared by the algorithms in `Polymorphic/ML/`.
-/

@[expose] public section

namespace ML

open Primitives

/-- A supervised dataset of `m` samples with `n` features. Regression targets are real
values; binary classification targets are `±1`. -/
structure Dataset (α : Type) (m n : Nat) where
  X : Mat α m n
  y : Vec α m

/-- An affine model `x ↦ ⟪w, x⟫ + b`, shared by linear regression and the perceptron. -/
structure LinearModel (α : Type) (n : Nat) where
  weights : Vec α n
  bias : α

/-- Hyperparameters for (sub)gradient methods: a constant step size `η` and a fixed
number of iterations. -/
structure GDConfig (α : Type) where
  stepSize : α
  iters : Nat

/-- Hyperparameters for the perceptron: learning rate `η` and number of passes over the
data. -/
structure PerceptronConfig (α : Type) where
  learningRate : α
  epochs : Nat

/-- A differentiable objective on `Vec α n`: the loss and the function that computes its
gradient. Algorithms only call `grad`; `loss` is there to state results and to monitor
training. That `grad` really is the gradient of `loss` is proved, for least squares, in
`Proofs/ML/LeastSquares.lean` (`mse_step`). -/
structure Objective (α : Type) (n : Nat) where
  loss : Vec α n → α
  grad : Vec α n → Vec α n

end ML

end
