module

public import LeanSMILES.Primitives.lin_algebra

/-!
# Algorithm parameters

Hyperparameters and problem inputs shared by the iterative algorithms in
`Machine_Learning/DEFINITIONS.lean`.
-/

@[expose] public section

namespace Primitives

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
training. The correctness hypothesis that `grad` really is the gradient of `loss` is
assumed in `PROOFS.lean` over `ℝ`, not enforced here. -/
structure Objective (α : Type) (n : Nat) where
  loss : Vec α n → α
  grad : Vec α n → Vec α n

end Primitives

end
