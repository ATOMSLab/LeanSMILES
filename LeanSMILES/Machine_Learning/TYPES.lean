module

public import LeanSMILES.Primitives.lin_algebra

/-!
# Machine Learning — Types

Data and model types shared by the algorithms in `DEFINITIONS.lean`.
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

end ML

end
