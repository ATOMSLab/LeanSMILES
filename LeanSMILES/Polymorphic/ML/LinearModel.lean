module

public import LeanSMILES.Polymorphic.ML.Types

/-!
# Machine Learning — Linear models

The affine model `x ↦ ⟪w, x⟫ + b` that every algorithm in `Polymorphic/ML/` trains, and
its parameter vector `θ = (w, b)`.
-/

@[expose] public section

namespace ML

open Primitives

namespace LinearModel

variable {α : Type} [Scalar α] {n : Nat}

/-- The raw score `⟪w, x⟫ + b`. -/
@[specialize] def score (model : LinearModel α n) (x : Vec α n) : α :=
  dot model.weights x + model.bias

/-- `+1` when the score is non-negative, `-1` otherwise. -/
def classify (model : LinearModel α n) (x : Vec α n) : α :=
  if 0 ≤ model.score x then 1 else -1

/-- The model with zero weights and zero bias. -/
def zero : LinearModel α n := ⟨vzero, 0⟩

/-- Scores of every row of `X`. -/
@[specialize] def predictAll {m : Nat} (model : LinearModel α n) (X : Mat α m n) : Vec α m :=
  Vector.ofFn fun i => model.score X[i]

/-- Pack the model as one parameter vector `θ = (w, b)`, the bias last. -/
def toParams (model : LinearModel α n) : Vec α (n + 1) :=
  model.weights.push model.bias

/-- Unpack `θ = (w, b)`. Over `ℝ`, `(ofParams θ).score x = dot θ (augment x)`. -/
def ofParams (θ : Vec α (n + 1)) : LinearModel α n :=
  { weights := Vector.ofFn fun j => θ[j.castSucc], bias := θ[Fin.last n] }

end LinearModel

end ML

end
