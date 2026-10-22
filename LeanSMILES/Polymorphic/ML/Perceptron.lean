module

public import LeanSMILES.Polymorphic.ML.LinearModel

/-!
# Machine Learning — Perceptron

Rosenblatt's perceptron for `±1` labels, trained by passes over the data in index
order.
-/

@[expose] public section

namespace ML

open Primitives

section Perceptron

variable {α : Type} [Scalar α] {m n : Nat}

/-- Perceptron loss `max(0, -y · score x)` for `y ∈ {±1}`. `perceptronStep` is a
stochastic subgradient step on this loss (restricted to mistakes, including the boundary
case `y · score x = 0`). -/
def perceptronLoss (model : LinearModel α n) (x : Vec α n) (y : α) : α :=
  Scalar.max 0 (-(y * model.score x))

/-- The model misclassifies `(x, y)` or puts it on the decision boundary. -/
abbrev IsMistake (model : LinearModel α n) (x : Vec α n) (y : α) : Prop :=
  y * model.score x ≤ 0

/-- Update on one sample `(x, y)` with `y ∈ {±1}`: on a mistake, set `w ← w + η y x` and
`b ← b + η y`; otherwise leave the model unchanged. Proofs case-split with
`perceptronStep_of_mistake` / `perceptronStep_of_not_mistake`. -/
def perceptronStep (η : α) (model : LinearModel α n) (x : Vec α n) (y : α) :
    LinearModel α n :=
  if IsMistake model x y then
    { weights := vadd model.weights (smul (η * y) x)
      bias := model.bias + η * y }
  else model

/-- One pass of `perceptronStep` over the samples in index order, as a left fold over
`List.finRange m` (prove facts about it by induction on the list). -/
def perceptronEpoch (η : α) (data : Dataset α m n) (model : LinearModel α n) :
    LinearModel α n :=
  (List.finRange m).foldl (fun model i => perceptronStep η model data.X[i] data.y[i]) model

/-- `cfg.epochs` passes starting from the zero model, i.e.
`iterate (perceptronEpoch η data) epochs LinearModel.zero`.
Proved (over `ℝ`, `Proofs/ML/Perceptron.lean`): on data separable with margin `γ` and radius
`R`, it makes at most `(R/γ)²` updates in total (`perceptron_mistake_bound`) and within
`⌊(R/γ)²⌋` epochs classifies every training example correctly
(`perceptron_classifies_training_set`). -/
def perceptronFit (cfg : PerceptronConfig α) (data : Dataset α m n) : LinearModel α n :=
  iterate (perceptronEpoch cfg.learningRate data) cfg.epochs LinearModel.zero

/-- `perceptronEpoch` that also counts its updates (the mistakes it corrected). -/
def perceptronEpochCounting (η : α) (data : Dataset α m n) (state : LinearModel α n × Nat) :
    LinearModel α n × Nat :=
  (List.finRange m).foldl (fun s i =>
    if IsMistake s.1 data.X[i] data.y[i] then (perceptronStep η s.1 data.X[i] data.y[i], s.2 + 1)
    else s) state

/-- `perceptronFit` that also returns the total number of updates. The model is
`perceptronFit cfg data` (`perceptronFitCounting_fst`), and on separable data the count is
at most `(R/γ)²` (`perceptron_mistake_bound` in `Proofs/ML/Perceptron.lean`). -/
def perceptronFitCounting (cfg : PerceptronConfig α) (data : Dataset α m n) :
    LinearModel α n × Nat :=
  iterate (perceptronEpochCounting cfg.learningRate data) cfg.epochs (LinearModel.zero, 0)

end Perceptron

end ML

end
