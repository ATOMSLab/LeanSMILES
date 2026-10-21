module

public import LeanSMILES.Primitives.scalar
public import LeanSMILES.Primitives.lin_algebra
public import LeanSMILES.Primitives.parameters
public import LeanSMILES.Machine_Learning.TYPES

/-!
# Machine Learning — Definitions

The ML algorithms used in the pipeline. Every algorithm is written once, polymorphic over a
scalar type `α` with a `[Scalar α]` instance:

* `α := ℝ`     — the noncomputable instance used to state and prove theorems
                 (see `PROOFS.lean`);
* `α := Float` — the computable instance used to run the algorithms
                 (see `EXECUTABLES.lean`).

`Scalar` lives in `Primitives/scalar.lean`; `Vec`, `Mat` and the linear algebra helpers
live in `Primitives/lin_algebra.lean`; configs and `Objective` live in
`Primitives/parameters.lean`; `Dataset` and `LinearModel` live in `TYPES.lean`.
-/

@[expose] public section

namespace ML

open Primitives

/-! ## Linear models -/

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

/-! ## Gradient Descent -/

section GradientDescent

variable {α : Type} [Scalar α] {n : Nat}

/-- One step `w ↦ w - η ∇f(w)`. Entrywise:
`(gdStep obj η w)[i] = w[i] - η * (obj.grad w)[i]` (`gdStep_getElem` in `PROOFS.lean`). -/
@[specialize] def gdStep (obj : Objective α n) (η : α) (w : Vec α n) : Vec α n :=
  vsub w (smul η (obj.grad w))

/-- `cfg.iters` steps of gradient descent from `w₀`, i.e. `iterate (gdStep obj η) k w₀`,
so proofs can induct on `k` with `gradientDescent_succ`.
Spec (over `ℝ`): for convex, `L`-smooth `obj.loss` with `0 < η ≤ 1/L`,
`loss wₖ - loss w* ≤ ‖w₀ - w*‖² / (2ηk)`. -/
@[specialize] def gradientDescent (obj : Objective α n) (cfg : GDConfig α) (w₀ : Vec α n) :
    Vec α n :=
  iterate (gdStep obj cfg.stepSize) cfg.iters w₀

/-- One step of `gradientDescentWithHistory`: a `gdStep`, then record `(k, loss)` every
`every` iterations. -/
@[specialize] def gdHistoryStep (obj : Objective α n) (η : α) (every : Nat)
    (state : Vec α n × Nat × Array (Nat × α)) : Vec α n × Nat × Array (Nat × α) :=
  let (w, k, hist) := state
  let w' := gdStep obj η w
  (w', k + 1, if (k + 1) % every == 0 then hist.push (k + 1, obj.loss w') else hist)

/-- `gradientDescent` that also records the loss at iteration 0 and every `every`
iterations (for training curves). The first component is `gradientDescent obj cfg w₀`
(`gradientDescentWithHistory_fst` in `PROOFS.lean`). -/
@[specialize] def gradientDescentWithHistory (obj : Objective α n) (cfg : GDConfig α)
    (w₀ : Vec α n) (every : Nat := 1) : Vec α n × Array (Nat × α) :=
  let (w, _, hist) := iterate (gdHistoryStep obj cfg.stepSize every) cfg.iters
    (w₀, 0, #[(0, obj.loss w₀)])
  (w, hist)

end GradientDescent

/-! ## Linear Regression

Least squares: minimise `mse` over affine models. The bias is handled by appending a
column of ones (`augmentMat`) and solving for `θ = (w, b)` in the augmented space.
-/

section LinearRegression

variable {α : Type} [Scalar α] {m n : Nat}

/-- Residuals `rᵢ = score xᵢ - yᵢ`. -/
@[specialize] def residuals (model : LinearModel α n) (data : Dataset α m n) : Vec α m :=
  Vector.ofFn fun i => model.score data.X[i] - data.y[i]

/-- Mean squared error `(1/m) ∑ᵢ (score xᵢ - yᵢ)² = ‖r‖² / m`. -/
@[specialize] def mse (model : LinearModel α n) (data : Dataset α m n) : α :=
  normSq (residuals model data) / Scalar.fromNat m

/-- `(2/m) Xₐᵀ (Xₐ θ - y)` with `Xₐ` and `Xₐᵀ` supplied, so callers can compute them once. -/
@[specialize] def mseGradAux (Xa : Mat α m (n + 1)) (XaT : Mat α (n + 1) m) (y : Vec α m)
    (θ : Vec α (n + 1)) : Vec α (n + 1) :=
  smul (Scalar.fromNat 2 / Scalar.fromNat m) (matVec XaT (vsub (matVec Xa θ) y))

/-- Gradient of `θ ↦ mse (ofParams θ) data`: `(2/m) Xₐᵀ (Xₐ θ - y)`, where `Xₐ` is the
augmented design matrix. -/
@[specialize] def mseGrad (data : Dataset α m n) (θ : Vec α (n + 1)) : Vec α (n + 1) :=
  let Xa := augmentMat data.X
  mseGradAux Xa (transpose Xa) data.y θ

/-- The least-squares objective in parameter space, for `gradientDescent`. `Xₐ` and `Xₐᵀ`
are computed once, outside the gradient closure; `grad` is definitionally `mseGrad data`. -/
@[specialize] def mseObjective (data : Dataset α m n) : Objective α (n + 1) :=
  let Xa := augmentMat data.X
  let XaT := transpose Xa
  { loss := fun θ => mse (LinearModel.ofParams θ) data
    grad := mseGradAux Xa XaT data.y }

/-- Closed-form least squares: solve the normal equations `(XₐᵀXₐ) θ = Xₐᵀ y`.
Spec (over `ℝ`): when `XₐᵀXₐ` is invertible (`m ≥ n + 1` samples in general position),
the result minimises `mse`. -/
@[specialize] def olsFit (data : Dataset α m n) : LinearModel α n :=
  let Xa := augmentMat data.X
  LinearModel.ofParams (linSolve (gram Xa) (matVec (transpose Xa) data.y))

/-- Least squares by gradient descent on `mseObjective`, starting from `θ = 0`.
Spec (over `ℝ`): with `0 < η ≤ 1/L`, where `L = (2/m) λ_max(XₐᵀXₐ)`, the `mse` converges
to the `olsFit` optimum at rate `O(1/k)`. -/
@[specialize] def linRegGD (cfg : GDConfig α) (data : Dataset α m n) : LinearModel α n :=
  LinearModel.ofParams (gradientDescent (mseObjective data) cfg vzero)

/-- `linRegGD` that also returns the training MSE every `every` iterations. -/
@[specialize] def linRegGDWithHistory (cfg : GDConfig α) (data : Dataset α m n)
    (every : Nat := 1) : LinearModel α n × Array (Nat × α) :=
  let (θ, hist) := gradientDescentWithHistory (mseObjective data) cfg vzero every
  (LinearModel.ofParams θ, hist)

end LinearRegression

/-! ## Perceptron -/

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
Spec (Novikoff): on data that is linearly separable with margin `γ` and radius `R`, the
algorithm makes at most `(R/γ)²` mistakes. Per mistake from the zero model,
`⟪w, u⟫` grows by at least `ηγ` and `‖w‖²` by at most `η²R²`. -/
def perceptronFit (cfg : PerceptronConfig α) (data : Dataset α m n) : LinearModel α n :=
  iterate (perceptronEpoch cfg.learningRate data) cfg.epochs LinearModel.zero

end Perceptron

end ML

end
