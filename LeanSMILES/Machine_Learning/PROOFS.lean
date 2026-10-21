module

public import LeanSMILES.Machine_Learning.DEFINITIONS
public import LeanSMILES.Primitives.real
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Machine Learning — Proofs

Theorems about the algorithms in `DEFINITIONS.lean`. Unfolding lemmas that hold for any
`Scalar` come first; the ones that need Mathlib algebra are stated over `ℝ`.
-/

public section

namespace ML

open Primitives

/-! ## Iteration -/

theorem iterate_succ' {β : Type} (f : β → β) (n : Nat) (x : β) :
    iterate f (n + 1) x = f (iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- `Primitives.iterate` is Mathlib's `Nat.iterate`, so Mathlib's lemmas about `f^[n]`
apply. -/
theorem iterate_eq_iterate {β : Type} (f : β → β) (n : Nat) : iterate f n = f^[n] := by
  funext x
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-! ## Sums -/

/-- The computable fold `sumFin` is Mathlib's `Finset.sum` over `ℝ`. -/
theorem sumFin_eq_sum {n : ℕ} (f : Fin n → ℝ) : sumFin f = ∑ i, f i := by
  induction n with
  | zero => simp [sumFin]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, ← ih]
    unfold sumFin
    rw [Fin.foldl_succ_last]

theorem dot_eq_sum {n : ℕ} (u v : Vec ℝ n) : dot u v = ∑ i : Fin n, u[i] * v[i] :=
  sumFin_eq_sum _

/-- Peel off the last term of a `sumFin` (holds for every `Scalar`). -/
theorem sumFin_succ {α : Type} [Scalar α] {n : ℕ} (f : Fin (n + 1) → α) :
    sumFin f = sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n) := by
  unfold sumFin
  rw [Fin.foldl_succ_last]

/-! ## Linear models

`simp` writes vector indices as natural numbers (`v[↑i]`), so these lemmas are stated with
`j : ℕ` and a bound.
-/

@[simp] theorem augment_getElem_lt {α : Type} [Scalar α] {n : ℕ} (x : Vec α n) (j : ℕ)
    (h : j < n + 1) (hj : j < n) : (augment x)[j] = x[j] := by
  simp [augment, hj]

@[simp] theorem augment_getElem_last {α : Type} [Scalar α] {n : ℕ} (x : Vec α n)
    (h : n < n + 1) : (augment x)[n] = 1 := by
  simp [augment]

@[simp] theorem ofParams_weights_getElem {α : Type} [Scalar α] {n : ℕ} (θ : Vec α (n + 1))
    (j : ℕ) (hj : j < n) : (LinearModel.ofParams θ).weights[j] = θ[j] := by
  simp [LinearModel.ofParams]

@[simp] theorem ofParams_bias {α : Type} [Scalar α] {n : ℕ} (θ : Vec α (n + 1)) :
    (LinearModel.ofParams θ).bias = θ[n] := rfl

theorem ofParams_toParams {α : Type} [Scalar α] {n : ℕ} (model : LinearModel α n) :
    LinearModel.ofParams model.toParams = model := by
  obtain ⟨w, b⟩ := model
  simp only [LinearModel.ofParams, LinearModel.toParams, LinearModel.mk.injEq]
  constructor
  · ext j hj
    simp
  · simp

/-- The affine score is the linear score on augmented inputs. -/
theorem score_ofParams {n : ℕ} (θ : Vec ℝ (n + 1)) (x : Vec ℝ n) :
    (LinearModel.ofParams θ).score x = dot θ (augment x) := by
  simp only [LinearModel.score, dot]
  rw [sumFin_succ]
  simp

/-! ## Gradient descent -/

section GradientDescent

variable {α : Type} [Scalar α] {n : ℕ}

@[simp] theorem gdStep_getElem (obj : Objective α n) (η : α) (w : Vec α n) (i : Fin n) :
    (gdStep obj η w)[i] = w[i] - η * (obj.grad w)[i] := by
  simp [gdStep, vsub, smul]

@[simp] theorem gradientDescent_zero (obj : Objective α n) (η : α) (w₀ : Vec α n) :
    gradientDescent obj ⟨η, 0⟩ w₀ = w₀ := rfl

theorem gradientDescent_succ (obj : Objective α n) (η : α) (k : ℕ) (w₀ : Vec α n) :
    gradientDescent obj ⟨η, k + 1⟩ w₀ = gdStep obj η (gradientDescent obj ⟨η, k⟩ w₀) :=
  iterate_succ' _ _ _

theorem iterate_gdHistoryStep_fst (obj : Objective α n) (η : α) (every : Nat) (k : Nat)
    (w : Vec α n) (j : Nat) (h : Array (Nat × α)) :
    (iterate (gdHistoryStep obj η every) k (w, j, h)).1 = iterate (gdStep obj η) k w := by
  induction k generalizing w j h with
  | zero => rfl
  | succ k ih => exact ih _ _ _

/-- Recording the loss history doesn't change the iterate. -/
theorem gradientDescentWithHistory_fst (obj : Objective α n) (cfg : GDConfig α)
    (w₀ : Vec α n) (every : Nat) :
    (gradientDescentWithHistory obj cfg w₀ every).1 = gradientDescent obj cfg w₀ :=
  iterate_gdHistoryStep_fst obj cfg.stepSize every cfg.iters w₀ 0 _

theorem linRegGDWithHistory_fst {m : Nat} (cfg : GDConfig α) (data : Dataset α m n)
    (every : Nat) : (linRegGDWithHistory cfg data every).1 = linRegGD cfg data := by
  simp only [linRegGDWithHistory, linRegGD]
  rw [← gradientDescentWithHistory_fst (every := every)]

end GradientDescent

/-! ## Perceptron -/

section Perceptron

variable {α : Type} [Scalar α] {m n : ℕ}

theorem perceptronStep_of_mistake (η : α) (model : LinearModel α n) (x : Vec α n) (y : α)
    (h : IsMistake model x y) :
    perceptronStep η model x y =
      { weights := vadd model.weights (smul (η * y) x), bias := model.bias + η * y } :=
  if_pos h

theorem perceptronStep_of_not_mistake (η : α) (model : LinearModel α n) (x : Vec α n)
    (y : α) (h : ¬ IsMistake model x y) : perceptronStep η model x y = model :=
  if_neg h

@[simp] theorem perceptronFit_zero (η : α) (data : Dataset α m n) :
    perceptronFit ⟨η, 0⟩ data = LinearModel.zero := rfl

theorem perceptronFit_succ (η : α) (k : ℕ) (data : Dataset α m n) :
    perceptronFit ⟨η, k + 1⟩ data = perceptronEpoch η data (perceptronFit ⟨η, k⟩ data) :=
  iterate_succ' _ _ _

end Perceptron

end ML

end
