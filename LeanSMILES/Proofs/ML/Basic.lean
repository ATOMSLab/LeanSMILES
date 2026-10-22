module

public import LeanSMILES.Proofs.LinAlg
public import LeanSMILES.Polymorphic.ML.Algorithm

/-!
# Machine Learning — Basic lemmas

Unfolding lemmas for the definitions in `Polymorphic/ML/`: linear models and their
parameter vector, gradient descent, the sparse least-squares solver, and the perceptron.
Lemmas that hold for every `Scalar` are stated generically; the rest over `ℝ`.
-/

public section

namespace ML

open Primitives

/-! ## Linear models -/

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

/-- Predictions are Lipschitz in the features: `(score x - score x')² ≤ ‖w‖² ‖x - x'‖²`. -/
theorem score_sub_sq_le {n : ℕ} (model : LinearModel ℝ n) (x x' : Vec ℝ n) :
    (model.score x - model.score x') ^ 2 ≤ normSq model.weights * distSq x x' := by
  have h : model.score x - model.score x' = dot model.weights (vsub x x') := by
    rw [dot_vsub]
    simp only [LinearModel.score]
    ring
  rw [h]
  exact dot_sq_le _ _

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

/-! ## Sparse least squares

Over `ℝ`, the sparse objective is the dense one, so `linRegGDSparse` computes exactly the
iterates of `linRegGD`.
-/

section Sparse

variable {m n : ℕ}

theorem mseObjectiveSparse_eq (data : Dataset ℝ m n) :
    mseObjectiveSparse data = mseObjective data := by
  simp only [mseObjectiveSparse, mseObjective, smatVec_ofDense]
  rfl

/-- The sparse solver runs exactly the same gradient descent as `linRegGD`. -/
theorem linRegGDSparse_eq (cfg : GDConfig ℝ) (data : Dataset ℝ m n) :
    linRegGDSparse cfg data = linRegGD cfg data := by
  simp only [linRegGDSparse, linRegGD, mseObjectiveSparse_eq]

end Sparse

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

/-! ## Algorithms -/

section Algorithm

variable {m n : ℕ}

@[simp] theorem Algorithm.fit_ols (data : Dataset ℝ m n) : Algorithm.ols.fit data = olsFit data :=
  rfl

@[simp] theorem Algorithm.fit_gradientDescent (cfg : GDConfig ℝ) (data : Dataset ℝ m n) :
    (Algorithm.gradientDescent cfg).fit data = linRegGD cfg data :=
  linRegGDSparse_eq cfg data

@[simp] theorem Algorithm.fit_perceptron (cfg : PerceptronConfig ℝ) (data : Dataset ℝ m n) :
    (Algorithm.perceptron cfg).fit data = perceptronFit cfg data :=
  rfl

end Algorithm

end ML

end
