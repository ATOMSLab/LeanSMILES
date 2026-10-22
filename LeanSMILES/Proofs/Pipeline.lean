module

public import LeanSMILES.Proofs.Chem.Representation
public import LeanSMILES.Proofs.ML.Convergence
public import LeanSMILES.Proofs.ML.Perceptron
public import LeanSMILES.Proofs.ML.Metrics
public import LeanSMILES.Polymorphic.Pipeline

/-!
# Pipeline guarantees

What a trained pipeline is guaranteed to satisfy, from conditions that are checked
**without training it**. Each algorithm has a *certificate*: a structure whose fields are
the conditions, and whose `sound` theorem is the guarantee.

* **Gradient descent** (`GDCertificate`). The conditions only involve the representation
  and the hyperparameters, never the data: a feature bound `‖φ(mol)‖² ≤ R²` (proved once
  per representation in `Proofs/Chem/Representation.lean`), `η > 0`,
  `2η (R² + 1) ≤ 1`, and `B ≤ 2ηkε`. The guarantee holds **for every dataset**: the
  trained model's training error is within `ε` of every linear model with
  `‖(w, b)‖² ≤ B` (`GDCertificate.sound`). Also: training error never increases with more
  iterations (`gd_antitone`), and the `O(1/k)` rate (`gd_rate`).
* **Perceptron** (`PerceptronCertificate`). The conditions: `±1` labels, a separator `u`
  with `‖u‖ ≤ 1` and margin `γ > 0` on the training molecules (checked by featurizing them,
  not by training), a feature bound, and `(R² + 1)/γ² ≤ epochs`. The guarantee: the
  trained model classifies every training molecule correctly
  (`PerceptronCertificate.sound`) and has training accuracy `1`.
* **Ordinary least squares** (`ols_optimal_of_fullColumnRank`): when the augmented
  features of the training molecules are linearly independent, no linear model has a
  smaller training error. (Gauss–Jordan elimination is proved correct in
  `Proofs/LinSolve.lean`.)

Every theorem is about `Pipeline.model`, the same definition that runs on `Float`
(`Float/Pipeline.lean`), so it describes the executed pipeline up to rounding.
-/

public section

namespace LeanSMILES

open Primitives Chem ML

namespace Pipeline

variable {m n : ℕ} (p : Pipeline ℝ m n)

/-! ## The dataset of a pipeline -/

@[simp] theorem dataset_X_getElem (i : ℕ) (hi : i < m) :
    p.dataset.X[i] = p.representation.featurize p.data.molecules[i] := by
  simp [dataset]

@[simp] theorem dataset_y : p.dataset.y = p.data.targets := rfl

theorem model_eq_fit : p.model = p.algorithm.fit p.dataset := rfl

/-- A feature bound for the representation bounds every augmented training sample. -/
theorem augment_bound {R2 : ℝ} (h : p.representation.Bounded R2) (i : Fin m) :
    normSq (augment p.dataset.X[i]) ≤ R2 + 1 := by
  simpa using h.augment p.data.molecules[i]

/-! ## Ordinary least squares -/

/-- **OLS is optimal**: when the normal equations were solved, no linear model has a
smaller training error than the trained one. -/
theorem ols_optimal (halg : p.algorithm = .ols) (hsolve : SolvesNormalEquations p.dataset)
    (u : LinearModel ℝ n) : p.trainMSE ≤ mse u p.dataset := by
  rw [trainMSE, model_eq_fit, halg, Algorithm.fit_ols]
  exact olsFit_optimal _ hsolve u

/-- **OLS is optimal on full-rank data**: if the training molecules' features, with a
constant `1` appended, are linearly independent, no linear model has a smaller training
error than the trained one. The condition is about the data, not the trained model. -/
theorem ols_optimal_of_fullColumnRank (halg : p.algorithm = .ols)
    (hrank : FullColumnRank (augmentMat p.dataset.X)) (u : LinearModel ℝ n) :
    p.trainMSE ≤ mse u p.dataset :=
  p.ols_optimal halg (solvesNormalEquations_of_fullColumnRank _ hrank) u

/-! ## Gradient descent -/

section GradientDescent

variable {η : ℝ} {k : ℕ}

theorem gd_stepSize_condition (hη : 0 ≤ η) {R2 : ℝ} (hrep : p.representation.Bounded R2)
    (hstep : 2 * η * (R2 + 1) ≤ 1) : 2 * η * augmentedNormSqSum p.dataset ≤ m :=
  stepSize_condition_of_bound _ hη (p.augment_bound hrep) hstep

/-- **More iterations never hurt**: with `2η (R² + 1) ≤ 1`, the training error of
gradient descent is non-increasing in the number of iterations. -/
theorem gd_antitone (hη : 0 ≤ η) {R2 : ℝ} (hrep : p.representation.Bounded R2)
    (hstep : 2 * η * (R2 + 1) ≤ 1) :
    Antitone fun k => mse ((Algorithm.gradientDescent ⟨η, k⟩).fit p.dataset) p.dataset := by
  simp only [Algorithm.fit_gradientDescent]
  refine mse_linRegGD_antitone _ hη ?_
  have h := p.gd_stepSize_condition hη hrep hstep
  have : 0 ≤ η * augmentedNormSqSum p.dataset :=
    mul_nonneg hη (Finset.sum_nonneg fun i _ => normSq_nonneg _)
  linarith

/-- **The `O(1/k)` rate**: after `k ≥ 1` iterations, the training error is within
`‖u‖² / (2ηk)` of that of every linear model `u`. -/
theorem gd_rate (halg : p.algorithm = .gradientDescent ⟨η, k⟩) (hη : 0 < η) {R2 : ℝ}
    (hrep : p.representation.Bounded R2) (hstep : 2 * η * (R2 + 1) ≤ 1) (hk : 0 < k)
    (u : LinearModel ℝ n) :
    p.trainMSE ≤ mse u p.dataset + normSq u.toParams / (2 * η * k) := by
  rw [trainMSE, model_eq_fit, halg, Algorithm.fit_gradientDescent]
  exact mse_linRegGD_le _ hη (p.gd_stepSize_condition hη.le hrep hstep) hk u

end GradientDescent

/-- A certificate for gradient descent with hyperparameters `cfg` on representation `rep`.
Every field is about `rep` and `cfg` alone (no data, no trained model), and the numeric
ones are closed by `norm_num` for concrete values. -/
structure GDCertificate (rep : Representation ℝ n) (cfg : GDConfig ℝ) where
  /-- A bound on the squared norm of the features. -/
  R2 : ℝ
  /-- The squared-norm budget of the models the trained one is compared with. -/
  B : ℝ
  /-- The tolerated excess training error. -/
  ε : ℝ
  bounded : rep.Bounded R2
  stepSize_pos : 0 < cfg.stepSize
  stepSize_small : 2 * cfg.stepSize * (R2 + 1) ≤ 1
  iters_pos : 0 < cfg.iters
  iters_enough : B ≤ 2 * cfg.stepSize * cfg.iters * ε

/-- **Soundness of a gradient-descent certificate.** For every pipeline with that
representation and algorithm — so for **every dataset** — the trained model's training
error is within `ε` of that of every linear model `u` with `‖(w, b)‖² ≤ B`. -/
theorem GDCertificate.sound {cfg : GDConfig ℝ} (c : GDCertificate p.representation cfg)
    (halg : p.algorithm = .gradientDescent cfg) (u : LinearModel ℝ n)
    (hu : normSq u.toParams ≤ c.B) : p.trainMSE ≤ mse u p.dataset + c.ε := by
  obtain ⟨η, k⟩ := cfg
  rw [trainMSE, model_eq_fit, halg, Algorithm.fit_gradientDescent]
  exact mse_linRegGD_le_add _ c.stepSize_pos
    (p.gd_stepSize_condition c.stepSize_pos.le c.bounded c.stepSize_small) c.iters_pos
    c.iters_enough u hu

/-! ## Perceptron -/

/-- A certificate for the perceptron with hyperparameters `cfg` on pipeline `p`. Its
conditions are checked on the featurized training molecules, without training; for bit
representations, `PerceptronWitness.certificate` (`Proofs/Certificates.lean`) builds one
from a check that the kernel evaluates. -/
structure PerceptronCertificate (cfg : PerceptronConfig ℝ) where
  /-- A bound on the squared norm of the training molecules' features (a static bound
  `p.representation.Bounded R2` gives one). -/
  R2 : ℝ
  bounded : ∀ i : Fin m, normSq (p.representation.featurize p.data.molecules[i]) ≤ R2
  labels : ∀ i : Fin m, p.data.targets[i] = 1 ∨ p.data.targets[i] = -1
  /-- A separating parameter vector `(w, b)`. -/
  separator : Vec ℝ (n + 1)
  separator_norm : normSq separator ≤ 1
  /-- The margin of the separator. -/
  γ : ℝ
  margin_pos : 0 < γ
  margin : ∀ i : Fin m,
    γ ≤ p.data.targets[i] * dot separator (augment (p.representation.featurize p.data.molecules[i]))
  rate_pos : 0 < cfg.learningRate
  epochs_enough : (R2 + 1) / γ ^ 2 ≤ cfg.epochs

namespace PerceptronCertificate

variable {p} {cfg : PerceptronConfig ℝ} (c : PerceptronCertificate p cfg)
include c

theorem augment_bound (i : Fin m) : normSq (augment p.dataset.X[i]) ≤ c.R2 + 1 := by
  simpa [normSq_augment] using c.bounded i

theorem hypotheses :
    (∀ i : Fin m, p.dataset.y[i] = 1 ∨ p.dataset.y[i] = -1) ∧
    (∀ i : Fin m, c.γ ≤ p.dataset.y[i] * dot c.separator (augment p.dataset.X[i])) ∧
    (∀ i : Fin m, normSq (augment p.dataset.X[i]) ≤ Real.sqrt (c.R2 + 1) ^ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
  · simpa using c.labels i
  · simpa using c.margin i
  · rw [Real.sq_sqrt ((normSq_nonneg _).trans (c.augment_bound i))]
    exact c.augment_bound i

theorem floor_le_epochs : ⌊Real.sqrt (c.R2 + 1) ^ 2 / c.γ ^ 2⌋₊ ≤ cfg.epochs := by
  by_cases h : 0 ≤ c.R2 + 1
  · rw [Real.sq_sqrt h]
    exact Nat.floor_le_of_le c.epochs_enough
  · rw [Real.sqrt_eq_zero'.mpr (le_of_lt (not_le.mp h))]
    simp

/-- The trained perceptron makes no mistake on any training molecule. -/
theorem no_mistakes (halg : p.algorithm = .perceptron cfg) (i : Fin m) :
    ¬ IsMistake p.model p.dataset.X[i] p.dataset.y[i] := by
  obtain ⟨η, E⟩ := cfg
  obtain ⟨hy, hmargin, hR⟩ := c.hypotheses
  obtain ⟨k, hk, hclean⟩ := perceptron_converges p.dataset c.rate_pos hy c.separator
    c.separator_norm hmargin c.margin_pos hR
  obtain ⟨j, hj⟩ : ∃ j, E = k + j := ⟨E - k, by have := c.floor_le_epochs; simp at this; omega⟩
  rw [model_eq_fit, halg, Algorithm.fit_perceptron, hj,
    perceptronFit_stable η p.dataset k hclean j]
  exact hclean i

/-- **Soundness of a perceptron certificate**: the trained model classifies every
training molecule correctly. -/
theorem sound (halg : p.algorithm = .perceptron cfg) (i : Fin m) :
    p.model.classify (p.representation.featurize p.data.molecules[i]) = p.data.targets[i] := by
  have := classify_eq_of_not_isMistake _ _ (c.hypotheses.1 i) (c.no_mistakes halg i)
  simpa using this

/-- The trained perceptron has training accuracy `1` (on a non-empty dataset). -/
theorem trainAccuracy_eq_one (halg : p.algorithm = .perceptron cfg) (hm : 0 < m) :
    p.trainAccuracy = 1 := by
  have hpos : ∀ i : Fin m, 0 < p.dataset.y[i] * p.model.score p.dataset.X[i] := fun i => by
    have := c.no_mistakes halg i
    unfold IsMistake at this
    linarith
  simp only [trainAccuracy, accuracy, sumFin_eq_sum, LinearModel.predictAll, Fin.getElem_fin,
    Vector.getElem_ofFn, fromNat_real]
  have hone : ∀ i : Fin m,
      (if 0 < p.dataset.y[(i : ℕ)] * p.model.score p.dataset.X[(i : ℕ)] then (1 : ℝ) else 0) = 1 :=
    fun i => if_pos (hpos i)
  simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr hm.ne')

end PerceptronCertificate

end Pipeline

end LeanSMILES

end
