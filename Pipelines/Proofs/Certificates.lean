/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import Pipelines.Certificates
public import Pipelines.Proofs.Representation
public import LeanLearn.Proofs.Regression.GradientDescent
public import LeanLearn.Proofs.Regression.Certificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Pipelines.Proofs.Certificates

Pipeline certificates — soundness.

What a trained pipeline is guaranteed to satisfy, from conditions checked **without
training it**. Write `L` for the training loss of the pipeline's problem read in `ℝ`
(`p.problem ℝ`), and `θ` for the trained parameters.

* **Gradient descent** (`GDCertificate.sound`). The conditions only involve the
  representation and the hyperparameters: a feature bound `‖φ(M)‖² ≤ R²` for every molecule
  (`Representation.Bounded`, proved once per representation), `λ ≥ 0`, `η > 0`,
  `2η (R² + 1 + λ) ≤ 1`, and `B ≤ 2ηkε`. The guarantee holds for **every dataset**:
  `L(θ) ≤ L(u) + ε` for every `u` with `‖u‖² ≤ B`.
* **Jacobi and Gauss–Seidel** (`Pipeline.checkSolver_sound`). The exact check
  `p.checkSolver W ε` (weighted diagonal dominance of the normal equations, computed over
  `ℚ` from the data) gives `L(θ) ≤ L(u) + ε` for **every** `u`: the trained model is within
  `ε` of the optimum.
* **After training** (`Pipeline.checkResidual_sound`). The exact residual check on any
  parameters `θ` — whatever produced them — gives `L(θ) ≤ L(u) + ε` for **every** `u`, at any
  `λ > 0`, with no condition on the normal equations.
* **Gauss–Seidel never increases the loss** (`Pipeline.gaussSeidel_antitone`), for every
  pipeline, with no condition.

The bridge between the exact `ℚ` data and the `ℝ` reading is `normalMatrix_real` /
`normalVector_real`, from `LeanLearn`'s `Problem.map_normalMatrix` / `map_normalVector`.
-/

@[expose] public section

namespace Pipelines

open LeanSMILES LeanLearn LeanLearn.Regression Finset

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

theorem problem_real : p.problem ℝ = p.exactProblem.map fun q : ℚ ↦ (q : ℝ) := rfl

theorem normalMatrix_real :
    (p.problem ℝ).normalMatrix = castMat p.exactProblem.normalMatrix := by
  ext i hi j hj
  have := Problem.map_normalMatrix p.exactProblem ⟨i, hi⟩ ⟨j, hj⟩
  simpa [problem_real] using this

theorem normalVector_real : (p.problem ℝ).normalVector = castVec p.exactProblem.normalVector := by
  ext i hi
  have := Problem.map_normalVector p.exactProblem ⟨i, hi⟩
  simpa [problem_real] using this

@[simp] theorem ridge_real : (p.problem ℝ).ridge = (p.ridge : ℝ) := rfl

theorem trainLoss_real :
    p.trainLoss ℝ = (p.problem ℝ).loss
      (p.algorithm.solve (p.problem ℝ).normalMatrix (p.problem ℝ).normalVector) := rfl

/-- Every training sample, with the constant `1`, has `‖xᵣ‖² ≤ R² + 1` when the
representation is bounded by `R²`. -/
theorem sample_bound {R2 : ℚ} (h : p.representation.Bounded R2) (r : Fin m) :
    ∑ i, (p.problem ℝ).x r i ^ 2 ≤ (R2 : ℝ) + 1 := by
  have hrow : ∀ i : Fin (d + 1), (p.problem ℝ).x r i =
      if hi : i.val < d then (((p.representation p.data.molecules[r])[i.val]'hi : ℚ) : ℝ)
      else 1 := fun i ↦ by
    simp only [Problem.x, Problem.row, augment, problem_real, Problem.map, exactProblem,
      Fin.getElem_fin, Vector.getElem_map]
    rw [Vector.getElem_push]
    split_ifs <;> simp
  simp only [hrow]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dif_pos, Fin.val_last, lt_irrefl, dif_neg,
    not_false_eq_true, one_pow]
  have := h p.data.molecules[r]
  have hcast : ∑ i : Fin d, (((p.representation p.data.molecules[r])[i.val] : ℚ) : ℝ) ^ 2 =
      ((∑ i : Fin d, (p.representation p.data.molecules[r])[i] ^ 2 : ℚ) : ℝ) := by
    push_cast; rfl
  rw [hcast]
  have h' : ((∑ i : Fin d, (p.representation p.data.molecules[r])[i] ^ 2 : ℚ) : ℝ) ≤ R2 := by
    exact_mod_cast this
  linarith

end Pipeline

/-! ## Gradient descent -/

/-- A certificate for gradient descent with step size `η`, `k` steps and ridge penalty
`λ` on representation `rep`. Every field is about `rep`, `λ`, `η` and `k` — no data, no
training. For concrete numbers, `norm_num` (or `decide`) closes the arithmetic fields. -/
structure GDCertificate {d : ℕ} (rep : Representation d) (ridge η : ℚ) (k : ℕ) where
  /-- A bound on the squared norm of the features of every molecule. -/
  R2 : ℚ
  /-- The squared-norm budget of the parameters the trained model is compared with. -/
  B : ℚ
  /-- The tolerated excess training loss. -/
  ε : ℚ
  bounded : rep.Bounded R2
  ridge_nonneg : 0 ≤ ridge
  stepSize_pos : 0 < η
  stepSize_small : 2 * η * (R2 + 1 + ridge) ≤ 1
  iters_pos : 0 < k
  iters_enough : B ≤ 2 * η * k * ε

/-- **Soundness of a gradient-descent certificate.** For every pipeline with that
representation, penalty and algorithm — so for **every dataset** — the trained model's
training loss is within `ε` of that of every `u` with `‖u‖² ≤ B`. -/
theorem GDCertificate.sound {m d : ℕ} {rep : Representation d} {ridge η : ℚ} {k : ℕ}
    (c : GDCertificate rep ridge η k) (p : Pipeline m d) (hrep : p.representation = rep)
    (hridge : p.ridge = ridge) (halg : p.algorithm = .gradientDescent η k)
    (u : Vec ℝ (d + 1)) (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ c.B) :
    p.trainLoss ℝ ≤ (p.problem ℝ).loss u + c.ε := by
  set P := p.problem ℝ
  have hr : 0 ≤ P.ridge := by
    simp only [P, Pipeline.ridge_real, hridge]; exact_mod_cast c.ridge_nonneg
  have hsmooth : P.smoothness ≤ ((c.R2 : ℝ) + 1) + (ridge : ℝ) := by
    have := P.smoothness_le (R2 := (c.R2 : ℝ) + 1)
      (by have := c.bounded.nonneg; positivity)
      (p.sample_bound (hrep ▸ c.bounded))
    simpa [P, hridge] using this
  have hη : (0 : ℝ) < η := by exact_mod_cast c.stepSize_pos
  have hstep : 2 * (η : ℝ) * P.smoothness ≤ 1 := by
    have h1 : (2 * η * (c.R2 + 1 + ridge) : ℝ) ≤ 1 := by exact_mod_cast c.stepSize_small
    calc 2 * (η : ℝ) * P.smoothness ≤ 2 * η * ((c.R2 + 1) + ridge) :=
          mul_le_mul_of_nonneg_left hsmooth (by positivity)
      _ ≤ 1 := by linarith
  have hB : (c.B : ℝ) ≤ 2 * (η : ℝ) * k * c.ε := by exact_mod_cast c.iters_enough
  rw [Pipeline.trainLoss_real, halg]
  exact P.loss_gradientDescent_le_add hr hη hstep c.iters_pos hB u hu

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

/-- **Soundness of `checkGD`**: with a feature bound `R²` for the representation, a passing
check gives the gradient-descent guarantee — for every `u` with `‖u‖² ≤ B`, the trained
model's training loss is within `ε` of `u`'s. -/
theorem checkGD_sound {R2 B ε : ℚ} (hR : p.representation.Bounded R2)
    (h : p.checkGD R2 B ε = true) (u : Vec ℝ (d + 1)) (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ B) :
    p.trainLoss ℝ ≤ (p.problem ℝ).loss u + ε := by
  rcases halg : p.algorithm with ⟨η, k⟩ | k | k
  · simp only [checkGD, halg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hr, hη⟩, hstep⟩, hk⟩, hB⟩ := h
    let c : GDCertificate p.representation p.ridge η k :=
      { R2, B, ε, bounded := hR, ridge_nonneg := hr, stepSize_pos := hη,
        stepSize_small := hstep, iters_pos := hk, iters_enough := hB }
    exact c.sound p rfl rfl halg u hu
  all_goals simp [checkGD, halg] at h

/-! ## Jacobi and Gauss–Seidel -/

/-- **Soundness of a Jacobi / Gauss–Seidel certificate.** If the exact check passes, the
trained model's training loss is within `ε` of that of **every** parameter vector `u`:
the model is `ε`-optimal. -/
theorem checkSolver_sound {W : SolverWitness (d + 1)} {ε : ℚ} (h : p.checkSolver W ε = true)
    (u : Vec ℝ (d + 1)) : p.trainLoss ℝ ≤ (p.problem ℝ).loss u + ε := by
  set P := p.problem ℝ
  rw [trainLoss_real]
  rcases halg : p.algorithm with ⟨η, k⟩ | k | k
  · simp [checkSolver, halg, solverIters] at h
  all_goals
    simp only [checkSolver, halg, solverIters, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, hW⟩ := h
    obtain ⟨hdd, hβ, hb, hexc⟩ := W.check_sound hW
    have hridge : 0 ≤ P.ridge := by simp only [P, ridge_real]; exact_mod_cast hr
    rw [← normalMatrix_real] at hdd hb hexc
    rw [← normalVector_real] at hb
  · have := P.loss_jacobi_le hridge hdd hβ hb k u
    simp only [Algorithm.solve]
    linarith
  · have := P.loss_gaussSeidel_le hridge hdd hβ hb k u
    simp only [Algorithm.solve]
    linarith

/-- **Soundness of the residual certificate.** If the exact check passes on parameters `θ` —
whatever solver produced them, in whatever arithmetic — then, read in `ℝ`, `θ`'s training loss
is within `ε` of that of **every** parameter vector `u`: `θ` is `ε`-optimal, at any `λ > 0`. -/
theorem checkResidual_sound {θ : Vec ℚ (d + 1)} {ε : ℚ} (h : p.checkResidual θ ε = true)
    (u : Vec ℝ (d + 1)) : (p.problem ℝ).loss (castVec θ) ≤ (p.problem ℝ).loss u + ε := by
  rw [problem_real]
  exact p.exactProblem.checkResidual_sound h u

/-- **Gauss–Seidel never increases the training loss**, for every pipeline with
`λ ≥ 0`: more sweeps are never worse. -/
theorem gaussSeidel_antitone (hr : 0 ≤ p.ridge) :
    Antitone fun k ↦ (p.problem ℝ).loss
      (gaussSeidel (p.problem ℝ).normalMatrix (p.problem ℝ).normalVector k) :=
  (p.problem ℝ).loss_gaussSeidel_antitone (by simp only [ridge_real]; exact_mod_cast hr)

end Pipeline

end Pipelines
