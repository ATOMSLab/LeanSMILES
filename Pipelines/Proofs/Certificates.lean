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
* **Gradient descent, on the data** (`Pipeline.checkGDData_sound`). The step-size
  condition `2ηΛ ≤ 1` decided with the exact smoothness `Λ` of the training set
  (`smoothness_real` bridges it to `Problem.smoothness` of the `ℝ` reading) gives
  `L(θ) ≤ L(u) + ‖u‖² / (2ηk)` for **every** `u`: the `O(1/k)` rate, for this very run.
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

/-- The `ℝ` problem the guarantees are about is the exact `ℚ` problem the checks compute on,
mapped through `Rat.cast`: the shape `LeanLearn`'s `Problem.map_*` bridge lemmas are stated for. -/
theorem problem_real : p.problem ℝ = p.exactProblem.map fun q : ℚ ↦ (q : ℝ) := rfl

/-- The normal matrix `A` of the `ℝ` problem is the cast of the exact `ℚ` matrix `checkSolver`
computes, so a dominance certificate checked in `ℚ` is about the `A` of the `ℝ` guarantee. -/
theorem normalMatrix_real : (p.problem ℝ).normalMatrix = castMat p.exactProblem.normalMatrix := by
  ext i hi j hj
  simpa [problem_real] using p.exactProblem.map_normalMatrix ⟨i, hi⟩ ⟨j, hj⟩

/-- The normal vector `b` of the `ℝ` problem is the cast of the exact `ℚ` vector `checkSolver`
computes, so the bound on `b` checked in `ℚ` is about the `b` of the `ℝ` guarantee. -/
theorem normalVector_real : (p.problem ℝ).normalVector = castVec p.exactProblem.normalVector := by
  ext i hi
  simpa [problem_real] using p.exactProblem.map_normalVector ⟨i, hi⟩

/-- The penalty `λ` of the `ℝ` problem is the cast of the pipeline's exact `λ`, so `0 ≤ λ`
checked in `ℚ` gives the `0 ≤ λ` every `ℝ` bound assumes (by `simp`). -/
@[simp] theorem ridge_real : (p.problem ℝ).ridge = (p.ridge : ℝ) := rfl

/-- `p.trainLoss ℝ` unfolded: the `ℝ` problem's loss at the algorithm's output on its normal
equations, the form through which `normalMatrix_real` / `normalVector_real` reach the `ℚ` data. -/
theorem trainLoss_real : p.trainLoss ℝ = (p.problem ℝ).loss
    (p.algorithm.solve (p.problem ℝ).normalMatrix (p.problem ℝ).normalVector) := rfl

/-- Entry `i` of training sample `r`, read in `ℝ`, is the cast of the exact entry. -/
theorem row_real (r : Fin m) (i : Fin (d + 1)) :
    ((p.problem ℝ).row r)[i] = (((p.exactProblem.row r)[i] : ℚ) : ℝ) := by
  simpa [Problem.design, problem_real] using p.exactProblem.map_design_getElem r i

/-- Reading the data in `ℝ` and forming the smoothness `Λ` gives the cast of the exact `Λ`. -/
theorem smoothness_real : (p.problem ℝ).smoothness = (p.smoothnessExact : ℝ) := by
  simp only [Problem.smoothness, smoothnessExact, Problem.smoothnessExact, sumFin_eq_sum,
    dot_eq_sum, count_eq_natCast, ridge_real, Problem.feature, row_real, sq]
  push_cast
  rfl

/-- Every training sample, with the constant `1`, has `‖xᵣ‖² ≤ R² + 1` when the
representation is bounded by `R²`. -/
theorem sample_bound {R2 : ℚ} (h : p.representation.Bounded R2) (r : Fin m) :
    ∑ i, (p.problem ℝ).feature r i ^ 2 ≤ (R2 : ℝ) + 1 := by
  have hq : ∑ i : Fin (d + 1), (p.exactProblem.row r)[i] ^ 2 ≤ R2 + 1 := by
    simpa [Fin.sum_univ_castSucc, Problem.row, augment, exactProblem, Vector.getElem_push]
      using h p.data.molecules[r]
  simp only [Problem.feature, row_real]
  exact_mod_cast hq

end Pipeline

/-! ## Gradient descent -/

/-- A certificate for gradient descent with step size `η`, `k` steps and ridge penalty
`λ` on representation `rep`. Every field is about `rep`, `λ`, `η` and `k` — no data, no
training. For concrete numbers, `norm_num` (or `decide`) closes the arithmetic fields. -/
structure GDCertificate {d : ℕ} (rep : Representation d) (ridge η : ℚ) (k : ℕ) where
  /-- A bound on the squared norm of the features of every molecule. -/
  R2 : ℚ
  /-- The squared-norm budget `B` of the parameters the trained model is compared with. -/
  budget : ℚ
  /-- The tolerated excess training loss `ε`. -/
  tolerance : ℚ
  /-- `‖φ(M)‖² ≤ R²` for every molecule, so every sample with its `1` has `‖xᵣ‖² ≤ R² + 1`. -/
  bounded : rep.Bounded R2
  /-- The penalty is non-negative, so the loss is convex. -/
  ridge_nonneg : 0 ≤ ridge
  /-- The step size is positive: the rate `‖u‖² / (2ηk)` divides by `η`. -/
  stepSize_pos : 0 < η
  /-- `2η (R² + 1 + λ) ≤ 1`: the step is small for the smoothness bound `Λ ≤ R² + 1 + λ`. -/
  stepSize_small : 2 * η * (R2 + 1 + ridge) ≤ 1
  /-- At least one step is taken: the rate `‖u‖² / (2ηk)` divides by `k`. -/
  iters_pos : 0 < k
  /-- `B ≤ 2ηkε`: enough steps for the `‖u‖² / (2ηk)` rate to fall below `ε` on the budget. -/
  iters_enough : budget ≤ 2 * η * k * tolerance

/-- **Soundness of a gradient-descent certificate.** For every pipeline with that
representation, penalty and algorithm — so for **every dataset** — the trained model's
training loss is within `ε` of that of every `u` with `‖u‖² ≤ B`. -/
theorem GDCertificate.sound {m d : ℕ} {rep : Representation d} {ridge η : ℚ} {k : ℕ}
    (c : GDCertificate rep ridge η k) (p : Pipeline m d) (hrep : p.representation = rep)
    (hridge : p.ridge = ridge) (halg : p.algorithm = .gradientDescent η k) (u : Vec ℝ (d + 1))
    (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ c.budget) :
    p.trainLoss ℝ ≤ (p.problem ℝ).loss u + c.tolerance := by
  set P := p.problem ℝ
  have hr : 0 ≤ P.ridge := by simpa [P, hridge] using c.ridge_nonneg
  have hsmooth : P.smoothness ≤ c.R2 + 1 + ridge := by
    simpa [P, hridge] using P.smoothness_le (R2 := (c.R2 : ℝ) + 1)
      (add_nonneg (Rat.cast_nonneg.mpr c.bounded.nonneg) zero_le_one)
      (p.sample_bound (hrep ▸ c.bounded))
  have hη : (0 : ℝ) < η := by exact_mod_cast c.stepSize_pos
  have hstep : 2 * (η : ℝ) * P.smoothness ≤ 1 :=
    (mul_le_mul_of_nonneg_left hsmooth (by positivity)).trans (by exact_mod_cast c.stepSize_small)
  have hB : (c.budget : ℝ) ≤ 2 * (η : ℝ) * k * c.tolerance := by exact_mod_cast c.iters_enough
  rw [Pipeline.trainLoss_real, halg]
  exact P.loss_gradientDescent_le_add hr hη hstep c.iters_pos hB u hu

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

/-- **Soundness of `checkGD`**: with a feature bound `R²` for the representation, a passing
check gives the gradient-descent guarantee — for every `u` with `‖u‖² ≤ B`, the trained
model's training loss is within `ε` of `u`'s. -/
theorem checkGD_sound {R2 B ε : ℚ} (hR : p.representation.Bounded R2) (h : p.checkGD R2 B ε = true)
    (u : Vec ℝ (d + 1)) (hu : ∑ i : Fin (d + 1), u[i] ^ 2 ≤ B) :
    p.trainLoss ℝ ≤ (p.problem ℝ).loss u + ε := by
  rcases halg : p.algorithm with ⟨η, k⟩ | _ | _
  · simp only [checkGD, halg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hr, hη⟩, hstep⟩, hk⟩, hB⟩ := h
    exact GDCertificate.sound ⟨R2, B, ε, hR, hr, hη, hstep, hk, hB⟩ p rfl rfl halg u hu
  all_goals simp [checkGD, halg] at h

/-- **Soundness of `checkGDData`**: if the exact step-size check on this training set
passes, the trained model's training loss is within `‖u‖² / (2ηk)` of that of **every**
parameter vector `u` — the `O(1/k)` rate of `loss_gradientDescent_le`, for this very run. -/
theorem checkGDData_sound (h : p.checkGDData = true) (u : Vec ℝ (d + 1)) :
    p.trainLoss ℝ ≤ (p.problem ℝ).loss u + p.gdRate * ∑ i : Fin (d + 1), u[i] ^ 2 := by
  rcases halg : p.algorithm with ⟨η, k⟩ | _ | _
  · simp only [checkGDData, halg, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hr, hη⟩, hstep⟩, hk⟩ := h
    have hstep' : 2 * (η : ℝ) * (p.problem ℝ).smoothness ≤ 1 := by
      rw [smoothness_real]
      exact_mod_cast hstep
    rw [trainLoss_real, halg]
    simpa [Algorithm.solve, gdRate, halg, div_eq_inv_mul] using
      (p.problem ℝ).loss_gradientDescent_le (by simpa using hr) (by exact_mod_cast hη) hstep' hk u
  all_goals simp [checkGDData, halg] at h

/-! ## Jacobi and Gauss–Seidel -/

/-- **Soundness of a Jacobi / Gauss–Seidel certificate.** If the exact check passes, the
trained model's training loss is within `ε` of that of **every** parameter vector `u`:
the model is `ε`-optimal. -/
theorem checkSolver_sound {W : SolverWitness (d + 1)} {ε : ℚ} (h : p.checkSolver W ε = true)
    (u : Vec ℝ (d + 1)) : p.trainLoss ℝ ≤ (p.problem ℝ).loss u + ε := by
  set P := p.problem ℝ
  rw [trainLoss_real]
  rcases halg : p.algorithm with _ | k | k
  · simp [checkSolver, halg, solverIters] at h
  all_goals
    simp only [checkSolver, halg, solverIters, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hr, hW⟩ := h
    obtain ⟨hdd, hβ, hb, hexc⟩ := W.check_sound hW
    have hridge : 0 ≤ P.ridge := by simpa [P] using hr
    rw [← normalMatrix_real] at hdd hb hexc
    rw [← normalVector_real] at hb
  · exact (P.loss_jacobi_le hridge hdd hβ hb k u).trans (by linarith)
  · exact (P.loss_gaussSeidel_le hridge hdd hβ hb k u).trans (by linarith)

/-- **Soundness of the residual certificate.** If the exact check passes on parameters `θ` —
whatever solver produced them, in whatever arithmetic — then, read in `ℝ`, `θ`'s training loss
is within `ε` of that of **every** parameter vector `u`: `θ` is `ε`-optimal, at any `λ > 0`. -/
theorem checkResidual_sound {θ : Vec ℚ (d + 1)} {ε : ℚ} (h : p.checkResidual θ ε = true)
    (u : Vec ℝ (d + 1)) : (p.problem ℝ).loss (castVec θ) ≤ (p.problem ℝ).loss u + ε :=
  p.exactProblem.checkResidual_sound h u

/-- **Gauss–Seidel never increases the training loss**, for every pipeline with
`λ ≥ 0`: more sweeps are never worse. -/
theorem gaussSeidel_antitone (hr : 0 ≤ p.ridge) : Antitone fun k ↦ (p.problem ℝ).loss
    (gaussSeidel (p.problem ℝ).normalMatrix (p.problem ℝ).normalVector k) :=
  (p.problem ℝ).loss_gaussSeidel_antitone (by simpa using hr)

end Pipeline

end Pipelines
