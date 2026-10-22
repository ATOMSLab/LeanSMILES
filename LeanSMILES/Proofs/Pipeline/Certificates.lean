/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.Pipeline.Certificates
import LeanSMILES.Proofs.Pipeline.Representation
import LeanSMILES.Proofs.Regression.GradientDescent
import LeanSMILES.Proofs.Regression.Iterative

/-!
# Pipeline certificates — soundness

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
* **Gauss–Seidel never increases the loss** (`Pipeline.gaussSeidel_antitone`), for every
  pipeline, with no condition.

The bridge between the exact `ℚ` data and the `ℝ` reading is `normalMatrix_real` /
`normalVector_real`: reading the data in `ℝ` and forming the normal equations gives the
casts of the exact normal equations.
-/

namespace LeanSMILES

open Regression Finset

/-! ## Exact data, read in `ℝ` -/

@[simp] theorem ratEmbed_real (q : ℚ) : (RatEmbed.ofRat q : ℝ) = q := rfl

theorem cast_sumGen {X : Type} (l : List X) (g : X → ℚ) :
    ((sumGen l g : ℚ) : ℝ) = sumGen l fun x => (g x : ℝ) := by
  induction l with
  | nil => simp [sumGen]
  | cons a l ih =>
    simp only [sumGen, List.foldr_cons] at ih ⊢
    push_cast
    rw [ih]

theorem cast_sumFin {n : ℕ} (g : Fin n → ℚ) : ((sumFin g : ℚ) : ℝ) = sumFin fun i => (g i : ℝ) :=
  cast_sumGen _ _

theorem cast_count (k : ℕ) : ((count k : ℚ) : ℝ) = count k := by
  induction k with
  | zero => simp [count, nsmulGen]
  | succ k ih =>
    simp only [count, nsmulGen] at ih ⊢
    push_cast
    rw [ih]

theorem cast_npowGen (x : ℚ) (k : ℕ) : ((npowGen x k : ℚ) : ℝ) = (x : ℝ) ^ k := by
  induction k with
  | zero => simp [npowGen]
  | succ k ih =>
    simp only [npowGen] at ih ⊢
    push_cast
    rw [ih, pow_succ, mul_comm]

/-- A rational matrix, read in `ℝ`. -/
abbrev castMat {m n : ℕ} (A : Mat ℚ m n) : Mat ℝ m n := A.map (·.map fun q : ℚ => (q : ℝ))

/-- A rational vector, read in `ℝ`. -/
abbrev castVec {n : ℕ} (v : Vec ℚ n) : Vec ℝ n := v.map fun q : ℚ => (q : ℝ)

namespace Regression.Problem

variable {m d : ℕ} (P : Problem ℚ m d)

theorem map_design_getElem (r : Fin m) (i : Fin (d + 1)) :
    (P.map fun q : ℚ => (q : ℝ)).design[r][i] = ((P.design[r][i] : ℚ) : ℝ) := by
  simp only [design, row, augment, Problem.map, Fin.getElem_fin, Vector.getElem_ofFn,
    Vector.getElem_map]
  rw [Vector.getElem_push, Vector.getElem_push]
  split_ifs <;> simp

/-- Reading the data in `ℝ` and forming `A` gives the cast of the exact `A`. -/
theorem map_normalMatrix (i j : Fin (d + 1)) :
    (P.map fun q : ℚ => (q : ℝ)).normalMatrix[i][j] = ((P.normalMatrix[i][j] : ℚ) : ℝ) := by
  simp only [normalMatrix, Fin.getElem_fin, Vector.getElem_ofFn]
  push_cast [cast_sumFin, cast_count, apply_ite (fun q : ℚ => (q : ℝ))]
  simp only [Fin.eta, ← Fin.getElem_fin, map_design_getElem]
  simp [Problem.map]

/-- Reading the data in `ℝ` and forming `b` gives the cast of the exact `b`. -/
theorem map_normalVector (i : Fin (d + 1)) :
    (P.map fun q : ℚ => (q : ℝ)).normalVector[i] = ((P.normalVector[i] : ℚ) : ℝ) := by
  simp only [normalVector, Fin.getElem_fin, Vector.getElem_ofFn]
  push_cast [cast_sumFin, cast_count]
  simp only [← Fin.getElem_fin, map_design_getElem]
  simp [Problem.map]

end Regression.Problem

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

theorem problem_real : p.problem ℝ = p.exactProblem.map fun q : ℚ => (q : ℝ) := rfl

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
      else 1 := fun i => by
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

/-! ## Jacobi and Gauss–Seidel -/

namespace SolverWitness

variable {n : ℕ}

theorem cast_offDiagWeight (A : Mat ℚ n n) (w : Vec ℚ n) (i : Fin n) :
    ((Check.offDiagWeight A w i : ℚ) : ℝ) = offDiagWeight (castMat A) (castVec w) i := by
  rw [Check.offDiagWeight, cast_sumFin, sumFin_eq_sum, offDiagWeight]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem cast_weightedMass (A : Mat ℚ n n) (w : Vec ℚ n) :
    ((Check.weightedMass A w : ℚ) : ℝ) = weightedMass (castMat A) (castVec w) := by
  rw [Check.weightedMass, cast_sumFin, sumFin_eq_sum, weightedMass]
  refine sum_congr rfl fun i _ => ?_
  rw [cast_sumFin, sumFin_eq_sum]
  exact sum_congr rfl fun j _ => by simp

/-- **What a passing check gives, in `ℝ`**: weighted diagonal dominance, the bound on the
right-hand side, and the excess loss below `ε`. -/
theorem check_sound {A : Mat ℚ n n} {b : Vec ℚ n} {k : ℕ} {ε : ℚ} (W : SolverWitness n)
    (h : W.check A b k ε = true) :
    DiagDominant (castMat A) (castVec W.weights) W.ratio ∧ (0 : ℝ) ≤ W.bound ∧
      (∀ i : Fin n, |(castVec b)[i]| ≤
        (1 - (W.ratio : ℝ)) * (castMat A)[i][i] * (castVec W.weights)[i] * W.bound) ∧
      weightedMass (castMat A) (castVec W.weights) * (W.bound : ℝ) ^ 2 *
        (W.ratio : ℝ) ^ (2 * k) ≤ ε := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨⟨⟨hρ0, hρ1⟩, hβ⟩, hrows⟩, hexc⟩ := h
  refine ⟨⟨by exact_mod_cast hρ0, by exact_mod_cast hρ1, fun i => ?_, fun i => ?_,
    fun i => ?_⟩, by exact_mod_cast hβ, fun i => ?_, ?_⟩
  · simpa using (hrows i).1.1.1
  · simpa using (hrows i).1.1.2
  · rw [← cast_offDiagWeight]
    have := (hrows i).1.2
    simpa using (Rat.cast_le (K := ℝ)).mpr this
  · have := (hrows i).2
    simpa using (Rat.cast_le (K := ℝ)).mpr this
  · rw [← cast_weightedMass, ← cast_npowGen W.ratio (2 * k)]
    have := (Rat.cast_le (K := ℝ)).mpr hexc
    simpa [excess] using this

end SolverWitness

namespace Pipeline

variable {m d : ℕ} (p : Pipeline m d)

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

/-- **Gauss–Seidel never increases the training loss**, for every pipeline with
`λ ≥ 0`: more sweeps are never worse. -/
theorem gaussSeidel_antitone (hr : 0 ≤ p.ridge) :
    Antitone fun k => (p.problem ℝ).loss
      (gaussSeidel (p.problem ℝ).normalMatrix (p.problem ℝ).normalVector k) :=
  (p.problem ℝ).loss_gaussSeidel_antitone (by simp only [ridge_real]; exact_mod_cast hr)

end Pipeline

end LeanSMILES
