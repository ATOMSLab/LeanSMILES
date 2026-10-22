/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import LeanLearn.Regression.Certificates
public import LeanLearn.Proofs.Regression.Iterative

/-!
# LeanLearn.Proofs.Regression.Certificates

Solver certificates — soundness, and the bridge from exact `ℚ` data to its `ℝ` reading.

* **Exact data, read in `ℝ`** (`Problem.map_normalMatrix`, `Problem.map_normalVector`):
  reading a rational problem in `ℝ` and forming its normal equations gives the casts of the
  exact normal equations. `castMat` / `castVec` are the casts.
* **What a passing check gives** (`SolverWitness.check_sound`): weighted diagonal dominance
  of `A` in `ℝ`, the bound on the right-hand side, and the certified excess below `ε` — the
  hypotheses of `loss_jacobi_le` and `loss_gaussSeidel_le`.
-/

@[expose] public section

namespace LeanLearn.Regression

open Finset

/-! ## Exact data, read in `ℝ` -/

@[simp] theorem ratEmbed_real (q : ℚ) : (RatEmbed.ofRat q : ℝ) = q := rfl

theorem cast_sumGen {X : Type} (l : List X) (g : X → ℚ) :
    ((sumGen l g : ℚ) : ℝ) = sumGen l fun x ↦ (g x : ℝ) := by
  induction l with
  | nil => simp [sumGen]
  | cons a l ih =>
    simp only [sumGen, List.foldr_cons] at ih ⊢
    push_cast
    rw [ih]

theorem cast_sumFin {n : ℕ} (g : Fin n → ℚ) : ((sumFin g : ℚ) : ℝ) = sumFin fun i ↦ (g i : ℝ) :=
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
abbrev castMat {m n : ℕ} (A : Mat ℚ m n) : Mat ℝ m n := A.map (·.map fun q : ℚ ↦ (q : ℝ))

/-- A rational vector, read in `ℝ`. -/
abbrev castVec {n : ℕ} (v : Vec ℚ n) : Vec ℝ n := v.map fun q : ℚ ↦ (q : ℝ)

namespace Problem

variable {m d : ℕ} (P : Problem ℚ m d)

theorem map_design_getElem (r : Fin m) (i : Fin (d + 1)) :
    (P.map fun q : ℚ ↦ (q : ℝ)).design[r][i] = ((P.design[r][i] : ℚ) : ℝ) := by
  simp only [design, row, augment, Problem.map, Fin.getElem_fin, Vector.getElem_ofFn,
    Vector.getElem_map]
  rw [Vector.getElem_push, Vector.getElem_push]
  split_ifs <;> simp

/-- Reading the data in `ℝ` and forming `A` gives the cast of the exact `A`. -/
theorem map_normalMatrix (i j : Fin (d + 1)) :
    (P.map fun q : ℚ ↦ (q : ℝ)).normalMatrix[i][j] = ((P.normalMatrix[i][j] : ℚ) : ℝ) := by
  simp only [normalMatrix, Fin.getElem_fin, Vector.getElem_ofFn]
  push_cast [cast_sumFin, cast_count, apply_ite (fun q : ℚ ↦ (q : ℝ))]
  simp only [Fin.eta, ← Fin.getElem_fin, map_design_getElem]
  simp [Problem.map]

/-- Reading the data in `ℝ` and forming `b` gives the cast of the exact `b`. -/
theorem map_normalVector (i : Fin (d + 1)) :
    (P.map fun q : ℚ ↦ (q : ℝ)).normalVector[i] = ((P.normalVector[i] : ℚ) : ℝ) := by
  simp only [normalVector, Fin.getElem_fin, Vector.getElem_ofFn]
  push_cast [cast_sumFin, cast_count]
  simp only [← Fin.getElem_fin, map_design_getElem]
  simp [Problem.map]

end Problem

/-! ## Jacobi and Gauss–Seidel -/

namespace SolverWitness

variable {n : ℕ}

theorem cast_offDiagWeight (A : Mat ℚ n n) (w : Vec ℚ n) (i : Fin n) :
    ((Check.offDiagWeight A w i : ℚ) : ℝ) = offDiagWeight (castMat A) (castVec w) i := by
  rw [Check.offDiagWeight, cast_sumFin, sumFin_eq_sum, offDiagWeight]
  refine sum_congr rfl fun j _ ↦ ?_
  split_ifs <;> simp

theorem cast_weightedMass (A : Mat ℚ n n) (w : Vec ℚ n) :
    ((Check.weightedMass A w : ℚ) : ℝ) = weightedMass (castMat A) (castVec w) := by
  rw [Check.weightedMass, cast_sumFin, sumFin_eq_sum, weightedMass]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [cast_sumFin, sumFin_eq_sum]
  exact sum_congr rfl fun j _ ↦ by simp

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
  refine ⟨⟨by exact_mod_cast hρ0, by exact_mod_cast hρ1, fun i ↦ ?_, fun i ↦ ?_,
    fun i ↦ ?_⟩, by exact_mod_cast hβ, fun i ↦ ?_, ?_⟩
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

end LeanLearn.Regression
