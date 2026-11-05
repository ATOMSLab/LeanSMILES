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

/-- `RatEmbed.ofRat` at `ℝ` is `Rat.cast`: the `simp` normal form of an exact rational constant
read in `ℝ` (the executable reading `Rat.toFloat` has no such lemma). -/
@[simp] theorem ratEmbed_real (q : ℚ) : (RatEmbed.ofRat q : ℝ) = q := rfl

/-- The cast to `ℝ` of an exact `sumGen` is the `sumGen` of the casts: `Rat.cast` through the
executable fold, over any index list. -/
theorem cast_sumGen {X : Type} (l : List X) (g : X → ℚ) :
    ((sumGen l g : ℚ) : ℝ) = sumGen l fun x ↦ (g x : ℝ) := by
  induction l <;> simp_all [sumGen]

/-- The cast to `ℝ` of an exact `sumFin` is the `sumFin` of the casts; with `sumFin_eq_sum` it
reads every exact sum of a check as a `Finset` sum in `ℝ`. -/
theorem cast_sumFin {n : ℕ} (g : Fin n → ℚ) : ((sumFin g : ℚ) : ℝ) = sumFin fun i ↦ (g i : ℝ) :=
  cast_sumGen _ _

/-- The cast to `ℝ` of the exact count `k` is the count in `ℝ` (which is `k`, by
`count_eq_natCast`): `Rat.cast` through `nsmulGen`, for the `1/m` of the normal equations. -/
theorem cast_count (k : ℕ) : ((count k : ℚ) : ℝ) = count k := by
  induction k <;> simp_all [count, nsmulGen]

/-- The cast to `ℝ` of the executable power `npowGen x k` is `(x : ℝ) ^ k`: how the `ρ²ᵏ` of
`SolverWitness.excess` is read in `ℝ`. -/
theorem cast_npowGen (x : ℚ) (k : ℕ) : ((npowGen x k : ℚ) : ℝ) = (x : ℝ) ^ k := by
  induction k <;> simp_all [npowGen, pow_succ']

/-- A rational matrix, read in `ℝ`. -/
abbrev castMat {m n : ℕ} (A : Mat ℚ m n) : Mat ℝ m n := A.map (·.map fun q : ℚ ↦ (q : ℝ))

/-- A rational vector, read in `ℝ`. -/
abbrev castVec {n : ℕ} (v : Vec ℚ n) : Vec ℝ n := v.map fun q : ℚ ↦ (q : ℝ)

namespace Problem

variable {m d : ℕ} (P : Problem ℚ m d)

/-- Reading the data in `ℝ` and forming the design matrix gives the cast of the exact design
matrix, entrywise: the base case of `map_normalMatrix` and `map_normalVector`. -/
theorem map_design_getElem (r : Fin m) (i : Fin (d + 1)) :
    (P.map fun q : ℚ ↦ (q : ℝ)).design[r][i] = ((P.design[r][i] : ℚ) : ℝ) := by
  simp [design, row, augment, Problem.map, Vector.getElem_push, apply_dite (fun q : ℚ ↦ (q : ℝ))]

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

/-- Reading the data in `ℝ` and forming the residual at the cast of `θ` gives the cast of
the exact residual. -/
theorem map_residualAt (θ : Vec ℚ (d + 1)) (i : Fin (d + 1)) :
    (residual (P.map fun q : ℚ ↦ (q : ℝ)).normalMatrix (P.map fun q : ℚ ↦ (q : ℝ)).normalVector
      (castVec θ))[i] = ((P.residualAt θ)[i] : ℚ) := by
  simp only [residualAt, residual, vsub, matVec, dot, Fin.getElem_fin, Vector.getElem_ofFn]
  push_cast [cast_sumFin]
  simp only [← Fin.getElem_fin, map_normalMatrix, map_normalVector]
  simp [castVec]

/-- **Soundness of `Problem.checkResidual`**: if the exact check passes, the cast of `θ` is
within `ε` of the loss of every `u`, read in `ℝ` — whatever solver produced `θ`. -/
theorem checkResidual_sound {θ : Vec ℚ (d + 1)} {ε : ℚ} (h : P.checkResidual θ ε = true)
    (u : Vec ℝ (d + 1)) :
    (P.map fun q : ℚ ↦ (q : ℝ)).loss (castVec θ) ≤ (P.map fun q : ℚ ↦ (q : ℝ)).loss u + ε := by
  simp only [checkResidual, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hridgePos, hres⟩ := h
  have hridgeReal : (0 : ℝ) < (P.map fun q : ℚ ↦ (q : ℝ)).ridge := Rat.cast_pos.mpr hridgePos
  refine ((P.map fun q : ℚ ↦ (q : ℝ)).loss_le_add_residual hridgeReal (castVec θ) u).trans ?_
  -- the squared residual norm in `ℝ` is the cast of the exact `⟪r, r⟫` the check compares
  have hcast : ∑ i : Fin (d + 1), (residual (P.map fun q : ℚ ↦ (q : ℝ)).normalMatrix
      (P.map fun q : ℚ ↦ (q : ℝ)).normalVector (castVec θ))[i] ^ 2 =
      ((dot (P.residualAt θ) (P.residualAt θ) : ℚ) : ℝ) := by
    rw [dot, cast_sumFin, sumFin_eq_sum]
    exact sum_congr rfl fun i _ ↦ by rw [map_residualAt, sq, Rat.cast_mul]
  rw [hcast, add_le_add_iff_left, div_le_iff₀ hridgeReal]
  change _ ≤ (ε : ℝ) * (P.ridge : ℝ)
  exact_mod_cast hres

end Problem

/-! ## Jacobi and Gauss–Seidel -/

namespace SolverWitness

variable {n : ℕ}

/-- The exact row weight `Check.offDiagWeight` casts to the `offDiagWeight` of the cast data: the
row condition of `SolverWitness.check` is the `dominant` field of `DiagDominant`, in `ℝ`. -/
theorem cast_offDiagWeight (A : Mat ℚ n n) (w : Vec ℚ n) (i : Fin n) :
    ((Check.offDiagWeight A w i : ℚ) : ℝ) = offDiagWeight (castMat A) (castVec w) i := by
  simp [Check.offDiagWeight, offDiagWeight, sumFin_eq_sum, apply_ite (fun q : ℚ ↦ (q : ℝ))]

/-- The exact `Check.weightedMass` casts to the `weightedMass` of the cast data: the `Γ` of
`SolverWitness.excess` is the `Γ` of `loss_jacobi_le` and `loss_gaussSeidel_le`, in `ℝ`. -/
theorem cast_weightedMass (A : Mat ℚ n n) (w : Vec ℚ n) :
    ((Check.weightedMass A w : ℚ) : ℝ) = weightedMass (castMat A) (castVec w) := by
  simp [Check.weightedMass, weightedMass, sumFin_eq_sum]

/-- **Soundness of `SolverWitness.check`**: a pass gives, in `ℝ`, weighted diagonal dominance, the
bound on `b` and the excess below `ε` — what `loss_jacobi_le` and `loss_gaussSeidel_le` need. -/
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
  refine ⟨⟨mod_cast hρ0, mod_cast hρ1, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩, mod_cast hβ,
    fun i ↦ ?_, ?_⟩
  · simpa using (hrows i).1.1.1
  · simpa using (hrows i).1.1.2
  · simpa [← cast_offDiagWeight] using (Rat.cast_le (K := ℝ)).mpr (hrows i).1.2
  · simpa using (Rat.cast_le (K := ℝ)).mpr (hrows i).2
  · rw [← cast_weightedMass, ← cast_npowGen W.ratio (2 * k)]
    exact_mod_cast hexc

end SolverWitness

end LeanLearn.Regression
