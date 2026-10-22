/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Proofs.LeastSquares.RidgeOLS
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Kernel-checked ridge examples over exact real numbers -/

public section
namespace LeanLearn.Regression.Ridge.Examples
open Matrix
open scoped Matrix
noncomputable section

def lineX : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]
def lineY : Fin 3 → ℝ := ![1, 3, 5]

/-- An explicit intercept is exempt from the slope penalty of 2. -/
theorem exempt_normalEquations : NormalEquations lineX lineY ![0, 2] ![2, 1] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, lineX, lineY, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, diagonal]

theorem exempt_minimizes : IsMinimizer lineX lineY ![0, 2] ![2, 1] := by
  apply normalEquations_minimize lineX lineY _ exempt_normalEquations
  intro j
  fin_cases j <;> norm_num

theorem exempt_loss : loss lineX lineY ![0, 2] ![2, 1] = 4 := by
  norm_num [loss_eq_sum, OLS.predict, lineX, lineY, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- A lower bound on the objective for every real intercept and slope. -/
theorem exempt_lower_bound (w : Fin 2 → ℝ) : 4 ≤ loss lineX lineY ![0, 2] w := by
  have h := exempt_minimizes w
  rwa [exempt_loss] at h

def duplicateX : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]
def duplicateY : Fin 2 → ℝ := ![1, 3]

/-- Ridge identifies both coefficients even when feature columns are identical. -/
theorem duplicate_normalEquations :
    NormalEquations duplicateX duplicateY (fun _ ↦ 1) ![4/5, 4/5] := by
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, duplicateX, duplicateY, Matrix.mulVec,
    Matrix.mul_apply, dotProduct, Fin.sum_univ_succ, diagonal]

theorem duplicate_fit : fitPositive duplicateX duplicateY (fun _ ↦ 1) (by intro j; norm_num) =
    ![4/5, 4/5] := by
  symm
  apply fitPositive_unique
  apply normalEquations_minimize duplicateX duplicateY (by intro j; norm_num)
  exact duplicate_normalEquations

/-- One observation and two coefficients: positive ridge still has a unique solution. -/
theorem underdetermined_minimizes :
    IsMinimizer (!![1, 2] : Matrix (Fin 1) (Fin 2) ℝ) ![3] (fun _ ↦ 1) ![1/2, 1] := by
  apply normalEquations_minimize _ _ (by intro j; norm_num)
  unfold NormalEquations
  ext j
  fin_cases j <;> norm_num [gram, OLS.gram, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_succ, diagonal]

/-! ## Ridge against OLS on the same data -/

/-- Without a penalty, the line `y = 1 + 2x` fits `lineX`, `lineY` exactly. -/
theorem ols_normalEquations : OLS.NormalEquations lineX lineY ![1, 2] := by
  rw [OLS.normalEquations_iff]
  ext j
  fin_cases j <;> norm_num [OLS.gram, lineX, lineY, Matrix.mulVec, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_succ]

/-- The trade-off, by theorem rather than by computation: the exempt-intercept ridge fit
`![2, 1]` has a smaller penalized norm than the OLS fit `![1, 2]` ... -/
theorem exempt_penalty_le : penalty ![0, 2] ![2, 1] ≤ penalty ![0, 2] ![1, 2] :=
  penalty_le_of_isMinimizer lineX lineY
    (OLS.normalEquations_minimize lineX lineY ols_normalEquations) exempt_minimizes

/-- ... namely `2 ≤ 8`, having given up squared error `0 ≤ 2` for it. -/
theorem exempt_tradeoff :
    penalty ![0, 2] ![2, 1] = 2 ∧ penalty ![0, 2] ![1, 2] = 8 ∧
      OLS.loss lineX lineY ![1, 2] = 0 ∧ OLS.loss lineX lineY ![2, 1] = 2 := by
  norm_num [penalty, OLS.loss_eq_sum, OLS.predict, lineX, lineY, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]

/-- Orthonormal columns. -/
def orthoX : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]

theorem orthoX_gram : OLS.gram orthoX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [OLS.gram, orthoX, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem orthoX_transpose : orthoXᵀ = !![1, 0, 0; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- With orthonormal columns, unit ridge halves the OLS coefficients `Xᵀy = ![2, 4]`. -/
theorem ortho_halves :
    fitPositive orthoX ![2, 4, 6] (fun _ ↦ 1) (fun _ ↦ one_pos) = ![1, 2] := by
  rw [fitPositive_eq_smul_of_gram_eq_one orthoX _ orthoX_gram one_pos, orthoX_transpose]
  ext j
  fin_cases j <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end
end LeanLearn.Regression.Ridge.Examples
