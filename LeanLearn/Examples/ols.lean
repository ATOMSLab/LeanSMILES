/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanLearn.Regression.OLS
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Small, exact examples of the OLS theorems

These examples are checked proofs over `ℝ`, not numerical training experiments.
The first column of each design matrix is the intercept column.
-/

public section

namespace LeanLearn.Regression.OLS.Examples

open Matrix
open scoped Matrix BigOperators

noncomputable section

/-- Three inputs `x = 0, 1, 2`, augmented by an intercept column of ones. -/
def lineDesign : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 1, 1; 1, 2]

/-- Targets lying exactly on `y = 1 + 2x`. -/
def lineTargets : Fin 3 → ℝ := ![1, 3, 5]

/-- Intercept first, then slope. -/
def lineCoefficients : Fin 2 → ℝ := ![1, 2]

/-- The Gram determinant is nonzero, so the closed-form algorithm is applicable. -/
theorem line_nonsingular : (gram lineDesign).det ≠ 0 := by
  norm_num [gram, lineDesign, det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The proposed exact line satisfies the normal equations. -/
theorem line_normalEquations : NormalEquations lineDesign lineTargets lineCoefficients := by
  rw [normalEquations_iff]
  ext j
  fin_cases j <;>
    norm_num [gram, lineDesign, lineTargets, lineCoefficients, Matrix.mulVec,
      Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

/-- The formula returns intercept `1` and slope `2`. -/
theorem line_fit : fit lineDesign lineTargets line_nonsingular = lineCoefficients := by
  exact (fit_unique lineDesign lineTargets line_nonsingular
    (normalEquations_minimize lineDesign lineTargets line_normalEquations)).symm

/-- This line fits every observation exactly. -/
theorem line_loss_zero : loss lineDesign lineTargets lineCoefficients = 0 := by
  norm_num [loss_eq_sum, predict, lineDesign, lineTargets, lineCoefficients,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- Noisy targets that do not lie on one line. -/
def noisyTargets : Fin 3 → ℝ := ![1, 2, 4]

/-- The best-fit line has intercept `5/6` and slope `3/2`. -/
def noisyCoefficients : Fin 2 → ℝ := ![5 / 6, 3 / 2]

/-- Even though the residual is nonzero, it is orthogonal to the feature columns. -/
theorem noisy_normalEquations : NormalEquations lineDesign noisyTargets noisyCoefficients := by
  rw [normalEquations_iff]
  ext j
  fin_cases j <;>
    norm_num [gram, lineDesign, noisyTargets, noisyCoefficients, Matrix.mulVec,
      Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

/-- Every intercept/slope pair has squared error at least `1/6` on the noisy data. -/
theorem noisy_loss_lower_bound (w : Fin 2 → ℝ) : 1 / 6 ≤ loss lineDesign noisyTargets w := by
  have h := normalEquations_minimize lineDesign noisyTargets noisy_normalEquations w
  have hloss : loss lineDesign noisyTargets noisyCoefficients = 1 / 6 := by
    norm_num [loss_eq_sum, predict, lineDesign, noisyTargets, noisyCoefficients,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rwa [hloss] at h

/-- The closed-form algorithm returns the proved best-fit coefficients on noisy data. -/
theorem noisy_fit : fit lineDesign noisyTargets line_nonsingular = noisyCoefficients := by
  exact (fit_unique lineDesign noisyTargets line_nonsingular
    (normalEquations_minimize lineDesign noisyTargets noisy_normalEquations)).symm

/-- Two identical feature columns: coefficients cannot be uniquely identified. -/
def singularDesign : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- The repeated inputs have two different observed targets. -/
def singularTargets : Fin 2 → ℝ := ![1, 3]

/-- The nonsingularity hypothesis required by `fit` genuinely fails in this example. -/
theorem singular_gram_det : (gram singularDesign).det = 0 := by
  norm_num [gram, singularDesign, det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ]

/-- A singular design can have different coefficient vectors that both minimize loss. -/
theorem singular_two_minimizers :
    IsMinimizer singularDesign singularTargets ![2, 0] ∧
    IsMinimizer singularDesign singularTargets ![0, 2] ∧
    (![2, 0] : Fin 2 → ℝ) ≠ ![0, 2] := by
  constructor
  · apply normalEquations_minimize
    rw [normalEquations_iff]
    ext j
    fin_cases j <;>
      norm_num [gram, singularDesign, singularTargets, Matrix.mulVec,
        Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  constructor
  · apply normalEquations_minimize
    rw [normalEquations_iff]
    ext j
    fin_cases j <;>
      norm_num [gram, singularDesign, singularTargets, Matrix.mulVec,
        Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]
  · intro h
    have hzero := congrFun h 0
    norm_num at hzero

end

end LeanLearn.Regression.OLS.Examples
