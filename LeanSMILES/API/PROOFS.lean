module

public import LeanSMILES.API.Metrics
public import LeanSMILES.API.Split
public import LeanSMILES.Machine_Learning.PROOFS
public import Mathlib.Algebra.Order.Field.Basic

/-!
# API — Proofs

Theorems over `ℝ` about the pipeline functions that run on `Float`: the regression
metrics and split sizes. (Exact decimal conversion is `Decimal.toScalar_eq_toReal` in
`Primitives/real.lean`.)
-/

public section

namespace API

open Primitives ML

/-! ## Metrics -/

section Metrics

variable {m : Nat}

theorem meanSquaredError_self (y : Vec ℝ m) : meanSquaredError y y = 0 := by
  simp [meanSquaredError, sumFin_eq_sum]

theorem meanSquaredError_nonneg (yTrue yPred : Vec ℝ m) :
    0 ≤ meanSquaredError yTrue yPred := by
  unfold meanSquaredError
  rw [sumFin_eq_sum]
  exact div_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg _) (Nat.cast_nonneg m)

theorem meanAbsoluteError_nonneg (yTrue yPred : Vec ℝ m) :
    0 ≤ meanAbsoluteError yTrue yPred := by
  unfold meanAbsoluteError
  rw [sumFin_eq_sum]
  exact div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (Nat.cast_nonneg m)

/-- Perfect predictions score `R² = 1`. -/
theorem r2Score_self (y : Vec ℝ m) : r2Score y y = 1 := by
  simp only [r2Score, sumFin_eq_sum, sub_self, mul_zero, Finset.sum_const_zero]
  split_ifs <;> simp_all

/-- `R² ≤ 1`: no model explains more than all of the variance. -/
theorem r2Score_le_one (yTrue yPred : Vec ℝ m) : r2Score yTrue yPred ≤ 1 := by
  unfold r2Score
  simp only [sumFin_eq_sum]
  split_ifs with h₁ h₂
  · exact le_rfl
  · exact zero_le_one
  · have hres : 0 ≤ ∑ i : Fin m, (yTrue[i] - yPred[i]) * (yTrue[i] - yPred[i]) :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have htot : 0 < ∑ i : Fin m, (yTrue[i] - vsum yTrue / Scalar.fromNat m) *
        (yTrue[i] - vsum yTrue / Scalar.fromNat m) := lt_of_not_ge h₁
    linarith [div_nonneg hres htot.le]

end Metrics

/-! ## Splits -/

/-- The training and test sets together have all `m` samples. -/
theorem split_sizes (t : TestSize) (m : Nat) : (m - t.testCount m) + t.testCount m = m :=
  Nat.sub_add_cancel (t.testCount_le m)

end API

end
