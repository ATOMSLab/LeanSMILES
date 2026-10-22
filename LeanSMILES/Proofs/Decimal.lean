/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/

module

public import LeanSMILES.Real.Scalar
public import Mathlib.Tactic.Ring

/-!
# Decimals are exact over `ℝ`
-/

public section

namespace Primitives

theorem Decimal.toScalar_eq_toReal (d : Decimal) :
    d.toScalar (α := ℝ) = d.toReal := by
  obtain ⟨mant, e⟩ := d
  have habs : ((mant.natAbs : ℕ) : ℝ) = |(mant : ℝ)| := by simp [Nat.cast_natAbs]
  unfold Decimal.toScalar Decimal.toReal
  change (if mant < 0 then -_ else _) = _
  by_cases he : 0 ≤ e
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
    simp only [he, if_true, Int.toNat_natCast, zpow_natCast]
    change (if mant < 0 then -(((mant.natAbs * 10 ^ k : ℕ) : ℝ))
      else ((mant.natAbs * 10 ^ k : ℕ) : ℝ)) = _
    push_cast [habs]
    split_ifs with hm
    · rw [abs_of_neg (by exact_mod_cast hm)]; ring
    · rw [abs_of_nonneg (by exact_mod_cast not_lt.mp hm)]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, e = -((k : ℤ)) := ⟨(-e).toNat, by omega⟩
    subst hk
    simp only [neg_neg, Int.toNat_natCast, zpow_neg, zpow_natCast]
    simp only [show ¬ (0 ≤ -(k : ℤ)) from by omega, if_false]
    change (if mant < 0 then -(((mant.natAbs : ℕ) : ℝ) / ((10 ^ k : ℕ) : ℝ))
      else ((mant.natAbs : ℕ) : ℝ) / ((10 ^ k : ℕ) : ℝ)) = _
    push_cast [habs]
    split_ifs with hm
    · rw [abs_of_neg (by exact_mod_cast hm)]; ring
    · rw [abs_of_nonneg (by exact_mod_cast not_lt.mp hm)]; ring

end Primitives

end
