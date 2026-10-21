module

public import LeanSMILES.Primitives.scalar
public import LeanSMILES.Primitives.decimal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring

/-!
# The real-number instance

The `Scalar ℝ` instance, which states and proves theorems about the same generic
definitions that run on `Float`. Only the proof files import it, so the executable code
stays free of Mathlib. It also proves that `Decimal.toScalar` is exact over `ℝ`.
-/

@[expose] public section

namespace Primitives

/-- Proof-side instance. The arithmetic fields reuse Mathlib's instances, so lemmas about
`ℝ` apply directly. -/
noncomputable instance : Scalar ℝ where
  toZero := inferInstance
  toOne := inferInstance
  toAdd := inferInstance
  toSub := inferInstance
  toMul := inferInstance
  toDiv := inferInstance
  toNeg := inferInstance
  toLT := inferInstance
  toLE := inferInstance
  fromNat n := (n : ℝ)
  sqrt := Real.sqrt
  exp := Real.exp
  log := Real.log
  abs x := |x|
  sin := Real.sin
  cos := Real.cos
  pi := Real.pi
  decLt := inferInstance
  decLe := inferInstance

/-! ## Decimals are exact over `ℝ` -/

/-- The real number a decimal denotes. -/
noncomputable def Decimal.toReal (d : Decimal) : ℝ :=
  d.mantissa * (10 : ℝ) ^ d.exponent

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
