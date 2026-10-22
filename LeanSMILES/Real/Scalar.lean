module

public import LeanSMILES.Polymorphic.Decimal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring

/-!
# The real-number instance

The noncomputable instance of `Scalar`. The theorems in `Proofs/` are stated about the
definitions in `Polymorphic/` at `α := ℝ`; the same definitions run on `Float`
(`Float/Scalar.lean`). Only `Proofs/` imports this file, so the executable code stays free
of Mathlib.
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

/-! ## The real value of a decimal -/

/-- The real number a decimal denotes. -/
noncomputable def Decimal.toReal (d : Decimal) : ℝ :=
  d.mantissa * (10 : ℝ) ^ d.exponent

end Primitives

end
