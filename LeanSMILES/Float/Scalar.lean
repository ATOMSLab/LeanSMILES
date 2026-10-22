module

public import LeanSMILES.Polymorphic.Decimal

/-!
# The `Float` instance

The computable instance of `Scalar`. Every definition in `Polymorphic/` runs on `Float`
through it; the theorems in `Proofs/` are about the same definitions at `α := ℝ`, so they
describe this code up to rounding.
-/

@[expose] public section

namespace Primitives

/-- Execution-side instance. -/
instance : Scalar Float where
  zero := 0
  one := 1
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := (- ·)
  lt := (· < ·)
  le := (· ≤ ·)
  fromNat n := n.toFloat
  sqrt := Float.sqrt
  exp := Float.exp
  log := Float.log
  abs := Float.abs
  sin := Float.sin
  cos := Float.cos
  pi := 3.141592653589793
  decLt := fun a b => Float.decLt a b
  decLe := fun a b => Float.decLe a b

/-- The nearest `Float` (a single rounding, via `Float.ofScientific`). -/
def Decimal.toFloat (d : Decimal) : Float :=
  let mag :=
    if 0 ≤ d.exponent then Float.ofScientific d.mantissa.natAbs false d.exponent.toNat
    else Float.ofScientific d.mantissa.natAbs true (-d.exponent).toNat
  if d.mantissa < 0 then -mag else mag

end Primitives

end
