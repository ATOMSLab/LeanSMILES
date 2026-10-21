module

/-!
# Scalar primitives

The `Scalar` interface that numeric code is written against, and the computable `Float`
instance used for execution. The noncomputable `ℝ` instance used for proofs is in
`Primitives/Real.lean`. This file and everything executable that builds on it import no
Mathlib, so they can be precompiled into native code that `#eval` calls directly.
-/

@[expose] public section

namespace Primitives

/-- The operations every algorithm may use. Anything not listed here (e.g. `Finset.sum`,
field lemmas) is only available on the proof side, over `ℝ`. -/
class Scalar (α : Type) extends Zero α, One α, Add α, Sub α, Mul α, Div α, Neg α,
    LT α, LE α where
  /-- Cast a natural number (counts, sample sizes, literals like `2`). -/
  fromNat : Nat → α
  sqrt : α → α
  exp : α → α
  log : α → α
  abs : α → α
  sin : α → α
  cos : α → α
  pi : α
  decLt : DecidableRel (α := α) (· < ·)
  decLe : DecidableRel (α := α) (· ≤ ·)

instance {α : Type} [Scalar α] : DecidableRel (α := α) (· < ·) := Scalar.decLt
instance {α : Type} [Scalar α] : DecidableRel (α := α) (· ≤ ·) := Scalar.decLe

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

namespace Scalar

variable {α : Type} [Scalar α]

def max (a b : α) : α := if a < b then b else a
def min (a b : α) : α := if a < b then a else b

end Scalar

/-- `iterate f n x = f (f (… (f x)))` with `n` applications. The same definition as
Mathlib's `Nat.iterate`; `iterate_eq_iterate` in `MachineLearning/Proofs.lean` proves
`iterate f n = f^[n]`. -/
def iterate {β : Type} (f : β → β) : Nat → β → β
  | 0, x => x
  | n + 1, x => iterate f n (f x)

end Primitives

end
