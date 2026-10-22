module

/-!
# The scalar interface

Every numeric definition in `Polymorphic/` is written once against `[Scalar α]`, and has
two instances:

* `Float` (`Float/Scalar.lean`) — computable, used to run the definitions;
* `ℝ` (`Real/Scalar.lean`) — noncomputable, used to prove theorems about them
  (`Proofs/`).

Nothing in `Polymorphic/` or `Float/` imports Mathlib, so both are precompiled to native
code.
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

namespace Scalar

variable {α : Type} [Scalar α]

def max (a b : α) : α := if a < b then b else a
def min (a b : α) : α := if a < b then a else b

/-- `x` clamped to the interval `[-c, c]`. -/
def clamp (c x : α) : α := max (-c) (min c x)

end Scalar

/-- `iterate f n x = f (f (… (f x)))` with `n` applications. The same definition as
Mathlib's `Nat.iterate`; `iterate_eq_iterate` in `Proofs/Basic.lean` proves
`iterate f n = f^[n]`. -/
def iterate {β : Type} (f : β → β) : Nat → β → β
  | 0, x => x
  | n + 1, x => iterate f n (f x)

end Primitives

end
