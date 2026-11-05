/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Ring
public import Batteries.Data.Rat.Float
public import Batteries.Data.Fin.Fold

/-!
# LeanLearn.Scalar

The scalar-arithmetic interface that LeanSMILES's numeric code — feature
values and the classical ML algorithms that consume them — is written over:
`ScalarLike`, a bundle of raw arithmetic classes — deliberately *not* `Field`,
because `Float` carries no lawful algebraic instances — with `npowGen` /
`nsmulGen` / `sumGen` / `sumFin`, the `Float`-usable power, scalar multiple and
sums, and `npowGen_eq` / `nsmulGen_eq` / `sumGen_eq` / `sumFin_eq_sum` bridging
them to `^`, `*`, `List.sum` and `∑ i, f i` over `ℝ` (the two sums over any additive
monoid, so over `ℚ` as well).

Extracted from LeanCatalyst (`LeanCatalyst/Scalar.lean`, `main` at `65d1e87`).
The definitions are unchanged apart from the namespace; the proofs are golfed, and
docstrings that pointed into LeanCatalyst's own modules are reworded for this library.
-/

@[expose] public section

namespace LeanLearn

/-- **The operations a polynomial needs, and no more**: `+`, `*`, `-`, `0`, `1`.

Much of classical ML is polynomial: a linear model's prediction, a squared
error, an inner product are all sums and products of weights and features.
Keeping that fragment separate allows an exact computable `ℚ` interpretation
alongside the `ℝ` specification and `Float` execution.

A bundle, not a structure: the instance that follows builds it for every type
carrying the five operations, so `PolynomialLike K` abbreviates that
conjunction and carries no law. Its second path, the projection from
`ScalarLike`, is the same term (`ScalarLike.toPolynomialLike_real`,
`ScalarLike.toPolynomialLike_float`). -/
class PolynomialLike (K : Type w) where
  /-- `x + y`. -/
  [addK : Add K]
  /-- `x * y`. -/
  [mulK : Mul K]
  /-- `x - y`. -/
  [subK : Sub K]
  /-- The literal `0`. -/
  [ofNat0K : OfNat K 0]
  /-- The literal `1`. -/
  [ofNat1K : OfNat K 1]

attribute [reducible, instance] PolynomialLike.addK PolynomialLike.mulK
  PolynomialLike.subK PolynomialLike.ofNat0K PolynomialLike.ofNat1K

/-- Every type with the five operations is a `PolynomialLike`. -/
instance (K : Type w) [Add K] [Mul K] [Sub K] [OfNat K 0] [OfNat K 1] :
    PolynomialLike K := ⟨⟩

/-- **Everything numeric code runs on, at one binder.** The polynomial
fragment plus negation and division, the literals algorithms write
(`2`, `4`, `6`, and decimal literals through `OfScientific`), and the
operations an iterative method and a pivoting solve decide with: a decidable order,
`==`, `max`, `min`, `abs`, `sqrt`, a real power, a finiteness test, and the
embedding of a count. Law-free, like `Float`.

Law-free means this is not a structure in Mathlib's sense but an interface for
code generation. Nothing follows from `ScalarLike K` alone beyond what needs no
arithmetic law, so a theorem about an algorithm fixes the scalar in its
binder — `K := ℝ` — and is a theorem about that one instance.

Two readings, deliberately: `Float` is what runs, `ℝ` — classical in its
order, so its instance is noncomputable — is what the theorems are about.
An algorithm written once over this class is the program that runs *and* the
text the theorem describes. `ℚ` and `ℚ≥0` have no square root and no real
power, so they read only the `PolynomialLike` fragment — which is why that
fragment keeps a name of its own. -/
class ScalarLike (K : Type w) extends PolynomialLike K where
  /-- `-x`. -/
  [negK : Neg K]
  /-- `x / y`. -/
  [divK : Div K]
  /-- The literal `2`. -/
  [ofNat2K : OfNat K 2]
  /-- The literal `4`. -/
  [ofNat4K : OfNat K 4]
  /-- The literal `6`. -/
  [ofNat6K : OfNat K 6]
  /-- Decimal literals such as `0.5`. -/
  [ofSciK : OfScientific K]
  /-- `x < y`. -/
  [ltK : LT K]
  /-- `x ≤ y`. -/
  [leK : LE K]
  /-- `<` is decidable, so code can branch on it. -/
  [decLtK : DecidableRel (α := K) (· < ·)]
  /-- `≤` is decidable, so code can branch on it. -/
  [decLeK : DecidableRel (α := K) (· ≤ ·)]
  /-- `x == y`. -/
  [beqK : BEq K]
  /-- `max x y`. -/
  [maxK : Max K]
  /-- `min x y`. -/
  [minK : Min K]
  /-- `|x|`. -/
  abs : K → K
  /-- `√x`. -/
  sqrt : K → K
  /-- `x ^ y` for a scalar exponent. -/
  rpow : K → K → K
  /-- Whether `x` is a finite number: `true` at `ℝ`, IEEE's test at `Float`. -/
  isFinite : K → Bool
  /-- The scalar `n`. -/
  ofNat : Nat → K

-- `reducible` before `instance`: the instance must be registered reducibly so
-- typeclass resolution sees through the bundle to the underlying operations.
-- `toPolynomialLike` needs no entry: `extends` registers it already, and it is
-- what makes the containment structural rather than two lists that agree.
attribute [reducible, instance] ScalarLike.negK ScalarLike.divK
  ScalarLike.ofNat2K ScalarLike.ofNat4K ScalarLike.ofNat6K ScalarLike.ofSciK
  ScalarLike.ltK ScalarLike.leK ScalarLike.decLtK ScalarLike.decLeK ScalarLike.beqK
  ScalarLike.maxK ScalarLike.minK

/-- The `Float` reading: IEEE-754 doubles, every operation the hardware's. -/
instance : ScalarLike Float where
  abs := Float.abs
  sqrt := Float.sqrt
  rpow := Float.pow
  isFinite := Float.isFinite
  ofNat := Float.ofNat

/-- The `ℝ` reading, for the theorems: classical in its order and equality,
`Real.sqrt`, `Real.rpow`, every real finite. -/
noncomputable instance : ScalarLike ℝ where
  abs := fun x ↦ |x|
  sqrt := Real.sqrt
  rpow := fun x y ↦ x ^ y
  isFinite := fun _ ↦ true
  ofNat := Nat.cast

/-- `ScalarLike.abs` on `ℝ` is `|·|`. -/
@[simp] theorem ScalarLike.abs_real (x : ℝ) : ScalarLike.abs x = |x| := rfl

/-- `ScalarLike.sqrt` on `ℝ` is `Real.sqrt`. -/
@[simp] theorem ScalarLike.sqrt_real (x : ℝ) : ScalarLike.sqrt x = Real.sqrt x := rfl

/-- `ScalarLike.rpow` on `ℝ` is the real power `x ^ y`. -/
@[simp] theorem ScalarLike.rpow_real (x y : ℝ) : ScalarLike.rpow x y = x ^ y := rfl

/-- Every real is finite: `ScalarLike.isFinite` on `ℝ` is constantly `true`. -/
@[simp] theorem ScalarLike.isFinite_real (x : ℝ) : ScalarLike.isFinite x = true := rfl

/-- `ScalarLike.ofNat` on `ℝ` is the cast `(n : ℝ)`. -/
@[simp] theorem ScalarLike.ofNat_real (n : Nat) : ScalarLike.ofNat n = (n : ℝ) := rfl

/-- **The two paths to `PolynomialLike ℝ` are one term.** The blanket instance
and the projection from `ScalarLike ℝ` build the same bundle, so a lemma proved
along either path rewrites along the other. -/
theorem ScalarLike.toPolynomialLike_real :
    (inferInstance : ScalarLike ℝ).toPolynomialLike = (⟨⟩ : PolynomialLike ℝ) := rfl

/-- The same at `Float`. -/
theorem ScalarLike.toPolynomialLike_float :
    (inferInstance : ScalarLike Float).toPolynomialLike = (⟨⟩ : PolynomialLike Float) := rfl

/-- **A scalar that exact rational constants embed into.** Not part of
`ScalarLike`, because most algorithms do not need it: it exists so a quantity
given as an exact rational can be defined once and interpreted in both the
executable and the theorem readings.

The two instances are the two coefficient maps, named once so a program can
quantify over them instead of a caller picking one. Law-free, like the classes
above: no theorem relates `Rat.cast` to `Rat.toFloat`, which is the line the
theorems stop at. -/
class RatEmbed (K : Type) where
  /-- A rational constant, as a scalar. -/
  ofRat : ℚ → K

/-- The theorem reading of a rational constant: `Rat.cast`. -/
noncomputable instance : RatEmbed ℝ := ⟨Rat.cast⟩

/-- The executable reading of a rational constant: `Rat.toFloat`. -/
instance : RatEmbed Float := ⟨Rat.toFloat⟩

section GenArith

variable {K : Type w}

/-- Natural-number power by repeated multiplication (usable at `Float`). -/
def npowGen [PolynomialLike K] (x : K) : Nat → K
  | 0 => 1
  | n + 1 => x * npowGen x n

/-- Natural-number scalar multiple by repeated addition (usable at `Float`). -/
def nsmulGen [PolynomialLike K] (n : Nat) (x : K) : K :=
  match n with
  | 0 => 0
  | n + 1 => x + nsmulGen n x

/-- Sum of `f` over a list of indices (usable at `Float`).

`Finset.sum` needs an `AddCommMonoid`, which `Float` is not, so a quantity
summed over an index — an inner product, a squared distance — has no executable
form through `∑`. The index list is an argument rather than derived from a
`Fintype`, since `Fintype.elems` is a `Finset` and unfolding one to fold over
is the same obstruction one level up; callers pass `FinEnum.toList`, which is
the order the index type declares. -/
def sumGen [PolynomialLike K] {X : Type u} (l : List X) (f : X → K) : K :=
  l.foldr (fun s acc ↦ f s + acc) 0

/-- `∑ i : Fin n, f i`, as the executable fold `sumGen` over `List.finRange n` (usable at
`Float`): an inner product, a squared error, a normal-equation entry. -/
def sumFin [PolynomialLike K] {n : Nat} (f : Fin n → K) : K := sumGen (List.finRange n) f

/-- `sumFin` as a counting loop, with no list: the same additions in the same order,
`f 0 + (f 1 + (⋯ + (f (n - 1) + 0)))`. Compiled code runs this in place of `sumFin`
(`sumFin_eq_sumFinLoop` is a `csimp` lemma); the theorems stay about `sumFin`. -/
@[specialize] def sumFinLoop [PolynomialLike K] {n : Nat} (f : Fin n → K) : K :=
  Fin.foldr n (fun i acc ↦ f i + acc) 0

/-- `sumFin` is `sumFinLoop`, so compiled code runs the counting loop in place of the list
fold (`@[csimp]`); proofs keep working with the list-based `sumFin`. -/
@[csimp] theorem sumFin_eq_sumFinLoop : @sumFin = @sumFinLoop := by
  funext K _ n f
  rw [sumFin, sumGen, sumFinLoop, Fin.foldr_eq_foldr_finRange]

/-- Sum once over every distinct index in a list, in `List.dedup`'s stable
last-occurrence order.

This is the executable counterpart of a `Finset.sum` when the scalar may be
`Float`: `List.dedup` chooses an order without quotient elimination, while the
`Real` bridge below proves that the order is immaterial in the lawful reading. -/
def sumDistinctGen {X : Type u} [PolynomialLike K] [DecidableEq X] (l : List X) (f : X → K) : K :=
  sumGen l.dedup f

/-- The executable fold `sumGen` is `List.sum` of the mapped list — the bridge from the
`Float`-usable sums to Mathlib's. Over any additive monoid `K` (`ℝ` for the proofs, `ℚ` for the
certificates); `*`, `-` and `1` are there only for `sumGen` to be defined. -/
theorem sumGen_eq [AddMonoid K] [Mul K] [Sub K] [One K] {X : Type u} (l : List X) (f : X → K) :
    sumGen l f = (l.map f).sum := by
  rw [sumGen, List.sum_eq_foldr, List.foldr_map]

/-- The executable sum over `Fin n` is the `Finset` sum, over any additive commutative monoid `K`
(`ℝ` for the proofs, `ℚ` for the certificates). -/
theorem sumFin_eq_sum [AddCommMonoid K] [Mul K] [Sub K] [One K] {n : Nat} (f : Fin n → K) :
    sumFin f = ∑ i, f i := by
  rw [sumFin, sumGen_eq, Fin.sum_univ_def]

/-- At `Real`, the distinct executable fold is exactly the corresponding
finite-set sum. -/
theorem sumDistinctGen_eq {X : Type u} [DecidableEq X] (l : List X) (f : X → ℝ) :
    sumDistinctGen l f = ∑ x ∈ l.toFinset, f x := by
  rw [sumDistinctGen, sumGen_eq, ← List.sum_toFinset f (List.nodup_dedup l),
    List.toFinset.ext_iff.mpr fun _ ↦ List.mem_dedup]

/-- Differencing two sums over one index list is summing their difference —
what lets an observable's error be read as an observable of the error. -/
theorem sumGen_sub {X : Type u} (l : List X) (f g : X → ℝ) :
    sumGen l f - sumGen l g = sumGen l fun s ↦ f s - g s := by
  induction l <;> grind [sumGen]

/-- A sum of nonnegative terms is nonnegative. -/
theorem sumGen_nonneg {X : Type u} {l : List X} {f : X → ℝ} (hf : ∀ x ∈ l, 0 ≤ f x) :
    0 ≤ sumGen l f := by
  rw [sumGen_eq]
  exact List.sum_nonneg (List.forall_mem_map.mpr hf)

/-- One member's term is a lower bound on a sum of nonnegative terms — how a
sum is bounded *below*, and what a quotient's denominator needs. -/
theorem le_sumGen {X : Type u} {l : List X} {f : X → ℝ} {a : X} (ha : a ∈ l)
    (hf : ∀ x ∈ l, 0 ≤ f x) : f a ≤ sumGen l f := by
  rw [sumGen_eq]
  exact List.single_le_sum (List.forall_mem_map.mpr hf) _ (List.mem_map_of_mem ha)

/-- On `ℝ`, the repeated-multiplication power `npowGen` is the monoid power `x ^ n`. -/
theorem npowGen_eq (x : ℝ) (n : Nat) : npowGen x n = x ^ n := by
  induction n <;> simp [npowGen, pow_succ', *]

/-- On `ℝ`, the repeated-addition multiple `nsmulGen n x` is `n * x` with `n` cast. -/
theorem nsmulGen_eq (n : Nat) (x : ℝ) : nsmulGen n x = (n : ℝ) * x := by
  induction n <;> simp [nsmulGen, add_mul, add_comm, *]

end GenArith

end LeanLearn
