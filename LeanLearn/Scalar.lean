module

public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Ring
public import Batteries.Data.Rat.Float

/-!
# LeanLearn.Scalar

The scalar-arithmetic interface that LeanSMILES's numeric code — feature
values and the classical ML algorithms that consume them — is written over:
`ScalarLike`, a bundle of raw arithmetic classes — deliberately *not* `Field`,
because `Float` carries no lawful algebraic instances — with `npowGen` /
`nsmulGen` / `sumGen` / `sumFin`, the `Float`-usable power, scalar multiple and
sums, and `npowGen_eq` / `nsmulGen_eq` / `sumGen_eq` / `sumFin_eq_sum` bridging
them to `^`, `*`, `List.sum` and `∑ i, f i` over `ℝ`.

Extracted from LeanCatalyst (`LeanCatalyst/Scalar.lean`, `main` at `65d1e87`).
The code is unchanged apart from the namespace; docstrings that pointed into
LeanCatalyst's own modules are reworded for this library.
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
  [addK : Add K]
  [mulK : Mul K]
  [subK : Sub K]
  [ofNat0K : OfNat K 0]
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
  [negK : Neg K]
  [divK : Div K]
  [ofNat2K : OfNat K 2]
  [ofNat4K : OfNat K 4]
  [ofNat6K : OfNat K 6]
  [ofSciK : OfScientific K]
  [ltK : LT K]
  [leK : LE K]
  [decLtK : DecidableRel (α := K) (· < ·)]
  [decLeK : DecidableRel (α := K) (· ≤ ·)]
  [beqK : BEq K]
  [maxK : Max K]
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
  abs := fun x => |x|
  sqrt := Real.sqrt
  rpow := fun x y => x ^ y
  isFinite := fun _ => true
  ofNat := Nat.cast

@[simp] lemma ScalarLike.abs_real (x : ℝ) : ScalarLike.abs x = |x| := rfl
@[simp] lemma ScalarLike.sqrt_real (x : ℝ) : ScalarLike.sqrt x = Real.sqrt x := rfl
@[simp] lemma ScalarLike.rpow_real (x y : ℝ) : ScalarLike.rpow x y = x ^ y := rfl
@[simp] lemma ScalarLike.isFinite_real (x : ℝ) : ScalarLike.isFinite x = true := rfl
@[simp] lemma ScalarLike.ofNat_real (n : Nat) : ScalarLike.ofNat n = (n : ℝ) := rfl

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

noncomputable instance : RatEmbed Real := ⟨Rat.cast⟩
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
  l.foldr (fun s acc => f s + acc) 0

/-- `∑ i : Fin n, f i`, as the executable fold `sumGen` over `List.finRange n` (usable at
`Float`): an inner product, a squared error, a normal-equation entry. -/
def sumFin [PolynomialLike K] {n : Nat} (f : Fin n → K) : K := sumGen (List.finRange n) f

/-- Sum once over every distinct index in a list, in `List.dedup`'s stable
last-occurrence order.

This is the executable counterpart of a `Finset.sum` when the scalar may be
`Float`: `List.dedup` chooses an order without quotient elimination, while the
`Real` bridge below proves that the order is immaterial in the lawful reading. -/
def sumDistinctGen [PolynomialLike K] [DecidableEq X]
    (l : List X) (f : X → K) : K :=
  sumGen l.dedup f

lemma sumGen_eq {X : Type u} (l : List X) (f : X → Real) :
    sumGen l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [sumGen, List.foldr_cons]; rw [sumGen] at ih; simp [ih]

/-- At `Real`, the executable sum over `Fin n` is the `Finset` sum. -/
theorem sumFin_eq_sum {n : Nat} (f : Fin n → Real) : sumFin f = ∑ i, f i := by
  rw [sumFin, sumGen_eq, Fin.sum_univ_def]

/-- At `Real`, the distinct executable fold is exactly the corresponding
finite-set sum. -/
lemma sumDistinctGen_eq {X : Type u} [DecidableEq X]
    (l : List X) (f : X → Real) :
    sumDistinctGen l f = ∑ x ∈ l.toFinset, f x := by
  rw [sumDistinctGen, sumGen_eq]
  rw [← List.sum_toFinset f (List.nodup_dedup l)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_dedup]

/-- Differencing two sums over one index list is summing their difference —
what lets an observable's error be read as an observable of the error. -/
lemma sumGen_sub {X : Type u} (l : List X) (f g : X → Real) :
    sumGen l f - sumGen l g = sumGen l fun s => f s - g s := by
  induction l with
  | nil => simp [sumGen]
  | cons a l ih =>
    simp only [sumGen, List.foldr_cons] at ih ⊢
    linarith

/-- A sum of nonnegative terms is nonnegative. -/
lemma sumGen_nonneg {X : Type u} {l : List X} {f : X → Real}
    (hf : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ sumGen l f := by
  induction l with
  | nil => exact le_of_eq rfl
  | cons a t ih =>
    have h1 : 0 ≤ f a := hf a (List.mem_cons_self ..)
    have h2 := ih fun x hx => hf x (List.mem_cons_of_mem _ hx)
    rw [sumGen, List.foldr_cons]
    rw [sumGen] at h2
    linarith

/-- One member's term is a lower bound on a sum of nonnegative terms — how a
sum is bounded *below*, and what a quotient's denominator needs. -/
lemma le_sumGen {X : Type u} {l : List X} {f : X → Real} {a : X} (ha : a ∈ l)
    (hf : ∀ x ∈ l, 0 ≤ f x) : f a ≤ sumGen l f := by
  induction l with
  | nil => exact absurd ha List.not_mem_nil
  | cons b t ih =>
    have hrest := sumGen_nonneg (l := t) (f := f)
      fun x hx => hf x (List.mem_cons_of_mem _ hx)
    rw [sumGen] at hrest
    rw [sumGen, List.foldr_cons]
    rcases List.mem_cons.mp ha with h | h
    · subst h
      linarith
    · have hb : 0 ≤ f b := hf b (List.mem_cons_self ..)
      have hle := ih h fun x hx => hf x (List.mem_cons_of_mem _ hx)
      rw [sumGen] at hle
      linarith

theorem npowGen_eq (x : Real) (n : Nat) : npowGen x n = x ^ n := by
  induction n with
  | zero => simp [npowGen]
  | succ n ih => rw [npowGen, ih, pow_succ]; ring

theorem nsmulGen_eq (n : Nat) (x : Real) : nsmulGen n x = (n : Real) * x := by
  induction n with
  | zero => simp [nsmulGen]
  | succ n ih => rw [nsmulGen, ih]; push_cast; ring

end GenArith

end LeanLearn
