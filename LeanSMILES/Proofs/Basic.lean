/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/

module

public import LeanSMILES.Real.Scalar
public import LeanSMILES.Polymorphic.LinAlg
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Basic bridges to Mathlib

The executable definitions use folds and their own `iterate`, because `Float` has no
Mathlib algebra. Over `ℝ` these are Mathlib's sums and `Nat.iterate`, which is how every
other proof file reaches Mathlib's lemmas.
-/

public section

namespace Primitives

/-! ## Iteration -/

theorem iterate_succ' {β : Type} (f : β → β) (n : Nat) (x : β) :
    iterate f (n + 1) x = f (iterate f n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-- `Primitives.iterate` is Mathlib's `Nat.iterate`, so Mathlib's lemmas about `f^[n]`
apply. -/
theorem iterate_eq_iterate {β : Type} (f : β → β) (n : Nat) : iterate f n = f^[n] := by
  funext x
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih (f x)

/-! ## Sums -/

@[simp] theorem fromNat_real (k : ℕ) : (Scalar.fromNat k : ℝ) = k := rfl

/-- A left fold that adds `f 0, …, f (n-1)` is `∑ i, f i`, in any commutative monoid. -/
theorem foldl_add_eq_sum {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin n → M) (a : M) :
    Fin.foldl n (fun acc i => acc + f i) a = a + ∑ i, f i := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc, ih (fun i => f i.castSucc), add_assoc]

/-- The computable fold `sumFin` is Mathlib's `Finset.sum` over `ℝ`. -/
theorem sumFin_eq_sum {n : ℕ} (f : Fin n → ℝ) : sumFin f = ∑ i, f i := by
  rw [sumFin, foldl_add_eq_sum, zero_add]

theorem dot_eq_sum {n : ℕ} (u v : Vec ℝ n) : dot u v = ∑ i : Fin n, u[i] * v[i] :=
  sumFin_eq_sum _

theorem vsum_eq_sum {n : ℕ} (v : Vec ℝ n) : vsum v = ∑ i : Fin n, v[i] :=
  sumFin_eq_sum _

/-- Peel off the last term of a `sumFin` (holds for every `Scalar`). -/
theorem sumFin_succ {α : Type} [Scalar α] {n : ℕ} (f : Fin (n + 1) → α) :
    sumFin f = sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n) := by
  unfold sumFin
  rw [Fin.foldl_succ_last]

theorem foldl_add_eq_add_sum (l : List ℝ) (a : ℝ) : l.foldl (· + ·) a = a + l.sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.sum_cons, add_assoc]

/-- The computable fold `listSum` is `List.sum` over `ℝ`. -/
theorem listSum_eq_sum (l : List ℝ) : listSum l = l.sum := by
  rw [listSum, foldl_add_eq_add_sum, zero_add]

theorem list_sum_map_sub {β : Type} (l : List β) (f g : β → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun b => f b - g b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

/-- Exchange a finite sum and a sum over a list. -/
theorem sum_list_map_sum {ι β : Type} [Fintype ι] (l : List β) (g : ι → β → ℝ) :
    ∑ i, (l.map (g i)).sum = (l.map fun b => ∑ i, g i b).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

end Primitives

end
