/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import LeanSMILES.Fingerprint.Morgan

/-!
# LeanSMILES.Fingerprint.Tanimoto

**Is Tanimoto a metric?** The title question of Surendran, Zsigmond, López-Pérez &
Miranda-Quintana (2025) has two answers, and this file proves both.

* **On binary fingerprints, yes.** A fingerprint is its set of on-bits `A : Finset α`.
  The Tanimoto similarity `|A ∩ B| / |A ∪ B|` (`Finset.tanimoto`) is the Jaccard index,
  and the Tanimoto distance `|A ∆ B| / |A ∪ B|` (`Finset.tanimotoDist`) is a metric:
  `Finset.tanimotoMetricSpace`. This is the theorem of Marczewski & Steinhaus (1958),
  reproved for chemists by Lipkus (1999). The triangle inequality is derived from the
  Hamming distance `|A ∆ B|` through the Steinhaus transform
  `δ(A,B) ↦ 2δ(A,B) / (δ(A,∅) + δ(B,∅) + δ(A,B))`, which is `|A ∆ B| / |A ∪ B|` because
  `2|A ∪ B| = |A| + |B| + |A ∆ B|`; the only inequality it needs is `steinhaus_triangle`.
* **On real-valued vectors, no.** The same formula written with inner products,
  `⟨x,y⟩ / (⟨x,x⟩ + ⟨y,y⟩ − ⟨x,y⟩)` (`tanimotoVec`, Eq. 2 of the paper), agrees with
  `Finset.tanimoto` on 0/1 vectors (`tanimotoVec_indicator`), but `1 - tanimotoVec` violates
  the triangle inequality already for three scalars in `[0, 1]`
  (`not_tanimotoVec_dist_triangle`: `1/3`, `2/3`, `1`), so no metric space on `Fin 1 → ℝ`
  has it as its distance (`not_exists_metricSpace_tanimotoVec`). Lipkus's proof is binary-only,
  as the paper says.

So "Tanimoto is a metric" exactly as far as the fingerprints are binary, and even then one
convention matters: `1 - T` is only a distance if `T(∅, ∅) = 1`, whereas `LeanSMILES.tanimoto`
(like RDKit) returns `0` for two empty fingerprints (`one_sub_tanimoto_empty_empty`).
`Finset.tanimotoDist` is `0/0 = 0` at `(∅, ∅)` and equals `1 - Finset.tanimoto` whenever either
fingerprint has a bit (`tanimotoDist_eq_one_sub`).

The last section connects the theorem to the code: `LeanSMILES.tanimoto` on lists of on-bits,
as `Molecule.morganBits` produces them, computes `Finset.tanimoto` of the corresponding sets
(`tanimoto_eq_toFinset`, `Molecule.tanimoto_morganBits`).

The paper proposes `√(1 - T)` as the metric to use with real-valued vectors; that claim is
not formalized here.
-/

@[expose] public section

open scoped Finset symmDiff

namespace LeanSMILES

/-- The inequality behind the Steinhaus transform of a metric. If `δ` satisfies the triangle
inequality on four points `p, u, v, w` — writing `a = δ(u,p)`, `b = δ(v,p)`, `c = δ(w,p)`,
`x = δ(u,v)`, `y = δ(v,w)`, `z = δ(u,w)` — then `δ'(u,w) = z / (a + c + z)` satisfies it too.
Only three of the triangle inequalities are needed. Division by zero is `0`, so the degenerate
cases need no hypotheses. -/
theorem steinhaus_triangle {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {a b c x y z : K} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hxyz : z ≤ x + y) (hbcy : b ≤ c + y) (hbax : b ≤ a + x) :
    z / (a + c + z) ≤ x / (a + b + x) + y / (b + c + y) := by
  have h1 : x / (a + c + x + y) ≤ x / (a + b + x) := by
    rcases hx.eq_or_lt with rfl | hx'
    · simp
    · exact div_le_div_of_nonneg_left hx'.le (by linarith) (by linarith)
  have h2 : y / (a + c + x + y) ≤ y / (b + c + y) := by
    rcases hy.eq_or_lt with rfl | hy'
    · simp
    · exact div_le_div_of_nonneg_left hy'.le (by linarith) (by linarith)
  have h3 : z / (a + c + z) ≤ (x + y) / (a + c + x + y) := by
    rcases (add_nonneg (add_nonneg ha hc) hz).eq_or_lt with h0 | hpos
    · have hz0 : z = 0 := by linarith
      rw [hz0, zero_div]
      exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_div_iff₀ hpos (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_right hxyz (add_nonneg ha hc)]
  calc z / (a + c + z) ≤ (x + y) / (a + c + x + y) := h3
    _ = x / (a + c + x + y) + y / (a + c + x + y) := add_div _ _ _
    _ ≤ x / (a + b + x) + y / (b + c + y) := add_le_add h1 h2

end LeanSMILES

namespace Finset

variable {α : Type*} [DecidableEq α]

/-! ### Similarity and distance of bit sets -/

/-- Tanimoto (Jaccard) similarity of two bit sets: shared bits over bits in either,
`|A ∩ B| / |A ∪ B|`. Exact, in `ℚ`. `0` when both sets are empty (Lean's `0 / 0`, which is
also the convention of RDKit and of `LeanSMILES.tanimoto`). -/
def tanimoto (A B : Finset α) : ℚ := #(A ∩ B) / #(A ∪ B)

/-- Tanimoto (Jaccard) distance of two bit sets: bits in exactly one over bits in either,
`|A ∆ B| / |A ∪ B|`. `0` when both sets are empty, which is what makes it a metric
(`tanimotoMetricSpace`) where `1 - tanimoto` is not. -/
def tanimotoDist (A B : Finset α) : ℚ := #(A ∆ B) / #(A ∪ B)

theorem tanimoto_comm (A B : Finset α) : A.tanimoto B = B.tanimoto A := by
  unfold tanimoto; rw [inter_comm A B, union_comm A B]

theorem tanimotoDist_comm (A B : Finset α) : A.tanimotoDist B = B.tanimotoDist A := by
  unfold tanimotoDist; rw [symmDiff_comm A B, union_comm A B]

@[simp] theorem tanimoto_empty_empty : (∅ : Finset α).tanimoto ∅ = 0 := by simp [tanimoto]

theorem tanimoto_self {A : Finset α} (h : A.Nonempty) : A.tanimoto A = 1 := by
  rw [tanimoto, inter_self, union_self, div_self]
  exact_mod_cast h.card_pos.ne'

@[simp] theorem tanimotoDist_self (A : Finset α) : A.tanimotoDist A = 0 := by
  simp [tanimotoDist]

theorem tanimoto_nonneg (A B : Finset α) : 0 ≤ A.tanimoto B := by
  unfold tanimoto; positivity

theorem tanimoto_le_one (A B : Finset α) : A.tanimoto B ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast card_le_card inter_subset_union) (by positivity)

theorem tanimotoDist_nonneg (A B : Finset α) : 0 ≤ A.tanimotoDist B := by
  unfold tanimotoDist; positivity

theorem tanimotoDist_le_one (A B : Finset α) : A.tanimotoDist B ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast card_le_card symmDiff_subset_union) (by positivity)

/-! ### Counting -/

theorem card_symmDiff_add_card_inter (A B : Finset α) : #(A ∆ B) + #(A ∩ B) = #(A ∪ B) := by
  rw [symmDiff_eq_sup_sdiff_inf, sup_eq_union, inf_eq_inter]
  exact card_sdiff_add_card_eq_card inter_subset_union

theorem two_mul_card_union (A B : Finset α) : 2 * #(A ∪ B) = #A + #B + #(A ∆ B) := by
  have h₁ := card_union_add_card_inter A B
  have h₂ := card_symmDiff_add_card_inter A B
  omega

/-- Similarity and distance sum to one, as soon as either set has an element. -/
theorem tanimoto_add_tanimotoDist (A B : Finset α) (h : (A ∪ B).Nonempty) :
    A.tanimoto B + A.tanimotoDist B = 1 := by
  unfold tanimoto tanimotoDist
  rw [← add_div, div_eq_one_iff_eq (by exact_mod_cast h.card_pos.ne')]
  exact_mod_cast (add_comm _ _).trans (card_symmDiff_add_card_inter A B)

theorem tanimotoDist_eq_one_sub (A B : Finset α) (h : (A ∪ B).Nonempty) :
    A.tanimotoDist B = 1 - A.tanimoto B := by
  rw [← tanimoto_add_tanimotoDist A B h]; ring

/-- The one pair where `1 - tanimoto` is not a distance: two empty fingerprints are at
distance `1` from each other, not `0`. -/
theorem one_sub_tanimoto_empty_empty : 1 - (∅ : Finset α).tanimoto ∅ = 1 := by simp

/-- The Hamming distance `|A ∆ B|` satisfies the triangle inequality. -/
theorem card_symmDiff_le (A B C : Finset α) : #(A ∆ C) ≤ #(A ∆ B) + #(B ∆ C) :=
  calc #(A ∆ C) ≤ #(A ∆ B ∪ B ∆ C) := card_le_card (symmDiff_triangle (a := A) (b := B) (c := C))
    _ ≤ #(A ∆ B) + #(B ∆ C) := card_union_le _ _

/-! ### The metric -/

theorem tanimotoDist_eq_zero_iff {A B : Finset α} : A.tanimotoDist B = 0 ↔ A = B := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact tanimotoDist_self A⟩
  rcases div_eq_zero_iff.1 h with h | h
  · exact symmDiff_eq_empty.1 (card_eq_zero.1 (by exact_mod_cast h))
  · obtain ⟨rfl, rfl⟩ := union_eq_empty.1 (card_eq_zero.1 (by exact_mod_cast h))
    rfl

/-- The Tanimoto distance as the Steinhaus transform of the Hamming distance. -/
theorem tanimotoDist_eq_two_mul_div (A B : Finset α) :
    A.tanimotoDist B = 2 * #(A ∆ B) / (#A + #B + #(A ∆ B) : ℚ) := by
  unfold tanimotoDist
  have h : (#(A ∪ B) : ℚ) = (#A + #B + #(A ∆ B)) / 2 := by
    rw [eq_div_iff two_ne_zero, mul_comm]; exact_mod_cast two_mul_card_union A B
  rw [h, div_div_eq_mul_div, mul_comm]

/-- **Triangle inequality for the Tanimoto distance** (Marczewski–Steinhaus 1958; Lipkus 1999).
-/
theorem tanimotoDist_triangle (A B C : Finset α) :
    A.tanimotoDist C ≤ A.tanimotoDist B + B.tanimotoDist C := by
  have hAC := card_symmDiff_le A B C
  have hB₁ := card_symmDiff_le B C ⊥
  have hB₂ := card_symmDiff_le B A ⊥
  rw [symmDiff_bot, symmDiff_bot] at hB₁ hB₂
  rw [symmDiff_comm B A] at hB₂
  rw [tanimotoDist_eq_two_mul_div, tanimotoDist_eq_two_mul_div, tanimotoDist_eq_two_mul_div,
    mul_div_assoc, mul_div_assoc, mul_div_assoc, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  exact LeanSMILES.steinhaus_triangle (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by exact_mod_cast hAC)
    (by exact_mod_cast (show #B ≤ #C + #(B ∆ C) by omega))
    (by exact_mod_cast (show #B ≤ #A + #(A ∆ B) by omega))

/-- **Tanimoto distance is a metric.** Binary fingerprints over bit type `α`, with
`dist A B = |A ∆ B| / |A ∪ B|`. A definition rather than an instance, so that `Finset α` is not
given a topology behind your back: `letI := Finset.tanimotoMetricSpace α` to use it. -/
@[reducible] def tanimotoMetricSpace (α : Type*) [DecidableEq α] : MetricSpace (Finset α) where
  dist A B := (A.tanimotoDist B : ℝ)
  dist_self A := by simp
  dist_comm A B := by rw [tanimotoDist_comm]
  dist_triangle A B C := by exact_mod_cast tanimotoDist_triangle A B C
  eq_of_dist_eq_zero h := tanimotoDist_eq_zero_iff.1 (by exact_mod_cast h)

example : ({0, 1, 2} : Finset ℕ).tanimoto {1, 2, 3} = 1 / 2 := by
  rw [tanimoto, show ({0, 1, 2} ∩ {1, 2, 3} : Finset ℕ).card = 2 by decide,
    show ({0, 1, 2} ∪ {1, 2, 3} : Finset ℕ).card = 4 by decide]
  norm_num

example : ({0, 1, 2} : Finset ℕ).tanimotoDist {1, 2, 3} = 1 / 2 := by
  rw [tanimotoDist, show ({0, 1, 2} ∆ {1, 2, 3} : Finset ℕ).card = 2 by decide,
    show ({0, 1, 2} ∪ {1, 2, 3} : Finset ℕ).card = 4 by decide]
  norm_num

end Finset

namespace LeanSMILES

/-! ### Real-valued fingerprints

Count fingerprints and continuous descriptors are vectors `ι → K`. The Tanimoto formula still
makes sense, agrees with the bit-set one on 0/1 vectors, and is no longer a metric. -/

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K]

/-- Tanimoto similarity of two real-valued (or count) vectors, Eq. (2) of Surendran et al.:
`⟨x, y⟩ / (⟨x, x⟩ + ⟨y, y⟩ - ⟨x, y⟩)`. The denominator is `‖x - y‖² + ⟨x, y⟩`, so for
nonnegative vectors it vanishes only at `x = y = 0`, where the value is `0`. -/
def tanimotoVec (x y : ι → K) : K := x ⬝ᵥ y / (x ⬝ᵥ x + y ⬝ᵥ y - x ⬝ᵥ y)

theorem tanimotoVec_comm (x y : ι → K) : tanimotoVec x y = tanimotoVec y x := by
  unfold tanimotoVec; rw [dotProduct_comm x y, add_comm (x ⬝ᵥ x)]

theorem dotProduct_indicator [DecidableEq ι] (A B : Finset ι) :
    (fun i ↦ if i ∈ A then (1 : K) else 0) ⬝ᵥ (fun i ↦ if i ∈ B then 1 else 0) = #(A ∩ B) := by
  have h : ∀ i, (if i ∈ A then (1 : K) else 0) * (if i ∈ B then 1 else 0) =
      if i ∈ A ∩ B then 1 else 0 := by
    intro i; by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
  simp only [dotProduct, h, Finset.sum_boole, Finset.filter_univ_mem]

/-- On 0/1 vectors, the vector formula is the bit-set Tanimoto of the supports. -/
theorem tanimotoVec_indicator [DecidableEq ι] [CharZero K] (A B : Finset ι) :
    tanimotoVec (fun i ↦ if i ∈ A then (1 : K) else 0) (fun i ↦ if i ∈ B then 1 else 0) =
      (A.tanimoto B : K) := by
  unfold tanimotoVec Finset.tanimoto
  rw [dotProduct_indicator, dotProduct_indicator, dotProduct_indicator, Finset.inter_self,
    Finset.inter_self]
  have h : (#(A ∪ B) : K) = #A + #B - #(A ∩ B) := by
    rw [eq_sub_iff_add_eq]; exact_mod_cast Finset.card_union_add_card_inter A B
  push_cast
  rw [h]

/-- **`1 - tanimotoVec` is not a metric** on real-valued vectors: the triangle inequality fails
already for three scalars in `[0, 1]`. With `x = 1/3`, `y = 2/3`, `z = 1` the distances are
`d(x,y) = 1/3`, `d(y,z) = 1/7`, `d(x,z) = 4/7`, and `1/3 + 1/7 = 10/21 < 12/21`. -/
theorem not_tanimotoVec_dist_triangle :
    ¬ ∀ x y z : Fin 1 → ℝ,
      1 - tanimotoVec x z ≤ (1 - tanimotoVec x y) + (1 - tanimotoVec y z) := by
  intro h
  have := h ![1 / 3] ![2 / 3] ![1]
  norm_num [tanimotoVec, dotProduct] at this

/-- The paper's counterexample, `x = (1, 0)`, `y = (1, 1)/√2`, `z = (0, 1)`, with `y` rounded to
`(0.7, 0.7)` to stay in `ℚ`: `d(x,y) + d(y,z) = 29/32 < 1 = d(x,z)`. `x` and `z` are binary; one
real-valued vector between them is enough. -/
example : ¬ ∀ x y z : Fin 2 → ℝ,
    1 - tanimotoVec x z ≤ (1 - tanimotoVec x y) + (1 - tanimotoVec y z) := by
  intro h
  have := h ![1, 0] ![7 / 10, 7 / 10] ![0, 1]
  norm_num [tanimotoVec, dotProduct, Fin.sum_univ_two] at this

/-- No metric space structure on real-valued vectors has `1 - tanimotoVec` as its distance. -/
theorem not_exists_metricSpace_tanimotoVec :
    ¬ ∃ m : MetricSpace (Fin 1 → ℝ),
      ∀ x y, @dist _ m.toPseudoMetricSpace.toDist x y = 1 - tanimotoVec x y := by
  rintro ⟨m, hm⟩
  exact not_tanimotoVec_dist_triangle fun x y z ↦ by
    rw [← hm, ← hm, ← hm]
    exact @dist_triangle _ m.toPseudoMetricSpace x y z

/-! ### The code: `tanimoto` on lists of on-bits -/

/-- `LeanSMILES.tanimoto` on duplicate-free lists of on-bits is `Finset.tanimoto` of their
sets. -/
theorem tanimoto_eq_toFinset {a b : List ℕ} (ha : a.Nodup) (hb : b.Nodup) :
    tanimoto a b = a.toFinset.tanimoto b.toFinset := by
  have hc : (a.filter b.contains).length = #(a.toFinset ∩ b.toFinset) := by
    rw [← List.toFinset_card_of_nodup (ha.filter _), List.toFinset_filter]
    congr 1
    ext x
    simp
  have hu : a.length + b.length - (a.filter b.contains).length = #(a.toFinset ∪ b.toFinset) := by
    have := Finset.card_union_add_card_inter a.toFinset b.toFinset
    rw [List.toFinset_card_of_nodup ha, List.toFinset_card_of_nodup hb] at this
    rw [hc]
    omega
  unfold tanimoto Finset.tanimoto
  dsimp only
  rw [hu, hc]
  simp only [beq_iff_eq]
  split_ifs with h
  · rw [h]; simp
  · rfl

/-- `List.eraseDups` removes all duplicates. (Core has `List.mem_eraseDups` but no `Nodup`
lemma for it at this toolchain.) -/
theorem _root_.List.nodup_eraseDups {β : Type*} [BEq β] [LawfulBEq β] :
    ∀ l : List β, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    refine List.Nodup.cons ?_ (List.nodup_eraseDups _)
    intro h
    rw [List.mem_eraseDups, List.mem_filter] at h
    simp at h
termination_by l => l.length
decreasing_by simp_wf; exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Folded Morgan fingerprints have no repeated bits. -/
theorem Molecule.nodup_morganBits {n : ℕ} (m : Molecule n) (radius fpSize : ℕ) :
    (m.morganBits radius fpSize).Nodup :=
  (perm_sortBy _).nodup_iff.2 (List.nodup_eraseDups _)

/-- The Tanimoto similarity LeanSMILES computes between two Morgan fingerprints is the bit-set
Tanimoto, so `Finset.tanimotoDist` of the two bit sets is a metric distance between them. -/
theorem Molecule.tanimoto_morganBits {n n' : ℕ} (m : Molecule n) (m' : Molecule n')
    (radius fpSize : ℕ) :
    tanimoto (m.morganBits radius fpSize) (m'.morganBits radius fpSize) =
      (m.morganBits radius fpSize).toFinset.tanimoto (m'.morganBits radius fpSize).toFinset :=
  tanimoto_eq_toFinset (m.nodup_morganBits _ _) (m'.nodup_morganBits _ _)

end LeanSMILES
