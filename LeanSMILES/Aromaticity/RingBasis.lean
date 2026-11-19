/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Rings

/-!
# LeanSMILES.Aromaticity.RingBasis

The GF(2) bookkeeping of `Work.relevantCycles`

Cycles are bond bitmasks, and a sum of cycles is the `xor` of their masks. `reduceBy` reduces a
mask by an echelon basis (pivot bit, vector), highest pivot first, and `addToBasis` adds a reduced
mask to the basis. This file proves what they compute: `reduceBy basis v = 0` exactly when `v` is
a sum of basis vectors (`reduceBy_eq_zero_iff`), and `addToBasis` keeps the basis in echelon form
and adds the cycle to its span (`addToBasis_spec`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- `v` is a sum (`xor`) of members of `S`. -/
inductive XSpan (S : List ℕ) : ℕ → Prop
  | zero : XSpan S 0
  | add {s v : ℕ} : s ∈ S → XSpan S v → XSpan S (s ^^^ v)

namespace XSpan

lemma xor {S : List ℕ} {a b : ℕ} (ha : XSpan S a) (hb : XSpan S b) : XSpan S (a ^^^ b) := by
  induction ha with
  | zero => simpa using hb
  | add hs _ ih => rw [Nat.xor_assoc]; exact .add hs ih

lemma mem {S : List ℕ} {s : ℕ} (hs : s ∈ S) : XSpan S s := by
  simpa using XSpan.add hs .zero

lemma of_span {S T : List ℕ} (h : ∀ x ∈ S, XSpan T x) {v : ℕ} (hv : XSpan S v) : XSpan T v := by
  induction hv with
  | zero => exact .zero
  | add hs _ ih => exact (h _ hs).xor ih

lemma mono {S T : List ℕ} (h : ∀ x ∈ S, x ∈ T) {v : ℕ} (hv : XSpan S v) : XSpan T v :=
  of_span (fun x hx ↦ mem (h x hx)) hv

lemma congr {S T : List ℕ} (h : ∀ x, x ∈ S ↔ x ∈ T) (v : ℕ) : XSpan S v ↔ XSpan T v :=
  ⟨mono fun x ↦ (h x).1, mono fun x ↦ (h x).2⟩

lemma xor_cancel (b v : ℕ) : b ^^^ (b ^^^ v) = v := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

lemma nil {v : ℕ} (h : XSpan [] v) : v = 0 := by
  cases h with
  | zero => rfl
  | add hs _ => cases hs

lemma cons_iff {b : ℕ} {S : List ℕ} {v : ℕ} :
    XSpan (b :: S) v ↔ XSpan S v ∨ XSpan S (b ^^^ v) := by
  constructor
  · intro h
    induction h with
    | zero => exact .inl .zero
    | @add s v hs _ ih =>
      rcases List.mem_cons.1 hs with rfl | hs
      · rcases ih with ih | ih
        · exact .inr (by rwa [xor_cancel])
        · exact .inl ih
      · rcases ih with ih | ih
        · exact .inl (.add hs ih)
        · refine .inr ?_
          rw [← Nat.xor_assoc, Nat.xor_comm b s, Nat.xor_assoc]
          exact .add hs ih
  · rintro (h | h)
    · exact mono (fun x hx ↦ List.mem_cons_of_mem _ hx) h
    · rw [← xor_cancel b v]
      exact .add List.mem_cons_self (mono (fun x hx ↦ List.mem_cons_of_mem _ hx) h)

/-- A sum of vectors below `2 ^ q` is below `2 ^ q`. -/
lemma lt_two_pow {S : List ℕ} {q : ℕ} (h : ∀ x ∈ S, x < 2 ^ q) {v : ℕ} (hv : XSpan S v) :
    v < 2 ^ q := by
  induction hv with
  | zero => exact Nat.two_pow_pos q
  | add hs _ ih => exact Nat.xor_lt_two_pow (h _ hs) ih

/-- A member of the span is still in it after adding a sum of members. -/
lemma xor_iff {S : List ℕ} {s : ℕ} (hs : XSpan S s) (v : ℕ) :
    XSpan S (s ^^^ v) ↔ XSpan S v := by
  constructor
  · intro h
    rw [← xor_cancel s v]
    exact hs.xor h
  · exact hs.xor

end XSpan

/-- An echelon basis: each vector's highest bit is its pivot, and the pivots strictly
decrease. -/
def Echelon (B : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ B, e.2.testBit e.1 = true ∧ e.2 < 2 ^ (e.1 + 1)) ∧ B.Pairwise fun x y ↦ y.1 < x.1

lemma reduceBy_nil (v : ℕ) : reduceBy [] v = v := rfl

lemma reduceBy_cons (p b : ℕ) (B : List (ℕ × ℕ)) (v : ℕ) :
    reduceBy ((p, b) :: B) v = reduceBy B (if v.testBit p then v ^^^ b else v) := rfl

/-- Reducing by vectors below `2 ^ q` keeps bit `q`. -/
lemma testBit_reduceBy_of_lt {q : ℕ} : ∀ {B : List (ℕ × ℕ)}, (∀ e ∈ B, e.2 < 2 ^ q) →
    ∀ v, (reduceBy B v).testBit q = v.testBit q
  | [], _, v => rfl
  | (p, b) :: B, h, v => by
    rw [reduceBy_cons, testBit_reduceBy_of_lt (fun e he ↦ h e (List.mem_cons_of_mem _ he))]
    split
    · rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (h _ List.mem_cons_self), Bool.xor_false]
    · rfl

/-- Reducing clears every pivot bit. -/
lemma reduceBy_pivot : ∀ {B : List (ℕ × ℕ)}, Echelon B → ∀ v, ∀ e ∈ B,
    (reduceBy B v).testBit e.1 = false
  | [], _, _, e, he => by cases he
  | (p, b) :: B, hE, v, e, he => by
    have hE' : Echelon B := ⟨fun e he ↦ hE.1 e (List.mem_cons_of_mem _ he),
      (List.pairwise_cons.1 hE.2).2⟩
    rw [reduceBy_cons]
    rcases List.mem_cons.1 he with rfl | he
    · have hlt : ∀ e ∈ B, e.2 < 2 ^ p := fun e he ↦ by
        have h1 := (hE.1 e (List.mem_cons_of_mem _ he)).2
        have h2 := (List.pairwise_cons.1 hE.2).1 e he
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by simpa using h2))
      rw [testBit_reduceBy_of_lt hlt]
      have hb := (hE.1 _ List.mem_cons_self).1
      split
      · rename_i hv
        simp only at hb
        rw [Nat.testBit_xor, hv, hb]
        rfl
      · exact Bool.eq_false_iff.2 (by assumption)
    · exact reduceBy_pivot hE' _ e he

/-- What reducing removes is a sum of basis vectors. -/
lemma reduceBy_span : ∀ (B : List (ℕ × ℕ)) (v : ℕ), XSpan (B.map (·.2)) (v ^^^ reduceBy B v)
  | [], v => by rw [reduceBy_nil, Nat.xor_self]; exact .zero
  | (p, b) :: B, v => by
    rw [reduceBy_cons, List.map_cons]
    by_cases hv : v.testBit p = true
    · rw [if_pos hv]
      have ih := (reduceBy_span B (v ^^^ b)).mono (fun x hx ↦ List.mem_cons_of_mem b hx)
      have e : v ^^^ reduceBy B (v ^^^ b) = b ^^^ ((v ^^^ b) ^^^ reduceBy B (v ^^^ b)) := by
        rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_comm b v, Nat.xor_assoc v b b,
          Nat.xor_self, Nat.xor_zero]
      rw [e]
      exact .add List.mem_cons_self ih
    · rw [if_neg hv]
      exact (reduceBy_span B v).mono (fun x hx ↦ List.mem_cons_of_mem b hx)

/-- A nonzero sum of echelon vectors has a pivot bit set. -/
lemma pivot_of_span : ∀ {B : List (ℕ × ℕ)}, Echelon B → ∀ {v : ℕ}, XSpan (B.map (·.2)) v →
    v ≠ 0 → ∃ e ∈ B, v.testBit e.1 = true
  | [], _, _, h, h0 => absurd (XSpan.nil h) h0
  | (p, b) :: B, hE, v, h, h0 => by
    have hE' : Echelon B := ⟨fun e he ↦ hE.1 e (List.mem_cons_of_mem _ he),
      (List.pairwise_cons.1 hE.2).2⟩
    rw [List.map_cons, XSpan.cons_iff] at h
    rcases h with h | h
    · obtain ⟨e, he, hb⟩ := pivot_of_span hE' h h0
      exact ⟨e, List.mem_cons_of_mem _ he, hb⟩
    · have hlt : ∀ x ∈ B.map (·.2), x < 2 ^ p := fun x hx ↦ by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
        have h1 := (hE.1 e (List.mem_cons_of_mem _ he)).2
        have h2 := (List.pairwise_cons.1 hE.2).1 e he
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by simpa using h2))
      refine ⟨(p, b), List.mem_cons_self, ?_⟩
      have hs := Nat.testBit_lt_two_pow (XSpan.lt_two_pow hlt h)
      have hb := (hE.1 _ List.mem_cons_self).1
      simp only at hb ⊢
      rw [← XSpan.xor_cancel b v, Nat.testBit_xor, hb, hs]
      rfl

/-- **Reduction decides the span**: `reduceBy B v = 0` exactly when `v` is a sum of basis
vectors. -/
theorem reduceBy_eq_zero_iff {B : List (ℕ × ℕ)} (hE : Echelon B) (v : ℕ) :
    reduceBy B v = 0 ↔ XSpan (B.map (·.2)) v := by
  constructor
  · intro h
    have := reduceBy_span B v
    rwa [h, Nat.xor_zero] at this
  · intro h
    by_contra h0
    have hr : XSpan (B.map (·.2)) (reduceBy B v) := by
      rw [← XSpan.xor_cancel v (reduceBy B v)]
      exact h.xor (reduceBy_span B v)
    obtain ⟨e, he, hb⟩ := pivot_of_span hE hr h0
    rw [reduceBy_pivot hE v e he] at hb
    cases hb

/-- **`addToBasis` keeps the basis in echelon form and adds the cycle to its span.** -/
theorem addToBasis_spec {B : List (ℕ × ℕ)} (hE : Echelon B) (c : ℕ × List ℕ) :
    Echelon (addToBasis B c) ∧
      ∀ v, XSpan ((addToBasis B c).map (·.2)) v ↔ XSpan (c.1 :: B.map (·.2)) v := by
  unfold addToBasis
  dsimp only
  set r := reduceBy B c.1 with hr
  have hspan : XSpan (B.map (·.2)) (c.1 ^^^ r) := reduceBy_span B c.1
  split
  · rename_i h0
    have h0 : r ≠ 0 := by simpa using h0
    set L := (B ++ [(r.log2, r)]).mergeSort fun x y ↦ decide (y.1 ≤ x.1)
    have hperm : L.Perm (B ++ [(r.log2, r)]) := List.mergeSort_perm _ _
    have hmem : ∀ e, e ∈ L ↔ e ∈ B ∨ e = (r.log2, r) := fun e ↦ by
      rw [hperm.mem_iff]; simp
    have hnew : r.log2 ∉ B.map (·.1) := fun h ↦ by
      obtain ⟨e, he, e1⟩ := List.mem_map.1 h
      have := reduceBy_pivot hE c.1 e he
      rw [e1, ← hr, Nat.testBit_log2 h0] at this
      cases this
    refine ⟨⟨fun e he ↦ ?_, ?_⟩, fun v ↦ ?_⟩
    · rcases (hmem e).1 he with he | rfl
      · exact hE.1 e he
      · exact ⟨Nat.testBit_log2 h0, Nat.lt_log2_self⟩
    · have hsorted : L.Pairwise fun x y ↦ decide (y.1 ≤ x.1) = true :=
        List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp at h1 h2 ⊢; omega)
          (fun a b ↦ by simp only [decide_eq_true_eq, Bool.or_eq_true]; omega) _
      have hnd : (L.map (·.1)).Nodup := by
        rw [(hperm.map _).nodup_iff, List.map_append, List.nodup_append]
        refine ⟨?_, by simp, fun a ha b hb e ↦ ?_⟩
        · exact (List.pairwise_map.2 hE.2).imp fun h ↦ Nat.ne_of_gt h
        · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
          rw [hb] at e
          exact hnew (e ▸ ha)
      have hne : L.Pairwise fun x y ↦ x.1 ≠ y.1 := List.pairwise_map.1 hnd
      exact (hsorted.and hne).imp fun ⟨h1, h2⟩ ↦ by simp only [decide_eq_true_eq] at h1; omega
    · rw [XSpan.congr (S := L.map (·.2)) (T := r :: B.map (·.2)) (fun x ↦ by
        simp only [List.mem_map, hmem, List.mem_cons]
        constructor
        · rintro ⟨e, he | rfl, rfl⟩
          · exact .inr ⟨e, he, rfl⟩
          · exact .inl rfl
        · rintro (rfl | ⟨e, he, rfl⟩)
          · exact ⟨_, .inr rfl, rfl⟩
          · exact ⟨e, .inl he, rfl⟩), XSpan.cons_iff, XSpan.cons_iff]
      have e1 : r ^^^ v = (c.1 ^^^ r) ^^^ (c.1 ^^^ v) := by
        rw [Nat.xor_assoc, ← Nat.xor_assoc r c.1 v, Nat.xor_comm r c.1, Nat.xor_assoc,
          XSpan.xor_cancel]
      rw [e1, XSpan.xor_iff hspan]
  · rename_i h0
    have h0 : r = 0 := by simpa using h0
    have hc : XSpan (B.map (·.2)) c.1 := (reduceBy_eq_zero_iff hE c.1).1 h0
    refine ⟨hE, fun v ↦ ?_⟩
    rw [XSpan.cons_iff, XSpan.xor_iff hc, or_self]

end LeanSMILES.Aromaticity
