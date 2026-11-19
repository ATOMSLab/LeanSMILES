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

lemma XSpan.congr_span {S T : List ℕ} (h : ∀ x ∈ S, XSpan T x) (h' : ∀ x ∈ T, XSpan S x)
    (v : ℕ) : XSpan S v ↔ XSpan T v :=
  ⟨XSpan.of_span h, XSpan.of_span h'⟩

/-- Adding cycles one by one: the basis stays echelon and spans them with the old basis. -/
lemma foldl_addToBasis_spec : ∀ (l : List (ℕ × List ℕ)) (B : List (ℕ × ℕ)), Echelon B →
    Echelon (l.foldl addToBasis B) ∧
      ∀ v, XSpan ((l.foldl addToBasis B).map (·.2)) v ↔ XSpan (l.map (·.1) ++ B.map (·.2)) v
  | [], B, h => ⟨h, by simp⟩
  | c :: l, B, h => by
    obtain ⟨h1, h2⟩ := addToBasis_spec h c
    obtain ⟨i1, i2⟩ := foldl_addToBasis_spec l _ h1
    refine ⟨i1, fun v ↦ ?_⟩
    rw [List.foldl_cons, i2, List.map_cons, List.cons_append]
    refine XSpan.congr_span (fun x hx ↦ ?_) (fun x hx ↦ ?_) v
    · rcases List.mem_append.1 hx with hx | hx
      · exact .mem (List.mem_cons_of_mem _ (List.mem_append_left _ hx))
      · refine ((h2 x).1 (.mem hx)).mono fun y hy ↦ ?_
        rcases List.mem_cons.1 hy with rfl | hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ hy)
    · have hA : ∀ y ∈ c.1 :: B.map (·.2), XSpan (l.map (·.1) ++ (addToBasis B c).map (·.2)) y :=
        fun y hy ↦ ((h2 y).2 (.mem hy)).mono fun z hz ↦ List.mem_append_right _ hz
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hA _ List.mem_cons_self
      · rcases List.mem_append.1 hx with hx | hx
        · exact .mem (List.mem_append_left _ hx)
        · exact hA x (List.mem_cons_of_mem _ hx)

/-- A candidate cycle (mask, atoms) of `sorted` is **relevant** when its mask is not a sum of
the masks of strictly smaller candidates. -/
def Relevant (sorted : List (ℕ × List ℕ)) (c : ℕ × List ℕ) : Prop :=
  ¬ XSpan ((sorted.filter fun d ↦ decide (popcount d.1 < popcount c.1)).map (·.1)) c.1

/-- In a list ordered by `f`, the members below `k` come before those at `k`. -/
lemma filter_or_of_sorted {α : Type} (f : α → ℕ) (k : ℕ) (P Q : α → Bool) :
    ∀ {l : List α}, l.Pairwise (fun a b ↦ f a ≤ f b) → (∀ x ∈ l, P x = true → f x < k) →
      (∀ x ∈ l, Q x = true → f x = k) →
      l.filter (fun x ↦ P x || Q x) = l.filter P ++ l.filter Q
  | [], _, _, _ => rfl
  | x :: l, hl, hP, hQ => by
    have hl' := (List.pairwise_cons.1 hl).2
    have ih := filter_or_of_sorted f k P Q hl' (fun y hy ↦ hP y (List.mem_cons_of_mem _ hy))
      (fun y hy ↦ hQ y (List.mem_cons_of_mem _ hy))
    by_cases hpx : P x = true
    · have hqx : Q x = false := by
        by_contra h
        have := hQ x List.mem_cons_self (by simpa using h)
        have := hP x List.mem_cons_self hpx
        omega
      simp only [List.filter_cons, hpx, hqx, Bool.true_or, if_true, ih, List.cons_append,
        Bool.false_eq_true, if_false]
    · by_cases hqx : Q x = true
      · have hnil : l.filter P = [] := List.filter_eq_nil_iff.2 fun y hy hpy ↦ by
          have h1 := (List.pairwise_cons.1 hl).1 y hy
          have h2 := hP y (List.mem_cons_of_mem _ hy) hpy
          have h3 := hQ x List.mem_cons_self hqx
          omega
        simp only [List.filter_cons, hpx, hqx, Bool.false_or, if_true, ih, hnil,
          List.nil_append, Bool.false_eq_true, if_false]
      · simp only [List.filter_cons, hpx, hqx, Bool.false_or, ih, Bool.false_eq_true, if_false]

open Classical in
/-- **One size of `relevantCycles`**: if the basis spans the candidates of the sizes done (those
below `k`) and the result lists their relevant ones, then after size `k` the same holds with `k`
done. -/
lemma relevantStep_spec {sorted : List (ℕ × List ℕ)}
    (hs : sorted.Pairwise fun a b ↦ popcount a.1 ≤ popcount b.1) {k : ℕ} {ks : List ℕ}
    (hks : (k :: ks).Pairwise (· < ·))
    (hinv : ∀ c ∈ sorted, popcount c.1 ∉ k :: ks ↔ ∀ k' ∈ k :: ks, popcount c.1 < k')
    {B : List (ℕ × ℕ)} (hE : Echelon B)
    (hB : ∀ v, XSpan (B.map (·.2)) v ↔
      XSpan ((sorted.filter fun c ↦ decide (popcount c.1 ∉ k :: ks)).map (·.1)) v)
    {res : Array (List ℕ)}
    (hres : res.toList = (sorted.filter fun c ↦
      decide (popcount c.1 ∉ k :: ks ∧ Relevant sorted c)).map (·.2)) :
    Echelon (relevantStep sorted (B, res) k).1 ∧
      (∀ v, XSpan ((relevantStep sorted (B, res) k).1.map (·.2)) v ↔
        XSpan ((sorted.filter fun c ↦ decide (popcount c.1 ∉ ks)).map (·.1)) v) ∧
      (relevantStep sorted (B, res) k).2.toList = (sorted.filter fun c ↦
        decide (popcount c.1 ∉ ks ∧ Relevant sorted c)).map (·.2) ∧
      ∀ c ∈ sorted, popcount c.1 ∉ ks ↔ ∀ k' ∈ ks, popcount c.1 < k' := by
  have hk_lt : ∀ k' ∈ ks, k < k' := (List.pairwise_cons.1 hks).1
  have hkn : k ∉ ks := fun h ↦ lt_irrefl _ (hk_lt k h)
  have hlt : ∀ d ∈ sorted, popcount d.1 ∉ k :: ks ↔ popcount d.1 < k := fun d hd ↦ by
    rw [hinv d hd]
    constructor
    · exact fun h ↦ h k List.mem_cons_self
    · intro h k' hk'
      rcases List.mem_cons.1 hk' with rfl | hk'
      · exact h
      · exact h.trans (hk_lt k' hk')
  have hkeep : ∀ c ∈ sorted, popcount c.1 = k → (reduceBy B c.1 ≠ 0 ↔ Relevant sorted c) := by
    intro c hc hck
    unfold Relevant
    rw [Ne, reduceBy_eq_zero_iff hE, hB]
    apply not_congr
    apply XSpan.congr
    intro x
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨d, ⟨hd, h⟩, rfl⟩
      exact ⟨d, ⟨hd, by rw [hck]; exact (hlt d hd).1 h⟩, rfl⟩
    · rintro ⟨d, ⟨hd, h⟩, rfl⟩
      exact ⟨d, ⟨hd, (hlt d hd).2 (hck ▸ h)⟩, rfl⟩
  unfold relevantStep
  dsimp only
  have hkept : (sorted.filter fun c ↦ popcount c.1 == k).filter (fun c ↦ reduceBy B c.1 != 0) =
      sorted.filter fun c ↦ decide (popcount c.1 = k ∧ Relevant sorted c) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro c hc
    by_cases hck : popcount c.1 = k
    · have := hkeep c hc hck
      rw [Bool.eq_iff_iff]
      simp only [hck, beq_self_eq_true, Bool.and_true, bne_iff_ne, ne_eq, true_and,
        decide_eq_true_eq]
      exact this
    · simp [hck]
  rw [hkept]
  obtain ⟨f1, f2⟩ := foldl_addToBasis_spec
    (sorted.filter fun c ↦ decide (popcount c.1 = k ∧ Relevant sorted c)) B hE
  refine ⟨f1, fun v ↦ ?_, ?_, fun c hc ↦ ?_⟩
  · rw [f2 v]
    refine XSpan.congr_span (fun x hx ↦ ?_) (fun x hx ↦ ?_) v
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
        simp only [List.mem_filter, decide_eq_true_eq] at hd
        exact .mem (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd.1, by
          simp only [decide_eq_true_eq]; rw [hd.2.1]; exact hkn⟩, rfl⟩)
      · refine ((hB x).1 (.mem hx)).mono fun y hy ↦ ?_
        obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hy
        simp only [List.mem_filter, decide_eq_true_eq] at hd
        exact List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd.1, by
          simp only [decide_eq_true_eq]; exact fun h ↦ hd.2 (List.mem_cons_of_mem _ h)⟩, rfl⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
      simp only [List.mem_filter, decide_eq_true_eq] at hd
      obtain ⟨hd, hdk⟩ := hd
      by_cases hk : popcount d.1 = k
      · by_cases hr : Relevant sorted d
        · exact .mem (List.mem_append_left _ (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd, by
            simp only [decide_eq_true_eq]; exact ⟨hk, hr⟩⟩, rfl⟩))
        · have h0 : reduceBy B d.1 = 0 := by
            by_contra h0; exact hr ((hkeep d hd hk).1 h0)
          exact ((reduceBy_eq_zero_iff hE _).1 h0).mono fun y hy ↦ List.mem_append_right _ hy
      · have hm : popcount d.1 ∉ k :: ks := by
          rw [List.mem_cons, not_or]; exact ⟨hk, hdk⟩
        exact ((hB d.1).2 (.mem (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨hd, by
          simpa using hm⟩, rfl⟩))).mono fun y hy ↦ List.mem_append_right _ hy
  · rw [Array.toList_append, hres, List.toList_toArray, ← List.map_append]
    congr 1
    rw [← filter_or_of_sorted (fun c ↦ popcount c.1) k _ _ hs]
    · apply List.filter_congr
      intro c hc
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons, not_or]
      constructor
      · rintro (⟨⟨_, h1⟩, h2⟩ | ⟨hck, h2⟩)
        · exact ⟨h1, h2⟩
        · exact ⟨hck ▸ hkn, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hck : popcount c.1 = k
        · exact .inr ⟨hck, h2⟩
        · exact .inl ⟨⟨hck, h1⟩, h2⟩
    · intro c hc h
      simp only [decide_eq_true_eq] at h
      exact (hlt c hc).1 h.1
    · intro c hc h
      simp only [decide_eq_true_eq] at h
      exact h.1
  · constructor
    · intro h k' hk'
      by_cases hck : popcount c.1 = k
      · rw [hck]; exact hk_lt k' hk'
      · have : popcount c.1 ∉ k :: ks := by rw [List.mem_cons, not_or]; exact ⟨hck, h⟩
        exact ((hlt c hc).1 this).trans (hk_lt k' hk')
    · exact fun h hm ↦ lt_irrefl _ (h _ hm)

lemma eraseDups_pairwise_lt : ∀ {l : List ℕ}, l.Pairwise (· ≤ ·) → l.eraseDups.Pairwise (· < ·)
  | [], _ => by simp
  | a :: as, h => by
    rw [List.eraseDups_cons]
    have h' : (as.filter fun b ↦ !b == a).Pairwise (· ≤ ·) := (List.pairwise_cons.1 h).2.filter _
    refine List.Pairwise.cons (fun y hy ↦ ?_) (eraseDups_pairwise_lt h')
    rw [List.mem_eraseDups, List.mem_filter] at hy
    have h1 := (List.pairwise_cons.1 h).1 y hy.1
    have h2 : y ≠ a := by simpa using hy.2
    omega
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

open Classical in
/-- **What the sizes loop of `relevantCycles` keeps**: over a candidate list ordered by size, the
relevant candidates, in order. -/
theorem relevantFold_eq {sorted : List (ℕ × List ℕ)}
    (hs : sorted.Pairwise fun a b ↦ popcount a.1 ≤ popcount b.1) :
    (((sorted.map (popcount ·.1)).eraseDups.foldl (relevantStep sorted) ([], #[])).2).toList =
      (sorted.filter fun c ↦ decide (Relevant sorted c)).map (·.2) := by
  have key : ∀ (ks : List ℕ) (B : List (ℕ × ℕ)) (res : Array (List ℕ)),
      ks.Pairwise (· < ·) → (∀ c ∈ sorted, popcount c.1 ∉ ks ↔ ∀ k' ∈ ks, popcount c.1 < k') →
      Echelon B →
      (∀ v, XSpan (B.map (·.2)) v ↔
        XSpan ((sorted.filter fun c ↦ decide (popcount c.1 ∉ ks)).map (·.1)) v) →
      res.toList = (sorted.filter fun c ↦
        decide (popcount c.1 ∉ ks ∧ Relevant sorted c)).map (·.2) →
      (ks.foldl (relevantStep sorted) (B, res)).2.toList =
        (sorted.filter fun c ↦ decide (Relevant sorted c)).map (·.2) := by
    intro ks
    induction ks with
    | nil =>
      intro B res _ _ _ _ hres
      rw [List.foldl_nil, hres]
      simp
    | cons k ks ih =>
      intro B res hks hinv hE hB hres
      obtain ⟨g1, g2, g3, g4⟩ := relevantStep_spec hs hks hinv hE hB hres
      rw [List.foldl_cons]
      exact ih _ _ (List.pairwise_cons.1 hks).2 g4 g1 g2 g3
  have hall : ∀ c ∈ sorted, popcount c.1 ∈ (sorted.map (popcount ·.1)).eraseDups :=
    fun c hc ↦ List.mem_eraseDups.2 (List.mem_map_of_mem hc)
  have hnil : sorted.filter (fun c ↦ decide (popcount c.1 ∉
      (sorted.map (popcount ·.1)).eraseDups)) = [] :=
    List.filter_eq_nil_iff.2 fun c hc h ↦ by simp only [decide_eq_true_eq] at h; exact h (hall c hc)
  apply key
  · exact eraseDups_pairwise_lt (List.pairwise_map.2 hs)
  · intro c hc
    exact ⟨fun h ↦ absurd (hall c hc) h, fun h ↦ absurd (h _ (hall c hc)) (lt_irrefl _)⟩
  · exact ⟨by simp, .nil⟩
  · intro v
    rw [hnil]
    simp only [List.map_nil]
  · rw [List.filter_eq_nil_iff.2 fun c hc h ↦ by
      simp only [decide_eq_true_eq] at h; exact h.1 (hall c hc)]
    rfl

lemma listLt_trans : ∀ {a b c : List ℕ}, listLt a b = true → listLt b c = true →
    listLt a c = true
  | [], [], _, h, _ => by simp [listLt] at h
  | [], _ :: _, [], _, h => by simp [listLt] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [listLt] at h
  | _ :: _, _ :: _, [], _, h => by simp [listLt] at h
  | x :: as, y :: bs, z :: cs, h1, h2 => by
    simp only [listLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
      at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · left; omega
    · left; exact h1
    · left; exact h2
    · right; exact ⟨rfl, listLt_trans h1 h2⟩

lemma listLt_total : ∀ a b : List ℕ, listLt a b = true ∨ a = b ∨ listLt b a = true
  | [], [] => .inr (.inl rfl)
  | [], _ :: _ => .inl rfl
  | _ :: _, [] => .inr (.inr rfl)
  | x :: as, y :: bs => by
    rcases lt_trichotomy x y with h | rfl | h
    · left; simp [listLt, h]
    · rcases listLt_total as bs with h | rfl | h
      · left; simp [listLt, h]
      · right; left; rfl
      · right; right; simp [listLt, h]
    · right; right; simp [listLt, h]

/-- The order `relevantCycles` sorts candidates by: size, then sorted atoms. -/
def relevantCmp (a b : ℕ × List ℕ) : Bool :=
  popcount a.1 < popcount b.1 || (popcount a.1 == popcount b.1 &&
    (listLt (a.2.mergeSort (· ≤ ·)) (b.2.mergeSort (· ≤ ·)) ||
      a.2.mergeSort (· ≤ ·) == b.2.mergeSort (· ≤ ·)))

lemma relevantCmp_trans (a b c : ℕ × List ℕ) (h1 : relevantCmp a b = true)
    (h2 : relevantCmp b c = true) : relevantCmp a c = true := by
  unfold relevantCmp at *
  generalize a.2.mergeSort (· ≤ ·) = sa at *
  generalize b.2.mergeSort (· ≤ ·) = sb at *
  generalize c.2.mergeSort (· ≤ ·) = sc at *
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2 ⊢
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · left; omega
  · left; omega
  · left; omega
  · right
    refine ⟨e1.trans e2, ?_⟩
    rcases h1 with h1 | rfl <;> rcases h2 with h2 | rfl
    · exact .inl (listLt_trans h1 h2)
    · exact .inl h1
    · exact .inl h2
    · exact .inr rfl

lemma relevantCmp_total (a b : ℕ × List ℕ) : (relevantCmp a b || relevantCmp b a) = true := by
  unfold relevantCmp
  generalize a.2.mergeSort (· ≤ ·) = sa
  generalize b.2.mergeSort (· ≤ ·) = sb
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq]
  rcases lt_trichotomy (popcount a.1) (popcount b.1) with h | h | h
  · exact .inl (.inl h)
  · rcases listLt_total sa sb with h' | rfl | h'
    · exact .inl (.inr ⟨h, .inl h'⟩)
    · exact .inl (.inr ⟨h, .inr rfl⟩)
    · exact .inr (.inr ⟨h.symm, .inl h'⟩)
  · exact .inr (.inl h)

/-- `relevantCycles` with its sort named. -/
lemma Work.relevantCycles_eq_fold (m : Work) : m.relevantCycles =
    ((((m.candidateCycles.toList.mergeSort relevantCmp).map (popcount ·.1)).eraseDups.foldl
      (relevantStep (m.candidateCycles.toList.mergeSort relevantCmp)) ([], #[])).2) := by
  unfold Work.relevantCycles
  rfl

/-- The candidates sorted for `relevantCycles` are in order of size. -/
lemma pairwise_mergeSort_relevantCmp (l : List (ℕ × List ℕ)) :
    (l.mergeSort relevantCmp).Pairwise fun a b ↦ popcount a.1 ≤ popcount b.1 :=
  (List.pairwise_mergeSort relevantCmp_trans relevantCmp_total l).imp fun h ↦ by
    unfold relevantCmp at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
    omega

open Classical in
/-- **The ring set is the relevant candidates**: `relevantCycles` lists, in its sorted order, the
candidate cycles whose mask is not a sum of masks of strictly smaller candidates. -/
theorem Work.relevantCycles_toList (m : Work) : m.relevantCycles.toList =
    ((m.candidateCycles.toList.mergeSort relevantCmp).filter fun c ↦
      decide (Relevant (m.candidateCycles.toList.mergeSort relevantCmp) c)).map (·.2) := by
  rw [Work.relevantCycles_eq_fold]
  exact relevantFold_eq (pairwise_mergeSort_relevantCmp _)

end LeanSMILES.Aromaticity
