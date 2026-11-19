/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingIso

/-!
# LeanSMILES.Aromaticity.RingSetIso

The ring set follows a renumbering

`Work.candidateCycles` keeps one cycle per bond mask, each tagged with its mask, and every cycle
found from any root is represented (`Work.candidateCycles_spec`). Under a renumbering
(`Work.WorkIso`) each candidate matches one of the other copy, with the same ring up to start and
direction and the bonds renamed (`Work.WorkIso.candidate`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

lemma foldl_addCandidate (m : Work) : ∀ (L : List (List ℕ)) (cands : Array (ℕ × List ℕ)),
    (cands.toList.map (·.1)).Nodup → (∀ e ∈ cands.toList, e.1 = m.cycleMask e.2) →
    ((L.foldl m.addCandidate cands).toList.map (·.1)).Nodup ∧
      (∀ e ∈ (L.foldl m.addCandidate cands).toList, e.1 = m.cycleMask e.2) ∧
      (∀ e ∈ (L.foldl m.addCandidate cands).toList, e ∈ cands.toList ∨ e.2 ∈ L) ∧
      (∀ c ∈ L, ∃ e ∈ (L.foldl m.addCandidate cands).toList, e.1 = m.cycleMask c) ∧
      ∀ e ∈ cands.toList, e ∈ (L.foldl m.addCandidate cands).toList
  | [], cands, h1, h2 => ⟨h1, h2, fun e he ↦ .inl he, by simp, fun _ h ↦ h⟩
  | c :: L, cands, h1, h2 => by
    rw [List.foldl_cons]
    unfold addCandidate
    dsimp only
    split
    · rename_i hnew
      have hnew' : ∀ e ∈ cands.toList, e.1 ≠ m.cycleMask c := by
        intro e he heq
        have : cands.toList.any (fun x ↦ x.1 == m.cycleMask c) = true :=
          List.any_eq_true.2 ⟨e, he, by simp [heq]⟩
        rw [Array.any_toList] at this
        rw [this] at hnew
        cases hnew
      obtain ⟨g1, g2, g3, g4, g5⟩ := foldl_addCandidate m L (cands.push (m.cycleMask c, c))
        (by rw [Array.toList_push, List.map_append]
            refine List.nodup_append.2 ⟨h1, by simp, fun a ha b hb e ↦ ?_⟩
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb
            obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 ha
            exact hnew' e0 he0 e)
        (fun e he ↦ by
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact h2 e he
          · rfl)
      refine ⟨g1, g2, fun e he ↦ ?_, fun c' hc' ↦ ?_, fun e he ↦ g5 e (by simp [he])⟩
      · rcases g3 e he with he' | he'
        · rw [Array.toList_push, List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · exact .inl he'
          · exact .inr List.mem_cons_self
        · exact .inr (List.mem_cons_of_mem _ he')
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · exact ⟨(m.cycleMask c', c'), g5 _ (by simp), rfl⟩
        · exact g4 c' hc'
    · rename_i hold
      obtain ⟨g1, g2, g3, g4, g5⟩ := foldl_addCandidate m L cands h1 h2
      refine ⟨g1, g2, fun e he ↦ ?_, fun c' hc' ↦ ?_, g5⟩
      · rcases g3 e he with he' | he'
        · exact .inl he'
        · exact .inr (List.mem_cons_of_mem _ he')
      · rcases List.mem_cons.1 hc' with rfl | hc'
        · have : cands.toList.any (fun x ↦ x.1 == m.cycleMask c') = true := by
            rw [Array.any_toList]; simpa using hold
          obtain ⟨e, he, heq⟩ := List.any_eq_true.1 this
          exact ⟨e, g5 e he, by simpa using heq⟩
        · exact g4 c' hc'

/-- **The candidates**: one per mask, each tagged with its mask, each found from a root, and
every cycle found from a root represented by its mask. -/
theorem candidateCycles_spec (m : Work) :
    (m.candidateCycles.toList.map (·.1)).Nodup ∧
      (∀ e ∈ m.candidateCycles.toList, e.1 = m.cycleMask e.2 ∧
        ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) ∧
      ∀ r < m.numAtoms, ∀ c ∈ m.cyclesFrom r,
        ∃ e ∈ m.candidateCycles.toList, e.1 = m.cycleMask c := by
  unfold candidateCycles
  have key : ∀ (rs : List ℕ) (cands : Array (ℕ × List ℕ)), (∀ r ∈ rs, r < m.numAtoms) →
      (cands.toList.map (·.1)).Nodup →
      (∀ e ∈ cands.toList, e.1 = m.cycleMask e.2 ∧ ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) →
      let res := rs.foldl (fun cands r ↦ (m.cyclesFrom r).foldl m.addCandidate cands) cands
      (res.toList.map (·.1)).Nodup ∧
        (∀ e ∈ res.toList, e.1 = m.cycleMask e.2 ∧ ∃ r < m.numAtoms, e.2 ∈ m.cyclesFrom r) ∧
        (∀ r ∈ rs, ∀ c ∈ m.cyclesFrom r, ∃ e ∈ res.toList, e.1 = m.cycleMask c) ∧
        ∀ e ∈ cands.toList, e ∈ res.toList := by
    intro rs
    induction rs with
    | nil => intro cands _ h1 h2; exact ⟨h1, h2, by simp, fun _ h ↦ h⟩
    | cons r rs ih =>
      intro cands hrs h1 h2
      dsimp only
      rw [List.foldl_cons]
      have hr : r < m.numAtoms := hrs r List.mem_cons_self
      obtain ⟨f1, f2, f3, f4, f5⟩ := foldl_addCandidate m (m.cyclesFrom r) cands h1
        (fun e he ↦ (h2 e he).1)
      obtain ⟨i1, i2, i3, i4⟩ := ih _ (fun r hr ↦ hrs r (List.mem_cons_of_mem _ hr)) f1
        (fun e he ↦ ⟨f2 e he, by
          rcases f3 e he with he' | he'
          · exact (h2 e he').2
          · exact ⟨r, hr, he'⟩⟩)
      refine ⟨i1, i2, fun r' hr' c hc ↦ ?_, fun e he ↦ i4 e (f5 e he)⟩
      rcases List.mem_cons.1 hr' with rfl | hr'
      · obtain ⟨e, he, hm⟩ := f4 c hc
        exact ⟨e, i4 e he, hm⟩
      · exact i3 r' hr' c hc
  obtain ⟨k1, k2, k3, -⟩ := key (List.range m.numAtoms) #[] (fun r hr ↦ List.mem_range.1 hr)
    (by simp) (by simp)
  exact ⟨k1, k2, fun r hr c hc ↦ k3 r (List.mem_range.2 hr) c hc⟩

/-! ### Renaming the bits of a mask -/

/-- The mask with bit `π k` for each bit `k < n` of `v`. -/
def bitMap (π : ℕ → ℕ) (n v : ℕ) : ℕ :=
  (List.range n).foldl (fun acc k ↦ if v.testBit k then acc ||| (1 <<< π k) else acc) 0

lemma testBit_bitMap (π : ℕ → ℕ) (n v j : ℕ) :
    (bitMap π n v).testBit j = decide (∃ k < n, π k = j ∧ v.testBit k = true) := by
  have key : ∀ (L : List ℕ) (init : ℕ),
      (L.foldl (fun acc k ↦ if v.testBit k then acc ||| (1 <<< π k) else acc) init).testBit j =
        (init.testBit j || decide (∃ k ∈ L, π k = j ∧ v.testBit k = true)) := by
    intro L
    induction L with
    | nil => simp
    | cons k L ih =>
      intro init
      rw [List.foldl_cons, ih, Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
      split
      · rename_i hk
        simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true,
          decide_eq_true_eq]
        constructor
        · rintro ((h | rfl) | ⟨k', hk', h⟩)
          · exact .inl h
          · exact .inr ⟨k, .inl rfl, rfl, hk⟩
          · exact .inr ⟨k', .inr hk', h⟩
        · rintro (h | ⟨k', rfl | hk', h⟩)
          · exact .inl (.inl h)
          · exact .inl (.inr h.1)
          · exact .inr ⟨k', hk', h⟩
      · rename_i hk
        constructor
        · rintro (h | ⟨k', hk', h⟩)
          · exact .inl h
          · exact .inr ⟨k', .inr hk', h⟩
        · rintro (h | ⟨k', rfl | hk', h⟩)
          · exact .inl h
          · exact absurd h.2 hk
          · exact .inr ⟨k', hk', h⟩
  rw [bitMap, key, Nat.zero_testBit, Bool.false_or]
  simp only [List.mem_range]

lemma bitMap_xor {π : ℕ → ℕ} {n : ℕ} (hinj : ∀ a < n, ∀ b < n, π a = π b → a = b) (a b : ℕ) :
    bitMap π n (a ^^^ b) = bitMap π n a ^^^ bitMap π n b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitMap, Nat.testBit_xor, testBit_bitMap, testBit_bitMap]
  by_cases h : ∃ k < n, π k = j
  · obtain ⟨k, hk, rfl⟩ := h
    have e : ∀ (c : ℕ), (∃ k' < n, π k' = π k ∧ c.testBit k' = true) ↔ c.testBit k = true :=
      fun c ↦ ⟨fun ⟨k', hk', e, h⟩ ↦ hinj k' hk' k hk e ▸ h, fun h ↦ ⟨k, hk, rfl, h⟩⟩
    simp only [e]
    simp only [Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k <;> rfl
  · have e : ∀ (c : ℕ), ¬ ∃ k' < n, π k' = j ∧ c.testBit k' = true :=
      fun c ⟨k', hk', e, _⟩ ↦ h ⟨k', hk', e⟩
    simp only [e, decide_false, Bool.xor_false]

lemma bitMap_zero (π : ℕ → ℕ) (n : ℕ) : bitMap π n 0 = 0 :=
  Nat.eq_of_testBit_eq fun j ↦ by simp [testBit_bitMap]

lemma lt_two_pow_of_testBit {v n : ℕ} (h : ∀ j, v.testBit j = true → j < n) : v < 2 ^ n :=
  Nat.lt_pow_two_of_testBit v fun j hj ↦ by
    by_contra h'
    have := h j (by simpa using h')
    omega

/-- Renaming back undoes renaming, on masks below `2 ^ n`. -/
lemma bitMap_bitMap {π ρ : ℕ → ℕ} {n : ℕ} (hb : IdxBij n π ρ) {v : ℕ} (hv : v < 2 ^ n) :
    bitMap ρ n (bitMap π n v) = v := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_bitMap, Bool.eq_iff_iff, decide_eq_true_eq]
  simp only [testBit_bitMap, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl, k', hk', rfl, h⟩
    rwa [hb.left k' hk']
  · intro h
    have hj : j < n := by
      by_contra hj
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at h
      cases h
    exact ⟨π j, hb.lt j hj, hb.left j hj, j, hj, rfl, h⟩

lemma xspan_map_bitMap {π : ℕ → ℕ} {n : ℕ} (hinj : ∀ a < n, ∀ b < n, π a = π b → a = b)
    {S : List ℕ} {v : ℕ} (h : XSpan S v) : XSpan (S.map (bitMap π n)) (bitMap π n v) := by
  induction h with
  | zero => rw [bitMap_zero]; exact .zero
  | add hs _ ih => rw [bitMap_xor hinj]; exact .add (List.mem_map_of_mem hs) ih

/-- **Renaming the bits keeps the span**, on masks below `2 ^ n`. -/
lemma xspan_bitMap_iff {π ρ : ℕ → ℕ} {n : ℕ} (hb : IdxBij n π ρ) {S : List ℕ}
    (hS : ∀ x ∈ S, x < 2 ^ n) {v : ℕ} (hv : v < 2 ^ n) :
    XSpan (S.map (bitMap π n)) (bitMap π n v) ↔ XSpan S v := by
  constructor
  · intro h
    have := xspan_map_bitMap (π := ρ) (n := n) (fun a ha b hb' e ↦ hb.symm.inj ha hb' e) h
    rw [List.map_map, bitMap_bitMap hb hv] at this
    refine this.mono fun x hx ↦ ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    simp only [Function.comp, bitMap_bitMap hb (hS y hy)]
    exact hy
  · exact xspan_map_bitMap fun a ha b hb' e ↦ hb.inj ha hb' e

/-- A cycle's mask has only bits of bonds. -/
lemma cycleMask_lt (m : Work) (c : List ℕ) : m.cycleMask c < 2 ^ m.numBonds :=
  lt_two_pow_of_testBit fun j hj ↦ by
    rw [testBit_cycleMask, decide_eq_true_eq, ringBonds_eq_filterMap, List.mem_filterMap] at hj
    obtain ⟨t, -, ht⟩ := hj
    exact bondBetween?_lt ht

end Work

end LeanSMILES.Aromaticity
