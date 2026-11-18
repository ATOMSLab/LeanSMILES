/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingFacts
public import LeanSMILES.Aromaticity.PerceiveFacts
public import LeanSMILES.Aromaticity.KekuleSim

/-!
# LeanSMILES.Aromaticity.MarkFacts

**At an atom with two bonds, perception marks both or neither** (`Work.mem_aromaticBondList_deg2`):
every ring through the atom takes both of its bonds, so in every group of rings perception tries,
the two bonds occur equally often, and `groupBonds` keeps a bond exactly when it occurs once.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

lemma nodup_filterMap_of {α β : Type*} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ a' ∈ l, ∀ b, b ∈ f a → b ∈ f a' → a = a') →
      (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hnd, h => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hnd
    have ih := nodup_filterMap_of hl fun x hx y hy b hb hb' ↦
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) b hb hb'
    rw [List.filterMap_cons]
    split
    · exact ih
    · rename_i b hb
      refine List.nodup_cons.2 ⟨fun hm ↦ ?_, ih⟩
      obtain ⟨a', ha', hb'⟩ := List.mem_filterMap.1 hm
      have := h a List.mem_cons_self a' (List.mem_cons_of_mem _ ha') b hb hb'
      exact ha (this ▸ ha')

/-- A ring's bonds are listed once each. -/
lemma IsRing.ringBonds_nodup {m : Work} {c : List ℕ} (h : m.IsRing c) : (m.ringBonds c).Nodup := by
  unfold ringBonds
  refine nodup_filterMap_of List.nodup_range ?_
  intro t ht t' ht' k hk hk'
  rw [Option.mem_def] at hk hk'
  rw [List.mem_range] at ht ht'
  have h3 := h.three
  set n := c.length with hn
  have hu : (t + 1) % n < n := Nat.mod_lt _ (by omega)
  have hu' : (t' + 1) % n < n := Nat.mod_lt _ (by omega)
  obtain ⟨-, a1, e⟩ := bondBetween?_spec hk
  obtain ⟨b0, b1, -⟩ := bondBetween?_spec hk'
  have e0 := e _ (touches_of_mem_bondsOf b0)
  have e1 := e _ (touches_of_mem_bondsOf b1)
  rw [getElem!_pos c t' ht', getElem!_pos c t ht, getElem!_pos c _ hu] at e0
  rw [getElem!_pos c _ hu', getElem!_pos c t ht, getElem!_pos c _ hu] at e1
  have inj := fun {x y : ℕ} (hx : x < n) (hy : y < n) (hxy : c[x] = c[y]) ↦
    (List.Nodup.getElem_inj_iff h.nodup (i := x) (j := y) (hi := hx) (hj := hy)).1 hxy
  have s1 := succ_mod ht
  have s2 := succ_mod ht'
  rcases e0 with e0 | e0
  · exact (inj ht' ht e0).symm
  · have i0 := inj ht' hu e0
    rcases e1 with e1 | e1
    · have i1 := inj hu' ht e1
      split_ifs at s1 s2 <;> omega
    · have i1 := inj hu' hu e1
      split_ifs at s1 s2 <;> omega

/-- At an atom with two bonds, a ring through it takes both: each of its bonds is in the ring as
often as the atom is. -/
lemma IsRing.count_deg2 {m : Work} {c : List ℕ} (h : m.IsRing c) {x k : ℕ}
    (hdeg : (m.bondsOf x).length = 2) (hk : k ∈ m.bondsOf x) :
    (m.ringBonds c).count k = if x ∈ c then 1 else 0 := by
  have hnd := h.ringBonds_nodup
  split
  · rename_i hx
    obtain ⟨k₁, k₂, hne, r₁, r₂, a₁, a₂⟩ := h.two_bonds hx
    have hmem : k ∈ m.ringBonds c := by
      have hbnd : (m.bondsOf x).Nodup := (List.nodup_range).filter _
      match hb : m.bondsOf x, hdeg with
      | [y₁, y₂], _ =>
        rw [hb] at hk a₁ a₂ hbnd
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk a₁ a₂
        rcases hk with rfl | rfl <;> rcases a₁ with rfl | rfl <;> rcases a₂ with rfl | rfl <;>
          first | assumption | exact absurd rfl hne
    exact List.count_eq_one_of_mem hnd hmem
  · rename_i hx
    rw [List.count_eq_zero]
    intro hm
    obtain ⟨hlt, hs, hd⟩ := mem_ringBonds hm
    have ht := touches_of_mem_bondsOf hk
    rw [getElem!_pos m.bonds k hlt] at ht
    simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with ht | ht
    · exact hx (ht ▸ hs)
    · exact hx (ht ▸ hd)

/-! ### Through perception's second pass -/

/-- `groupBonds` keeps `k₂` whenever it keeps `k₁`, if the two occur equally often in every
ring. -/
lemma groupBonds_closed {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {donor : Array Donor}
    {nbrs : Array (List ℕ)} {k₁ k₂ : ℕ}
    (hc : ∀ r : ℕ, (rbonds[r]!).count k₁ = (rbonds[r]!).count k₂)
    (cur : List ℕ) (h : k₁ ∈ groupBonds numAtoms rbonds candRings donor nbrs cur) :
    k₂ ∈ groupBonds numAtoms rbonds candRings donor nbrs cur := by
  unfold groupBonds at h ⊢
  split at h
  · cases h
  rename_i hcon
  rw [if_neg hcon]
  dsimp only at h ⊢
  split at h
  · rename_i hh
    rw [if_pos hh]
    have hcnt : ∀ k, (cur.flatMap (rbonds[·]!)).count k =
        (cur.map fun r ↦ (rbonds[r]!).count k).sum :=
      fun k ↦ by rw [List.count_flatMap]; rfl
    have e : (cur.flatMap (rbonds[·]!)).count k₂ = (cur.flatMap (rbonds[·]!)).count k₁ := by
      rw [hcnt, hcnt]; simp [hc]
    simp only [List.mem_filter, List.mem_mergeSort, List.mem_eraseDups, beq_iff_eq] at h ⊢
    refine ⟨?_, by rw [e]; exact h.2⟩
    exact List.count_pos_iff.1 (by rw [e, h.2]; omega)
  · cases h

/-- `systemBonds` keeps `k₂` whenever it keeps `k₁`, if every group does. -/
lemma systemBonds_closed {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {donor : Array Donor}
    {nbrs : Array (List ℕ)} {k₁ k₂ : ℕ}
    (hg : ∀ cur, k₁ ∈ groupBonds numAtoms rbonds candRings donor nbrs cur →
      k₂ ∈ groupBonds numAtoms rbonds candRings donor nbrs cur)
    (fused : List ℕ) (h : k₁ ∈ systemBonds numAtoms rbonds candRings donor nbrs fused) :
    k₂ ∈ systemBonds numAtoms rbonds candRings donor nbrs fused := by
  unfold systemBonds at h ⊢
  revert h
  refine foldl_induction (fun st : List ℕ × List ℕ × Bool ↦ k₁ ∈ st.1 → k₂ ∈ st.1) _ _ _
    (fun h ↦ by cases h) ?_
  rintro ⟨out, done, stop⟩ size - hst
  dsimp only
  split
  · exact hst
  · intro hm
    rw [List.mem_append] at hm ⊢
    rcases hm with hm | hm
    · exact .inl (hst hm)
    · right
      obtain ⟨comb, hcomb, hm⟩ := List.mem_flatMap.1 hm
      exact List.mem_flatMap.2 ⟨comb, hcomb, hg _ hm⟩

/-- **At an atom with two bonds, perception marks both or neither.** -/
theorem mem_aromaticBondList_deg2 (w : Work) (rings : Array (List ℕ))
    (hr : ∀ ring ∈ rings.toList, w.IsRing ring) {x k₁ k₂ : ℕ}
    (hdeg : (w.bondsOf x).length = 2) (h₁ : k₁ ∈ w.bondsOf x) (h₂ : k₂ ∈ w.bondsOf x)
    (hk : k₁ ∈ w.aromaticBondList rings) : k₂ ∈ w.aromaticBondList rings := by
  unfold aromaticBondList fusedBonds at hk ⊢
  obtain ⟨-, hcr⟩ := ringInv_donorData w rings
  have hc : ∀ r : ℕ, (((w.donorData rings).candRings.map w.ringBonds)[r]!).count k₁ =
      (((w.donorData rings).candRings.map w.ringBonds)[r]!).count k₂ := by
    intro r
    by_cases hlt : r < (w.donorData rings).candRings.size
    · rw [getElem!_pos _ r (by simpa using hlt), Array.getElem_map]
      have hring := hr _ (hcr _ (Array.getElem_mem hlt)).1
      rw [hring.count_deg2 hdeg h₁, hring.count_deg2 hdeg h₂]
    · rw [getElem!_neg _ r (by simpa using hlt)]
      rfl
  obtain ⟨fused, hf, hm⟩ := List.mem_flatMap.1 hk
  exact List.mem_flatMap.2 ⟨fused, hf, systemBonds_closed (groupBonds_closed hc) fused hm⟩

end LeanSMILES.Aromaticity.Work
