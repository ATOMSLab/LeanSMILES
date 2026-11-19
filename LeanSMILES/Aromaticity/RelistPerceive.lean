/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Relist

/-!
# LeanSMILES.Aromaticity.RelistPerceive

Perception on a relisted copy

Over the same rings, a relisted copy gets the same donor types (`Work.Relisted.donorType`): the
only thing read in bond order is the first exocyclic multiple bond, and an atom of a ring with at
most three bonds has at most one; with more it gets no donor type at all. So the first pass agrees
(`Work.Relisted.donorData`), Hückel's rule picks the same groups, the bonds marked aromatic are the
same bonds renumbered (`Work.Relisted.mem_aromaticBondList`), and perception keeps the relisting
(`Work.Relisted.setAromaticity`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- `find?` on two orderings of a list where at most one element passes. -/
lemma find?_perm_of_unique {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool)
    (hu : ∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) : l.find? p = l'.find? p := by
  cases h1 : l.find? p with
  | none =>
    cases h2 : l'.find? p with
    | none => rfl
    | some b =>
      exfalso
      have := List.find?_eq_none.1 h1 b (h.mem_iff.2 (List.mem_of_find?_eq_some h2))
      exact this (List.find?_some h2)
  | some a =>
    have ha := List.mem_of_find?_eq_some h1
    have hpa := List.find?_some h1
    cases h2 : l'.find? p with
    | none =>
      exact absurd hpa (List.find?_eq_none.1 h2 a (h.mem_iff.1 ha))
    | some b =>
      have hb := h.mem_iff.2 (List.mem_of_find?_eq_some h2)
      rw [hu a ha b hb hpa (List.find?_some h2)]

namespace Relisted

variable {w w' : Work} {π ρ : ℕ → ℕ}

lemma ringBonds (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {r : List ℕ} (hr : w.IsRing r) :
    w'.ringBonds r = (w.ringBonds r).map π := by
  have := (h.workIso hwf hnd hnd').ringBonds hwf hr
  rwa [List.map_id] at this

lemma lt_of_mem_ringBonds' {x : Work} {r : List ℕ} {k : ℕ} (hk : k ∈ x.ringBonds r) :
    k < x.bonds.size := lt_of_mem_ringBonds hk

/-- The ring bonds of a list of rings, renumbered. -/
lemma mem_ringBondSet (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {L : List (List ℕ)} (hL : ∀ r ∈ L, w.IsRing r) {k : ℕ}
    (hk : k < w.bonds.size) :
    (π k ∈ (L.flatMap w'.ringBonds).eraseDups) ↔ k ∈ (L.flatMap w.ringBonds).eraseDups := by
  rw [List.mem_eraseDups, List.mem_eraseDups, List.mem_flatMap, List.mem_flatMap]
  constructor
  · rintro ⟨r, hr, hk'⟩
    rw [h.ringBonds hwf hnd hnd' (hL r hr), List.mem_map] at hk'
    obtain ⟨k0, hk0, e⟩ := hk'
    rw [h.bij.inj (lt_of_mem_ringBonds hk0) hk e] at hk0
    exact ⟨r, hr, hk0⟩
  · rintro ⟨r, hr, hk'⟩
    exact ⟨r, hr, by rw [h.ringBonds hwf hnd hnd' (hL r hr)]; exact List.mem_map_of_mem hk'⟩

lemma hasMultipleBond (h : Relisted w w' π ρ) (i : ℕ) :
    w'.hasMultipleBond i = w.hasMultipleBond i := by
  have e : ∀ x : Work, x.hasMultipleBond i = (x.kindsAt i).any isMultiple := fun x ↦ by
    simp only [Work.hasMultipleBond, kindsAt, List.any_map]; rfl
  rw [e, e, (h.kindsAt_perm i).any_eq']

/-- **An atom of a ring with at most three bonds has at most one bond off the rings.** -/
lemma off_ring_unique {x : Work} (hwf : x.WF) {B : List ℕ} {r : List ℕ} (hr : x.IsRing r)
    (hrB : ∀ k ∈ x.ringBonds r, k ∈ B) {i : ℕ} (hi : i ∈ r) (hdeg : (x.bondsOf i).length ≤ 3)
    (p : ℕ → Bool) (hp : ∀ k, p k = true → k ∉ B) :
    ∀ a ∈ x.neighbors i, ∀ b ∈ x.neighbors i, p a.1 = true → p b.1 = true → a = b := by
  intro a ha b hb hpa hpb
  obtain ⟨ka, hka, rfl⟩ := List.mem_map.1 ha
  obtain ⟨kb, hkb, rfl⟩ := List.mem_map.1 hb
  by_cases e : ka = kb
  · subst e; rfl
  exfalso
  obtain ⟨k₁, k₂, h12, r₁, r₂, a₁, a₂⟩ := hr.two_bonds hi
  have na := hp ka hpa
  have nb := hp kb hpb
  have hnd : [k₁, k₂, ka, kb].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true]
    refine ⟨?_, ?_, e, by simp⟩
    · rintro (h' | h' | h')
      · exact h12 h'
      · exact na (h' ▸ hrB _ r₁)
      · exact nb (h' ▸ hrB _ r₁)
    · rintro (h' | h')
      · exact na (h' ▸ hrB _ r₂)
      · exact nb (h' ▸ hrB _ r₂)
  have := (List.subperm_of_subset hnd (by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> assumption)).length_le
  simp at this
  omega

variable (w w') in
/-- The ring bonds of a list of rings. -/
abbrev rbs (x : Work) (L : List (List ℕ)) : List ℕ := (L.flatMap x.ringBonds).eraseDups

/-- **Over the same rings, a relisted copy gives an atom of them the same donor type.** -/
lemma donorType (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {L : List (List ℕ)} (hL : ∀ r ∈ L, w.IsRing r) {r : List ℕ}
    (hr : r ∈ L) {i : ℕ} (hi : i ∈ r) :
    w'.donorType (rbs w' L) i = w.donorType (rbs w L) i := by
  have hc : ∀ k < w.bonds.size, (rbs w' L).contains (π k) = (rbs w L).contains k :=
    fun k hk ↦ by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
      exact h.mem_ringBondSet hwf hnd hnd' hL hk
  have hlt : ∀ k ∈ w.bondsOf i, k < w.bonds.size := fun k hk ↦ by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  have hany : ((w'.bondsOf i).any fun k ↦
        (rbs w' L).contains k && isMultiple (w'.bonds[k]! : WBond).kind) =
      (w.bondsOf i).any fun k ↦ (rbs w L).contains k && isMultiple (w.bonds[k]! : WBond).kind := by
    rw [(h.bondsOf_perm i).any_eq', List.any_map]
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    refine exists_congr fun k ↦ and_congr_right fun hk ↦ ?_
    simp only [Function.comp_apply, hc k (hlt k hk), h.kind k (hlt k hk)]
  by_cases hneg : w.countAtomElec i < 0
  · have e : ∀ (x : Work) (B : List ℕ), x.countAtomElec i < 0 → x.donorType B i = .none :=
      fun x B hx ↦ by unfold Work.donorType; simp [Id.run, hx]; rfl
    rw [e w _ hneg, e w' _ (by rw [h.countAtomElec]; exact hneg)]
  -- at most three bonds, so at most one off the rings
  have hdeg : (w.bondsOf i).length ≤ 3 := by
    by_contra hd
    apply hneg
    rw [countAtomElec_eq_loc]
    exact elec_neg_of_degree (by rw [← degree_eq_loc]; unfold Work.degree; omega)
  have hex : w'.exocyclicMultiple? (rbs w' L) i = w.exocyclicMultiple? (rbs w L) i := by
    unfold exocyclicMultiple?
    set p : ℕ × ℕ → Bool := fun e ↦
      !(rbs w L).contains e.1 && isMultiple (w.bonds[e.1]! : WBond).kind
    set p' : ℕ × ℕ → Bool := fun e ↦
      !(rbs w' L).contains e.1 && isMultiple (w'.bonds[e.1]! : WBond).kind
    have hu := off_ring_unique hwf (B := rbs w L) (hL r hr)
      (fun k hk ↦ List.mem_eraseDups.2 (List.mem_flatMap.2 ⟨r, hr, hk⟩)) hi hdeg
      (fun k ↦ !(rbs w L).contains k && isMultiple (w.bonds[k]! : WBond).kind)
      (fun k hk hm ↦ by
        have hcm : (rbs w L).contains k = true := List.contains_iff_mem.2 hm
        simp only [hcm] at hk
        cases hk)
    have hg : ∀ x ∈ w.neighbors i, p' (π x.1, x.2) = p x := fun x hx ↦ by
      have hx1 : x.1 < w.bonds.size := by
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx; exact hlt k hk
      simp only [p, p', hc _ hx1, h.kind _ hx1]
    have e1 : (w'.neighbors i).find? p' =
        ((w.neighbors i).map fun e ↦ (π e.1, e.2)).find? p' := by
      refine (find?_perm_of_unique (h.neighbors_perm hwf i).symm p' ?_).symm
      intro a ha b hb hpa hpb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
      rw [hg x hx] at hpa
      rw [hg y hy] at hpb
      rw [hu x hx y hy hpa hpb]
    have e2 : ((w.neighbors i).map fun e ↦ (π e.1, e.2)).find? p' =
        ((w.neighbors i).find? p).map fun e ↦ (π e.1, e.2) := by
      rw [List.find?_map]
      congr 1
      exact find?_congr_mem fun x hx ↦ by simp only [Function.comp_apply, hg x hx]
    show ((w'.neighbors i).find? p').map (·.2) = ((w.neighbors i).find? p).map (·.2)
    rw [e1, e2, Option.map_map]
    rfl
  unfold Work.donorType
  simp only [Id.run, hex, h.countAtomElec, h.atom, hany, h.cachedValence, h.degree]

lemma ringDonor (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {L : List (List ℕ)} (hL : ∀ r ∈ L, w.IsRing r) {r : List ℕ}
    (hr : r ∈ L) {i : ℕ} (hi : i ∈ r) (len : ℕ) :
    w'.ringDonor (rbs w' L) len i = w.ringDonor (rbs w L) len i := by
  simp only [Work.ringDonor, h.donorType hwf hnd hnd' hL hr hi, h.atom, h.degree,
    h.hasMultipleBond]

end Relisted

end LeanSMILES.Aromaticity.Work
