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

lemma firstDonor (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {L : List (List ℕ)} (hL : ∀ r ∈ L, w.IsRing r) (i : ℕ) :
    Work.firstDonor w' (rbs w' L) L i = Work.firstDonor w (rbs w L) L i := by
  unfold Work.firstDonor
  cases hf : L.find? (·.contains i) with
  | none => rfl
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hi : i ∈ r := by
      have h1 := List.find?_some hf
      exact List.contains_iff_mem.1 h1
    exact h.ringDonor hwf hnd hnd' hL hr hi _

lemma firstCand (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {L : List (List ℕ)} (hL : ∀ r ∈ L, w.IsRing r) (i : ℕ) :
    Work.firstCand w' (rbs w' L) L i = Work.firstCand w (rbs w L) L i := by
  unfold Work.firstCand
  cases hf : L.find? (·.contains i) with
  | none => rfl
  | some r =>
    have hr := List.mem_of_find?_eq_some hf
    have hi : i ∈ r := by
      have h1 := List.find?_some hf
      exact List.contains_iff_mem.1 h1
    simp only [h.ringDonor hwf hnd hnd' hL hr hi, h.isAromaticCandidate]

/-- **The first pass agrees on a relisted copy**: the same donor types and candidate rings. -/
theorem donorData (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) {R : Array (List ℕ)} (hR : ∀ r ∈ R.toList, w.IsRing r) :
    (w'.donorData R).donor = (w.donorData R).donor ∧
      (w'.donorData R).candRings = (w.donorData R).candRings := by
  have I := donorData_inv w R
  have I' := donorData_inv w' R
  have hN : w'.numAtoms = w.numAtoms := by simp [numAtoms, h.atoms]
  refine ⟨array_ext_of_getElem! (n := w.numAtoms) (by rw [I'.donor_size, hN]) I.donor_size
    fun i hi ↦ ?_, Array.ext' ?_⟩
  · rw [I'.donor i (by rw [hN]; exact hi), I.donor i hi]
    exact h.firstDonor hwf hnd hnd' hR i
  · rw [I'.candRings, I.candRings, hN]
    apply List.filter_congr
    intro r hr
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun i _ ↦ ?_
    rw [h.firstCand hwf hnd hnd' hR i]

/-! ### The second pass -/

lemma count_map_inj {f : ℕ → ℕ} {l : List ℕ} {N : ℕ} (hl : ∀ x ∈ l, x < N)
    (hf : ∀ a < N, ∀ b < N, f a = f b → a = b) {x : ℕ} (hx : x < N) :
    (l.map f).count (f x) = l.count x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.count_cons, List.count_cons,
      ih fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)]
    have ha := hl a List.mem_cons_self
    congr 1
    by_cases e : a = x
    · subst e; simp
    · have : f a ≠ f x := fun h' ↦ e (hf a ha x hx h')
      simp [e, this]

lemma length_filter_contains_map {f : ℕ → ℕ} {l₁ l₂ : List ℕ} {N : ℕ}
    (h₁ : ∀ x ∈ l₁, x < N) (h₂ : ∀ x ∈ l₂, x < N) (hf : ∀ a < N, ∀ b < N, f a = f b → a = b) :
    ((l₁.map f).filter (l₂.map f).contains).length = (l₁.filter l₂.contains).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro x hx
  show (l₂.map f).contains (f x) = l₂.contains x
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ ↦ hf y (h₂ y hy) x (h₁ x hx) e ▸ hy, fun hx' ↦ ⟨x, hx', rfl⟩⟩


end Relisted

section SecondPass

variable {N : ℕ} {π : ℕ → ℕ} {rb rb' : Array (List ℕ)}

/-- `rb'` is `rb` with every bond renumbered by `π`, injective below `N`. -/
structure RbMap (N : ℕ) (π : ℕ → ℕ) (rb rb' : Array (List ℕ)) : Prop where
  size : rb'.size = rb.size
  get : ∀ j : ℕ, rb'[j]! = (rb[j]! : List ℕ).map π
  lt : ∀ j : ℕ, ∀ x ∈ (rb[j]! : List ℕ), x < N
  inj : ∀ a < N, ∀ b < N, π a = π b → a = b

lemma RbMap.fusedNbrs (h : RbMap N π rb rb') : Work.fusedNbrs rb' = Work.fusedNbrs rb := by
  have hp : ∀ i j, fusedPair rb' i j = fusedPair rb i j := fun i j ↦ by
    unfold fusedPair
    rw [h.get, h.get, List.length_map, List.length_map,
      Relisted.length_filter_contains_map (h.lt i) (h.lt j) h.inj]
  rw [fusedNbrs_eq_pairs, fusedNbrs_eq_pairs, h.size]
  congr 1
  funext nbrs q
  simp only [fusedStep, hp]

lemma RbMap.flat (h : RbMap N π rb rb') (cur : List ℕ) :
    cur.flatMap (rb'[·]!) = (cur.flatMap (rb[·]!)).map π := by
  rw [List.map_flatMap]
  exact flatMap_congr_mem cur fun j _ ↦ h.get j

lemma RbMap.flat_lt (h : RbMap N π rb rb') (cur : List ℕ) :
    ∀ x ∈ cur.flatMap (rb[·]!), x < N := fun x hx ↦ by
  obtain ⟨j, -, hx⟩ := List.mem_flatMap.1 hx
  exact h.lt j x hx

lemma mem_groupBonds_sub {numAtoms : ℕ} {rb C : Array (List ℕ)} {d : Array Donor}
    {nbrs : Array (List ℕ)} {cur : List ℕ} {b : ℕ}
    (hb : b ∈ Work.groupBonds numAtoms rb C d nbrs cur) : b ∈ cur.flatMap (rb[·]!) := by
  unfold groupBonds at hb
  dsimp only at hb
  split at hb
  · cases hb
  · split at hb
    · simp only [List.mem_filter, List.mem_mergeSort, List.mem_eraseDups] at hb
      exact hb.1
    · cases hb

/-- **A group's bonds, renumbered.** -/
lemma RbMap.groupBonds (h : RbMap N π rb rb') {numAtoms : ℕ} {C : Array (List ℕ)}
    {d : Array Donor} {nbrs : Array (List ℕ)} (cur : List ℕ) (b' : ℕ) :
    b' ∈ Work.groupBonds numAtoms rb' C d nbrs cur ↔
      ∃ b ∈ Work.groupBonds numAtoms rb C d nbrs cur, π b = b' := by
  unfold Work.groupBonds
  dsimp only
  split
  · simp
  split
  · rw [h.flat]
    simp only [List.mem_filter, List.mem_mergeSort, List.mem_eraseDups, beq_iff_eq]
    have hl := h.flat_lt cur
    constructor
    · rintro ⟨hb, hc⟩
      obtain ⟨b, hbm, rfl⟩ := List.mem_map.1 hb
      exact ⟨b, ⟨hbm, by rw [← Relisted.count_map_inj hl h.inj (hl b hbm)]; exact hc⟩, rfl⟩
    · rintro ⟨b, ⟨hbm, hc⟩, rfl⟩
      exact ⟨List.mem_map_of_mem hbm, by rw [Relisted.count_map_inj hl h.inj (hl b hbm)]; exact hc⟩
  · simp

lemma eraseDups_map_length (h : RbMap N π rb rb') (l : List ℕ) (hl : ∀ x ∈ l, x < N) :
    (l.map π).eraseDups.length = l.eraseDups.length := by
  have hp : (l.map π).eraseDups.Perm (l.eraseDups.map π) :=
    (List.perm_ext_iff_of_nodup (eraseDups_nodup _) ((eraseDups_nodup l).map_on fun a ha b hb e ↦
      h.inj a (hl a (List.mem_eraseDups.1 ha)) b (hl b (List.mem_eraseDups.1 hb)) e)).2 fun x ↦ by
      simp only [List.mem_eraseDups, List.mem_map]
  rw [hp.length_eq, List.length_map]

/-- **A fused system's bonds, renumbered.** -/
lemma RbMap.systemBonds (h : RbMap N π rb rb') {numAtoms : ℕ} {C : Array (List ℕ)}
    {d : Array Donor} {nbrs : Array (List ℕ)} (F : List ℕ) (b' : ℕ) :
    b' ∈ systemBonds numAtoms rb' C d nbrs F ↔
      ∃ b ∈ systemBonds numAtoms rb C d nbrs F, π b = b' := by
  have hnew : ∀ size x', x' ∈ (combinations F.length size).flatMap
        (fun comb ↦ Work.groupBonds numAtoms rb' C d nbrs (comb.map (F[·]!))) ↔
      ∃ x ∈ (combinations F.length size).flatMap
        (fun comb ↦ Work.groupBonds numAtoms rb C d nbrs (comb.map (F[·]!))), π x = x' := by
    intro size x'
    simp only [List.mem_flatMap, h.groupBonds]
    constructor
    · rintro ⟨c, hc, x, hx, rfl⟩; exact ⟨x, ⟨c, hc, hx⟩, rfl⟩
    · rintro ⟨x, ⟨c, hc, hx⟩, rfl⟩; exact ⟨c, hc, x, hx, rfl⟩
  have hnewlt : ∀ size x, x ∈ (combinations F.length size).flatMap
      (fun comb ↦ Work.groupBonds numAtoms rb C d nbrs (comb.map (F[·]!))) → x < N := by
    intro size x hx
    obtain ⟨c, -, hx⟩ := List.mem_flatMap.1 hx
    exact h.flat_lt _ x (mem_groupBonds_sub hx)
  have hall : (F.flatMap (rb'[·]!)).eraseDups.length = (F.flatMap (rb[·]!)).eraseDups.length := by
    rw [h.flat]; exact eraseDups_map_length h _ (h.flat_lt F)
  unfold Work.systemBonds
  dsimp only
  rw [hall]
  set step := fun (r : Array (List ℕ)) (st : List ℕ × List ℕ × Bool) (size : ℕ) ↦
    let (out, doneBonds, stop) := st
    if stop || (size == 3 && 300 < F.length) ||
        (F.flatMap (rb[·]!)).eraseDups.length ≤ doneBonds.length then
      (out, doneBonds, true)
    else
      let new := (combinations F.length size).flatMap fun comb : List ℕ ↦
        Work.groupBonds numAtoms r C d nbrs (comb.map (F[·]!))
      (out ++ new, new.foldl (fun d b ↦ if d.contains b then d else d ++ [b]) doneBonds, false)
    with hstep
  have key : ∀ (sizes : List ℕ) (st st' : List ℕ × List ℕ × Bool),
      (∀ x', x' ∈ st'.1 ↔ ∃ x ∈ st.1, π x = x') → (∀ x', x' ∈ st'.2.1 ↔ ∃ x ∈ st.2.1, π x = x') →
      st.2.1.Nodup → st'.2.1.Nodup → (∀ x ∈ st.2.1, x < N) → st'.2.2 = st.2.2 →
      ∀ x', x' ∈ (sizes.foldl (step rb') st').1 ↔ ∃ x ∈ (sizes.foldl (step rb) st).1, π x = x' := by
    intro sizes
    induction sizes with
    | nil => intro st st' h1 _ _ _ _ _ x; exact h1 x
    | cons size sizes ih =>
      intro st st' h1 h2 hn hn' hl h3
      obtain ⟨o, dn, sp⟩ := st
      obtain ⟨o', dn', sp'⟩ := st'
      simp only at h1 h2 hn hn' hl h3
      subst h3
      have hdl : dn'.length = dn.length := by
        have hp : dn'.Perm (dn.map π) := (List.perm_ext_iff_of_nodup hn' (hn.map_on
          fun a ha b hb e ↦ h.inj a (hl a ha) b (hl b hb) e)).2 fun x ↦ by
          rw [h2 x, List.mem_map]
        rw [hp.length_eq, List.length_map]
      rw [List.foldl_cons, List.foldl_cons]
      simp only [hstep, hdl]
      split
      · exact ih _ _ h1 h2 hn hn' hl rfl
      · obtain ⟨n1, m1⟩ := addDone_spec ((combinations F.length size).flatMap fun comb ↦
          Work.groupBonds numAtoms rb C d nbrs (comb.map (F[·]!))) dn hn
        obtain ⟨n2, m2⟩ := addDone_spec ((combinations F.length size).flatMap fun comb ↦
          Work.groupBonds numAtoms rb' C d nbrs (comb.map (F[·]!))) dn' hn'
        refine ih _ _ (fun x ↦ ?_) (fun x ↦ ?_) n1 n2 (fun x hx ↦ ?_) rfl
        · simp only [List.mem_append, h1 x, hnew size x]
          constructor
          · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
            · exact ⟨y, .inl hy, rfl⟩
            · exact ⟨y, .inr hy, rfl⟩
          · rintro ⟨y, hy | hy, rfl⟩
            · exact .inl ⟨y, hy, rfl⟩
            · exact .inr ⟨y, hy, rfl⟩
        · rw [m2, h2 x, hnew size x]
          simp only [m1]
          constructor
          · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
            · exact ⟨y, .inl hy, rfl⟩
            · exact ⟨y, .inr hy, rfl⟩
          · rintro ⟨y, hy | hy, rfl⟩
            · exact .inl ⟨y, hy, rfl⟩
            · exact .inr ⟨y, hy, rfl⟩
        · rcases (m1 x).1 hx with hx | hx
          · exact hl x hx
          · exact hnewlt size x hx
  exact key _ ([], [], false) ([], [], false) (fun _ ↦ by simp) (fun _ ↦ by simp)
    List.nodup_nil List.nodup_nil (by simp) rfl b'

/-- **The fused systems' bonds, renumbered.** -/
lemma RbMap.fusedBonds (h : RbMap N π rb rb') {numAtoms : ℕ} {C : Array (List ℕ)}
    {d : Array Donor} (b' : ℕ) :
    b' ∈ Work.fusedBonds numAtoms rb' C d ↔ ∃ b ∈ Work.fusedBonds numAtoms rb C d, π b = b' := by
  unfold Work.fusedBonds
  dsimp only
  rw [h.fusedNbrs]
  simp only [List.mem_flatMap, h.systemBonds]
  constructor
  · rintro ⟨F, hF, b, hb, rfl⟩; exact ⟨b, ⟨F, hF, hb⟩, rfl⟩
  · rintro ⟨b, ⟨F, hF, hb⟩, rfl⟩; exact ⟨F, hF, b, hb, rfl⟩

end SecondPass

end LeanSMILES.Aromaticity.Work
