/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Passes

/-!
# LeanSMILES.Aromaticity.Congruence

Two working copies that differ only in which of some bonds `F` are single and which double, every
atom keeping its sum of bond orders (`Work.Swapped`): another Kekulé structure of the same atoms.
Every quantity aromaticity perception reads at an atom is a function of the multiset of bond kinds
there, which the swap keeps (`Work.Swapped.perm_map`), so the two copies have the same hydrogen
counts, valences, donor types and candidacies, and the same rings.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A relation kept by every pair of steps of two left folds over the same list holds of their
results. -/
theorem foldl_sim {α β γ : Type*} (R : β → γ → Prop) (f : β → α → β) (g : γ → α → γ) :
    ∀ (l : List α) (b : β) (c : γ), R b c → (∀ b c a, a ∈ l → R b c → R (f b a) (g c a)) →
      R (l.foldl f b) (l.foldl g c)
  | [], _, _, h, _ => h
  | a :: l, b, c, h, hf =>
    foldl_sim R f g l (f b a) (g c a) (hf b c a List.mem_cons_self h)
      fun b' c' a' ha' h' ↦ hf b' c' a' (List.mem_cons_of_mem _ ha') h'

/-- `find?` with two predicates that agree on the list. -/
theorem find?_congr_mem {α : Type*} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find?_congr_mem fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

/-- `any` does not see the order of a list. -/
theorem _root_.List.Perm.any_eq' {α : Type*} {l l' : List α} (h : l.Perm l') (p : α → Bool) :
    l.any p = l'.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  exact ⟨fun ⟨a, ha, hp⟩ ↦ ⟨a, h.mem_iff.mp ha, hp⟩, fun ⟨a, ha, hp⟩ ↦ ⟨a, h.mem_iff.mpr ha, hp⟩⟩

/-- Single or double. -/
def IsSD (x : BondKind) : Prop := x = .single ∨ x = .double

/-- A list of single and double bonds: twice the sum of its orders is twice its length plus
twice its number of double bonds. -/
lemma sum_halfOrder_of_sd : ∀ {L : List BondKind}, (∀ x ∈ L, IsSD x) →
    (L.map halfOrder).sum = 2 * L.length + 2 * L.count .double
  | [], _ => rfl
  | x :: L, h => by
    have ih := sum_halfOrder_of_sd fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    rcases h x List.mem_cons_self with rfl | rfl <;> simp [ih, halfOrder] <;> omega

/-- A list of single and double bonds: its singles and doubles make up its length. -/
lemma count_single_add_count_double : ∀ {L : List BondKind}, (∀ x ∈ L, IsSD x) →
    L.count .single + L.count .double = L.length
  | [], _ => rfl
  | x :: L, h => by
    have ih := count_single_add_count_double fun y hy ↦ h y (List.mem_cons_of_mem _ hy)
    rcases h x List.mem_cons_self with rfl | rfl <;> simp <;> omega

/-- Two lists of single and double bonds of one length and one sum of orders are permutations of
each other. -/
lemma perm_of_sd {L L' : List BondKind} (hl : L.length = L'.length) (h : ∀ x ∈ L, IsSD x)
    (h' : ∀ x ∈ L', IsSD x) (hs : (L.map halfOrder).sum = (L'.map halfOrder).sum) :
    L.Perm L' := by
  have hd : L.count .double = L'.count .double := by
    rw [sum_halfOrder_of_sd h, sum_halfOrder_of_sd h'] at hs
    omega
  have hs' : L.count .single = L'.count .single := by
    have := count_single_add_count_double h
    have := count_single_add_count_double h'
    omega
  rw [List.perm_iff_count]
  intro x
  by_cases hx1 : x = .single
  · subst hx1; exact hs'
  by_cases hx2 : x = .double
  · subst hx2; exact hd
  have n1 : x ∉ L := fun hm ↦ (h x hm).elim hx1 hx2
  have n2 : x ∉ L' := fun hm ↦ (h' x hm).elim hx1 hx2
  rw [List.count_eq_zero_of_not_mem n1, List.count_eq_zero_of_not_mem n2]

namespace Work

/-- The kind of bond `k`, read with `!`. -/
lemma kind?_eq_of_lt (w : Work) {k : ℕ} (hk : k < w.bonds.size) :
    w.kind? k = some w.bonds[k]!.kind := by
  simp [kind?, getElem!_def, Array.getElem?_eq_getElem hk]

/-- Two copies whose bonds join the same atoms: read with `!`, each bond has the same ends. -/
lemma ends_getElem! {w w' : Work} (hs : w'.bonds.size = w.bonds.size)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) (k : ℕ) :
    w'.bonds[k]!.src = w.bonds[k]!.src ∧ w'.bonds[k]!.dst = w.bonds[k]!.dst := by
  have := he k
  by_cases hk : k < w.bonds.size
  · have hk' : k < w'.bonds.size := hs ▸ hk
    simp only [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem hk', Option.map_some,
      Option.some.injEq, Prod.mk.injEq] at this
    simp [getElem!_def, Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem hk', this]
  · have hk' : ¬ k < w'.bonds.size := hs ▸ hk
    simp [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt hk),
      Array.getElem?_eq_none (Nat.le_of_not_lt hk')]

/-- `w'` is `w` with some of the bonds `F` switched between single and double: the same atoms,
the same bonds but for the kinds of `F`, which are single or double in both, and every atom with
the same sum of bond orders. -/
structure Swapped (F : ℕ → Bool) (w w' : Work) : Prop where
  /-- The same atoms. -/
  atoms : w'.atoms = w.atoms
  /-- As many bonds. -/
  size : w'.bonds.size = w.bonds.size
  /-- Each bond joins the same atoms. -/
  ends : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
    w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))
  /-- Off `F`, the same kinds. -/
  kind : ∀ k, F k = false → w'.kind? k = w.kind? k
  /-- On `F`, single or double in both. -/
  sd : ∀ k, F k = true → (∃ x, w.kind? k = some x ∧ IsSD x) ∧ ∃ x, w'.kind? k = some x ∧ IsSD x
  /-- Every atom keeps its sum of bond orders. -/
  sum : ∀ i, w'.bondHalfSum i = w.bondHalfSum i

variable {F : ℕ → Bool} {w w' : Work}

namespace Swapped

lemma src (h : Swapped F w w') (k : ℕ) : w'.bonds[k]!.src = w.bonds[k]!.src :=
  (ends_getElem! h.size h.ends k).1

lemma dst (h : Swapped F w w') (k : ℕ) : w'.bonds[k]!.dst = w.bonds[k]!.dst :=
  (ends_getElem! h.size h.ends k).2

lemma numAtoms_eq (h : Swapped F w w') : w'.numAtoms = w.numAtoms := by
  simp [numAtoms, h.atoms]

lemma numBonds_eq (h : Swapped F w w') : w'.numBonds = w.numBonds := h.size

lemma bondsOf_eq (h : Swapped F w w') : w'.bondsOf = w.bondsOf := by
  funext i
  simp only [bondsOf, h.numBonds_eq, WBond.touches, h.src, h.dst]

lemma neighbors_eq (h : Swapped F w w') : w'.neighbors = w.neighbors := by
  funext i
  simp only [neighbors, h.bondsOf_eq, WBond.other, h.src, h.dst]

lemma degree_eq (h : Swapped F w w') : w'.degree = w.degree := by
  funext i
  simp only [degree, h.bondsOf_eq]

lemma bondBetween?_eq (h : Swapped F w w') : w'.bondBetween? = w.bondBetween? := by
  funext i j
  simp only [bondBetween?, h.numBonds_eq, h.src, h.dst]

lemma ringBonds_eq (h : Swapped F w w') : w'.ringBonds = w.ringBonds := by
  funext ring
  simp only [ringBonds, h.bondBetween?_eq]

/-- **The same rings**: ring perception reads only which atoms the bonds join. -/
lemma relevantCycles_eq (h : Swapped F w w') : w'.relevantCycles = w.relevantCycles := by
  simp only [relevantCycles, candidateCycles,
    bfs_congr h.neighbors_eq h.numAtoms_eq h.numBonds_eq, allShortestPaths, cycleMask,
    h.neighbors_eq, h.bondBetween?_eq, h.numAtoms_eq]

lemma mem_bondsOf_lt {i k : ℕ} (hk : k ∈ w.bondsOf i) : k < w.bonds.size := by
  simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk
  exact hk.1

lemma kind_eq (h : Swapped F w w') {k : ℕ} (hk : k < w.bonds.size) (hF : F k = false) :
    w'.bonds[k]!.kind = w.bonds[k]!.kind := by
  have := h.kind k hF
  rw [kind?_eq_of_lt w hk, kind?_eq_of_lt w' (h.size ▸ hk)] at this
  exact Option.some.inj this

lemma sd_left (h : Swapped F w w') {k : ℕ} (hk : k < w.bonds.size) (hF : F k = true) :
    IsSD w.bonds[k]!.kind := by
  obtain ⟨⟨x, hx, hsd⟩, -⟩ := h.sd k hF
  rw [kind?_eq_of_lt w hk] at hx
  exact Option.some.inj hx ▸ hsd

lemma sd_right (h : Swapped F w w') {k : ℕ} (hk : k < w.bonds.size) (hF : F k = true) :
    IsSD w'.bonds[k]!.kind := by
  obtain ⟨-, ⟨x, hx, hsd⟩⟩ := h.sd k hF
  rw [kind?_eq_of_lt w' (h.size ▸ hk)] at hx
  exact Option.some.inj hx ▸ hsd

/-- **The bonds at an atom have the same kinds, up to order.**  Anything read off them that sees
a bond of `F` only through its kind is the same up to order. -/
theorem perm_map (h : Swapped F w w') {β : Type*} (i : ℕ) (g : ℕ → BondKind → β)
    (G : BondKind → β) (hg : ∀ k, F k = true → g k = G) :
    ((w'.bondsOf i).map fun k ↦ g k w'.bonds[k]!.kind).Perm
      ((w.bondsOf i).map fun k ↦ g k w.bonds[k]!.kind) := by
  rw [h.bondsOf_eq]
  set ks := w.bondsOf i with hks
  have hp : (ks.filter F ++ ks.filter (fun k ↦ !F k)).Perm ks := List.filter_append_perm F ks
  -- off `F`: the same
  have hN : (ks.filter (fun k ↦ !F k)).map (fun k ↦ g k w'.bonds[k]!.kind) =
      (ks.filter (fun k ↦ !F k)).map (fun k ↦ g k w.bonds[k]!.kind) := by
    refine List.map_congr_left fun k hk ↦ ?_
    simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
    rw [h.kind_eq (mem_bondsOf_lt hk.1) hk.2]
  -- on `F`: single and double bonds with the same sum
  have hsum : ((ks.filter F).map fun k ↦ halfOrder w'.bonds[k]!.kind).sum =
      ((ks.filter F).map fun k ↦ halfOrder w.bonds[k]!.kind).sum := by
    have h1 := h.sum i
    simp only [bondHalfSum, h.bondsOf_eq] at h1
    rw [← hks] at h1
    have e : ∀ (f : ℕ → ℕ), (ks.map f).sum =
        ((ks.filter F).map f).sum + ((ks.filter fun k ↦ !F k).map f).sum := fun f ↦ by
      rw [← List.sum_append, ← List.map_append, (hp.map f).sum_eq]
    rw [e (fun k ↦ halfOrder w'.bonds[k]!.kind), e (fun k ↦ halfOrder w.bonds[k]!.kind)] at h1
    have h2 : ((ks.filter fun k ↦ !F k).map fun k ↦ halfOrder w'.bonds[k]!.kind) =
        ((ks.filter fun k ↦ !F k).map fun k ↦ halfOrder w.bonds[k]!.kind) := by
      refine List.map_congr_left fun k hk ↦ ?_
      simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hk
      rw [h.kind_eq (mem_bondsOf_lt hk.1) hk.2]
    rw [h2] at h1
    omega
  have hF : ((ks.filter F).map fun k ↦ w'.bonds[k]!.kind).Perm
      ((ks.filter F).map fun k ↦ w.bonds[k]!.kind) := by
    refine perm_of_sd (by simp) ?_ ?_ (by simpa [List.map_map, Function.comp_def] using hsum)
    · simp only [List.mem_map, List.mem_filter]
      rintro _ ⟨k, ⟨hk, hFk⟩, rfl⟩
      exact h.sd_right (mem_bondsOf_lt hk) hFk
    · simp only [List.mem_map, List.mem_filter]
      rintro _ ⟨k, ⟨hk, hFk⟩, rfl⟩
      exact h.sd_left (mem_bondsOf_lt hk) hFk
  have hFg : ((ks.filter F).map fun k ↦ g k w'.bonds[k]!.kind).Perm
      ((ks.filter F).map fun k ↦ g k w.bonds[k]!.kind) := by
    have e : ∀ (f : ℕ → BondKind), (ks.filter F).map (fun k ↦ g k (f k)) =
        ((ks.filter F).map f).map G := fun f ↦ by
      rw [List.map_map]
      refine List.map_congr_left fun k hk ↦ ?_
      simp only [List.mem_filter] at hk
      simp [hg k hk.2]
    rw [e (fun k ↦ w'.bonds[k]!.kind), e (fun k ↦ w.bonds[k]!.kind)]
    exact hF.map G
  refine (hp.map _).symm.trans ?_
  rw [List.map_append]
  refine (hFg.append (List.Perm.of_eq hN)).trans ?_
  rw [← List.map_append]
  exact hp.map _

/-- Whether some bond at an atom has a kind with a property does not change. -/
lemma any_eq (h : Swapped F w w') (i : ℕ) (p : BondKind → Bool) :
    (w'.bondsOf i).any (fun k ↦ p w'.bonds[k]!.kind) =
      (w.bondsOf i).any (fun k ↦ p w.bonds[k]!.kind) := by
  have := (h.perm_map i (fun _ x ↦ p x) p fun _ _ ↦ rfl).any_eq' id
  simpa [List.any_map, Function.comp_def] using this

/-- Whether some bond of `rbs` at an atom has a kind with a property does not change, when `rbs`
contains the bonds of `F`. -/
lemma any_ring_eq (h : Swapped F w w') (rbs : List ℕ) (hF : ∀ k, F k = true → rbs.contains k = true)
    (i : ℕ) (p : BondKind → Bool) :
    (w'.bondsOf i).any (fun k ↦ rbs.contains k && p w'.bonds[k]!.kind) =
      (w.bondsOf i).any (fun k ↦ rbs.contains k && p w.bonds[k]!.kind) := by
  have := (h.perm_map i (fun k x ↦ rbs.contains k && p x) p
    fun k hk ↦ funext fun x ↦ by
      have hm : k ∈ rbs := by simpa using hF k hk
      simp [hm]).any_eq' id
  simpa [List.any_map, Function.comp_def] using this

/-- The number of bonds at an atom whose kind has a property does not change. -/
lemma length_filter_eq (h : Swapped F w w') (i : ℕ) (p : BondKind → Bool) :
    ((w'.bondsOf i).filter (fun k ↦ p w'.bonds[k]!.kind)).length =
      ((w.bondsOf i).filter (fun k ↦ p w.bonds[k]!.kind)).length := by
  have := (h.perm_map i (fun _ x ↦ p x) p fun _ _ ↦ rfl).countP_eq id
  simpa [List.countP_map, List.countP_eq_length_filter, List.filter_map, Function.comp_def]
    using this

lemma isAromaticAtom_eq (h : Swapped F w w') : w'.isAromaticAtom = w.isAromaticAtom := by
  funext i
  simp only [isAromaticAtom, h.atoms, h.any_eq i (· == .aromatic)]

lemma explicitValence_eq (h : Swapped F w w') : w'.explicitValence = w.explicitValence := by
  funext i
  simp only [explicitValence, h.atoms, h.sum, h.isAromaticAtom_eq]

lemma implicitHs_eq (h : Swapped F w w') : w'.implicitHs = w.implicitHs := by
  funext i
  simp only [implicitHs, h.atoms, h.explicitValence_eq, h.isAromaticAtom_eq]

lemma totalHs_eq (h : Swapped F w w') : w'.totalHs = w.totalHs := by
  funext i
  simp only [totalHs, h.atoms, h.implicitHs_eq]

lemma kekuleValence_eq (h : Swapped F w w') : w'.kekuleValence = w.kekuleValence := by
  funext i
  simp only [kekuleValence, h.atoms, h.sum]

lemma cachedValence_eq (h : Swapped F w w') : w'.cachedValence = w.cachedValence := by
  funext i
  simp only [cachedValence, h.atoms, h.kekuleValence_eq]

lemma cachedTotalHs_eq (h : Swapped F w w') : w'.cachedTotalHs = w.cachedTotalHs := by
  funext i
  simp only [cachedTotalHs, h.atoms]

lemma countAtomElec_eq (h : Swapped F w w') : w'.countAtomElec = w.countAtomElec := by
  funext i
  simp only [countAtomElec, h.atoms, h.degree_eq, h.cachedTotalHs_eq, h.cachedValence_eq]

lemma exocyclicMultiple?_eq (h : Swapped F w w') (rbs : List ℕ)
    (hF : ∀ k, F k = true → rbs.contains k = true) :
    w'.exocyclicMultiple? rbs = w.exocyclicMultiple? rbs := by
  funext i
  simp only [exocyclicMultiple?, h.neighbors_eq]
  congr 1
  refine find?_congr_mem fun ⟨k, j⟩ hkj ↦ ?_
  simp only [neighbors, List.mem_map] at hkj
  obtain ⟨k', hk', he⟩ := hkj
  cases he
  cases hFk : F k
  · rw [h.kind_eq (mem_bondsOf_lt hk') hFk]
  · have hm : k ∈ rbs := by simpa using hF k hFk
    simp [hm]

lemma donorType_eq (h : Swapped F w w') (rbs : List ℕ)
    (hF : ∀ k, F k = true → rbs.contains k = true) :
    w'.donorType rbs = w.donorType rbs := by
  funext i
  simp only [donorType, h.atoms, h.countAtomElec_eq, h.exocyclicMultiple?_eq rbs hF,
    h.any_ring_eq rbs hF i isMultiple, h.cachedValence_eq, h.degree_eq]

lemma isAromaticCandidate_eq (h : Swapped F w w') :
    w'.isAromaticCandidate = w.isAromaticCandidate := by
  funext i d
  simp only [isAromaticCandidate, h.atoms, h.cachedValence_eq, h.degree_eq,
    h.length_filter_eq i isMultiple]

lemma hasMultipleBond_eq (h : Swapped F w w') : w'.hasMultipleBond = w.hasMultipleBond := by
  funext i
  simp only [hasMultipleBond, h.any_eq i isMultiple]

lemma ringDonor_eq (h : Swapped F w w') (rbs : List ℕ)
    (hF : ∀ k, F k = true → rbs.contains k = true) :
    w'.ringDonor rbs = w.ringDonor rbs := by
  funext len i
  simp only [ringDonor, h.donorType_eq rbs hF, h.atoms, h.degree_eq, h.hasMultipleBond_eq]

lemma radicalCount_eq (h : Swapped F w w') : w'.radicalCount = w.radicalCount := by
  funext i
  simp only [radicalCount, h.atoms, h.kekuleValence_eq]

/-- Replacing the atoms of both copies by the same atoms keeps the swap. -/
lemma withAtoms (h : Swapped F w w') (A : Array WAtom) :
    Swapped F { w with atoms := A } { w' with atoms := A } :=
  ⟨rfl, h.size, h.ends, h.kind, h.sd, h.sum⟩

lemma freezeHs (h : Swapped F w w') : Swapped F w.freezeHs w'.freezeHs := by
  have e : w'.freezeHs = { w' with atoms := w.freezeHs.atoms } := by
    simp only [Work.freezeHs, numAtoms, h.atoms, h.totalHs_eq]
  rw [e]
  exact h.withAtoms _

lemma cacheValences (h : Swapped F w w') : Swapped F w.cacheValences w'.cacheValences := by
  have e : w'.cacheValences = { w' with atoms := w.cacheValences.atoms } := by
    simp only [Work.cacheValences, numAtoms, h.atoms, h.explicitValence_eq, h.implicitHs_eq,
      h.isAromaticAtom_eq]
  rw [e]
  exact h.withAtoms _

lemma radicalStep (h : Swapped F w w') (i : ℕ) :
    Swapped F (w.radicalStep i) (w'.radicalStep i) := by
  unfold Work.radicalStep
  simp only [h.atoms]
  split
  · exact h
  · have e : w'.modifyAtom i ({ · with radicals := w'.radicalCount i }) =
        { w' with atoms := (w.modifyAtom i ({ · with radicals := w.radicalCount i })).atoms } := by
      simp only [modifyAtom, h.atoms, h.radicalCount_eq]
    rw [e]
    exact h.withAtoms _

lemma assignRadicals (h : Swapped F w w') : Swapped F w.assignRadicals w'.assignRadicals := by
  unfold Work.assignRadicals
  rw [show w'.numAtoms = w.numAtoms from h.numAtoms_eq]
  exact foldl_sim (Swapped F) _ _ _ _ _ h fun _ _ i _ hb ↦ hb.radicalStep i

lemma donorData_eq (h : Swapped F w w') (rings : Array (List ℕ))
    (hF : ∀ k, F k = true → k ∈ rings.toList.flatMap w.ringBonds) :
    w'.donorData rings = w.donorData rings := by
  have hF' : ∀ k, F k = true → ((rings.toList.flatMap w.ringBonds).eraseDups).contains k = true :=
    fun k hk ↦ by simpa [List.mem_eraseDups] using hF k hk
  have hatom : w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) =
      w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) := by
    funext len p i
    simp only [Work.donorAtomStep, h.ringDonor_eq _ hF', h.isAromaticCandidate_eq]
  have hstep : w'.donorRingStep ((rings.toList.flatMap w.ringBonds).eraseDups) =
      w.donorRingStep ((rings.toList.flatMap w.ringBonds).eraseDups) := by
    funext s ring
    simp only [Work.donorRingStep, hatom]
  simp only [Work.donorData, h.ringBonds_eq, hstep, h.numAtoms_eq]

lemma aromaticBondList_eq (h : Swapped F w w') (rings : Array (List ℕ))
    (hF : ∀ k, F k = true → k ∈ rings.toList.flatMap w.ringBonds) :
    w'.aromaticBondList rings = w.aromaticBondList rings := by
  simp only [Work.aromaticBondList, h.donorData_eq rings hF, h.numAtoms_eq, h.ringBonds_eq]

end Swapped

/-- The relation the mark fold of `setAromaticity` keeps between two swapped copies: the same
atoms, the same bonds but for the kinds of `F`, which are equal or single or double in both. -/
structure KindRel (F : ℕ → Bool) (w w' : Work) : Prop where
  /-- The same atoms. -/
  atoms : w'.atoms = w.atoms
  /-- As many bonds. -/
  size : w'.bonds.size = w.bonds.size
  /-- Each bond joins the same atoms. -/
  ends : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
    w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))
  /-- Off `F`, the same kinds; on `F`, the same or single or double in both. -/
  kind : ∀ k, w'.kind? k = w.kind? k ∨
    F k = true ∧ (∃ x, w.kind? k = some x ∧ IsSD x) ∧ ∃ x, w'.kind? k = some x ∧ IsSD x

lemma Swapped.kindRel (h : Swapped F w w') : KindRel F w w' := by
  refine ⟨h.atoms, h.size, h.ends, fun k ↦ ?_⟩
  cases hk : F k
  · exact .inl (h.kind k hk)
  · exact .inr ⟨rfl, h.sd k hk⟩

namespace KindRel

lemma src (h : KindRel F w w') (k : ℕ) : w'.bonds[k]!.src = w.bonds[k]!.src :=
  (ends_getElem! h.size h.ends k).1

lemma dst (h : KindRel F w w') (k : ℕ) : w'.bonds[k]!.dst = w.bonds[k]!.dst :=
  (ends_getElem! h.size h.ends k).2

/-- At any bond, the two kinds read with `!` are equal, or both single or double. -/
lemma kind_getElem! (h : KindRel F w w') (k : ℕ) :
    w'.bonds[k]!.kind = w.bonds[k]!.kind ∨ IsSD w.bonds[k]!.kind ∧ IsSD w'.bonds[k]!.kind := by
  by_cases hk : k < w.bonds.size
  · have hk' : k < w'.bonds.size := h.size ▸ hk
    rcases h.kind k with e | ⟨-, ⟨x, hx, hsx⟩, ⟨y, hy, hsy⟩⟩
    · rw [kind?_eq_of_lt w hk, kind?_eq_of_lt w' hk'] at e
      exact .inl (Option.some.inj e)
    · rw [kind?_eq_of_lt w hk] at hx
      rw [kind?_eq_of_lt w' hk'] at hy
      exact .inr ⟨Option.some.inj hx ▸ hsx, Option.some.inj hy ▸ hsy⟩
  · have hk' : ¬ k < w'.bonds.size := h.size ▸ hk
    left
    simp [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt hk),
      Array.getElem?_eq_none (Nat.le_of_not_lt hk')]

/-- Making the same bond aromatic, with the same two atoms, in both copies keeps the relation. -/
lemma mark (h : KindRel F w w') (b s d : ℕ) :
    KindRel F (((w.setKind b .aromatic).modifyAtom s ({ · with aromatic := true })).modifyAtom d
        ({ · with aromatic := true }))
      (((w'.setKind b .aromatic).modifyAtom s ({ · with aromatic := true })).modifyAtom d
        ({ · with aromatic := true })) where
  atoms := by simp only [modifyAtom, setKind_atoms, h.atoms]
  size := by simp [h.size]
  ends k := by
    simp only [modifyAtom_bonds, getElem?_setKind_bonds]
    split <;> simp [Option.map_map, Function.comp_def, h.ends k]
  kind k := by
    simp only [kind?, modifyAtom_bonds, getElem?_setKind_bonds]
    split
    · left
      have e := congrArg (Option.isSome) (h.ends k)
      simp only [Option.isSome_map] at e
      cases h1 : w.bonds[k]? <;> cases h2 : w'.bonds[k]? <;> simp_all
    · exact h.kind k

lemma markAromatic (h : KindRel F w w') (b : ℕ) :
    KindRel F (w.markAromatic b) (w'.markAromatic b) := by
  unfold Work.markAromatic
  dsimp only
  rw [h.src, h.dst]
  rcases h.kind_getElem! b with e | ⟨hs, hs'⟩
  · rw [e]
    split
    · exact h.mark b _ _
    · exact h
  · have c : (w.bonds[b]!.kind == .single || w.bonds[b]!.kind == .double) = true := by
      rcases hs with e | e <;> simp [e]
    have c' : (w'.bonds[b]!.kind == .single || w'.bonds[b]!.kind == .double) = true := by
      rcases hs' with e | e <;> simp [e]
    rw [if_pos c, if_pos c']
    exact h.mark b _ _

/-- **Equal once `F` is aromatic**: if every bond of `F` is aromatic in `w`, the two copies are
equal. -/
lemma eq_of_aromatic (h : KindRel F w w') (hA : ∀ k, F k = true → w.kind? k = some .aromatic) :
    w' = w := by
  obtain ⟨A, B⟩ := w
  obtain ⟨A', B'⟩ := w'
  have ha : A' = A := h.atoms
  subst ha
  congr 1
  apply Array.ext_getElem?
  intro k
  have he := h.ends k
  have hk : (B'[k]?).map (·.kind) = (B[k]?).map (·.kind) := by
    rcases h.kind k with e | ⟨hF, ⟨x, hx, hsx⟩, -⟩
    · exact e
    · have := hA k hF
      simp only [kind?] at this hx
      rw [this] at hx
      cases Option.some.inj hx
      rcases hsx with e | e <;> cases e
  simp only at he
  cases h1 : B[k]? <;> cases h2 : B'[k]?
  · rfl
  · simp [h1, h2] at he
  · simp [h1, h2] at he
  · rename_i b b'
    simp only [h1, h2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he hk
    obtain ⟨s, d, kd⟩ := b
    obtain ⟨s', d', kd'⟩ := b'
    simp only at he hk
    obtain ⟨rfl, rfl⟩ := he
    rw [hk]

end KindRel

/-- `assignRadicals` does not touch the bonds. -/
lemma assignRadicals_bonds (w : Work) : w.assignRadicals.bonds = w.bonds := by
  unfold assignRadicals
  refine foldl_induction (fun w' : Work ↦ w'.bonds = w.bonds) _ _ _ rfl fun w' i _ h ↦ ?_
  unfold radicalStep
  dsimp only
  split
  · exact h
  · exact h

/-- Ring bonds are read off the bonds. -/
lemma ringBonds_of_bonds_eq {w w' : Work} (h : w'.bonds = w.bonds) :
    w'.ringBonds = w.ringBonds := by
  funext ring
  simp only [ringBonds, bondBetween?, numBonds, h]

namespace Swapped

/-- **Two Kekulé structures over the bonds `F` are perceived alike**, if `setAromaticity` makes
every bond of `F` aromatic in one of them: the finished copies are equal. -/
theorem finish_eq (h : Swapped F w w') (rings : Array (List ℕ))
    (hF : ∀ k, F k = true → k ∈ rings.toList.flatMap w.ringBonds)
    (hA : ∀ k, F k = true → (w.assignRadicals.setAromaticity rings).kind? k = some .aromatic) :
    w'.finish rings = w.finish rings := by
  have h1 := h.assignRadicals
  have hF1 : ∀ k, F k = true → k ∈ rings.toList.flatMap w.assignRadicals.ringBonds := by
    rw [ringBonds_of_bonds_eq (assignRadicals_bonds w)]
    exact hF
  have hs : w'.assignRadicals.setAromaticity rings = w.assignRadicals.setAromaticity rings := by
    unfold Work.setAromaticity
    rw [h1.aromaticBondList_eq rings hF1]
    refine KindRel.eq_of_aromatic ?_ hA
    exact foldl_sim (KindRel F) _ _ _ _ _ h1.kindRel fun _ _ b _ hb ↦ hb.markAromatic b
  unfold Work.finish
  rw [hs]

end Swapped

/-! ### Bond-order sums of a molecule's working copy -/

/-- Filtering the positions of an array and reading them is filtering the array. -/
lemma map_filter_range_getElem! {β γ : Type*} [Inhabited β] (a : Array β) (p : β → Bool)
    (f : β → γ) : ((List.range a.size).filter (fun k ↦ p a[k]!)).map (fun k ↦ f a[k]!) =
      (a.toList.filter p).map f := by
  have e : (List.range a.size).map (fun k ↦ a[k]!) = a.toList :=
    List.ext_getElem (by simp) fun k h1 h2 ↦ by
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      simp at h1
      simp [getElem!_def, Array.getElem?_eq_getElem h1]
  rw [← e, List.filter_map, List.map_map]
  rfl

/-- Twice a list's bond orders, counted in half units, cast to `ℚ`. -/
lemma cast_sum_halfOrder {n : ℕ} : ∀ L : List (Bond n),
    (((L.map fun b ↦ halfOrder b.kind).sum : ℕ) : ℚ) = 2 * (L.map fun b ↦ b.kind.order).sum
  | [] => by simp
  | b :: L => by
    rw [List.map_cons, List.sum_cons, Nat.cast_add, cast_sum_halfOrder L, List.map_cons,
      List.sum_cons, mul_add]
    congr 1
    cases b.kind <;> norm_num [halfOrder, BondKind.order]

/-- Twice the bond-order sum of an atom of a molecule is what its working copy counts. -/
lemma bondHalfSum_ofMolecule {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((ofMolecule m).bondHalfSum i : ℚ) = 2 * m.bondOrderSum i := by
  simp only [bondHalfSum, bondsOf, numBonds]
  rw [map_filter_range_getElem! (ofMolecule m).bonds (·.touches i) (halfOrder ·.kind)]
  have ht : (fun b : Bond n ↦ (({ src := b.src.val, dst := b.dst.val, kind := b.kind } : WBond)
      |>.touches i.val)) = (·.touches i) := by
    funext b
    simp only [WBond.touches, Bond.touches]
    congr 1 <;> rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.val_inj]
  simp only [ofMolecule, Array.toList_map, List.filter_map, List.map_map, Function.comp_def, ht]
  rw [Molecule.bondOrderSum, Molecule.bondsAt, ← cast_sum_halfOrder]

/-- An atom number past the end of a molecule has no bonds in its working copy. -/
lemma bondHalfSum_ofMolecule_of_le {n : ℕ} (m : Molecule n) {i : ℕ} (hi : n ≤ i) :
    (ofMolecule m).bondHalfSum i = 0 := by
  simp only [bondHalfSum, bondsOf, numBonds]
  rw [map_filter_range_getElem! (ofMolecule m).bonds (·.touches i) (halfOrder ·.kind)]
  simp only [ofMolecule, Array.toList_map, List.filter_map]
  rw [List.filter_eq_nil_iff.mpr fun b _ ↦ ?_]
  · rfl
  · simp only [Function.comp_apply, WBond.touches, Bool.or_eq_true, beq_iff_eq, not_or]
    exact ⟨by have := b.src.isLt; omega, by have := b.dst.isLt; omega⟩

/-! ### `cleanUp` on another Kekulé structure -/

/-- A left fold with two step functions that agree on the list. -/
theorem _root_.LeanSMILES.Aromaticity.foldl_congr_mem {α β : Type*} {f g : β → α → β} :
    ∀ {l : List α}, (∀ b, ∀ a ∈ l, f b a = g b a) → ∀ b, l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, h, b => by
    rw [List.foldl_cons, List.foldl_cons, h b a List.mem_cons_self]
    exact foldl_congr_mem (fun b' a' ha' ↦ h b' a' (List.mem_cons_of_mem _ ha')) _

/-- Atom `i` is one `cleanUp` could rewrite at: a neutral N or P of valence 5, or a neutral Cl,
Br or I of valence 3, 5 or 7. -/
def Hypervalent (w : Work) (i : ℕ) : Prop :=
  w.atoms[i]!.charge = 0 ∧ ((w.atoms[i]!.z = 7 ∨ w.atoms[i]!.z = 15) ∧ w.explicitValence i = 5 ∨
    (w.atoms[i]!.z = 17 ∨ w.atoms[i]!.z = 35 ∨ w.atoms[i]!.z = 53) ∧
      (w.explicitValence i = 3 ∨ w.explicitValence i = 5 ∨ w.explicitValence i = 7))

lemma mem_bondsOf_of_mem_neighbors {w : Work} {i k j : ℕ} (h : (k, j) ∈ w.neighbors i) :
    k ∈ w.bondsOf i := by
  simp only [neighbors, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨k', hk', rfl, -⟩ := h
  exact hk'

namespace Swapped

lemma nitroCand_eq (h : Swapped F w w') : w'.nitroCand = w.nitroCand := by
  funext i
  simp only [nitroCand, h.atoms, h.explicitValence_eq]

lemma phosphorusGuard_eq (h : Swapped F w w') : w'.phosphorusGuard = w.phosphorusGuard := by
  funext i
  simp only [phosphorusGuard, h.atoms, h.explicitValence_eq, h.degree_eq]

lemma halogenGuard_eq (h : Swapped F w w') : w'.halogenGuard = w.halogenGuard := by
  funext i
  simp only [halogenGuard, h.atoms, h.explicitValence_eq, h.neighbors_eq]

/-- **`cleanUp` does nothing on another Kekulé structure either**, if it does nothing on `w` and no
bond of `F` touches an atom it could rewrite at. -/
theorem quiet (h : Swapped F w w') (hq : w.Quiet)
    (hc : ∀ k, F k = true → ∀ i, k ∈ w.bondsOf i → ¬ Hypervalent w i) : w'.Quiet := by
  have hsz : w'.atoms.size = w.atoms.size := by rw [h.atoms]
  have kindEq : ∀ i, Hypervalent w i → ∀ x ∈ w.neighbors i,
      w'.bonds[x.1]!.kind = w.bonds[x.1]!.kind := by
    intro i hv ⟨k, j⟩ hx
    have hk := mem_bondsOf_of_mem_neighbors hx
    cases hF : F k
    · exact h.kind_eq (mem_bondsOf_lt hk) hF
    · exact absurd hv (hc k hF i hk)
  have hvN : ∀ i, w.nitroCand i = true → Hypervalent w i := by
    intro i hn
    simp only [nitroCand, Bool.and_eq_true, beq_iff_eq] at hn
    exact ⟨hn.1.2, .inl ⟨.inl hn.1.1, hn.2⟩⟩
  refine ⟨fun i hi ↦ ?_, fun i hi hn ↦ ?_, fun i hi ↦ ?_⟩
  · have hw := (nitroStep_fst_eq_iff w [] i).mp (hq.1 i (hsz ▸ hi))
    rw [nitroStep_fst_eq_iff, h.nitroCand_eq, h.neighbors_eq]
    intro hn x hx
    rw [← hw hn x hx]
    simp only [nitroO, h.atoms, kindEq i (hvN i hn) x hx]
  · rw [h.nitroCand_eq] at hn
    have hw := (azideStep_eq_iff w i).mp (hq.2.1 i (hsz ▸ hi) hn)
    rw [azideStep_eq_iff, h.neighbors_eq]
    intro x hx
    rw [← hw x hx]
    simp only [azideN, h.atoms, kindEq i (hvN i hn) x hx]
  · have hi' : i < w.atoms.size := hsz ▸ hi
    have hw := hq.2.2 i hi'
    unfold cleanUpStep at hw ⊢
    simp only [h.atoms] at ⊢
    by_cases hz : (w.atoms[i]!.z == 15) = true
    · simp only [hz, if_true] at hw ⊢
      rw [phosphorusCleanup_eq_iff w' hi, h.phosphorusGuard_eq]
      have hw' := (phosphorusCleanup_eq_iff w hi').mp hw
      intro hg
      have hv : Hypervalent w i := by
        simp only [phosphorusGuard, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hg
        simp only [beq_iff_eq] at hz
        exact ⟨hg.1.1, .inl ⟨.inr hz, hg.1.2⟩⟩
      have hs : w'.phosphorusScan i = w.phosphorusScan i := by
        unfold phosphorusScan
        rw [h.neighbors_eq]
        refine foldl_congr_mem (fun s x hx ↦ ?_) _
        obtain ⟨k, j⟩ := x
        simp only [h.atoms, h.degree_eq, kindEq i hv (k, j) hx]
      rw [hs]
      exact hw' hg
    · simp only [hz, Bool.false_eq_true, if_false] at hw ⊢
      by_cases hz' : (w.atoms[i]!.z == 17 || w.atoms[i]!.z == 35 || w.atoms[i]!.z == 53) = true
      · simp only [hz', if_true] at hw ⊢
        rw [halogenCleanup_eq_iff w' hi, h.halogenGuard_eq, h.neighbors_eq]
        have hw' := (halogenCleanup_eq_iff w hi').mp hw
        intro hg kj hkj
        have hv : Hypervalent w i := by
          simp only [halogenGuard, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hg
          simp only [Bool.or_eq_true, beq_iff_eq] at hz'
          refine ⟨hg.1.1, .inr ⟨by tauto, ?_⟩⟩
          have := hg.1.2
          simp only [Bool.not_eq_false', List.contains_cons, List.contains_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at this
          omega
        rw [kindEq i hv kj hkj]
        exact hw' hg kj hkj
      · simp only [hz', Bool.false_eq_true, if_false]

end Swapped

/-! ### Aromatic candidates are not hypervalent -/

/-- The first two checks of `isAromaticCandidate`: a candidate is in the first three rows (or Se,
Te), and not over its default valence. -/
lemma isAromaticCandidate_spec {w : Work} {i : ℕ} {d : Donor}
    (h : w.isAromaticCandidate i d = true) :
    ¬ (18 < w.atoms[i]!.z ∧ w.atoms[i]!.z ≠ 34 ∧ w.atoms[i]!.z ≠ 52) ∧
      ¬ (0 < defaultValence w.atoms[i]!.z ∧
        defaultValence (((w.atoms[i]!.z : ℤ) - w.atoms[i]!.charge).toNat) <
          w.cachedValence i + w.atoms[i]!.cachedImplicit) := by
  unfold isAromaticCandidate at h
  simp only [Id.run] at h
  constructor
  · intro hz
    simp [hz.1, hz.2.1, hz.2.2] at h
  · intro hv
    split at h
    · exact Bool.false_ne_true h
    split at h
    · exact Bool.false_ne_true h
    split at h
    · exact Bool.false_ne_true h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc hv

/-- `assignRadicals` changes only the radical counts. -/
lemma assignRadicals_atoms (w : Work) (j : ℕ) :
    (w.assignRadicals.atoms[j]?).map (fun a : WAtom ↦ { a with radicals := 0 }) =
      (w.atoms[j]?).map (fun a : WAtom ↦ { a with radicals := 0 }) := by
  unfold assignRadicals
  refine foldl_induction (fun w' : Work ↦ (w'.atoms[j]?).map (fun a : WAtom ↦
    { a with radicals := 0 }) = (w.atoms[j]?).map (fun a : WAtom ↦ { a with radicals := 0 }))
    _ _ _ rfl fun w' i _ h ↦ ?_
  unfold radicalStep
  dsimp only
  split
  · exact h
  · rw [← h, getElem?_modifyAtom_atoms]
    split <;> simp [Option.map_map, Function.comp_def]

/-- **An aromatic candidate is not hypervalent**: perception runs on the working copy with its
valences cached, and a neutral N or P of valence 5, or a neutral Cl of valence 3, 5 or 7, is over
its default valence (Br and I are past the third row). -/
theorem not_hypervalent_of_isAromaticCandidate (w : Work) {i : ℕ} (hi : i < w.atoms.size)
    {d : Donor} (h : w.cacheValences.assignRadicals.isAromaticCandidate i d = true) :
    ¬ Hypervalent w i := by
  obtain ⟨hz, hv⟩ := isAromaticCandidate_spec h
  -- the atom perception sees: `w`'s, with its valence cached
  obtain ⟨a1, ha1, hz1, hc1, hv1⟩ : ∃ a1, w.cacheValences.assignRadicals.atoms[i]? = some a1 ∧
      a1.z = w.atoms[i]!.z ∧ a1.charge = w.atoms[i]!.charge ∧
      a1.cachedValence = some (w.explicitValence i) := by
    have e := assignRadicals_atoms w.cacheValences i
    rw [getElem?_cacheValences_atoms, Array.getElem?_eq_getElem hi] at e
    obtain ⟨a1, ha1, he⟩ := Option.map_eq_some_iff.mp e
    refine ⟨a1, ha1, ?_, ?_, ?_⟩
    · have := congrArg WAtom.z he; simpa [getElem!_def, Array.getElem?_eq_getElem hi] using this
    · have := congrArg WAtom.charge he
      simpa [getElem!_def, Array.getElem?_eq_getElem hi] using this
    · have := congrArg WAtom.cachedValence he; simpa using this
  have hb : w.cacheValences.assignRadicals.atoms[i]! = a1 := by simp [getElem!_def, ha1]
  have hcv : w.cacheValences.assignRadicals.cachedValence i = w.explicitValence i := by
    simp [cachedValence, hb, hv1]
  rw [hb, hz1, hc1, hcv] at hv
  rw [hb, hz1] at hz
  rintro ⟨h0, ⟨hz', hev⟩ | ⟨hz', hev⟩⟩
  · rw [h0, hev] at hv
    have h7 : defaultValence 7 = 3 := by decide
    have h15 : defaultValence 15 = 3 := by decide
    rcases hz' with e | e <;> rw [e] at hv <;> apply hv <;>
      simp only [Int.sub_zero, Int.toNat_natCast, h7, h15] <;> omega
  · rw [h0] at hv
    rcases hz' with e | e | e
    · rw [e] at hv
      apply hv
      refine ⟨by decide, ?_⟩
      simp only [Int.sub_zero, Int.toNat_natCast]
      have : defaultValence 17 = 1 := by decide
      rw [this]
      omega
    · rw [e] at hz; exact hz ⟨by decide, by decide, by decide⟩
    · rw [e] at hz; exact hz ⟨by decide, by decide, by decide⟩

end Work

end LeanSMILES.Aromaticity
