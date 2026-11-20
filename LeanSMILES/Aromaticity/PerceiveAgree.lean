/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeFacts

/-!
# LeanSMILES.Aromaticity.PerceiveAgree

Aromaticity perception on two working copies whose atoms' bookkeeping differs.

`Work.Swapped` (`Aromaticity/Congruence.lean`) relates copies with the same atoms and different
bond kinds.  The witness of `Molecule.exists_kekule_aromatize` needs the other case: the same
bonds, and atoms that record their hydrogens differently (written in brackets in one, implied in
the other) and whose valences were cached at different times (before kekulization, rounded the
RDKit way, or after).  Perception reads only some combinations of those, and
`Work.PerceiveAgree` asks the two copies to agree on exactly these:

* the same bonds, elements and charges;
* the same cached hydrogen total (written plus implied), and the same cached valence less written
  hydrogens (the bond part of the valence);
* on the first copy, that bond part is the Kekulé bond-order sum (what kekulization makes true);
* at every atom of a ring, the same verdict of the candidate test, for the donor type the ring
  gives it;
* at every candidate atom of a ring, the same donor type.  Not the same `countAtomElec`, nor the
  same radicals: an atom whose hydrogen is written in one copy and implied in the other
  (`[sH]1ccccc1`, written `S1=CC=CC=C1` back) can count its electrons differently and still get
  the same donor type, and an over-valent atom RDKit's valence check skips (bonded to a metal,
  `C[B](C)(C)[Fe]`) can carry a radical in one copy only, but fails the candidate test in both.

Then the first pass of perception agrees on its candidates, candidate rings and their donor types
(`PerceiveAgree.donorData_rel`), and the second reads donor types only at atoms of candidate
rings, so `aromaticBondList` is the same (`PerceiveAgree.aromaticBondList_eq`).

## Main definitions

* `Work.PerceiveAgree`: two working copies that perception over `rings` reads alike.
* `Work.SameMarks`: two copies with the same bonds and the same aromatic flags.
* `Work.HsRestored`: the step of `adjustHs` at an atom gives back its cached hydrogen total.

## Main statements

* `Work.PerceiveAgree.donorData_rel`: the first pass of perception agrees on the candidates,
  candidate rings and their donor types.
* `Work.PerceiveAgree.aromaticBondList_eq`: the same bonds are made aromatic.
* `Work.PerceiveAgree.setAromaticity`: perception marks the same bonds and atoms.
* `Work.frozenHs_finalizeHs_of_restored`: the final hydrogen count is the cached one where the
  `adjustHs` step restores it.
* `Work.cachedValence_sub_of_noArom`: with nothing aromatic, the cached valence less the written
  hydrogens is the bond-order sum.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- An atom with no aromatic bond has at least its degree plus its number of multiple bonds as
bond-order sum: a single bond counts 1, a double or triple at least 2. -/
lemma length_filter_isMultiple_add_degree_le (w : Work) (i : ℕ)
    (h : ∀ k ∈ w.bondsOf i, (w.bonds[k]! : WBond).kind ≠ .aromatic) :
    ((w.bondsOf i).filter fun k ↦ isMultiple (w.bonds[k]! : WBond).kind).length + w.degree i ≤
      w.bondHalfSum i / 2 := by
  unfold degree bondHalfSum
  suffices H : ∀ l : List ℕ, (∀ k ∈ l, (w.bonds[k]! : WBond).kind ≠ .aromatic) →
      2 * ((l.filter fun k ↦ isMultiple (w.bonds[k]! : WBond).kind).length + l.length) ≤
        (l.map fun k ↦ halfOrder (w.bonds[k]! : WBond).kind).sum by
    have := H _ h
    omega
  intro l hl
  induction l with
  | nil => simp
  | cons k l ih =>
    have hk := hl k List.mem_cons_self
    have ih := ih fun k' hk' ↦ hl k' (List.mem_cons_of_mem _ hk')
    simp only [List.filter_cons, List.length_cons, List.map_cons, List.sum_cons]
    cases hkind : (w.bonds[k]! : WBond).kind <;> simp_all [isMultiple, halfOrder] <;> omega

/-- Two working copies that aromaticity perception over `rings` reads alike (module docstring). -/
structure PerceiveAgree (rings : Array (List ℕ)) (w w' : Work) : Prop where
  /-- The same bonds. -/
  bonds : w'.bonds = w.bonds
  /-- As many atoms. -/
  size : w'.atoms.size = w.atoms.size
  /-- The same elements. -/
  z : ∀ i : ℕ, (w'.atoms[i]! : WAtom).z = (w.atoms[i]! : WAtom).z
  /-- The same charges. -/
  charge : ∀ i : ℕ, (w'.atoms[i]! : WAtom).charge = (w.atoms[i]! : WAtom).charge
  /-- The same cached hydrogen totals. -/
  total : ∀ i : ℕ, w'.cachedTotalHs i = w.cachedTotalHs i
  /-- The same bond part of the cached valence. -/
  bondPart : ∀ i : ℕ, (w'.cachedValence i : ℤ) - (w'.atoms[i]! : WAtom).explicitHs =
    (w.cachedValence i : ℤ) - (w.atoms[i]! : WAtom).explicitHs
  /-- On the first copy, the bond part is the Kekulé bond-order sum. -/
  kekule : ∀ i : ℕ, (w.cachedValence i : ℤ) - (w.atoms[i]! : WAtom).explicitHs =
    ((w.bondHalfSum i / 2 : ℕ) : ℤ)
  /-- No bond is aromatic. -/
  noArom : ∀ b ∈ w.bonds, b.kind ≠ .aromatic
  /-- At every atom of a ring, the same verdict of the candidate test, for the donor type the ring
  gives it. -/
  cand : ∀ ring ∈ rings.toList, ∀ i ∈ ring, ∀ len : ℕ,
    w'.isAromaticCandidate i (w'.ringDonor ((rings.toList.flatMap w.ringBonds).eraseDups) len i) =
      w.isAromaticCandidate i (w.ringDonor ((rings.toList.flatMap w.ringBonds).eraseDups) len i)
  /-- At every candidate atom of a ring, the same donor type. -/
  donor : ∀ ring ∈ rings.toList, ∀ i ∈ ring, ∀ len : ℕ,
    w.isAromaticCandidate i (w.ringDonor ((rings.toList.flatMap w.ringBonds).eraseDups) len i) =
      true →
    w'.ringDonor ((rings.toList.flatMap w.ringBonds).eraseDups) len i =
      w.ringDonor ((rings.toList.flatMap w.ringBonds).eraseDups) len i

/-- Entry `j` of a donor array after `set! i v`: `v` if `j` is `i` and in range, else the old
entry. -/
lemma getElem!_set!_donor (a : Array Donor) (i j : ℕ) (v : Donor) :
    (a.set! i v)[j]! = if i = j ∧ j < a.size then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj]
    simp [Array.set!, Array.getElem_setIfInBounds, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    simp [hj]

namespace PerceiveAgree

variable {rings : Array (List ℕ)} {w w' : Work} (h : PerceiveAgree rings w w')
include h

/-- The two copies have as many atoms. -/
lemma numAtoms_eq : w'.numAtoms = w.numAtoms := h.size

/-- The two copies have the same bonds at every atom. -/
lemma bondsOf_eq : w'.bondsOf = w.bondsOf := by
  funext i
  simp only [bondsOf, numBonds, h.bonds]

/-- The two copies have the same neighbors at every atom. -/
lemma neighbors_eq : w'.neighbors = w.neighbors := by
  funext i
  simp only [neighbors, h.bondsOf_eq, h.bonds]

/-- The two copies have the same degree at every atom. -/
lemma degree_eq : w'.degree = w.degree := by
  funext i
  simp only [degree, h.bondsOf_eq]

/-- The two copies have the same bond between any two atoms. -/
lemma bondBetween?_eq : w'.bondBetween? = w.bondBetween? := by
  funext i j
  simp only [bondBetween?, numBonds, h.bonds]

/-- The two copies give every ring the same bonds. -/
lemma ringBonds_eq : w'.ringBonds = w.ringBonds := by
  funext r
  simp only [ringBonds, h.bondBetween?_eq]

/-- The two copies have the same bond half-order sum at every atom. -/
lemma bondHalfSum_eq : w'.bondHalfSum = w.bondHalfSum := by
  funext i
  simp only [bondHalfSum, h.bondsOf_eq, h.bonds]

/-- An atom has a multiple bond in one copy exactly when it has one in the other. -/
lemma hasMultipleBond_eq : w'.hasMultipleBond = w.hasMultipleBond := by
  funext i
  simp only [hasMultipleBond, h.bondsOf_eq, h.bonds]

/-- The two copies give every atom the same exocyclic multiple bond partner. -/
lemma exocyclicMultiple?_eq : w'.exocyclicMultiple? = w.exocyclicMultiple? := by
  funext rbs i
  simp only [exocyclicMultiple?, h.neighbors_eq, h.bonds]

/-- Valence plus implied hydrogens: the bond part plus the hydrogen total. -/
lemma cachedValence_add_cachedImplicit (i : ℕ) :
    w'.cachedValence i + (w'.atoms[i]! : WAtom).cachedImplicit =
      w.cachedValence i + (w.atoms[i]! : WAtom).cachedImplicit := by
  have h1 := h.bondPart i
  have h2 := h.total i
  simp only [cachedTotalHs] at h2
  omega

/-- Two states of perception's first pass that agree on what it has seen, which atoms are
candidates, the candidate rings, and the donor types of the candidates. -/
def DonorRel (s s' : DonorState) : Prop :=
  s'.seen = s.seen ∧ s'.cand = s.cand ∧ s'.candRings = s.candRings ∧
    s'.donor.size = s.donor.size ∧ ∀ j : ℕ, s.cand[j]! = true → s'.donor[j]! = s.donor[j]!

/-- One atom of a ring in the first pass keeps two related states related, and both copies give
the same "every atom so far is a candidate" flag. -/
lemma donorAtomStep_rel {ring : List ℕ} (hr : ring ∈ rings.toList) {i : ℕ} (hi : i ∈ ring)
    {s s' : DonorState} (hs : DonorRel s s') (a : Bool) :
    DonorRel (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length (s, a) i).1
        (w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length (s', a) i).1 ∧
      (w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length (s', a) i).2 =
        (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length
          (s, a) i).2 := by
  obtain ⟨h1, h2, h3, h5, h4⟩ := hs
  have hc := h.cand ring hr i hi ring.length
  have hd := h.donor ring hr i hi ring.length
  unfold donorAtomStep
  dsimp only
  rw [h1, h2]
  split
  · exact ⟨⟨h1, h2, h3, h5, h4⟩, rfl⟩
  · refine ⟨⟨rfl, by rw [hc], h3, by simp [h5], fun j hj ↦ ?_⟩, by rw [hc]⟩
    simp only at hj ⊢
    rw [getElem!_set!_bool] at hj
    rw [getElem!_set!_donor, getElem!_set!_donor, h5]
    by_cases hij : i = j
    · subst hij
      by_cases hlt : i < s.cand.size
      · rw [if_pos ⟨rfl, hlt⟩] at hj
        simp only [hd hj]
        by_cases hds : i < s.donor.size
        · simp [hds]
        · simp only [hds, and_false, if_false]
          rw [getElem!_neg s'.donor i (by omega), getElem!_neg s.donor i hds]
      · rw [if_neg (fun h ↦ hlt h.2)] at hj
        rw [getElem!_neg s.cand i hlt] at hj
        cases hj
    · rw [if_neg (fun h ↦ hij h.1)] at hj
      rw [if_neg (fun h ↦ hij h.1), if_neg (fun h ↦ hij h.1)]
      exact h4 j hj

/-- Any list of atoms of a ring, folded through the first pass, keeps two related states related
and gives the same candidate flag in both copies. -/
lemma foldl_donorAtomStep_rel {ring : List ℕ} (hr : ring ∈ rings.toList) :
    ∀ (l : List ℕ), (∀ i ∈ l, i ∈ ring) → ∀ (s s' : DonorState) (a : Bool), DonorRel s s' →
      DonorRel (l.foldl (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length) (s, a)).1
        (l.foldl (w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length) (s', a)).1 ∧
      (l.foldl (w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length) (s', a)).2 =
        (l.foldl (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length) (s, a)).2
  | [], _, _, _, _, hs => ⟨hs, rfl⟩
  | i :: l, hl, s, s', a, hs => by
    rw [List.foldl_cons, List.foldl_cons]
    obtain ⟨r1, r2⟩ := h.donorAtomStep_rel hr (hl i List.mem_cons_self) hs a
    have e : (w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length
        (s', a) i) = ((w'.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length (s', a) i).1,
        (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length
          (s, a) i).2) := by rw [← r2]
    have e' : (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length
        (s, a) i) = ((w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
          ring.length (s, a) i).1,
        (w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups) ring.length
          (s, a) i).2) := rfl
    rw [e, e']
    exact foldl_donorAtomStep_rel hr l (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) _ _ _ r1

/-- **The first pass of perception agrees** where it matters: the same candidates and candidate
rings, and the same donor types at the candidates. -/
lemma donorData_rel : DonorRel (w.donorData rings) (w'.donorData rings) := by
  unfold donorData
  rw [h.ringBonds_eq, h.numAtoms_eq]
  have key : ∀ (l : List (List ℕ)), (∀ r ∈ l, r ∈ rings.toList) → ∀ s s' : DonorState,
      DonorRel s s' →
      DonorRel (l.foldl (w.donorRingStep ((rings.toList.flatMap w.ringBonds).eraseDups)) s)
        (l.foldl (w'.donorRingStep ((rings.toList.flatMap w.ringBonds).eraseDups)) s') := by
    intro l
    induction l with
    | nil => intro _ s s' hs; exact hs
    | cons ring l ih =>
      intro hl s s' hs
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr))
      have hr := hl ring List.mem_cons_self
      obtain ⟨r1, r2⟩ := h.foldl_donorAtomStep_rel hr ring (fun _ h ↦ h) s s' true hs
      unfold donorRingStep
      dsimp only
      rw [r2]
      split
      · obtain ⟨g1, g2, g3, g5, g4⟩ := r1
        exact ⟨g1, g2, by simp [g3], g5, g4⟩
      · exact r1
  exact key _ (fun _ h ↦ h) _ _ ⟨rfl, rfl, rfl, rfl, fun _ _ ↦ rfl⟩

end PerceiveAgree

/-! ### The second pass reads donor types only at atoms of candidate rings -/

/-- Hückel's rule over `atoms` reads the donor types only at those atoms. -/
lemma huckel_congr {atoms : List ℕ} {d d' : Array Donor} (h : ∀ a ∈ atoms, d'[a]! = d[a]!) :
    huckel atoms d' = huckel atoms d := by
  have e1 : atoms.filter (d'[·]! == .any) = atoms.filter (d[·]! == .any) :=
    List.filter_congr fun a ha ↦ by rw [h a ha]
  have e3 : ∀ (f : Donor → ℕ) (l : List ℕ) (n : ℕ), (∀ a ∈ l, d'[a]! = d[a]!) →
      l.foldl (fun s a ↦ s + f d'[a]!) n = l.foldl (fun s a ↦ s + f d[a]!) n := by
    intro f l
    induction l with
    | nil => intro _ _; rfl
    | cons a l ih =>
      intro n hl
      simp only [List.foldl_cons]
      rw [hl a List.mem_cons_self]
      exact ih _ (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx))
  have e2 : ∀ (f : Donor → ℕ), atoms.foldl (fun s a ↦ s + f d'[a]!) 0 =
      atoms.foldl (fun s a ↦ s + f d[a]!) 0 := fun f ↦ e3 f atoms 0 h
  unfold huckel
  simp only [Id.run, e1]
  rw [e2 (fun x ↦ x.range.1), e2 (fun x ↦ x.range.2)]

/-- An atom no ring of the group passes through has count zero. -/
lemma counts_eq_zero {numAtoms : ℕ} {candRings : Array (List ℕ)} {cur : List ℕ} {a : ℕ}
    (ha : ∀ r ∈ cur, a ∉ candRings[r]!) :
    (cur.foldl (fun acc r ↦ candRings[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)
      (Array.replicate numAtoms 0))[a]! = 0 := by
  have inner : ∀ (l : List ℕ) (acc : Array ℕ), a ∉ l →
      (l.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)[a]! = acc[a]! := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons x l ih =>
      intro acc hl
      rw [List.foldl_cons, ih _ (fun h ↦ hl (List.mem_cons_of_mem _ h))]
      have hx : x ≠ a := fun e ↦ hl (e ▸ List.mem_cons_self)
      simp [getElem!_def, Array.getElem?_modify, hx]
  have outer : ∀ (l : List ℕ) (acc : Array ℕ), (∀ r ∈ l, a ∉ candRings[r]!) →
      (l.foldl (fun acc r ↦ candRings[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)
        acc)[a]! = acc[a]! := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons r l ih =>
      intro acc hl
      rw [List.foldl_cons, ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr)),
        inner _ _ (hl r List.mem_cons_self)]
  rw [outer cur _ ha]
  by_cases hlt : a < numAtoms
  · simp [hlt]
  · simp [hlt]

/-- `groupBonds` reads the donor types only at atoms of candidate rings. -/
lemma groupBonds_congr {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {d d' : Array Donor}
    {nbrs : Array (List ℕ)} (h : ∀ r : ℕ, ∀ a ∈ candRings[r]!, d'[a]! = d[a]!) (cur : List ℕ) :
    groupBonds numAtoms rbonds candRings d' nbrs cur =
      groupBonds numAtoms rbonds candRings d nbrs cur := by
  unfold groupBonds
  split
  · rfl
  · dsimp only
    rw [huckel_congr]
    intro a ha
    simp only [List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq] at ha
    by_contra hne
    have : ∀ r ∈ cur, a ∉ candRings[r]! := fun r _ har ↦ hne (h r a har)
    rw [counts_eq_zero this] at ha
    omega

/-- `fusedBonds` reads the donor types only at atoms of candidate rings. -/
lemma fusedBonds_congr {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {d d' : Array Donor}
    (h : ∀ r : ℕ, ∀ a ∈ candRings[r]!, d'[a]! = d[a]!) :
    fusedBonds numAtoms rbonds candRings d' = fusedBonds numAtoms rbonds candRings d := by
  unfold fusedBonds systemBonds
  simp only [groupBonds_congr h]

namespace PerceiveAgree

variable {rings : Array (List ℕ)} {w w' : Work} (h : PerceiveAgree rings w w')
include h

/-- **The same bonds are made aromatic.** -/
lemma aromaticBondList_eq : w'.aromaticBondList rings = w.aromaticBondList rings := by
  obtain ⟨-, h2, h3, -, h4⟩ := h.donorData_rel
  obtain ⟨-, hcr⟩ := ringInv_donorData w rings
  simp only [aromaticBondList]
  rw [h.ringBonds_eq, h.numAtoms_eq, h3]
  apply fusedBonds_congr
  intro r a ha
  by_cases hlt : r < (w.donorData rings).candRings.size
  · rw [getElem!_pos _ r hlt] at ha
    exact h4 a ((hcr _ (Array.getElem_mem hlt)).2 a ha)
  · rw [getElem!_neg _ r hlt] at ha
    cases ha

end PerceiveAgree

/-! ### Marking the aromatic bonds -/

/-- Two copies with the same bonds and the same aromatic flags. -/
structure SameMarks (w w' : Work) : Prop where
  /-- The same bonds. -/
  bonds : w'.bonds = w.bonds
  /-- The same aromatic flags. -/
  flags : ∀ j : ℕ, w'.atoms[j]?.map (·.aromatic) = w.atoms[j]?.map (·.aromatic)

namespace SameMarks

variable {w w' : Work}

/-- Every atom read with `!` has the same aromatic flag in both copies. -/
lemma aromatic_getElem! (h : SameMarks w w') (j : ℕ) :
    (w'.atoms[j]! : WAtom).aromatic = (w.atoms[j]! : WAtom).aromatic := by
  have := h.flags j
  simp only [getElem!_def]
  cases h1 : w'.atoms[j]? <;> cases h2 : w.atoms[j]? <;> simp_all

/-- RDKit reads the same atoms as aromatic in both copies. -/
lemma isAromaticAtom_eq (h : SameMarks w w') : w'.isAromaticAtom = w.isAromaticAtom := by
  funext i
  simp only [isAromaticAtom, h.aromatic_getElem!, bondsOf, numBonds, h.bonds]

/-- Flagging the same atom aromatic in both copies keeps them `SameMarks`. -/
lemma modifyAtom_aromatic (h : SameMarks w w') (i : ℕ) :
    SameMarks (w.modifyAtom i ({ · with aromatic := true }))
      (w'.modifyAtom i ({ · with aromatic := true })) where
  bonds := h.bonds
  flags j := by
    simp only [getElem?_modifyAtom_atoms]
    split
    · have := h.flags j
      cases h1 : w'.atoms[j]? <;> cases h2 : w.atoms[j]? <;> simp_all
    · exact h.flags j

/-- Marking the same bond aromatic in both copies keeps them `SameMarks`. -/
lemma markAromatic (h : SameMarks w w') (b : ℕ) :
    SameMarks (w.markAromatic b) (w'.markAromatic b) := by
  unfold Work.markAromatic
  simp only [h.bonds]
  split
  · refine (SameMarks.modifyAtom_aromatic ?_ _).modifyAtom_aromatic _
    exact ⟨by simp [setKind, h.bonds], h.flags⟩
  · exact h

/-- Marking the same list of bonds keeps the bonds and flags in step. -/
lemma foldl_markAromatic (h : SameMarks w w') (l : List ℕ) :
    SameMarks (l.foldl Work.markAromatic w) (l.foldl Work.markAromatic w') :=
  foldl_sim SameMarks _ _ l w w' h fun _ _ b _ hb ↦ hb.markAromatic b

end SameMarks

/-- **Perception marks the same bonds and atoms** on two copies it reads alike. -/
theorem PerceiveAgree.setAromaticity {rings : Array (List ℕ)} {w w' : Work}
    (h : PerceiveAgree rings w w') (hf : SameMarks w w') :
    SameMarks (w.setAromaticity rings) (w'.setAromaticity rings) := by
  unfold Work.setAromaticity
  rw [h.aromaticBondList_eq]
  exact hf.foldl_markAromatic _

/-! ### The final hydrogen counts -/

/-- An atom's implied hydrogens depend only on that atom and the bonds. -/
lemma implicitHs_congr {w w' : Work} (hb : w'.bonds = w.bonds) {i : ℕ}
    (ha : (w'.atoms[i]! : WAtom) = (w.atoms[i]! : WAtom)) : w'.implicitHs i = w.implicitHs i := by
  have hbo : w'.bondsOf = w.bondsOf := by
    funext j
    simp only [bondsOf, numBonds, hb]
  simp only [implicitHs, explicitValence, isAromaticAtom, bondHalfSum, hbo, hb, ha]
  rfl

/-- The step of `adjustHs` keeps the bonds. -/
@[simp] lemma adjustHsStep_bonds (w : Work) (j : ℕ) : (adjustHsStep w j).bonds = w.bonds := by
  unfold adjustHsStep
  dsimp only
  split <;> (try split) <;> rfl

/-- The step of `adjustHs` keeps the number of atoms. -/
@[simp] lemma size_adjustHsStep_atoms (w : Work) (j : ℕ) :
    (adjustHsStep w j).atoms.size = w.atoms.size := by
  unfold adjustHsStep
  dsimp only
  split <;> (try split) <;> simp

/-- Atom `i` after editing it with `g`. -/
lemma modifyAtom_atom_self (w : Work) (i : ℕ) (g : WAtom → WAtom) :
    ((w.modifyAtom i g).atoms[i]! : WAtom) =
      if i < w.atoms.size then g (w.atoms[i]! : WAtom) else (w.atoms[i]! : WAtom) := by
  by_cases hi : i < w.atoms.size
  · have hi' : i < (w.atoms.modify i g).size := by simpa using hi
    rw [if_pos hi, getElem!_pos _ i hi', getElem!_pos _ i hi]
    simp [modifyAtom, Array.getElem_modify]
  · have hi' : ¬ i < (w.modifyAtom i g).atoms.size := by simpa [modifyAtom] using hi
    rw [if_neg hi, getElem!_neg _ i hi', getElem!_neg _ i hi]

/-- Any run of `adjustHs` steps keeps the number of atoms. -/
@[simp] lemma size_foldl_adjustHsStep_atoms :
    ∀ (l : List ℕ) (w : Work), (l.foldl adjustHsStep w).atoms.size = w.atoms.size
  | [], _ => rfl
  | j :: l, w => by rw [List.foldl_cons, size_foldl_adjustHsStep_atoms l, size_adjustHsStep_atoms]

/-- Any run of `adjustHs` steps keeps the bonds. -/
@[simp] lemma foldl_adjustHsStep_bonds :
    ∀ (l : List ℕ) (w : Work), (l.foldl adjustHsStep w).bonds = w.bonds
  | [], _ => rfl
  | j :: l, w => by rw [List.foldl_cons, foldl_adjustHsStep_bonds l, adjustHsStep_bonds]

/-- A step at another atom leaves atom `i` alone. -/
lemma adjustHsStep_atom_of_ne (w : Work) {i j : ℕ} (hij : j ≠ i) :
    ((adjustHsStep w j).atoms[i]! : WAtom) = (w.atoms[i]! : WAtom) := by
  unfold adjustHsStep
  dsimp only
  split <;> (try split) <;> try rfl
  simp only [modifyAtom, getElem!_def, Array.getElem?_modify, if_neg hij]

/-- The step at atom `i` reads only atom `i` and the bonds. -/
lemma adjustHsStep_atom_congr {w w' : Work} (hb : w'.bonds = w.bonds)
    (hs : w'.atoms.size = w.atoms.size) {i : ℕ}
    (ha : (w'.atoms[i]! : WAtom) = (w.atoms[i]! : WAtom)) :
    ((adjustHsStep w' i).atoms[i]! : WAtom) = ((adjustHsStep w i).atoms[i]! : WAtom) := by
  have hi := implicitHs_congr hb ha
  have harom : w'.isAromaticAtom i = w.isAromaticAtom i := by
    simp only [isAromaticAtom, bondsOf, numBonds, hb, ha]
  unfold adjustHsStep
  dsimp only
  simp only [ha, hi, harom]
  split <;> (try split) <;> try exact ha
  rw [modifyAtom_atom_self, modifyAtom_atom_self, hs, ha]

/-- Through the whole first pass of `finalizeHs`, atom `i` ends as the step at `i` leaves it. -/
lemma foldl_adjustHsStep_atom (w : Work) (i : ℕ) :
    ∀ (l : List ℕ) (w0 : Work), l.Nodup → w0.bonds = w.bonds → w0.atoms.size = w.atoms.size →
      (w0.atoms[i]! : WAtom) = (w.atoms[i]! : WAtom) →
      ((l.foldl adjustHsStep w0).atoms[i]! : WAtom) =
        if i ∈ l then ((adjustHsStep w i).atoms[i]! : WAtom) else (w.atoms[i]! : WAtom)
  | [], _, _, _, _, ha => by simpa using ha
  | j :: l, w0, hnd, hb, hs, ha => by
    rw [List.foldl_cons]
    obtain ⟨hj, hnd⟩ := List.nodup_cons.mp hnd
    by_cases hji : j = i
    · subst hji
      -- the rest of the fold does not visit `j` again
      have hrest : ∀ (l : List ℕ) (v : Work), j ∉ l →
          ((l.foldl adjustHsStep v).atoms[j]! : WAtom) = (v.atoms[j]! : WAtom) := by
        intro l
        induction l with
        | nil => intro v _; rfl
        | cons x l ih =>
          intro v hx
          rw [List.mem_cons, not_or] at hx
          rw [List.foldl_cons, ih _ hx.2, adjustHsStep_atom_of_ne v (Ne.symm hx.1)]
      rw [hrest l _ hj, if_pos List.mem_cons_self, adjustHsStep_atom_congr hb hs ha]
    · have := foldl_adjustHsStep_atom w i l (adjustHsStep w0 j) hnd (by simp [hb]) (by simp [hs])
        (by rw [adjustHsStep_atom_of_ne w0 hji, ha])
      rw [this]
      simp [List.mem_cons, Ne.symm hji]

/-- **An atom's final hydrogen count is what the step at that atom gives**: its written
hydrogens after `adjustHs`, plus those then implied. -/
lemma frozenHs_finalizeHs (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    ((w.finalizeHs.atoms[i]! : WAtom)).frozenHs =
      some (((adjustHsStep w i).atoms[i]! : WAtom).explicitHs +
        (adjustHsStep w i).implicitHs i) := by
  set w1 := (List.range w.numAtoms).foldl adjustHsStep w with hw1
  have hb1 : w1.bonds = w.bonds := by rw [hw1, foldl_adjustHsStep_bonds]
  have hs1 : w1.atoms.size = w.atoms.size := by rw [hw1, size_foldl_adjustHsStep_atoms]
  have ha1 := foldl_adjustHsStep_atom w i (List.range w.numAtoms) w List.nodup_range rfl rfl rfl
  rw [if_pos (List.mem_range.mpr (by simpa [numAtoms] using hi))] at ha1
  have himp : w1.implicitHs i = (adjustHsStep w i).implicitHs i :=
    implicitHs_congr (by simp [hb1]) (by rw [← hw1] at ha1; exact ha1)
  unfold finalizeHs
  rw [← hw1]
  have hi1 : i < w1.atoms.size := hs1 ▸ hi
  simp only [numAtoms, getElem!_def, List.getElem?_toArray, Array.getElem?_map,
    List.getElem?_range hi1, List.getElem?_map, Option.map_some,
    Array.getElem?_eq_getElem hi1]
  rw [← hw1] at ha1
  simp only [getElem!_def, Array.getElem?_eq_getElem hi1] at ha1 himp
  rw [ha1, himp]

/-- Atom `i` after editing atom `j ≠ i`. -/
lemma modifyAtom_atom_of_ne (w : Work) {i j : ℕ} (hij : j ≠ i) (g : WAtom → WAtom) :
    ((w.modifyAtom j g).atoms[i]! : WAtom) = (w.atoms[i]! : WAtom) := by
  simp only [modifyAtom, getElem!_def, Array.getElem?_modify, if_neg hij]

/-- An edit that keeps the written and cached implied hydrogens keeps every cached total. -/
lemma cachedTotalHs_modifyAtom (w : Work) (j : ℕ) (g : WAtom → WAtom)
    (hg : ∀ a, (g a).explicitHs = a.explicitHs ∧ (g a).cachedImplicit = a.cachedImplicit) :
    (w.modifyAtom j g).cachedTotalHs = w.cachedTotalHs := by
  funext i
  by_cases hij : j = i
  · subst hij
    simp only [cachedTotalHs, modifyAtom_atom_self]
    split <;> simp [hg]
  · simp only [cachedTotalHs, modifyAtom_atom_of_ne w hij]

/-- Assigning radicals keeps the cached hydrogen totals. -/
lemma cachedTotalHs_assignRadicals (w : Work) :
    w.assignRadicals.cachedTotalHs = w.cachedTotalHs := by
  unfold assignRadicals
  generalize List.range w.numAtoms = l
  induction l generalizing w with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    unfold radicalStep
    dsimp only
    split
    · rfl
    · exact cachedTotalHs_modifyAtom _ _ _ fun _ ↦ ⟨rfl, rfl⟩

/-- Marking aromatic bonds keeps the cached hydrogen totals. -/
lemma cachedTotalHs_setAromaticity (w : Work) (rings : Array (List ℕ)) :
    (w.setAromaticity rings).cachedTotalHs = w.cachedTotalHs := by
  unfold setAromaticity
  generalize w.aromaticBondList rings = l
  induction l generalizing w with
  | nil => rfl
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    unfold markAromatic
    dsimp only
    split
    · rw [cachedTotalHs_modifyAtom _ _ (fun x ↦ { x with aromatic := true }) fun _ ↦ ⟨rfl, rfl⟩,
        cachedTotalHs_modifyAtom _ _ (fun x ↦ { x with aromatic := true }) fun _ ↦ ⟨rfl, rfl⟩]
      rfl
    · rfl

/-- The step at atom `i` keeps its aromatic flag. -/
lemma aromatic_adjustHsStep (w : Work) (i : ℕ) :
    ((adjustHsStep w i).atoms[i]! : WAtom).aromatic = (w.atoms[i]! : WAtom).aromatic := by
  unfold adjustHsStep
  dsimp only
  split <;> (try split) <;> try rfl
  rw [modifyAtom_atom_self]
  split <;> rfl

/-- `finalizeHs` keeps the aromatic flags. -/
lemma aromatic_finalizeHs (w : Work) (i : ℕ) :
    ((w.finalizeHs.atoms[i]! : WAtom)).aromatic = (w.atoms[i]! : WAtom).aromatic := by
  set w1 := (List.range w.numAtoms).foldl adjustHsStep w with hw1
  have hs1 : w1.atoms.size = w.atoms.size := by rw [hw1, size_foldl_adjustHsStep_atoms]
  have hfs : w.finalizeHs.atoms.size = w.atoms.size := by
    simp [finalizeHs, numAtoms]
  by_cases hi : i < w.atoms.size
  · have ha1 := foldl_adjustHsStep_atom w i (List.range w.numAtoms) w List.nodup_range rfl rfl rfl
    rw [if_pos (List.mem_range.mpr (by simpa [numAtoms] using hi))] at ha1
    have hi1 : i < w1.atoms.size := hs1 ▸ hi
    unfold finalizeHs
    rw [← hw1]
    simp only [numAtoms, getElem!_def, List.getElem?_toArray, Array.getElem?_map,
      List.getElem?_range hi1, Option.map_some, Array.getElem?_eq_getElem hi1]
    rw [← hw1] at ha1
    simp only [getElem!_def, Array.getElem?_eq_getElem hi1] at ha1
    rw [ha1, ← getElem!_def, aromatic_adjustHsStep, getElem!_def]
  · rw [getElem!_neg _ i (by omega), getElem!_neg _ i (by omega)]

/-- `finalizeHs` keeps which atoms are aromatic. -/
lemma isAromaticAtom_finalizeHs (w : Work) : w.finalizeHs.isAromaticAtom = w.isAromaticAtom := by
  funext i
  simp only [isAromaticAtom, aromatic_finalizeHs, bondsOf, numBonds, finalizeHs_bonds]

/-- The step at atom `i` gives back the hydrogen total cached before kekulization: what both
runs of the witness argument satisfy at every atom (`Work.frozenHs_finalizeHs_of_restored`). -/
def HsRestored (w : Work) (i : ℕ) : Prop :=
  ((adjustHsStep w i).atoms[i]! : WAtom).explicitHs + (adjustHsStep w i).implicitHs i =
    w.cachedTotalHs i

/-- **The final hydrogen count is the cached one** at an atom where the step restores it. -/
lemma frozenHs_finalizeHs_of_restored (w : Work) {i : ℕ} (hi : i < w.atoms.size)
    (h : HsRestored w i) :
    ((w.finalizeHs.atoms[i]! : WAtom)).frozenHs = some (w.cachedTotalHs i) := by
  rw [frozenHs_finalizeHs w hi, h]

/-! ### Reading atom fields -/

/-- Two arrays whose entries agree under `f` at `j` agree under `f` read with `!`. -/
lemma getElem!_eq_of_map {α β : Type*} [Inhabited α] {a b : Array α} (f : α → β) {j : ℕ}
    (h : b[j]?.map f = a[j]?.map f) : f b[j]! = f a[j]! := by
  simp only [getElem!_def]
  cases ha : a[j]? <;> cases hb : b[j]? <;> simp_all

/-- Assigning radicals changes nothing about the atoms but their radicals. -/
lemma getElem?_assignRadicals_atoms (w : Work) (j : ℕ) :
    w.assignRadicals.atoms[j]?.map (fun a : WAtom ↦ { a with radicals := 0 }) =
      w.atoms[j]?.map (fun a : WAtom ↦ { a with radicals := 0 }) := by
  unfold assignRadicals
  generalize List.range w.numAtoms = l
  induction l generalizing w with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih]
    unfold radicalStep
    dsimp only
    split
    · rfl
    · rw [getElem?_modifyAtom_atoms]
      split <;> simp [Option.map_map, Function.comp_def]

/-- A field other than the radicals, read through `assignRadicals`. -/
lemma getElem?_assignRadicals_map {β : Type*} (w : Work) (f : WAtom → β)
    (hf : ∀ a : WAtom, f { a with radicals := 0 } = f a) (j : ℕ) :
    w.assignRadicals.atoms[j]?.map f = w.atoms[j]?.map f := by
  have := congrArg (Option.map f) (getElem?_assignRadicals_atoms w j)
  simpa [Option.map_map, Function.comp_def, hf] using this

/-- `assignRadicals` keeps every atom's written hydrogens. -/
lemma explicitHs_assignRadicals (w : Work) (i : ℕ) :
    (w.assignRadicals.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs :=
  getElem!_eq_of_map (fun x : WAtom ↦ x.explicitHs)
    (getElem?_assignRadicals_map w _ (fun _ ↦ rfl) i)

/-- `assignRadicals` keeps every cached valence. -/
lemma cachedValence_assignRadicals (w : Work) (i : ℕ) :
    w.assignRadicals.cachedValence i = w.cachedValence i := by
  have h1 : (w.assignRadicals.atoms[i]! : WAtom).cachedValence =
      (w.atoms[i]! : WAtom).cachedValence :=
    getElem!_eq_of_map (fun x : WAtom ↦ x.cachedValence)
      (getElem?_assignRadicals_map w _ (fun _ ↦ rfl) i)
  simp only [cachedValence, kekuleValence, h1, explicitHs_assignRadicals, bondHalfSum, bondsOf,
    numBonds, assignRadicals_bonds]

/-- `cacheValences` caches every atom's explicit valence. -/
lemma cachedValence_cacheValences_atom (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    (w.cacheValences.atoms[i]! : WAtom).cachedValence = some (w.explicitValence i) := by
  rw [getElem!_pos _ i (by simpa [cacheValences, numAtoms] using hi)]
  simp [cacheValences, numAtoms]

/-! ### A copy with nothing aromatic -/

/-- With no aromatic bond, every bond-order sum is whole: twice it is even. -/
lemma two_dvd_bondHalfSum {w : Work} (h : ∀ b ∈ w.bonds, b.kind ≠ .aromatic) (i : ℕ) :
    2 ∣ w.bondHalfSum i := by
  unfold bondHalfSum
  have key : ∀ l : List ℕ, (∀ k ∈ l, k < w.bonds.size) →
      2 ∣ (l.map fun k ↦ halfOrder (w.bonds[k]! : WBond).kind).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons k l ih =>
      rw [List.map_cons, List.sum_cons]
      refine Nat.dvd_add ?_ (ih fun k' hk' ↦ hl k' (List.mem_cons_of_mem _ hk'))
      have hlt := hl k List.mem_cons_self
      rw [getElem!_pos _ k hlt]
      have := h _ (Array.getElem_mem hlt)
      cases hkind : (w.bonds[k]).kind <;> simp_all [halfOrder]
  exact key _ fun k hk ↦ Swapped.mem_bondsOf_lt hk

/-- With nothing aromatic, no atom is aromatic. -/
lemma isAromaticAtom_of_noArom {w : Work} (h : w.NoArom) (i : ℕ) : w.isAromaticAtom i = false := by
  unfold isAromaticAtom
  rw [Bool.or_eq_false_iff]
  refine ⟨?_, ?_⟩
  · by_cases hi : i < w.atoms.size
    · rw [getElem!_pos _ i hi]
      exact h.1 _ (Array.getElem_mem hi)
    · rw [getElem!_neg _ i hi]
      rfl
  · rw [List.any_eq_false]
    intro k hk hkk
    have hlt := Swapped.mem_bondsOf_lt hk
    rw [getElem!_pos _ k hlt] at hkk
    exact h.2 _ (Array.getElem_mem hlt) (by simpa using hkk)

/-- **With nothing aromatic, the explicit valence is the written hydrogens plus the bond-order
sum**: RDKit's aromatic rounding does not apply. -/
lemma explicitValence_of_noArom {w : Work} (h : w.NoArom) (i : ℕ) :
    w.explicitValence i = (w.atoms[i]! : WAtom).explicitHs + w.bondHalfSum i / 2 := by
  have hA := isAromaticAtom_of_noArom h i
  obtain ⟨c, hc⟩ := two_dvd_bondHalfSum h.2 i
  unfold explicitValence
  simp only [hA, Bool.and_false]
  split <;> (try split) <;> simp_all [Id.run_pure] <;> omega

/-- **With nothing aromatic, the cached valence less the written hydrogens is the bond-order
sum**, after `cacheValences` and radicals. -/
lemma cachedValence_sub_of_noArom {w : Work} (h : w.NoArom) (i : ℕ) :
    (w.cacheValences.assignRadicals.cachedValence i : ℤ) -
        (w.cacheValences.assignRadicals.atoms[i]! : WAtom).explicitHs =
      ((w.cacheValences.assignRadicals.bondHalfSum i / 2 : ℕ) : ℤ) := by
  set c := w.cacheValences with hc
  have hb : c.assignRadicals.bonds = c.bonds := assignRadicals_bonds _
  have hhs : c.assignRadicals.bondHalfSum = c.bondHalfSum := by
    funext j
    simp only [bondHalfSum, bondsOf, numBonds, hb]
  have heH : (c.assignRadicals.atoms[i]! : WAtom).explicitHs = (c.atoms[i]! : WAtom).explicitHs :=
    getElem!_eq_of_map (fun x : WAtom ↦ x.explicitHs)
      (getElem?_assignRadicals_map _ _ (fun _ ↦ rfl) i)
  have hcv : (c.assignRadicals.atoms[i]! : WAtom).cachedValence =
      (c.atoms[i]! : WAtom).cachedValence :=
    getElem!_eq_of_map (fun x : WAtom ↦ x.cachedValence)
      (getElem?_assignRadicals_map _ _ (fun _ ↦ rfl) i)
  have hcb : c.bondHalfSum = w.bondHalfSum := by
    funext j
    simp only [bondHalfSum, bondsOf, numBonds, hc, cacheValences_bonds]
  simp only [cachedValence, kekuleValence, hcv, heH, hhs, hcb]
  by_cases hi : i < w.atoms.size
  · have hi' : i < c.atoms.size := by simpa [hc] using hi
    have hget := getElem?_cacheValences_atoms w i
    rw [← hc, Array.getElem?_eq_getElem hi', Array.getElem?_eq_getElem hi] at hget
    simp only [Option.map_some, Option.some.injEq] at hget
    have e1 : (c.atoms[i]! : WAtom).cachedValence = some (w.explicitValence i) := by
      rw [getElem!_pos _ i hi', hget]
    have e2 : (c.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs := by
      rw [getElem!_pos _ i hi', hget, getElem!_pos _ i hi]
    rw [e1, Option.getD_some, explicitValence_of_noArom h i, e2]
    omega
  · have hi' : ¬ i < c.atoms.size := by simpa [hc] using hi
    rw [getElem!_neg _ i hi']
    have d1 : (default : WAtom).cachedValence = none := rfl
    have d2 : (default : WAtom).explicitHs = 0 := rfl
    simp [d1, d2]

end LeanSMILES.Aromaticity.Work
