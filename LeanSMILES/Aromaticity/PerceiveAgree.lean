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

* the same bonds, elements, charges and radicals;
* the same cached hydrogen total (written plus implied), and the same cached valence less written
  hydrogens (the bond part of the valence);
* on the first copy, that bond part is the Kekulé bond-order sum (what kekulization makes true);
* at every atom of a ring, the same `countAtomElec`.

Then `donorData`, and so `aromaticBondList`, are the same (`PerceiveAgree.donorData_eq`,
`PerceiveAgree.aromaticBondList_eq`).  The one place perception reads a cached valence alone,
`isAromaticCandidate`'s "two multiple bonds at an atom of valence above degree + 1", cannot tell
the copies apart: where they differ there, the atom has at most one multiple bond.
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
  /-- The same radicals. -/
  radicals : ∀ i : ℕ, (w'.atoms[i]! : WAtom).radicals = (w.atoms[i]! : WAtom).radicals
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
  /-- At every atom of a ring, the same `countAtomElec`. -/
  elec : ∀ ring ∈ rings.toList, ∀ i ∈ ring, w'.countAtomElec i = w.countAtomElec i

namespace PerceiveAgree

variable {rings : Array (List ℕ)} {w w' : Work} (h : PerceiveAgree rings w w')
include h

lemma numAtoms_eq : w'.numAtoms = w.numAtoms := h.size

lemma bondsOf_eq : w'.bondsOf = w.bondsOf := by
  funext i
  simp only [bondsOf, numBonds, h.bonds]

lemma neighbors_eq : w'.neighbors = w.neighbors := by
  funext i
  simp only [neighbors, h.bondsOf_eq, h.bonds]

lemma degree_eq : w'.degree = w.degree := by
  funext i
  simp only [degree, h.bondsOf_eq]

lemma bondBetween?_eq : w'.bondBetween? = w.bondBetween? := by
  funext i j
  simp only [bondBetween?, numBonds, h.bonds]

lemma ringBonds_eq : w'.ringBonds = w.ringBonds := by
  funext r
  simp only [ringBonds, h.bondBetween?_eq]

lemma bondHalfSum_eq : w'.bondHalfSum = w.bondHalfSum := by
  funext i
  simp only [bondHalfSum, h.bondsOf_eq, h.bonds]

lemma hasMultipleBond_eq : w'.hasMultipleBond = w.hasMultipleBond := by
  funext i
  simp only [hasMultipleBond, h.bondsOf_eq, h.bonds]

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

/-- **The candidate test sees the same.**  Its one read of the cached valence alone, "more than
one multiple bond at an atom of valence above degree + 1", cannot differ: where the two copies
fall on different sides of degree + 1, the bond part is at most degree + 1, so the atom has at
most one multiple bond. -/
lemma isAromaticCandidate_eq (i : ℕ) (d : Donor) :
    w'.isAromaticCandidate i d = w.isAromaticCandidate i d := by
  have hcv := h.cachedValence_add_cachedImplicit i
  have hbp := h.bondPart i
  have hk := h.kekule i
  have hle := length_filter_isMultiple_add_degree_le w i fun k hk' hkk ↦ by
    have hlt := Swapped.mem_bondsOf_lt hk'
    rw [getElem!_pos w.bonds k hlt] at hkk
    exact h.noArom _ (Array.getElem_mem hlt) hkk
  unfold isAromaticCandidate
  simp only [Id.run, h.z, h.charge, h.radicals, h.degree_eq, h.bondsOf_eq, h.bonds, hcv]
  by_cases hM : 1 < ((w.bondsOf i).filter fun k ↦ isMultiple (w.bonds[k]! : WBond).kind).length
  · have key : w.degree i + 1 < w'.cachedValence i ↔ w.degree i + 1 < w.cachedValence i := by
      omega
    simp only [key]
  · simp [hM]

/-- **The donor type of a ring atom is the same**: it reads `countAtomElec` (the same at ring
atoms), the bonds and neighbours' elements, and the cached valence only through "is it more than
degree plus written hydrogens", which is the bond part against the degree. -/
lemma donorType_eq (rbs : List ℕ) {ring : List ℕ} (hr : ring ∈ rings.toList) {i : ℕ}
    (hi : i ∈ ring) : w'.donorType rbs i = w.donorType rbs i := by
  have hbp := h.bondPart i
  have hne : (w'.cachedValence i != w.degree i + (w'.atoms[i]! : WAtom).explicitHs) =
      (w.cachedValence i != w.degree i + (w.atoms[i]! : WAtom).explicitHs) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
    omega
  unfold donorType
  simp only [Id.run, h.elec ring hr i hi, h.exocyclicMultiple?_eq, h.z, h.charge, h.degree_eq,
    h.bondsOf_eq, h.bonds, hne]

/-- The donor type a ring gives its atom is the same. -/
lemma ringDonor_eq (rbs : List ℕ) {ring : List ℕ} (hr : ring ∈ rings.toList) (len : ℕ) {i : ℕ}
    (hi : i ∈ ring) : w'.ringDonor rbs len i = w.ringDonor rbs len i := by
  simp only [ringDonor, h.donorType_eq rbs hr hi, h.z, h.charge, h.degree_eq,
    h.hasMultipleBond_eq]

/-- **The first pass of perception is the same**: it visits only ring atoms, where the donor
types and candidacies agree. -/
lemma donorData_eq : w'.donorData rings = w.donorData rings := by
  unfold donorData
  rw [h.ringBonds_eq, h.numAtoms_eq]
  refine foldl_congr_mem (fun s ring hr ↦ ?_) _
  unfold donorRingStep
  rw [foldl_congr_mem (g := w.donorAtomStep ((rings.toList.flatMap w.ringBonds).eraseDups)
    ring.length) (fun p i hi ↦ by
    simp only [donorAtomStep, h.ringDonor_eq _ hr _ hi, h.isAromaticCandidate_eq]) (s, true)]

/-- **The same bonds are made aromatic.** -/
lemma aromaticBondList_eq : w'.aromaticBondList rings = w.aromaticBondList rings := by
  simp only [aromaticBondList, h.donorData_eq, h.numAtoms_eq, h.ringBonds_eq]

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

lemma aromatic_getElem! (h : SameMarks w w') (j : ℕ) :
    (w'.atoms[j]! : WAtom).aromatic = (w.atoms[j]! : WAtom).aromatic := by
  have := h.flags j
  simp only [getElem!_def]
  cases h1 : w'.atoms[j]? <;> cases h2 : w.atoms[j]? <;> simp_all <;> rfl

lemma isAromaticAtom_eq (h : SameMarks w w') : w'.isAromaticAtom = w.isAromaticAtom := by
  funext i
  simp only [isAromaticAtom, h.aromatic_getElem!, bondsOf, numBonds, h.bonds]

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

end LeanSMILES.Aromaticity.Work
