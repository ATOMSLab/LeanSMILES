/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.WorkRelabel
public import LeanSMILES.Aromaticity.HsRestoreK

/-!
# LeanSMILES.Aromaticity.RelabelPerceive

Perception commutes with renumbering the atoms

Donor types and candidacies are read at an atom and across its first exocyclic multiple bond, so
they follow the renaming (`Work.ringDonor_relabelW`); the first pass of perception over the renamed
rings is the renamed first pass, and Hückel's rule reads only the donor types of a group's atoms,
so the bonds perception marks are the same bonds (`Work.aromaticBondList_relabelW`), and marking
them commutes with the renaming (`Work.setAromaticity_relabelW`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

variable {w : Work} {σ ψ : ℕ → ℕ}

lemma cachedValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).cachedValence (σ i) = w.cachedValence i := by
  rw [cachedValence_eq_loc, cachedValence_eq_loc, kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

lemma countAtomElec_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).countAtomElec (σ i) = w.countAtomElec i := by
  rw [countAtomElec_eq_loc, countAtomElec_eq_loc, kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

lemma exocyclicMultiple?_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {i : ℕ} (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).exocyclicMultiple? B (σ i) = (w.exocyclicMultiple? B i).map σ := by
  unfold exocyclicMultiple?
  rw [neighbors_relabelW hwf hb hi, List.find?_map, Option.map_map, Option.map_map]
  congr 1
  · congr 1
    funext e
    simp only [Function.comp, kind_relabelW]

lemma hasMultipleBond_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).hasMultipleBond (σ i) = w.hasMultipleBond i := by
  simp only [hasMultipleBond, bondsOf_relabelW hwf hb hi, kind_relabelW]

lemma donorType_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).donorType B (σ i) = w.donorType B i := by
  have hex := exocyclicMultiple?_relabelW hwf hb B hi
  have hz : ∀ j, w.exocyclicMultiple? B i = some j →
      ((w.relabelW σ ψ).atoms[σ j]! : WAtom) = w.atoms[j]! := fun j hj ↦ by
    have : j < w.atoms.size := by
      unfold exocyclicMultiple? at hj
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hj
      exact (Adj.lt hwf (adj_of_mem_neighbors (k := e.1)
        (List.mem_of_find?_eq_some he))).2
    exact atom_relabelW hb this
  unfold donorType
  simp only [Id.run, countAtomElec_relabelW hwf hb hi, hex, atom_relabelW hb hi,
    bondsOf_relabelW hwf hb hi, kind_relabelW, cachedValence_relabelW hwf hb hi,
    degree_relabelW hwf hb hi]
  cases h : w.exocyclicMultiple? B i with
  | none => rfl
  | some j => simp [hz j h]

lemma ringDonor_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ) (len : ℕ)
    {i : ℕ} (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).ringDonor B len (σ i) = w.ringDonor B len i := by
  simp only [ringDonor, donorType_relabelW hwf hb B hi, atom_relabelW hb hi,
    degree_relabelW hwf hb hi, hasMultipleBond_relabelW hwf hb hi]

lemma isAromaticCandidate_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) (d : Donor) :
    (w.relabelW σ ψ).isAromaticCandidate (σ i) d = w.isAromaticCandidate i d := by
  by_cases hd : d = .none
  · subst hd
    have hnn : (Donor.none == Donor.none) = true := rfl
    simp [isAromaticCandidate, Id.run, hnn]
  · rw [isAromaticCandidate_eq_loc _ _ hd, isAromaticCandidate_eq_loc _ _ hd,
      kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

/-- The bonds of a ring of atoms in range are the same bonds once renamed. -/
lemma ringBonds_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {r : List ℕ}
    (hr : ∀ a ∈ r, a < w.atoms.size) : (w.relabelW σ ψ).ringBonds (r.map σ) = w.ringBonds r := by
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.length_map]
  apply List.filterMap_congr
  intro t ht
  rw [List.mem_range] at ht
  have h2 : (t + 1) % r.length < r.length := Nat.mod_lt _ (by omega)
  rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ _ (by simpa using h2),
    List.getElem_map, List.getElem_map, bondBetween?_relabelW hwf hb (hr _ (List.getElem_mem _))
      (hr _ (List.getElem_mem _)), ← getElem!_pos r t ht, ← getElem!_pos r _ h2]

/-! ### The first pass -/

lemma contains_map_σ (hb : IdxBij w.numAtoms σ ψ) {r : List ℕ} (hr : ∀ a ∈ r, a < w.atoms.size)
    {i : ℕ} (hi : i < w.atoms.size) : (r.map σ).contains (σ i) = r.contains i := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨a, ha, e⟩ ↦ hb.inj (hr a ha) hi e ▸ ha, fun h ↦ ⟨i, h, rfl⟩⟩

lemma find?_map_σ (hb : IdxBij w.numAtoms σ ψ) {L : List (List ℕ)}
    (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ} (hi : i < w.atoms.size) :
    (L.map (List.map σ)).find? (·.contains (σ i)) = (L.find? (·.contains i)).map (List.map σ) := by
  rw [List.find?_map]
  congr 1
  exact find?_congr_mem fun r hr ↦ by
    simp only [Function.comp]
    exact contains_map_σ hb (hL r hr) hi

lemma firstDonor_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {L : List (List ℕ)} (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ}
    (hi : i < w.atoms.size) :
    firstDonor (w.relabelW σ ψ) B (L.map (List.map σ)) (σ i) = firstDonor w B L i := by
  unfold firstDonor
  rw [find?_map_σ hb hL hi]
  cases L.find? (·.contains i) with
  | none => rfl
  | some r => simp only [Option.map_some, List.length_map, ringDonor_relabelW hwf hb B _ hi]

lemma firstCand_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {L : List (List ℕ)} (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ}
    (hi : i < w.atoms.size) :
    firstCand (w.relabelW σ ψ) B (L.map (List.map σ)) (σ i) = firstCand w B L i := by
  unfold firstCand
  rw [find?_map_σ hb hL hi]
  cases L.find? (·.contains i) with
  | none => rfl
  | some r => simp only [Option.map_some, List.length_map, ringDonor_relabelW hwf hb B _ hi,
      isAromaticCandidate_relabelW hwf hb hi]

/-- **The first pass of perception follows the renaming**: over the renamed rings, the renamed
atoms get the same donor types, and the candidate rings are the renamed ones. -/
theorem donorData_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {R : Array (List ℕ)}
    (hR : ∀ r ∈ R.toList, ∀ a ∈ r, a < w.atoms.size) :
    (∀ i < w.atoms.size, ((w.relabelW σ ψ).donorData (R.map (List.map σ))).donor[σ i]! =
      (w.donorData R).donor[i]!) ∧
    ((w.relabelW σ ψ).donorData (R.map (List.map σ))).donor.size = w.atoms.size ∧
    ((w.relabelW σ ψ).donorData (R.map (List.map σ))).candRings.toList =
      (w.donorData R).candRings.toList.map (List.map σ) := by
  have I := donorData_inv w R
  have I' := donorData_inv (w.relabelW σ ψ) (R.map (List.map σ))
  have hB : ((R.map (List.map σ)).toList.flatMap (w.relabelW σ ψ).ringBonds).eraseDups =
      (R.toList.flatMap w.ringBonds).eraseDups := by
    rw [Array.toList_map, List.flatMap_map]
    congr 1
    exact flatMap_congr_mem _ fun r hr ↦ ringBonds_relabelW hwf hb (hR r hr)
  rw [hB] at I'
  rw [Array.toList_map] at I'
  refine ⟨fun i hi ↦ ?_, by rw [I'.donor_size]; simp [numAtoms], ?_⟩
  · rw [I'.donor _ (by simpa [numAtoms] using hb.lt i hi), I.donor _ hi,
      firstDonor_relabelW hwf hb _ hR hi]
  · rw [I'.candRings, I.candRings, List.filter_map]
    congr 1
    apply List.filter_congr
    intro r hr
    simp only [Function.comp_apply, List.all_map, numAtoms_relabelW]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun a ha ↦ ?_
    have hra := hR r hr a ha
    simp only [Function.comp_apply]
    rw [firstCand_relabelW hwf hb _ hR hra]
    have h1 : σ a < w.atoms.size := hb.lt a hra
    simp [numAtoms, h1, hra]

end Work

end LeanSMILES.Aromaticity
