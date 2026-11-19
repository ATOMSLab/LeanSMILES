/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RelabelPerceive

/-!
# LeanSMILES.Aromaticity.RelabelPipeline

The pipeline commutes with relabeling the atoms

A permutation `σ` of `Fin n` acts on atom numbers (`finPermFun`); the working copy of the relabeled
molecule is the relabeled working copy (`Work.ofMolecule_relabel`), and the passes after
kekulization commute with it (`Work.finish_relabelW`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A permutation of `Fin n` acting on atom numbers (the identity past `n`). -/
def finPermFun {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ → ℕ :=
  fun i ↦ if h : i < n then (σ ⟨i, h⟩).val else i

lemma finPermFun_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) : finPermFun σ i < n := by
  simp [finPermFun, h]

lemma finPermFun_fin {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    finPermFun σ i.val = (σ i).val := by
  simp [finPermFun]

lemma idxBij_finPermFun {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Work.IdxBij n (finPermFun σ) (finPermFun σ.symm) :=
  ⟨fun _ h ↦ finPermFun_lt σ h, fun _ h ↦ finPermFun_lt σ.symm h,
    fun i h ↦ by simp [finPermFun, h], fun i h ↦ by simp [finPermFun, h]⟩

namespace Work

lemma getElem!_finRangeMap {α : Type} [Inhabited α] {n : ℕ} (f : Fin n → α) {j : ℕ}
    (hj : j < n) : ((List.finRange n).toArray.map f)[j]! = f ⟨j, hj⟩ := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

/-- **The working copy of a relabeled molecule is the relabeled working copy.** -/
theorem ofMolecule_relabel {n : ℕ} (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    Work.ofMolecule (m.relabel σ) =
      (Work.ofMolecule m).relabelW (finPermFun σ) (finPermFun σ.symm) := by
  apply ext_work
  · apply array_ext_of_getElem! (n := n) (by simp [Work.ofMolecule])
      (by simp [Work.ofMolecule, relabelW])
    intro j hj
    rw [atom_relabelW' (by simpa [Work.ofMolecule] using hj)]
    simp only [Work.ofMolecule]
    rw [getElem!_finRangeMap _ hj, getElem!_finRangeMap _ (finPermFun_lt σ.symm hj)]
    have e : (m.relabel σ).atom ⟨j, hj⟩ =
        m.atom ⟨finPermFun σ.symm j, finPermFun_lt σ.symm hj⟩ := by
      have := Molecule.atom_relabel m σ (σ.symm ⟨j, hj⟩)
      rw [Equiv.apply_symm_apply] at this
      rw [this]
      congr 1
      ext
      simp [finPermFun, hj]
    rw [e]
  · simp only [Work.ofMolecule, relabelW, Molecule.relabel, Array.map_map]
    apply Array.ext'
    simp only [Array.toList_map, List.map_map]
    apply List.map_congr_left
    intro b _
    simp [Bond.map, finPermFun_fin]

lemma setAromaticity_wf_size {w : Work} (hwf : w.WF) (R : Array (List ℕ)) :
    (w.setAromaticity R).WF ∧ (w.setAromaticity R).atoms.size = w.atoms.size := by
  unfold setAromaticity
  generalize w.aromaticBondList R = L
  induction L generalizing w with
  | nil => exact ⟨hwf, rfl⟩
  | cons b L ih =>
    have ha : (w.markAromatic b).atoms.size = w.atoms.size := by
      unfold markAromatic; dsimp only; split <;> simp [modifyAtom, setKind]
    obtain ⟨h1, h2⟩ := ih (wf_markAromatic hwf b)
    exact ⟨h1, h2.trans ha⟩

/-- **The passes after kekulization commute with relabeling.** -/
theorem finish_relabelW {w : Work} {σ ψ : ℕ → ℕ} (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ)
    {R : Array (List ℕ)} (hR : ∀ r ∈ R.toList, ∀ a ∈ r, a < w.atoms.size) :
    (w.relabelW σ ψ).finish (R.map (List.map σ)) = (w.finish R).relabelW σ ψ := by
  unfold finish
  have hsz1 : w.assignRadicals.atoms.size = w.atoms.size := atomStep_radicalStep.foldl_size _ _
  have hwf1 : w.assignRadicals.WF := wf_of_bonds (assignRadicals_bonds w) hsz1 hwf
  have hb1 : IdxBij w.assignRadicals.numAtoms σ ψ := by rw [numAtoms, hsz1]; exact hb
  have hsz2 := (setAromaticity_wf_size hwf1 R).2
  have hwf2 := (setAromaticity_wf_size hwf1 R).1
  have hb2 : IdxBij (w.assignRadicals.setAromaticity R).numAtoms σ ψ := by
    rw [numAtoms, hsz2, hsz1]; exact hb
  rw [assignRadicals_relabelW hwf hb,
    setAromaticity_relabelW hwf1 hb1 (fun r hr a ha ↦ hsz1 ▸ hR r hr a ha),
    finalizeHs_relabelW hwf2 hb2]

end Work

end LeanSMILES.Aromaticity
