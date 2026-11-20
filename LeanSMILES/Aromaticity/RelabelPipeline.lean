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

## Main definitions

* `finPermFun`: a permutation of `Fin n` acting on atom numbers, the identity past `n`.

## Main statements

* `Work.ofMolecule_relabel`: the working copy of a relabeled molecule is the relabeled copy.
* `Work.finish_relabelW`: the passes after kekulization commute with relabeling.
* `Work.quiet_relabelW`: a copy `cleanUp` leaves alone stays so when relabeled.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A permutation of `Fin n` acting on atom numbers (the identity past `n`). -/
def finPermFun {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ → ℕ :=
  fun i ↦ if h : i < n then (σ ⟨i, h⟩).val else i

/-- `finPermFun σ` sends atom numbers below `n` below `n`. -/
lemma finPermFun_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) : finPermFun σ i < n := by
  simp [finPermFun, h]

/-- On the number of an atom `i : Fin n`, `finPermFun σ` is `σ i`. -/
lemma finPermFun_fin {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    finPermFun σ i.val = (σ i).val := by
  simp [finPermFun]

/-- `finPermFun σ` and `finPermFun σ.symm` are inverse bijections of the first `n` numbers. -/
lemma idxBij_finPermFun {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Work.IdxBij n (finPermFun σ) (finPermFun σ.symm) :=
  ⟨fun _ h ↦ finPermFun_lt σ h, fun _ h ↦ finPermFun_lt σ.symm h,
    fun i h ↦ by simp [finPermFun, h], fun i h ↦ by simp [finPermFun, h]⟩

namespace Work

/-- Entry `j < n` of `f` mapped over `Fin n` as an array is `f ⟨j, hj⟩`. -/
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

/-- Perception keeps a working copy well formed and keeps its number of atoms. -/
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

/-! ### `cleanUp` -/

section CleanUp

variable {w : Work} {σ ψ : ℕ → ℕ}

/-- In a well-formed copy, a `(bond, neighbor)` pair of an atom has its bond and its neighbor in
range. -/
lemma nbr_lt (hwf : w.WF) {i : ℕ} {x : ℕ × ℕ} (hx : x ∈ w.neighbors i) :
    x.1 < w.bonds.size ∧ x.2 < w.atoms.size := by
  refine ⟨?_, (Adj.lt hwf (adj_of_mem_neighbors (k := x.1) hx)).2⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk
  exact hk.1

/-- A renamed atom is a `nitroCand` exactly when the original atom is. -/
lemma nitroCand_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).nitroCand (σ i) = w.nitroCand i := by
  simp only [nitroCand, atom_relabelW hb hi, explicitValence_relabelW hwf hb hi]

/-- A neighbor pair of an atom, its neighbor renamed, is a `nitroO` in the renamed copy exactly
when it is one in `w`. -/
lemma nitroO_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ w.neighbors i) : (w.relabelW σ ψ).nitroO (x.1, σ x.2) = w.nitroO x := by
  simp only [nitroO, atom_relabelW hb (nbr_lt hwf hx).2, kind_relabelW]

/-- A neighbor pair of an atom, its neighbor renamed, is an `azideN` in the renamed copy exactly
when it is one in `w`. -/
lemma azideN_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ w.neighbors i) : (w.relabelW σ ψ).azideN (x.1, σ x.2) = w.azideN x := by
  simp only [azideN, atom_relabelW hb (nbr_lt hwf hx).2, kind_relabelW]

/-- At a renamed atom, `phosphorusScan` finds a `=O` exactly when it does at the original atom,
and the same `=C`/`=N` flag. -/
lemma phosphorusScan_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    ((w.relabelW σ ψ).phosphorusScan (σ i)).1.isSome = (w.phosphorusScan i).1.isSome ∧
      ((w.relabelW σ ψ).phosphorusScan (σ i)).2 = (w.phosphorusScan i).2 := by
  unfold phosphorusScan
  rw [neighbors_relabelW hwf hb hi, List.foldl_map]
  refine foldl_sim (fun (p q : Option (ℕ × ℕ) × Bool) ↦ q.1.isSome = p.1.isSome ∧ q.2 = p.2)
    _ _ _ _ _ ⟨rfl, rfl⟩ ?_
  rintro ⟨b1, b2⟩ ⟨c1, c2⟩ ⟨k, j⟩ ha ⟨h1, h2⟩
  have hj := (nbr_lt hwf ha).2
  dsimp only at h1 h2 ⊢
  rw [atom_relabelW hb hj, degree_relabelW hwf hb hj, kind_relabelW]
  split_ifs <;> simp_all

/-- `cleanUpStep` changes nothing at `i` exactly when, for phosphorus, `phosphorusCleanup` changes
nothing, and for chlorine, bromine or iodine, `halogenCleanup` changes nothing. -/
lemma cleanUpStep_eq_iff' {i : ℕ} :
    cleanUpStep w i = w ↔
      ((w.atoms[i]! : WAtom).z = 15 → w.phosphorusCleanup i = w) ∧
      ((w.atoms[i]! : WAtom).z ≠ 15 →
        ((w.atoms[i]! : WAtom).z = 17 ∨ (w.atoms[i]! : WAtom).z = 35 ∨
          (w.atoms[i]! : WAtom).z = 53) → w.halogenCleanup i = w) := by
  unfold cleanUpStep
  dsimp only
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    exact ⟨fun e ↦ ⟨fun _ ↦ e, fun hne ↦ absurd h hne⟩, fun ⟨e, _⟩ ↦ e h⟩
  · rename_i h
    simp only [beq_iff_eq] at h
    split
    · rename_i h'
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at h'
      exact ⟨fun e ↦ ⟨fun hz ↦ absurd hz h, fun _ _ ↦ e⟩, fun ⟨_, e⟩ ↦ e h h'⟩
    · rename_i h'
      simp only [Bool.or_eq_true, beq_iff_eq, or_assoc] at h'
      exact ⟨fun _ ↦ ⟨fun hz ↦ absurd hz h, fun _ hh ↦ absurd hh h'⟩, fun _ ↦ rfl⟩

/-- **A copy `cleanUp` leaves alone stays so when relabeled.** -/
theorem quiet_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (hq : w.Quiet) :
    (w.relabelW σ ψ).Quiet := by
  obtain ⟨q1, q2, q3⟩ := hq
  have hσ : ∀ i' < (w.relabelW σ ψ).atoms.size, ∃ i < w.atoms.size, i' = σ i := fun i' hi' ↦
    ⟨ψ i', hb.lt' i' (by simpa using hi'), (hb.right i' (by simpa using hi')).symm⟩
  refine ⟨fun i' hi' ↦ ?_, fun i' hi' hc ↦ ?_, fun i' hi' ↦ ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hσ i' hi'
    rw [nitroStep_fst_eq_iff, nitroCand_relabelW hwf hb hi, neighbors_relabelW hwf hb hi]
    have := (nitroStep_fst_eq_iff (w := w) [] i).1 (q1 i hi)
    intro hc x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [nitroO_relabelW hwf hb hy]
    exact this hc y hy
  · obtain ⟨i, hi, rfl⟩ := hσ i' hi'
    rw [nitroCand_relabelW hwf hb hi] at hc
    rw [azideStep_eq_iff, neighbors_relabelW hwf hb hi]
    have := (azideStep_eq_iff (w := w) i).1 (q2 i hi hc)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [azideN_relabelW hwf hb hy]
    exact this y hy
  · obtain ⟨i, hi, rfl⟩ := hσ i' hi'
    have hi'' : σ i < (w.relabelW σ ψ).atoms.size := hi'
    obtain ⟨c1, c2⟩ := cleanUpStep_eq_iff'.1 (q3 i hi)
    rw [cleanUpStep_eq_iff', atom_relabelW hb hi]
    refine ⟨fun hz ↦ ?_, fun hz hz' ↦ ?_⟩
    · have := (phosphorusCleanup_eq_iff w hi).1 (c1 hz)
      rw [phosphorusCleanup_eq_iff _ hi'']
      obtain ⟨s1, s2⟩ := phosphorusScan_relabelW hwf hb hi
      simp only [phosphorusGuard, atom_relabelW hb hi, explicitValence_relabelW hwf hb hi,
        degree_relabelW hwf hb hi, s1, s2] at this ⊢
      exact this
    · have := (halogenCleanup_eq_iff w hi).1 (c2 hz hz')
      rw [halogenCleanup_eq_iff _ hi'']
      simp only [halogenGuard, atom_relabelW hb hi, explicitValence_relabelW hwf hb hi,
        neighbors_relabelW hwf hb hi, List.all_map, List.forall_mem_map] at this ⊢
      have hall : ((w.neighbors i).all ((fun x ↦ (w.relabelW σ ψ).atoms[x.2]!.z == 8) ∘
          fun e ↦ (e.1, σ e.2))) = (w.neighbors i).all (fun x ↦ w.atoms[x.2]!.z == 8) := by
        rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
        exact forall₂_congr fun y hy ↦ by
          simp only [Function.comp_apply, atom_relabelW hb (nbr_lt hwf hy).2]
      intro hg x hx
      rw [kind_relabelW]
      rw [hall] at hg
      exact this hg x hx

end CleanUp

end Work

end LeanSMILES.Aromaticity
