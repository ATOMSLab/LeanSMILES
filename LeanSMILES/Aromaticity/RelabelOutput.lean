/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeRelabel

/-!
# LeanSMILES.Aromaticity.RelabelOutput

The output molecule from a relabeled working copy is the relabeled output
(`Molecule.aromatizeOutput_relabel`).
-/

@[expose] public section

namespace LeanSMILES

open Aromaticity Aromaticity.Work

lemma Molecule.outAtom_relabel {n : ℕ} (m : Molecule n) {W : Work} (hwf : WF W)
    (hn : W.atoms.size = n) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (m.relabel σ).outAtom (W.relabelW (finPermFun σ) (finPermFun σ.symm)) j =
      m.outAtom W (σ.symm j) := by
  have hb : IdxBij W.numAtoms (finPermFun σ) (finPermFun σ.symm) := by
    rw [numAtoms, hn]; exact idxBij_finPermFun σ
  have hi : (σ.symm j).val < W.atoms.size := by rw [hn]; exact (σ.symm j).isLt
  have hj : j.val = finPermFun σ (σ.symm j).val := by rw [finPermFun_fin]; simp
  have ha : (m.relabel σ).atom j = m.atom (σ.symm j) := by
    have := Molecule.atom_relabel m σ (σ.symm j)
    rwa [Equiv.apply_symm_apply] at this
  unfold Molecule.outAtom
  dsimp only
  rw [ha, hj, atom_relabelW hb hi, implicitHs_relabelW hwf hb hi, isAromaticAtom_relabelW hwf hb hi]

lemma withKinds_relabel {n : ℕ} (m : Molecule n) (W : Work) (σ : Equiv.Perm (Fin n)) :
    withKinds (m.relabel σ) (W.relabelW (finPermFun σ) (finPermFun σ.symm)) =
      (withKinds m W).map (Bond.map σ σ.injective) := by
  unfold withKinds
  simp only [Molecule.relabel, List.zipIdx_map, List.map_map]
  apply List.map_congr_left
  rintro ⟨b, k⟩ -
  simp only [Function.comp_apply, Prod.map, getElem?_relabelW_bonds, Option.map_map]
  rfl

/-- **The output from a relabeled working copy is the relabeled output.** -/
theorem Molecule.aromatizeOutput_relabel {n : ℕ} (m : Molecule n) {W : Work} (hwf : WF W)
    (hn : W.atoms.size = n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).aromatizeOutput (W.relabelW (finPermFun σ) (finPermFun σ.symm)) =
      (m.aromatizeOutput W).relabel σ := by
  unfold Molecule.aromatizeOutput
  rw [← Molecule.normalizeBrackets_relabel]
  congr 1
  apply Molecule.ext
  · apply Vector.ext
    intro j hj
    have e := Molecule.outAtom_relabel m hwf hn σ ⟨j, hj⟩
    simpa [Molecule.relabel] using e
  · simp only [Molecule.relabel]
    exact withKinds_relabel m W σ
  · rfl

end LeanSMILES
