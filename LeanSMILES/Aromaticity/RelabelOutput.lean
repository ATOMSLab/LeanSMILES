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

## Main statements

* `Molecule.outAtom_relabel`: an output atom read from a relabeled copy is the original one's.
* `Molecule.aromatizeOutput_relabel`: the output from a relabeled working copy is the relabeled
  output.
* `Aromaticity.Work.ringBonds_eq_of_ends`: copies with the same bond ends have the same ring
  bonds.
-/

@[expose] public section

namespace LeanSMILES

open Aromaticity Aromaticity.Work

/-- Atom `j` of the output read from the relabeled copy, for the relabeled molecule, is atom
`σ.symm j` of the output read from `W` for `m`. -/
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

/-- The bonds of the relabeled molecule with the relabeled copy's kinds are `m`'s bonds with
`W`'s kinds, relabeled. -/
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

namespace Aromaticity.Work

/-- Two copies with as many bonds and the same ends at every bond find the same bond between any
two atoms. -/
lemma bondBetween?_eq_of_ends {w w' : Work} (hs : w'.bonds.size = w.bonds.size)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) : w'.bondBetween? = w.bondBetween? := by
  have hsrc : ∀ k, (w'.bonds[k]! : WBond).src = (w.bonds[k]! : WBond).src :=
    fun k ↦ (ends_getElem! hs he k).1
  have hdst : ∀ k, (w'.bonds[k]! : WBond).dst = (w.bonds[k]! : WBond).dst :=
    fun k ↦ (ends_getElem! hs he k).2
  have hB : w'.numBonds = w.numBonds := hs
  funext u v
  simp only [bondBetween?, hB, hsrc, hdst]

/-- Two copies with as many bonds and the same ends at every bond give every ring the same bonds. -/
lemma ringBonds_eq_of_ends {w w' : Work} (hs : w'.bonds.size = w.bonds.size)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) : w'.ringBonds = w.ringBonds := by
  funext r
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, bondBetween?_eq_of_ends hs he]

/-- Renaming keeps the kind of every bond, as an option. -/
lemma kind?_relabelW (w : Work) (σ ψ : ℕ → ℕ) (k : ℕ) : (w.relabelW σ ψ).kind? k = w.kind? k := by
  simp only [kind?, getElem?_relabelW_bonds, Option.map_map]
  rfl

/-- Two copies with the same ends at every bond still have the same ends once both are renamed. -/
lemma ends_relabelW {w w' : Work} (σ ψ : ℕ → ℕ)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) (k : ℕ) :
    (w'.relabelW σ ψ).bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      (w.relabelW σ ψ).bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) := by
  rw [getElem?_relabelW_bonds, getElem?_relabelW_bonds, Option.map_map, Option.map_map]
  have := congrArg (Option.map fun p : ℕ × ℕ ↦ (σ p.1, σ p.2)) (he k)
  simpa [Option.map_map, Function.comp_def] using this

end Aromaticity.Work

end LeanSMILES
