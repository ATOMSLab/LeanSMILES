/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingSetIso
public import LeanSMILES.Aromaticity.KekulizeAtoms
public import LeanSMILES.Aromaticity.PerceiveAgree

/-!
# LeanSMILES.Aromaticity.WorkRelabel

Renumbering the atoms of a working copy

`Work.relabelW w σ ψ` renames atom `i` of `w` to `σ i` (`ψ` the inverse), keeping the bond list in
order. Everything read at an atom, its record and the kinds of its bonds, is read at the renamed
atom (`Work.kindsAt_relabelW`); the bond between two atoms is the same bond
(`Work.bondBetween?_relabelW`), so the renamed copy is a `Work.WorkIso` with the bonds unrenamed.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

/-- `w` with atom `i` renamed `σ i` (`ψ` the inverse renaming); bonds in the same order. -/
def relabelW (w : Work) (σ ψ : ℕ → ℕ) : Work where
  atoms := (List.range w.atoms.size).toArray.map fun j ↦ w.atoms[ψ j]!
  bonds := w.bonds.map fun b ↦ { b with src := σ b.src, dst := σ b.dst }

variable {w : Work} {σ ψ : ℕ → ℕ}

@[simp] lemma relabelW_atoms_size : (w.relabelW σ ψ).atoms.size = w.atoms.size := by
  simp [relabelW]

@[simp] lemma relabelW_bonds_size : (w.relabelW σ ψ).bonds.size = w.bonds.size := by
  simp [relabelW]

@[simp] lemma numAtoms_relabelW : (w.relabelW σ ψ).numAtoms = w.numAtoms := by
  simp [numAtoms]

@[simp] lemma numBonds_relabelW : (w.relabelW σ ψ).numBonds = w.numBonds := by
  simp [numBonds]

lemma atom_relabelW' {j : ℕ} (hj : j < w.atoms.size) :
    ((w.relabelW σ ψ).atoms[j]! : WAtom) = w.atoms[ψ j]! := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [relabelW]

lemma atom_relabelW (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} (hi : i < w.atoms.size) :
    ((w.relabelW σ ψ).atoms[σ i]! : WAtom) = w.atoms[i]! := by
  rw [atom_relabelW' (hb.lt i hi), hb.left i hi]

lemma bond_relabelW {k : ℕ} (hk : k < w.bonds.size) :
    ((w.relabelW σ ψ).bonds[k]! : WBond) =
      { (w.bonds[k]! : WBond) with
                                  src := σ (w.bonds[k]! : WBond).src
                                  dst := σ (w.bonds[k]! : WBond).dst } := by
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos w.bonds k hk]
  simp [relabelW]

lemma kind_relabelW (k : ℕ) :
    ((w.relabelW σ ψ).bonds[k]! : WBond).kind = (w.bonds[k]! : WBond).kind := by
  by_cases hk : k < w.bonds.size
  · rw [bond_relabelW hk]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg w.bonds k hk]

lemma beq_σ (hb : IdxBij w.numAtoms σ ψ) {a c : ℕ} (ha : a < w.numAtoms) (hc : c < w.numAtoms) :
    (σ a == σ c) = (a == c) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h ↦ hb.inj ha hc h, fun h ↦ h ▸ rfl⟩

lemma touches_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {k i : ℕ}
    (hk : k < w.bonds.size) (hi : i < w.atoms.size) :
    ((w.relabelW σ ψ).bonds[k]! : WBond).touches (σ i) = (w.bonds[k]! : WBond).touches i := by
  rw [bond_relabelW hk]
  have := hwf k hk
  simp only [WBond.touches]
  rw [beq_σ hb this.1 hi, beq_σ hb this.2.1 hi]

/-- **The bonds at a renamed atom are the same bonds.** -/
lemma bondsOf_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).bondsOf (σ i) = w.bondsOf i := by
  unfold bondsOf
  rw [numBonds_relabelW]
  exact List.filter_congr fun k hk ↦ touches_relabelW hwf hb (List.mem_range.1 hk) hi

/-- **The kinds at a renamed atom are the same kinds.** -/
lemma kindsAt_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).kindsAt (σ i) = w.kindsAt i := by
  unfold kindsAt
  rw [bondsOf_relabelW hwf hb hi]
  simp only [kind_relabelW]

lemma degree_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).degree (σ i) = w.degree i := by
  simp only [degree, bondsOf_relabelW hwf hb hi]

lemma other_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {k i : ℕ}
    (hk : k < w.bonds.size) (hi : i < w.atoms.size) :
    ((w.relabelW σ ψ).bonds[k]! : WBond).other (σ i) = σ ((w.bonds[k]! : WBond).other i) := by
  rw [bond_relabelW hk]
  have := hwf k hk
  simp only [WBond.other, beq_iff_eq]
  have e : σ (w.bonds[k]! : WBond).src = σ i ↔ (w.bonds[k]! : WBond).src = i :=
    ⟨fun h ↦ hb.inj this.1 hi h, fun h ↦ h ▸ rfl⟩
  by_cases h : (w.bonds[k]! : WBond).src = i
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (fun h' ↦ h (e.1 h')), if_neg h]

/-- **The neighbours of a renamed atom are the neighbours renamed.** -/
lemma neighbors_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).neighbors (σ i) = (w.neighbors i).map fun e ↦ (e.1, σ e.2) := by
  unfold neighbors
  rw [bondsOf_relabelW hwf hb hi, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hk' : k < w.bonds.size := by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  simp only [Function.comp, other_relabelW hwf hb hk' hi]

/-- **The bond between renamed atoms is the same bond.** -/
lemma bondBetween?_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {u v : ℕ}
    (hu : u < w.atoms.size) (hv : v < w.atoms.size) :
    (w.relabelW σ ψ).bondBetween? (σ u) (σ v) = w.bondBetween? u v := by
  unfold bondBetween?
  rw [numBonds_relabelW]
  apply find?_congr_mem
  intro k hk
  have hk' := List.mem_range.1 hk
  rw [bond_relabelW hk']
  have := hwf k hk'
  dsimp only
  rw [beq_σ hb this.1 hu, beq_σ hb this.1 hv, beq_σ hb this.2.1 hu, beq_σ hb this.2.1 hv]

lemma wf_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) : (w.relabelW σ ψ).WF := by
  intro k hk
  rw [numBonds_relabelW] at hk
  rw [bond_relabelW hk, numAtoms_relabelW]
  have := hwf k hk
  refine ⟨hb.lt _ this.1, hb.lt _ this.2.1, fun h ↦ this.2.2 (hb.inj this.1 this.2.1 h)⟩

/-- **A relabeled copy is a renumbering**, the bonds kept. -/
lemma workIso_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) :
    WorkIso w (w.relabelW σ ψ) σ ψ id id :=
  ⟨hb, ⟨fun _ h ↦ h, fun _ h ↦ h, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩, numAtoms_relabelW,
    numBonds_relabelW, fun u v hu hv ↦ by
      rw [bondBetween?_relabelW hwf hb hu hv]; simp⟩

/-! ### Atom quantities -/

lemma bondHalfSum_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).bondHalfSum (σ i) = w.bondHalfSum i := by
  rw [bondHalfSum_eq_loc, bondHalfSum_eq_loc, kindsAt_relabelW hwf hb hi]

lemma isAromaticAtom_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).isAromaticAtom (σ i) = w.isAromaticAtom i := by
  rw [isAromaticAtom_eq_loc, isAromaticAtom_eq_loc, kindsAt_relabelW hwf hb hi,
    atom_relabelW hb hi]

lemma explicitValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).explicitValence (σ i) = w.explicitValence i := by
  rw [explicitValence_eq_loc, explicitValence_eq_loc, bondHalfSum_relabelW hwf hb hi,
    isAromaticAtom_relabelW hwf hb hi, atom_relabelW hb hi]

lemma implicitHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).implicitHs (σ i) = w.implicitHs i := by
  rw [implicitHs_eq_loc, implicitHs_eq_loc, bondHalfSum_relabelW hwf hb hi,
    isAromaticAtom_relabelW hwf hb hi, atom_relabelW hb hi]

lemma totalHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).totalHs (σ i) = w.totalHs i := by
  simp only [totalHs, implicitHs_relabelW hwf hb hi, atom_relabelW hb hi]

lemma kekuleValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).kekuleValence (σ i) = w.kekuleValence i := by
  simp only [kekuleValence, bondHalfSum_relabelW hwf hb hi, atom_relabelW hb hi]

lemma radicalCount_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).radicalCount (σ i) = w.radicalCount i := by
  simp only [radicalCount, kekuleValence_relabelW hwf hb hi, atom_relabelW hb hi]

end Work

end LeanSMILES.Aromaticity
