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

## Main definitions

* `Work.relabelW`: a working copy with its atoms renamed and its bond list in the same order.
* `Work.AtomStep`: what a step that rewrites one atom from its record and bond kinds satisfies.

## Main statements

* `Work.kindsAt_relabelW`: the bond kinds at a renamed atom are the kinds at the original atom.
* `Work.bondBetween?_relabelW`: the bond between two renamed atoms is the same bond.
* `Work.workIso_relabelW`: a relabeled copy is a `WorkIso` of the original, bonds unrenamed.
* `Work.AtomStep.foldl_relabelW`: a pass over all atoms, atom by atom, commutes with renumbering.
* `Work.freezeHs_relabelW`, `Work.cacheValences_relabelW`, `Work.assignRadicals_relabelW`,
  `Work.finalizeHs_relabelW`: the per-atom passes commute with renumbering.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

/-- `w` with atom `i` renamed `σ i` (`ψ` the inverse renaming); bonds in the same order. -/
def relabelW (w : Work) (σ ψ : ℕ → ℕ) : Work where
  atoms := (List.range w.atoms.size).toArray.map fun j ↦ w.atoms[ψ j]!
  bonds := w.bonds.map fun b ↦ { b with src := σ b.src, dst := σ b.dst }

variable {w : Work} {σ ψ : ℕ → ℕ}

/-- Renaming keeps the size of the atom array. -/
@[simp] lemma relabelW_atoms_size : (w.relabelW σ ψ).atoms.size = w.atoms.size := by
  simp [relabelW]

/-- Renaming keeps the size of the bond array. -/
@[simp] lemma relabelW_bonds_size : (w.relabelW σ ψ).bonds.size = w.bonds.size := by
  simp [relabelW]

/-- Renaming keeps the number of atoms. -/
@[simp] lemma numAtoms_relabelW : (w.relabelW σ ψ).numAtoms = w.numAtoms := by
  simp [numAtoms]

/-- Renaming keeps the number of bonds. -/
@[simp] lemma numBonds_relabelW : (w.relabelW σ ψ).numBonds = w.numBonds := by
  simp [numBonds]

/-- Atom `j` of the renamed copy is atom `ψ j` of `w`, for `j` in range. -/
lemma atom_relabelW' {j : ℕ} (hj : j < w.atoms.size) :
    ((w.relabelW σ ψ).atoms[j]! : WAtom) = w.atoms[ψ j]! := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp [relabelW]

/-- Atom `σ i` of the renamed copy is atom `i` of `w`, when `σ` and `ψ` are inverse bijections. -/
lemma atom_relabelW (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} (hi : i < w.atoms.size) :
    ((w.relabelW σ ψ).atoms[σ i]! : WAtom) = w.atoms[i]! := by
  rw [atom_relabelW' (hb.lt i hi), hb.left i hi]

/-- Bond `k` of the renamed copy is bond `k` of `w` with both endpoints renamed by `σ`. -/
lemma bond_relabelW {k : ℕ} (hk : k < w.bonds.size) :
    ((w.relabelW σ ψ).bonds[k]! : WBond) =
      { (w.bonds[k]! : WBond) with
                                  src := σ (w.bonds[k]! : WBond).src
                                  dst := σ (w.bonds[k]! : WBond).dst } := by
  rw [getElem!_pos _ k (by simpa using hk), getElem!_pos w.bonds k hk]
  simp [relabelW]

/-- Renaming keeps the kind of every bond, in range or not. -/
lemma kind_relabelW (k : ℕ) :
    ((w.relabelW σ ψ).bonds[k]! : WBond).kind = (w.bonds[k]! : WBond).kind := by
  by_cases hk : k < w.bonds.size
  · rw [bond_relabelW hk]
  · rw [getElem!_neg _ k (by simpa using hk), getElem!_neg w.bonds k hk]

/-- `σ` is injective on the atoms: `σ a == σ c` exactly when `a == c`. -/
lemma beq_σ (hb : IdxBij w.numAtoms σ ψ) {a c : ℕ} (ha : a < w.numAtoms) (hc : c < w.numAtoms) :
    (σ a == σ c) = (a == c) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h ↦ hb.inj ha hc h, fun h ↦ h ▸ rfl⟩

/-- Bond `k` of the renamed copy touches `σ i` exactly when bond `k` of `w` touches `i`. -/
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

/-- A renamed atom has the degree of the original atom. -/
lemma degree_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).degree (σ i) = w.degree i := by
  simp only [degree, bondsOf_relabelW hwf hb hi]

/-- The far end of bond `k` from `σ i` in the renamed copy is the far end from `i` in `w`,
renamed. -/
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

/-- Renaming a well-formed copy by a bijection gives a well-formed copy. -/
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

/-- A renamed atom has the bond half-order sum of the original atom. -/
lemma bondHalfSum_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).bondHalfSum (σ i) = w.bondHalfSum i := by
  rw [bondHalfSum_eq_loc, bondHalfSum_eq_loc, kindsAt_relabelW hwf hb hi]

/-- A renamed atom is aromatic in RDKit's sense exactly when the original atom is. -/
lemma isAromaticAtom_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).isAromaticAtom (σ i) = w.isAromaticAtom i := by
  rw [isAromaticAtom_eq_loc, isAromaticAtom_eq_loc, kindsAt_relabelW hwf hb hi,
    atom_relabelW hb hi]

/-- A renamed atom has the explicit valence of the original atom. -/
lemma explicitValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).explicitValence (σ i) = w.explicitValence i := by
  rw [explicitValence_eq_loc, explicitValence_eq_loc, bondHalfSum_relabelW hwf hb hi,
    isAromaticAtom_relabelW hwf hb hi, atom_relabelW hb hi]

/-- A renamed atom has the implicit hydrogen count of the original atom. -/
lemma implicitHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).implicitHs (σ i) = w.implicitHs i := by
  rw [implicitHs_eq_loc, implicitHs_eq_loc, bondHalfSum_relabelW hwf hb hi,
    isAromaticAtom_relabelW hwf hb hi, atom_relabelW hb hi]

/-- A renamed atom has the total hydrogen count of the original atom. -/
lemma totalHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).totalHs (σ i) = w.totalHs i := by
  simp only [totalHs, implicitHs_relabelW hwf hb hi, atom_relabelW hb hi]

/-- A renamed atom has the Kekulé valence of the original atom. -/
lemma kekuleValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).kekuleValence (σ i) = w.kekuleValence i := by
  simp only [kekuleValence, bondHalfSum_relabelW hwf hb hi, atom_relabelW hb hi]

/-- A renamed atom has the radical count of the original atom. -/
lemma radicalCount_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).radicalCount (σ i) = w.radicalCount i := by
  simp only [radicalCount, kekuleValence_relabelW hwf hb hi, atom_relabelW hb hi]

/-! ### Passes that work atom by atom -/

/-- Two working copies with the same atoms and the same bonds are equal. -/
lemma ext_work {w₁ w₂ : Work} (ha : w₁.atoms = w₂.atoms) (hb : w₁.bonds = w₂.bonds) : w₁ = w₂ := by
  cases w₁; cases w₂; simp_all

/-- Entry `j < N` of `f` mapped over `0, …, N - 1` as an array is `f j`. -/
lemma getElem!_rangeMap {α : Type} [Inhabited α] (f : ℕ → α) {N j : ℕ} (hj : j < N) :
    ((List.range N).toArray.map f)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

/-- Two working copies with the same bonds have the same bond kinds at every atom. -/
lemma kindsAt_of_bonds {w₁ w₂ : Work} (h : w₁.bonds = w₂.bonds) : w₁.kindsAt = w₂.kindsAt := by
  funext i
  simp only [kindsAt, bondsOf, numBonds, h]

/-- What a step that works on one atom needs: it keeps the bonds and the other atoms, and the
new atom is read off the atom and the kinds of its bonds. -/
structure AtomStep (S : Work → ℕ → Work) : Prop where
  /-- The step keeps the bonds. -/
  bonds : ∀ w j, (S w j).bonds = w.bonds
  /-- The step keeps the number of atoms. -/
  size : ∀ w j, (S w j).atoms.size = w.atoms.size
  /-- The step at `j` leaves every other atom unchanged. -/
  off : ∀ w j i, i ≠ j → ((S w j).atoms[i]! : WAtom) = w.atoms[i]!
  /-- Two atoms with the same record and the same bond kinds come out the same. -/
  loc : ∀ w w' j j', j < w.atoms.size → j' < w'.atoms.size →
    (w.atoms[j]! : WAtom) = w'.atoms[j']! → w.kindsAt j = w'.kindsAt j' →
    ((S w j).atoms[j]! : WAtom) = (S w' j').atoms[j']!

/-- Folding an atom step over any list of atoms keeps the bonds. -/
lemma AtomStep.foldl_bonds {S : Work → ℕ → Work} (hS : AtomStep S) :
    ∀ (l : List ℕ) (w : Work), (l.foldl S w).bonds = w.bonds
  | [], _ => rfl
  | x :: l, w => by rw [List.foldl_cons, hS.foldl_bonds l, hS.bonds]

/-- Folding an atom step over any list of atoms keeps the number of atoms. -/
lemma AtomStep.foldl_size {S : Work → ℕ → Work} (hS : AtomStep S) :
    ∀ (l : List ℕ) (w : Work), (l.foldl S w).atoms.size = w.atoms.size
  | [], _ => rfl
  | x :: l, w => by rw [List.foldl_cons, hS.foldl_size l, hS.size]

/-- After folding an atom step over a duplicate-free list, atom `i` is what one step at `i` makes
of it in the starting copy if `i` is in the list, and is unchanged otherwise. -/
lemma AtomStep.foldl_atom {S : Work → ℕ → Work} (hS : AtomStep S) :
    ∀ (l : List ℕ) (w : Work) (i : ℕ), l.Nodup → i < w.atoms.size →
      ((l.foldl S w).atoms[i]! : WAtom) = if i ∈ l then (S w i).atoms[i]! else w.atoms[i]!
  | [], _, _, _, _ => by simp
  | x :: l, w, i, hnd, hi => by
    rw [List.foldl_cons, hS.foldl_atom l _ i (List.nodup_cons.1 hnd).2 (by rw [hS.size]; exact hi)]
    by_cases hix : i = x
    · subst hix
      rw [if_neg (List.nodup_cons.1 hnd).1, if_pos List.mem_cons_self]
    · rw [hS.off w x i hix]
      by_cases hil : i ∈ l
      · rw [if_pos hil, if_pos (List.mem_cons_of_mem _ hil)]
        exact hS.loc _ _ i i (by rw [hS.size]; exact hi) hi (hS.off w x i hix)
          (by rw [kindsAt_of_bonds (hS.bonds w x)])
      · rw [if_neg hil, if_neg (by simp [hix, hil])]

/-- **A pass over all atoms, atom by atom, commutes with renumbering.** -/
lemma AtomStep.foldl_relabelW {S : Work → ℕ → Work} (hS : AtomStep S) (hwf : w.WF)
    (hb : IdxBij w.numAtoms σ ψ) :
    (List.range w.numAtoms).foldl S (w.relabelW σ ψ) =
      ((List.range w.numAtoms).foldl S w).relabelW σ ψ := by
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) (by rw [hS.foldl_size]; simp)
      (by simp [hS.foldl_size])
    intro j hj
    have hpj := hb.lt' j hj
    rw [hS.foldl_atom _ _ j List.nodup_range (by simpa using hj),
      if_pos (List.mem_range.2 hj : j ∈ List.range w.numAtoms),
      atom_relabelW' (by rw [hS.foldl_size]; exact hj),
      hS.foldl_atom _ _ _ List.nodup_range hpj,
      if_pos (List.mem_range.2 hpj : ψ j ∈ List.range w.numAtoms)]
    conv_lhs => rw [← hb.right j hj]
    exact hS.loc _ _ _ _ (by simpa using hb.lt _ hpj) hpj (atom_relabelW hb hpj)
      (kindsAt_relabelW hwf hb hpj)
  · rw [hS.foldl_bonds]
    simp only [relabelW, hS.foldl_bonds]

/-- The atom numbers of the renamed copy are those of `w`. -/
lemma relabelW_numAtoms_eq : (List.range (w.relabelW σ ψ).numAtoms) = List.range w.numAtoms := by
  simp

/-- A copy with the bonds and the atom count of a well-formed copy is well formed. -/
lemma wf_of_bonds {w₁ w₂ : Work} (hb : w₁.bonds = w₂.bonds) (ha : w₁.atoms.size = w₂.atoms.size)
    (h : w₂.WF) : w₁.WF := by
  intro k hk
  simp only [numBonds, numAtoms, hb, ha] at hk ⊢
  exact h k hk

/-- Entry `j < N` of `f` mapped over `0, …, N - 1` as a list is `f j`. -/
lemma getElem!_listRangeMap {α : Type} [Inhabited α] (f : ℕ → α) {N j : ℕ} (hj : j < N) :
    ((List.range N).map f)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

/-- `freezeHs` commutes with renumbering. -/
lemma freezeHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) :
    (w.relabelW σ ψ).freezeHs = w.freezeHs.relabelW σ ψ := by
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) (by simp [freezeHs, numAtoms])
      (by simp [freezeHs, numAtoms])
    intro j hj
    have hpj := hb.lt' j hj
    rw [atom_relabelW' (w := w.freezeHs) (by simpa [freezeHs, numAtoms] using hj)]
    simp only [freezeHs]
    rw [getElem!_rangeMap _ (by simpa [numAtoms] using hj),
      getElem!_rangeMap _ (by simpa [numAtoms] using hpj), atom_relabelW' hj]
    conv_lhs => rw [← hb.right j hj]
    rw [totalHs_relabelW hwf hb hpj, hb.right j hj]
  · rfl

/-- `cacheValences` commutes with renumbering. -/
lemma cacheValences_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) :
    (w.relabelW σ ψ).cacheValences = w.cacheValences.relabelW σ ψ := by
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) (by simp [cacheValences, numAtoms])
      (by simp [cacheValences, numAtoms])
    intro j hj
    have hpj := hb.lt' j hj
    rw [atom_relabelW' (w := w.cacheValences) (by simpa [cacheValences, numAtoms] using hj)]
    simp only [cacheValences]
    rw [getElem!_rangeMap _ (by simpa [numAtoms] using hj),
      getElem!_rangeMap _ (by simpa [numAtoms] using hpj), atom_relabelW' hj]
    conv_lhs => rw [← hb.right j hj]
    rw [explicitValence_relabelW hwf hb hpj, implicitHs_relabelW hwf hb hpj,
      isAromaticAtom_relabelW hwf hb hpj, hb.right j hj]
  · rfl

/-- Two atoms with the same record and the same bond kinds have the same radical count. -/
lemma radicalCount_congr {w₁ w₂ : Work} {j j' : ℕ} (ha : (w₁.atoms[j]! : WAtom) = w₂.atoms[j']!)
    (hk : w₁.kindsAt j = w₂.kindsAt j') : w₁.radicalCount j = w₂.radicalCount j' := by
  simp only [radicalCount, kekuleValence, bondHalfSum_eq_loc, ha, hk]

/-- `radicalStep` is an atom step. -/
lemma atomStep_radicalStep : AtomStep radicalStep := by
  refine ⟨fun w j ↦ ?_, fun w j ↦ ?_, fun w j i hij ↦ ?_, fun w w' j j' hj hj' ha hk ↦ ?_⟩
  · unfold radicalStep; dsimp only; split <;> rfl
  · unfold radicalStep; dsimp only; split
    · rfl
    · simp [modifyAtom]
  · unfold radicalStep; dsimp only; split
    · rfl
    · exact modifyAtom_atom_of_ne _ (Ne.symm hij) _
  · unfold radicalStep
    dsimp only
    rw [ha]
    split
    · exact ha
    · rw [modifyAtom_atom_self, modifyAtom_atom_self, if_pos hj, if_pos hj', ha,
        radicalCount_congr ha hk]

/-- `assignRadicals` commutes with renumbering. -/
lemma assignRadicals_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) :
    (w.relabelW σ ψ).assignRadicals = w.assignRadicals.relabelW σ ψ := by
  unfold assignRadicals
  rw [numAtoms_relabelW]
  exact atomStep_radicalStep.foldl_relabelW hwf hb

/-- `adjustHsStep` is an atom step. -/
lemma atomStep_adjustHsStep : AtomStep adjustHsStep := by
  refine ⟨fun w j ↦ ?_, fun w j ↦ ?_, fun w j i hij ↦ ?_, fun w w' j j' hj hj' ha hk ↦ ?_⟩
  · unfold adjustHsStep; dsimp only; split
    · split <;> rfl
    · rfl
  · unfold adjustHsStep; dsimp only; split
    · split
      · simp [modifyAtom]
      · rfl
    · rfl
  · unfold adjustHsStep; dsimp only; split
    · split
      · exact modifyAtom_atom_of_ne _ (Ne.symm hij) _
      · rfl
    · rfl
  · have hiA : w.isAromaticAtom j = w'.isAromaticAtom j' := by
      rw [isAromaticAtom_eq_loc, isAromaticAtom_eq_loc, ha, hk]
    have hiH : w.implicitHs j = w'.implicitHs j' := by
      rw [implicitHs_eq_loc, implicitHs_eq_loc, ha, hiA, bondHalfSum_eq_loc, bondHalfSum_eq_loc,
        hk]
    unfold adjustHsStep
    dsimp only
    rw [ha, hiA, hiH]
    split
    · split
      · rw [modifyAtom_atom_self, modifyAtom_atom_self, if_pos hj, if_pos hj', ha]
      · exact ha
    · exact ha

/-- `finalizeHs` commutes with renumbering. -/
lemma finalizeHs_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) :
    (w.relabelW σ ψ).finalizeHs = w.finalizeHs.relabelW σ ψ := by
  have h1 := atomStep_adjustHsStep.foldl_relabelW hwf hb
  set w1 := (List.range w.numAtoms).foldl adjustHsStep w with hw1
  have hsz : w1.atoms.size = w.atoms.size := atomStep_adjustHsStep.foldl_size _ _
  have hwf1 : w1.WF := wf_of_bonds (atomStep_adjustHsStep.foldl_bonds _ _) hsz hwf
  have hb1 : IdxBij w1.numAtoms σ ψ := by rw [numAtoms, hsz]; exact hb
  unfold finalizeHs
  dsimp only
  rw [numAtoms_relabelW, h1, ← hw1]
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) (by simp [numAtoms, hsz])
      (by simp [numAtoms, hsz])
    intro j hj
    have hpj := hb.lt' j hj
    have hpj1 : ψ j < w1.atoms.size := by rw [hsz]; exact hpj
    rw [atom_relabelW' (w := { w1 with atoms := _ }) (by simpa [numAtoms, hsz] using hj)]
    rw [getElem!_rangeMap _ (by simpa [numAtoms, hsz] using hj),
      getElem!_rangeMap _ (by simpa [numAtoms, hsz] using hpj),
      getElem!_listRangeMap _ (by simpa [numAtoms, hsz] using hj),
      getElem!_listRangeMap _ (by simpa [numAtoms, hsz] using hpj),
      atom_relabelW' (w := w1) (by rw [hsz]; exact hj)]
    conv_lhs => rw [← hb.right j hj]
    rw [implicitHs_relabelW hwf1 hb1 hpj1, hb.right j hj]
  · rfl

end Work

end LeanSMILES.Aromaticity
