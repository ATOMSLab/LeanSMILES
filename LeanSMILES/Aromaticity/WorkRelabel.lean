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

/-! ### Passes that work atom by atom -/

lemma ext_work {w₁ w₂ : Work} (ha : w₁.atoms = w₂.atoms) (hb : w₁.bonds = w₂.bonds) : w₁ = w₂ := by
  cases w₁; cases w₂; simp_all

lemma getElem!_rangeMap {α : Type} [Inhabited α] (f : ℕ → α) {N j : ℕ} (hj : j < N) :
    ((List.range N).toArray.map f)[j]! = f j := by
  rw [getElem!_pos _ j (by simpa using hj)]
  simp

lemma kindsAt_of_bonds {w₁ w₂ : Work} (h : w₁.bonds = w₂.bonds) : w₁.kindsAt = w₂.kindsAt := by
  funext i
  simp only [kindsAt, bondsOf, numBonds, h]

/-- What a step that works on one atom needs: it keeps the bonds and the other atoms, and the
new atom is read off the atom and the kinds of its bonds. -/
structure AtomStep (S : Work → ℕ → Work) : Prop where
  bonds : ∀ w j, (S w j).bonds = w.bonds
  size : ∀ w j, (S w j).atoms.size = w.atoms.size
  off : ∀ w j i, i ≠ j → ((S w j).atoms[i]! : WAtom) = w.atoms[i]!
  loc : ∀ w w' j j', j < w.atoms.size → j' < w'.atoms.size →
    (w.atoms[j]! : WAtom) = w'.atoms[j']! → w.kindsAt j = w'.kindsAt j' →
    ((S w j).atoms[j]! : WAtom) = (S w' j').atoms[j']!

lemma AtomStep.foldl_bonds {S : Work → ℕ → Work} (hS : AtomStep S) :
    ∀ (l : List ℕ) (w : Work), (l.foldl S w).bonds = w.bonds
  | [], _ => rfl
  | x :: l, w => by rw [List.foldl_cons, hS.foldl_bonds l, hS.bonds]

lemma AtomStep.foldl_size {S : Work → ℕ → Work} (hS : AtomStep S) :
    ∀ (l : List ℕ) (w : Work), (l.foldl S w).atoms.size = w.atoms.size
  | [], _ => rfl
  | x :: l, w => by rw [List.foldl_cons, hS.foldl_size l, hS.size]

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

lemma relabelW_numAtoms_eq : (List.range (w.relabelW σ ψ).numAtoms) = List.range w.numAtoms := by
  simp

lemma wf_of_bonds {w₁ w₂ : Work} (hb : w₁.bonds = w₂.bonds) (ha : w₁.atoms.size = w₂.atoms.size)
    (h : w₂.WF) : w₁.WF := by
  intro k hk
  simp only [numBonds, numAtoms, hb, ha] at hk ⊢
  exact h k hk

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

lemma radicalCount_congr {w₁ w₂ : Work} {j j' : ℕ} (ha : (w₁.atoms[j]! : WAtom) = w₂.atoms[j']!)
    (hk : w₁.kindsAt j = w₂.kindsAt j') : w₁.radicalCount j = w₂.radicalCount j' := by
  simp only [radicalCount, kekuleValence, bondHalfSum_eq_loc, ha, hk]

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
