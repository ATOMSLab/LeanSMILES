/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Congruence
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# LeanSMILES.Aromaticity.KekuleSim

Two working copies that differ only in where their double bonds sit run through
`Molecule.aromatize` in lockstep, `cleanUp` included. This is the working-copy
half of the proofs in `LeanSMILES.Aromaticity.ResonanceProofs`.

* `Work.RelD D w₁ w₂`: the same atoms and skeleton, the same kind on every bond
  outside `D`, and on `D` one single and one double, with every atom keeping
  its number of doubles among its `D` bonds. `Work.Sim` drops `D`, and
  `Work.MarkRel` keeps only what marking aromatic bonds needs.
* `cleanUp` makes the same rewrites on both sides when no moved bond touches
  an atom it may rewrite (`Work.CleanInv.cleanUp`). `Congruence` covers the
  case where `cleanUp` rewrites nothing (`Work.Swapped.quiet`); this is the
  case where it does, away from the moved bonds.
* Perception is `Congruence`'s: a `RelD` is a `Work.Swapped` over the moved
  bonds (`Work.RelD.swapped`), so both sides make the same bonds aromatic when
  every moved bond is a bond of one of the rings (`Work.RelD.aromaticBondList`).
* **Moved bonds lie on cycles** (`Work.RelD.onCycle_of_D`). `onCycle` sweeps
  out from one end of a bond to a closed set; if the other end is outside it,
  a parity count of the moved bonds at the atoms of the set fails. That a bond
  on a cycle is a bond of one of the `relevantCycles` is not proved; property 1
  assumes it (`Molecule.RingsCoverCycles`).
* After `markAromatic`, a bond is aromatic exactly when it is in the list and
  was single or double (`Work.kind_foldl_markAromatic`).

The steps of `cleanUp` are taken in the form of `nitroStep_eq`, `azideStep_eq`,
`phosphorusScan_eq` and `halogenStep_eq`, which name the searches `Basic` writes
inline. The loops these passes run are folds (`Basic`, `Perceive`), so each is
an induction on a list.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A left fold carries any relation its step carries (`foldl_sim` with one step function). -/
lemma foldl_lockstep {α β : Type*} {R : α → α → Prop} {f : α → β → α} (l : List β)
    (hf : ∀ a₁ a₂ b, b ∈ l → R a₁ a₂ → R (f a₁ b) (f a₂ b)) {a₁ a₂ : α} (h : R a₁ a₂) :
    R (l.foldl f a₁) (l.foldl f a₂) :=
  foldl_sim R f f l a₁ a₂ h hf

namespace Work

/-! ### Same skeleton -/

/-- Same number of atoms and bonds, and the same bond endpoints. -/
structure SameSkel (w₁ w₂ : Work) : Prop where
  numAtoms : w₁.numAtoms = w₂.numAtoms
  numBonds : w₁.numBonds = w₂.numBonds
  src : ∀ k : ℕ, (w₁.bonds[k]! : WBond).src = (w₂.bonds[k]! : WBond).src
  dst : ∀ k : ℕ, (w₁.bonds[k]! : WBond).dst = (w₂.bonds[k]! : WBond).dst

namespace SameSkel

variable {w₁ w₂ : Work} (h : SameSkel w₁ w₂)
include h

lemma touches (k i : ℕ) : w₁.bonds[k]!.touches i = w₂.bonds[k]!.touches i := by
  simp [WBond.touches, h.src, h.dst]

lemma other (k i : ℕ) : w₁.bonds[k]!.other i = w₂.bonds[k]!.other i := by
  simp [WBond.other, h.src, h.dst]

lemma bondsOf : w₁.bondsOf = w₂.bondsOf := by
  funext i
  simp [Work.bondsOf, h.numBonds, h.touches]

lemma neighbors : w₁.neighbors = w₂.neighbors := by
  funext i
  simp [Work.neighbors, h.bondsOf, h.other]

lemma degree : w₁.degree = w₂.degree := by
  funext i
  simp [Work.degree, h.bondsOf]

lemma bondBetween? : w₁.bondBetween? = w₂.bondBetween? := by
  funext i j
  simp [Work.bondBetween?, h.numBonds, h.src, h.dst]

lemma ringBonds : w₁.ringBonds = w₂.ringBonds := by
  funext r
  simp [Work.ringBonds, h.bondBetween?]

lemma relevantCycles : w₁.relevantCycles = w₂.relevantCycles := by
  exact Work.relevantCycles_congr h.neighbors h.bondBetween? h.numAtoms h.numBonds

lemma reachSweep : w₁.reachSweep = w₂.reachSweep := by
  funext skip seen
  simp [Work.reachSweep, h.numBonds, h.src, h.dst]

lemma onCycle : w₁.onCycle = w₂.onCycle := by
  funext k
  simp [Work.onCycle, h.reachSweep, h.numAtoms, h.src, h.dst]

end SameSkel

/-! ### Kekulé-partner simulation -/

/-- Single or double: what a Kekulé partner may trade, and what `markAromatic` makes aromatic. -/
def isSD (k : BondKind) : Bool := k == .single || k == .double

/-- `w₁` and `w₂` are one working copy with the double bonds placed differently: the same atoms
and skeleton, bonds differing only between single and double, the same bond-order sum at every
atom. -/
structure Sim (w₁ w₂ : Work) : Prop extends SameSkel w₁ w₂ where
  atoms : w₁.atoms = w₂.atoms
  kind : ∀ k : ℕ, (w₁.bonds[k]! : WBond).kind ≠ (w₂.bonds[k]! : WBond).kind →
    isSD w₁.bonds[k]!.kind ∧ isSD w₂.bonds[k]!.kind
  sum : ∀ i : ℕ, w₁.bondHalfSum i = w₂.bondHalfSum i

namespace Sim

variable {w₁ w₂ : Work} (h : Sim w₁ w₂)
include h

lemma kind_aromatic (k : ℕ) :
    (w₁.bonds[k]!.kind == .aromatic) = (w₂.bonds[k]!.kind == .aromatic) := by
  by_cases hk : w₁.bonds[k]!.kind = w₂.bonds[k]!.kind
  · rw [hk]
  · obtain ⟨h₁, h₂⟩ := h.kind k hk
    revert h₁ h₂
    cases w₁.bonds[k]!.kind <;> cases w₂.bonds[k]!.kind <;> simp [isSD]

lemma isAromaticAtom : w₁.isAromaticAtom = w₂.isAromaticAtom := by
  funext i
  simp [Work.isAromaticAtom, h.atoms, h.bondsOf, h.kind_aromatic]

lemma explicitValence : w₁.explicitValence = w₂.explicitValence := by
  funext i
  simp only [Work.explicitValence, h.sum i, h.atoms, h.isAromaticAtom]

lemma implicitHs : w₁.implicitHs = w₂.implicitHs := by
  funext i
  simp only [Work.implicitHs, h.atoms, h.explicitValence, h.isAromaticAtom]

lemma totalHs : w₁.totalHs = w₂.totalHs := by
  funext i
  simp only [Work.totalHs, h.atoms, h.implicitHs]

lemma kekuleValence : w₁.kekuleValence = w₂.kekuleValence := by
  funext i
  simp only [Work.kekuleValence, h.sum i, h.atoms]

lemma radicalCount : w₁.radicalCount = w₂.radicalCount := by
  funext i
  simp only [Work.radicalCount, h.atoms, h.kekuleValence]

lemma cachedValence : w₁.cachedValence = w₂.cachedValence := by
  funext i
  simp only [Work.cachedValence, h.atoms, h.kekuleValence]

lemma cachedTotalHs : w₁.cachedTotalHs = w₂.cachedTotalHs := by
  funext i
  simp only [Work.cachedTotalHs, h.atoms]

/-- New atoms, the same bonds: still in lockstep. -/
lemma of_bonds {w₁' w₂' : Work} (hb₁ : w₁'.bonds = w₁.bonds) (hb₂ : w₂'.bonds = w₂.bonds)
    (ha : w₁'.atoms = w₂'.atoms) : Sim w₁' w₂' where
  numAtoms := by simp [Work.numAtoms, ha]
  numBonds := by simpa [Work.numBonds, hb₁, hb₂] using h.numBonds
  src := by simpa [hb₁, hb₂] using h.src
  dst := by simpa [hb₁, hb₂] using h.dst
  atoms := ha
  kind := by simpa [hb₁, hb₂] using h.kind
  sum := by simpa [bondHalfSum, Work.bondsOf, Work.numBonds, hb₁, hb₂] using h.sum

lemma modifyAtom (i : ℕ) (f : WAtom → WAtom) : Sim (w₁.modifyAtom i f) (w₂.modifyAtom i f) :=
  h.of_bonds rfl rfl (by simp [Work.modifyAtom, h.atoms])

lemma freezeHs : Sim w₁.freezeHs w₂.freezeHs :=
  h.of_bonds rfl rfl (by simp only [Work.freezeHs, h.numAtoms, h.atoms, h.totalHs])

lemma cacheValences : Sim w₁.cacheValences w₂.cacheValences :=
  h.of_bonds rfl rfl (by
    simp only [Work.cacheValences, h.numAtoms, h.atoms, h.explicitValence, h.implicitHs,
      h.isAromaticAtom])

lemma assignRadicals : Sim w₁.assignRadicals w₂.assignRadicals := by
  unfold Work.assignRadicals
  rw [h.numAtoms]
  refine foldl_lockstep _ (fun w₁ w₂ _ _ h ↦ ?_) h
  simp only [Work.radicalStep, h.atoms, h.radicalCount]
  split
  · exact h
  · exact h.modifyAtom _ _

end Sim

/-! ### Rewriting one bond or one atom -/

lemma getElem!_modify {α : Type*} [Inhabited α] (a : Array α) (k j : ℕ) (f : α → α) :
    (a.modify k f)[j]! = if k = j ∧ j < a.size then f a[j]! else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos (a.modify k f) j (by simpa using hj), Array.getElem_modify,
      getElem!_pos a j hj]
    by_cases hkj : k = j <;> simp [hkj, hj]
  · rw [getElem!_neg (a.modify k f) j (by simpa using hj), getElem!_neg a j hj]
    simp [hj]

@[simp] lemma bonds_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).bonds = w.bonds := rfl

@[simp] lemma atoms_setKind (w : Work) (k : ℕ) (o : BondKind) : (w.setKind k o).atoms = w.atoms :=
  rfl

lemma atom_modifyAtom (w : Work) (i j : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).atoms[j]! =
      if i = j ∧ j < w.atoms.size then f w.atoms[j]! else w.atoms[j]! :=
  getElem!_modify _ _ _ _

lemma bond_setKind (w : Work) (k j : ℕ) (o : BondKind) :
    (w.setKind k o).bonds[j]! =
      if k = j ∧ j < w.bonds.size then { w.bonds[j]! with kind := o } else w.bonds[j]! :=
  getElem!_modify _ _ _ _

@[simp] lemma src_setKind (w : Work) (k j : ℕ) (o : BondKind) :
    ((w.setKind k o).bonds[j]! : WBond).src = (w.bonds[j]! : WBond).src := by
  rw [bond_setKind]
  split <;> rfl

@[simp] lemma dst_setKind (w : Work) (k j : ℕ) (o : BondKind) :
    ((w.setKind k o).bonds[j]! : WBond).dst = (w.bonds[j]! : WBond).dst := by
  rw [bond_setKind]
  split <;> rfl

lemma kind_setKind (w : Work) (k j : ℕ) (o : BondKind) :
    ((w.setKind k o).bonds[j]! : WBond).kind =
      if k = j ∧ j < w.bonds.size then o else (w.bonds[j]! : WBond).kind := by
  rw [bond_setKind]
  split <;> rfl

@[simp] lemma numBonds_setKind (w : Work) (k : ℕ) (o : BondKind) :
    (w.setKind k o).numBonds = w.numBonds := by
  simp [Work.numBonds, Work.setKind]

@[simp] lemma numBonds_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).numBonds = w.numBonds := rfl

@[simp] lemma numAtoms_setKind (w : Work) (k : ℕ) (o : BondKind) :
    (w.setKind k o).numAtoms = w.numAtoms := rfl

@[simp] lemma numAtoms_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).numAtoms = w.numAtoms := by
  simp [Work.numAtoms, Work.modifyAtom]

@[simp] lemma bondsOf_setKind (w : Work) (k : ℕ) (o : BondKind) :
    (w.setKind k o).bondsOf = w.bondsOf := by
  funext i
  simp [Work.bondsOf, WBond.touches]

@[simp] lemma size_atoms_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).atoms.size = w.atoms.size := by
  simp [Work.modifyAtom]

@[simp] lemma bondsOf_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).bondsOf = w.bondsOf := rfl

/-! ### Lockstep with a fixed set of moved bonds -/

/-- `w₁` and `w₂` have the same atoms and skeleton, the same kind on every bond outside `D`, and on
`D` one is single and the other double, with every atom keeping its number of doubles among its
`D` bonds. -/
structure RelD (D : ℕ → Bool) (w₁ w₂ : Work) : Prop extends SameSkel w₁ w₂ where
  atoms : w₁.atoms = w₂.atoms
  off : ∀ k : ℕ, D k = false → (w₁.bonds[k]! : WBond).kind = (w₂.bonds[k]! : WBond).kind
  on : ∀ k : ℕ, D k = true → isSD (w₁.bonds[k]! : WBond).kind ∧ isSD (w₂.bonds[k]! : WBond).kind ∧
    (w₁.bonds[k]! : WBond).kind ≠ (w₂.bonds[k]! : WBond).kind
  dsum : ∀ i : ℕ, (((w₁.bondsOf i).filter D).map fun k ↦ halfOrder w₁.bonds[k]!.kind).sum =
    (((w₂.bondsOf i).filter D).map fun k ↦ halfOrder w₂.bonds[k]!.kind).sum

lemma sum_map_filter {β M : Type*} [AddMonoid M] (l : List β) (p : β → Bool) (f : β → M) :
    ((l.filter p).map f).sum = (l.map fun k ↦ if p k then f k else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih => cases hx : p x <;> simp [hx, ih]

namespace RelD

variable {D : ℕ → Bool} {w₁ w₂ : Work} (h : RelD D w₁ w₂)
include h

lemma sim : Sim w₁ w₂ where
  toSameSkel := h.toSameSkel
  atoms := h.atoms
  kind k hk := by
    cases hD : D k
    · exact absurd (h.off k hD) hk
    · exact ⟨(h.on k hD).1, (h.on k hD).2.1⟩
  sum i := by
    have hd := h.dsum i
    simp only [sum_map_filter, ← h.bondsOf] at hd
    have e : ((w₁.bondsOf i).map fun k ↦ halfOrder w₁.bonds[k]!.kind) =
        (w₁.bondsOf i).map fun k ↦ (if D k then halfOrder w₁.bonds[k]!.kind else 0) +
          (if D k then 0 else halfOrder w₂.bonds[k]!.kind) := by
      refine List.map_congr_left fun k _ ↦ ?_
      cases hD : D k
      · simp [h.off k hD]
      · simp
    have e₂ : ((w₁.bondsOf i).map fun k ↦ halfOrder w₂.bonds[k]!.kind) =
        (w₁.bondsOf i).map fun k ↦ (if D k then halfOrder w₂.bonds[k]!.kind else 0) +
          (if D k then 0 else halfOrder w₂.bonds[k]!.kind) := by
      refine List.map_congr_left fun k _ ↦ ?_
      cases hD : D k <;> simp
    simp only [bondHalfSum, ← h.bondsOf, e, e₂, List.sum_map_add, hd]

/-- Rewriting a bond outside `D` the same way on both sides keeps the lockstep. -/
lemma setKind (k : ℕ) (hk : D k = false) (o : BondKind) :
    RelD D (w₁.setKind k o) (w₂.setKind k o) where
  numAtoms := h.numAtoms
  numBonds := by simpa using h.numBonds
  src j := by simpa using h.src j
  dst j := by simpa using h.dst j
  atoms := h.atoms
  off j hj := by
    have := h.numBonds
    simp only [Work.numBonds] at this
    simp only [kind_setKind, this, h.off j hj]
  on j hj := by
    have hkj : k ≠ j := fun e ↦ by simp [e, hj] at hk
    simpa [kind_setKind, hkj] using h.on j hj
  dsum i := by
    have hkj : ∀ j, D j = true → k ≠ j := fun j hj e ↦ by simp [e, hj] at hk
    simp only [bondsOf_setKind]
    rw [List.map_congr_left (l := (w₁.bondsOf i).filter D) fun j hj ↦ by
      rw [kind_setKind, if_neg fun e ↦ hkj j (List.mem_filter.mp hj).2 e.1]]
    rw [List.map_congr_left (l := (w₂.bondsOf i).filter D) fun j hj ↦ by
      rw [kind_setKind, if_neg fun e ↦ hkj j (List.mem_filter.mp hj).2 e.1]]
    exact h.dsum i

/-- Rewriting one atom the same way on both sides keeps the lockstep. -/
lemma modifyAtom (i : ℕ) (f : WAtom → WAtom) : RelD D (w₁.modifyAtom i f) (w₂.modifyAtom i f) where
  numAtoms := by simpa using h.numAtoms
  numBonds := h.numBonds
  src := h.src
  dst := h.dst
  atoms := by simp [Work.modifyAtom, h.atoms]
  off := h.off
  on := h.on
  dsum := h.dsum

/-- New atoms, the same bonds: still in lockstep. -/
lemma of_bonds {w₁' w₂' : Work} (hb₁ : w₁'.bonds = w₁.bonds) (hb₂ : w₂'.bonds = w₂.bonds)
    (ha : w₁'.atoms = w₂'.atoms) : RelD D w₁' w₂' where
  numAtoms := by simp [Work.numAtoms, ha]
  numBonds := by simpa [Work.numBonds, hb₁, hb₂] using h.numBonds
  src := by simpa [hb₁, hb₂] using h.src
  dst := by simpa [hb₁, hb₂] using h.dst
  atoms := ha
  off := by simpa [hb₁, hb₂] using h.off
  on := by simpa [hb₁, hb₂] using h.on
  dsum := by simpa [Work.bondsOf, Work.numBonds, hb₁, hb₂] using h.dsum

lemma freezeHs : RelD D w₁.freezeHs w₂.freezeHs :=
  h.of_bonds rfl rfl (by simp only [Work.freezeHs, h.numAtoms, h.atoms, h.sim.totalHs])

lemma cacheValences : RelD D w₁.cacheValences w₂.cacheValences :=
  h.of_bonds rfl rfl (by
    simp only [Work.cacheValences, h.numAtoms, h.atoms, h.sim.explicitValence, h.sim.implicitHs,
      h.sim.isAromaticAtom])

lemma assignRadicals : RelD D w₁.assignRadicals w₂.assignRadicals := by
  unfold Work.assignRadicals
  rw [h.numAtoms]
  refine foldl_lockstep _ (fun w₁ w₂ _ _ h ↦ ?_) h
  simp only [Work.radicalStep, h.atoms, h.sim.radicalCount]
  split
  · exact h
  · exact h.modifyAtom _ _

end RelD

/-! ### Marking aromatic bonds -/

/-- What `markAromatic` needs: the same atoms and skeleton, and bonds that differ only between
single and double. -/
structure MarkRel (w₁ w₂ : Work) : Prop extends SameSkel w₁ w₂ where
  atoms : w₁.atoms = w₂.atoms
  kind : ∀ k : ℕ, (w₁.bonds[k]! : WBond).kind ≠ (w₂.bonds[k]! : WBond).kind →
    isSD (w₁.bonds[k]! : WBond).kind ∧ isSD (w₂.bonds[k]! : WBond).kind

lemma Sim.markRel {w₁ w₂ : Work} (h : Sim w₁ w₂) : MarkRel w₁ w₂ :=
  ⟨h.toSameSkel, h.atoms, h.kind⟩

lemma MarkRel.isSD {w₁ w₂ : Work} (h : MarkRel w₁ w₂) (k : ℕ) :
    isSD (w₁.bonds[k]! : WBond).kind = isSD (w₂.bonds[k]! : WBond).kind := by
  by_cases hk : (w₁.bonds[k]! : WBond).kind = (w₂.bonds[k]! : WBond).kind
  · rw [hk]
  · rw [(h.kind k hk).1, (h.kind k hk).2]

lemma MarkRel.markAromatic {w₁ w₂ : Work} (h : MarkRel w₁ w₂) (b : ℕ) :
    MarkRel (w₁.markAromatic b) (w₂.markAromatic b) := by
  have hsd := h.isSD b
  simp only [Work.isSD] at hsd
  unfold Work.markAromatic
  dsimp only
  rw [hsd, h.src b, h.dst b]
  split
  · have hn := h.numBonds
    simp only [Work.numBonds] at hn
    refine ⟨⟨by simp [Work.numAtoms, Work.modifyAtom, h.atoms], by simpa using h.numBonds,
      fun j ↦ by simpa using h.src j, fun j ↦ by simpa using h.dst j⟩,
      by simp [Work.modifyAtom, h.atoms], fun j hj ↦ ?_⟩
    simp only [bonds_modifyAtom, kind_setKind, hn] at hj ⊢
    by_cases hbj : b = j ∧ j < w₂.bonds.size
    · simp [hbj] at hj
    · simpa [hbj] using h.kind j (by simpa [hbj] using hj)
  · exact h

lemma MarkRel.foldl_markAromatic {w₁ w₂ : Work} (h : MarkRel w₁ w₂) (l : List ℕ) :
    MarkRel (l.foldl Work.markAromatic w₁) (l.foldl Work.markAromatic w₂) :=
  foldl_lockstep (f := Work.markAromatic) l (fun _ _ b _ h ↦ h.markAromatic b) h

@[simp] lemma size_markAromatic (w : Work) (b : ℕ) :
    (w.markAromatic b).bonds.size = w.bonds.size := by
  unfold Work.markAromatic
  dsimp only
  split <;> simp [Work.setKind]

/-- After marking the bonds of `l`, bond `k` is aromatic if it is in `l` and was single or double,
and has its old kind otherwise. -/
lemma kind_foldl_markAromatic (w : Work) (l : List ℕ) (k : ℕ) (hk : k < w.bonds.size) :
    ((l.foldl markAromatic w).bonds[k]! : WBond).kind =
      if k ∈ l ∧ isSD (w.bonds[k]! : WBond).kind then .aromatic
      else (w.bonds[k]! : WBond).kind := by
  induction l generalizing w with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih _ (by simpa using hk)]
    unfold Work.markAromatic
    by_cases hb : isSD (w.bonds[b]! : WBond).kind
    · simp only [isSD] at hb
      simp only [hb, if_true, bonds_modifyAtom, kind_setKind, hk, and_true]
      by_cases hkb : b = k
      · subst hkb
        simp [isSD, hb]
      · simp [hkb, Ne.symm hkb]
    · simp only [isSD] at hb
      simp only [hb]
      by_cases hkb : b = k
      · subst hkb
        simp [isSD, hb]
      · simp [Ne.symm hkb]

/-! ### The last passes -/

/-- No aromatic atom and no aromatic bond: nothing to kekulize. -/
def NoAromatic (w : Work) : Prop :=
  (∀ k : ℕ, (w.bonds[k]! : WBond).kind ≠ .aromatic) ∧
    ∀ i : ℕ, (w.atoms[i]! : WAtom).aromatic = false

lemma kekulize_of_noAromatic (w : Work) (h : NoAromatic w) (rings : Array (List ℕ)) :
    w.kekulize rings = .ok w := by
  have hb : ((List.range w.numBonds).filter (fun k ↦ w.bonds[k]!.kind == .aromatic)).isEmpty := by
    simp [h.1]
  have ha : (w.atoms.any (·.aromatic)) = false := by
    rw [Array.any_eq_false]
    intro i hi
    have := h.2 i
    rw [getElem!_pos w.atoms i hi] at this
    simp [this]
  simp [Work.kekulize, hb, ha]
  rfl

/-! ### Moved bonds lie on cycles

`onCycle` sweeps outward from one end of a bond, never crossing it. After `numAtoms` sweeps the
marked set is closed: no other bond leaves it. If the far end is unmarked, count bond orders over
the marked atoms: every atom keeps its number of doubles among the moved bonds, so the moved bonds
leaving the set would have to balance, and the bond itself is the only one leaving. A parity count
rules that out, so every moved bond is on a cycle. -/

lemma getElem!_set! (a : Array Bool) (j i : ℕ) (v : Bool) :
    (a.set! j v)[i]! = if j = i ∧ i < a.size then v else a[i]! := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases hi : i < a.size
  · rw [getElem!_pos (a.setIfInBounds j v) i (by simpa using hi), Array.getElem_setIfInBounds hi,
      getElem!_pos a i hi]
    by_cases hji : j = i <;> simp [hji, hi]
  · rw [getElem!_neg (a.setIfInBounds j v) i (by simpa using hi), getElem!_neg a i hi]
    simp [hi]

/-- One bond of a sweep. -/
def sweepStep (w : Work) (skip : ℕ) (seen : Array Bool) (k : ℕ) : Array Bool :=
  if k == skip then seen else
    let b := w.bonds[k]!
    if seen[b.src]! && !seen[b.dst]! then seen.set! b.dst true
    else if seen[b.dst]! && !seen[b.src]! then seen.set! b.src true
    else seen

lemma reachSweep_eq (w : Work) (skip : ℕ) (s : Array Bool) :
    w.reachSweep skip s = (List.range w.numBonds).foldl (w.sweepStep skip) s := rfl

@[simp] lemma size_sweepStep (w : Work) (skip : ℕ) (s : Array Bool) (k : ℕ) :
    (w.sweepStep skip s k).size = s.size := by
  unfold sweepStep
  split
  · rfl
  · dsimp only
    split
    · simp
    · split <;> simp

lemma mono_sweepStep (w : Work) (skip : ℕ) (s : Array Bool) (k i : ℕ) (hi : s[i]! = true) :
    (w.sweepStep skip s k)[i]! = true := by
  unfold sweepStep
  split
  · exact hi
  · dsimp only
    split
    · rw [getElem!_set!]; split <;> simp_all
    · split
      · rw [getElem!_set!]; split <;> simp_all
      · exact hi

@[simp] lemma size_foldl_sweepStep (w : Work) (skip : ℕ) (l : List ℕ) (s : Array Bool) :
    (l.foldl (w.sweepStep skip) s).size = s.size := by
  induction l generalizing s with
  | nil => rfl
  | cons k l ih => simp [ih]

lemma mono_foldl_sweepStep (w : Work) (skip : ℕ) (l : List ℕ) (s : Array Bool) (i : ℕ)
    (hi : s[i]! = true) : (l.foldl (w.sweepStep skip) s)[i]! = true := by
  induction l generalizing s with
  | nil => exact hi
  | cons k l ih => exact ih _ (mono_sweepStep w skip s k i hi)

/-- Every bond's endpoints are atoms of `w`, and distinct. -/
def WF (w : Work) : Prop :=
  ∀ k < w.numBonds, (w.bonds[k]! : WBond).src < w.numAtoms ∧
    (w.bonds[k]! : WBond).dst < w.numAtoms ∧ (w.bonds[k]! : WBond).src ≠ (w.bonds[k]! : WBond).dst

lemma closed_aux (w : Work) (skip : ℕ) (s : Array Bool) (l : List ℕ) (t : Array Bool)
    (hst : ∀ i : ℕ, s[i]! = true → t[i]! = true)
    (hfix : ∀ i : ℕ, (l.foldl (w.sweepStep skip) t)[i]! = true → s[i]! = true)
    (k : ℕ) (hk : k ∈ l) (hks : k ≠ skip) (hsrc : (w.bonds[k]! : WBond).src < t.size)
    (hdst : (w.bonds[k]! : WBond).dst < t.size) :
    s[(w.bonds[k]! : WBond).src]! = s[(w.bonds[k]! : WBond).dst]! := by
  induction l generalizing t with
  | nil => simp at hk
  | cons k₀ l ih =>
    rw [List.foldl_cons] at hfix
    have ht₁ : ∀ i : ℕ, t[i]! = true → (w.sweepStep skip t k₀)[i]! = true :=
      fun i hi ↦ mono_sweepStep w skip t k₀ i hi
    rcases List.mem_cons.mp hk with rfl | hk
    · -- every state from `t` to the end agrees with `s`
      have eq_t : ∀ i : ℕ, t[i]! = s[i]! := fun i ↦ by
        cases hs : s[i]!
        · cases htt : t[i]!
          · rfl
          · exact absurd (hfix i (mono_foldl_sweepStep _ _ _ _ _ (ht₁ i htt))) (by simp [hs])
        · exact hst i hs
      have eq_t₁ : ∀ i : ℕ, (w.sweepStep skip t k)[i]! = s[i]! := fun i ↦ by
        cases hs : s[i]!
        · cases htt : (w.sweepStep skip t k)[i]!
          · rfl
          · exact absurd (hfix i (mono_foldl_sweepStep _ _ _ _ _ htt)) (by simp [hs])
        · exact ht₁ i (hst i hs)
      have h₁ := eq_t₁ (w.bonds[k]! : WBond).dst
      have h₂ := eq_t₁ (w.bonds[k]! : WBond).src
      rw [← eq_t, ← eq_t]
      unfold sweepStep at h₁ h₂
      simp only [show (k == skip) = false from by simpa using hks] at h₁ h₂
      rw [← eq_t] at h₁ h₂
      cases hs : t[(w.bonds[k]! : WBond).src]! <;> cases hd : t[(w.bonds[k]! : WBond).dst]! <;>
        simp_all
    · exact ih _ (fun i hi ↦ ht₁ i (hst i hi)) hfix hk (by simpa using hsrc) (by simpa using hdst)

/-- A sweep that marks nothing new leaves a set no bond but `skip` leaves. -/
lemma closed_of_fix (w : Work) (skip : ℕ) (s : Array Bool) (hfix : w.reachSweep skip s = s)
    (k : ℕ) (hk : k < w.numBonds) (hks : k ≠ skip) (hsrc : (w.bonds[k]! : WBond).src < s.size)
    (hdst : (w.bonds[k]! : WBond).dst < s.size) :
    s[(w.bonds[k]! : WBond).src]! = s[(w.bonds[k]! : WBond).dst]! := by
  refine closed_aux w skip s (List.range w.numBonds) s (fun _ h ↦ h) (fun i h ↦ ?_) k
    (List.mem_range.mpr hk) hks hsrc hdst
  rwa [← reachSweep_eq, hfix] at h

/-- Marked atoms among the first `N`. -/
def marked (N : ℕ) (s : Array Bool) : ℕ := ((List.range N).filter (s[·]!)).length

lemma marked_le (N : ℕ) (s : Array Bool) : marked N s ≤ N := by
  simpa [marked] using (List.filter_sublist (l := List.range N)).length_le

/-- A sweep that is not a fixed point marks a new atom. -/
lemma marked_lt (w : Work) (skip : ℕ) (s : Array Bool) (hfix : w.reachSweep skip s ≠ s) :
    marked s.size s < marked s.size (w.reachSweep skip s) := by
  have hsz : (w.reachSweep skip s).size = s.size := by simp [reachSweep_eq]
  have hmono : ∀ i, s[i]! = true → (w.reachSweep skip s)[i]! = true := fun i hi ↦ by
    rw [reachSweep_eq]
    exact mono_foldl_sweepStep _ _ _ _ _ hi
  obtain ⟨i, hi, hne⟩ : ∃ i < s.size, (w.reachSweep skip s)[i]! ≠ s[i]! := by
    by_contra hall
    refine hfix (Array.ext hsz fun i h₁ h₂ ↦ ?_)
    by_contra hne
    refine hall ⟨i, h₂, ?_⟩
    rwa [getElem!_pos _ i h₁, getElem!_pos _ i h₂]
  have hnew : (w.reachSweep skip s)[i]! = true ∧ s[i]! = false := by
    cases hs : s[i]!
    · cases hr : (w.reachSweep skip s)[i]!
      · simp_all
      · exact ⟨rfl, rfl⟩
    · exact absurd (hmono i hs) (by simp_all)
  have hsub := List.monotone_filter_right (List.range s.size) (p := (s[·]!))
    (q := ((w.reachSweep skip s)[·]!)) fun j hj ↦ hmono j hj
  refine lt_of_le_of_ne hsub.length_le fun heq ↦ ?_
  have hlist := hsub.eq_of_length heq
  have hmem : i ∈ (List.range s.size).filter ((w.reachSweep skip s)[·]!) :=
    List.mem_filter.mpr ⟨List.mem_range.mpr hi, hnew.1⟩
  rw [← hlist] at hmem
  simp [hnew.2] at hmem

/-- `numAtoms` sweeps from a nonempty start reach a fixed point. -/
lemma iterate_fix (w : Work) (skip : ℕ) (s₀ : Array Bool) (hs₀ : 0 < marked s₀.size s₀) :
    w.reachSweep skip ((w.reachSweep skip)^[s₀.size] s₀) =
      (w.reachSweep skip)^[s₀.size] s₀ := by
  set f := w.reachSweep skip
  have hsz : ∀ t, (f^[t] s₀).size = s₀.size := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', ← ih]; simp [f, reachSweep_eq]
  have key : ∀ t, f (f^[t] s₀) = f^[t] s₀ ∨ t + marked s₀.size s₀ ≤ marked s₀.size (f^[t] s₀) := by
    intro t
    induction t with
    | zero => right; simp
    | succ t ih =>
      by_cases hfix : f (f^[t] s₀) = f^[t] s₀
      · left
        rw [Function.iterate_succ_apply', hfix, hfix]
      · rcases ih with h | h
        · exact absurd h hfix
        · by_cases hfix' : f (f^[t + 1] s₀) = f^[t + 1] s₀
          · exact Or.inl hfix'
          · right
            have : marked (f^[t] s₀).size (f^[t] s₀) < marked (f^[t] s₀).size (f (f^[t] s₀)) :=
              marked_lt w skip (f^[t] s₀) hfix
            rw [hsz] at this
            rw [Function.iterate_succ_apply']
            omega
  rcases key s₀.size with h | h
  · exact h
  · have := marked_le s₀.size (f^[s₀.size] s₀)
    omega

/-- The sweeps of `onCycle k` end in a set that holds the first end of `k` and that no other bond
leaves. -/
lemma onCycle_closed (w : Work) (hwf : WF w) (k : ℕ) (hk : k < w.numBonds) :
    let S := (w.reachSweep k)^[w.numAtoms]
      ((Array.replicate w.numAtoms false).set! (w.bonds[k]! : WBond).src true)
    S[(w.bonds[k]! : WBond).src]! = true ∧ w.onCycle k = S[(w.bonds[k]! : WBond).dst]! ∧
      ∀ k' < w.numBonds, k' ≠ k →
        S[(w.bonds[k']! : WBond).src]! = S[(w.bonds[k']! : WBond).dst]! := by
  intro S
  set s₀ := (Array.replicate w.numAtoms false).set! (w.bonds[k]! : WBond).src true
  have hsrc := (hwf k hk).1
  have hs₀size : s₀.size = w.numAtoms := by simp [s₀]
  have hs₀ : s₀[(w.bonds[k]! : WBond).src]! = true := by
    simp [s₀, hsrc]
  have hS : ∀ t, ((w.reachSweep k)^[t] s₀).size = w.numAtoms ∧
      ((w.reachSweep k)^[t] s₀)[(w.bonds[k]! : WBond).src]! = true := by
    intro t
    induction t with
    | zero => exact ⟨hs₀size, hs₀⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply', reachSweep_eq]
      exact ⟨by simp [ih.1], mono_foldl_sweepStep _ _ _ _ _ ih.2⟩
  refine ⟨(hS _).2, rfl, fun k' hk' hne ↦ ?_⟩
  have hpos : 0 < marked s₀.size s₀ := by
    refine List.length_pos_iff_exists_mem.mpr ⟨_, List.mem_filter.mpr ⟨?_, hs₀⟩⟩
    simpa [hs₀size] using hsrc
  have hfix := iterate_fix w k s₀ hpos
  rw [hs₀size] at hfix
  exact closed_of_fix w k S hfix k' hk' hne (by rw [(hS _).1]; exact (hwf k' hk').1)
    (by rw [(hS _).1]; exact (hwf k' hk').2.1)

lemma sum_range_eq_finset (M : ℕ) (g : ℕ → ℕ) :
    ((List.range M).map g).sum = ∑ k ∈ Finset.range M, g k := by
  induction M with
  | zero => simp
  | succ M ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma halfOrder_sub_of_isSD {a b : BondKind} (ha : isSD a = true) (hb : isSD b = true)
    (hab : a ≠ b) : (halfOrder a : ℤ) - halfOrder b = 2 ∨ (halfOrder a : ℤ) - halfOrder b = -2 := by
  revert ha hb hab
  cases a <;> cases b <;> simp [isSD, halfOrder]

/-- Atoms of `S` at the ends of a bond, counted: one for each end in `S`. -/
lemma sum_touches (N : ℕ) (S : ℕ → Bool) (b : WBond) (hs : b.src < N) (hd : b.dst < N)
    (hne : b.src ≠ b.dst) :
    (∑ i ∈ Finset.range N, if S i = true ∧ b.touches i = true then (1 : ℤ) else 0) =
      (if S b.src then 1 else 0) + (if S b.dst then 1 else 0) := by
  have : ∀ i, (if S i = true ∧ b.touches i = true then (1 : ℤ) else 0) =
      (if b.src = i then (if S b.src then 1 else 0) else 0) +
        (if b.dst = i then (if S b.dst then 1 else 0) else 0) := by
    intro i
    by_cases h₁ : b.src = i
    · subst h₁
      simp [WBond.touches, Ne.symm hne]
    · by_cases h₂ : b.dst = i
      · subst h₂
        simp [WBond.touches, h₁]
      · simp [WBond.touches, h₁, h₂]
  rw [Finset.sum_congr rfl fun i _ ↦ this i, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.sum_ite_eq]
  simp [hs, hd]

namespace RelD

variable {D : ℕ → Bool} {w₁ w₂ : Work} (h : RelD D w₁ w₂)
include h

lemma lt_of_D {k : ℕ} (hk : D k = true) : k < w₁.numBonds := by
  by_contra hlt
  have h₂ : ¬ k < w₂.bonds.size := by
    have := h.numBonds
    simp only [Work.numBonds] at this hlt
    omega
  refine (h.on k hk).2.2 ?_
  rw [getElem!_neg w₁.bonds k (by simpa [Work.numBonds] using hlt), getElem!_neg w₂.bonds k h₂]

/-- **Moved bonds lie on cycles.** Every bond in `D` is on a cycle of the skeleton. -/
theorem onCycle_of_D (hwf : WF w₁) {k : ℕ} (hk : D k = true) : w₁.onCycle k = true := by
  have hkM := h.lt_of_D hk
  obtain ⟨hsrc, hon, hclosed⟩ := onCycle_closed w₁ hwf k hkM
  set S := (w₁.reachSweep k)^[w₁.numAtoms]
      ((Array.replicate w₁.numAtoms false).set! (w₁.bonds[k]! : WBond).src true)
  rw [hon]
  by_contra hdst
  simp only [Bool.not_eq_true] at hdst
  set N := w₁.numAtoms
  set M := w₁.numBonds
  -- the signed half-order difference of each moved bond
  let δ : ℕ → ℤ := fun k' ↦ (halfOrder (w₁.bonds[k']! : WBond).kind : ℤ) -
    halfOrder (w₂.bonds[k']! : WBond).kind
  let g : ℕ → ℤ := fun k' ↦
    ∑ i ∈ Finset.range N, if S[i]! = true ∧ ((w₁.bonds[k']! : WBond).touches i && D k') = true
      then δ k' else 0
  -- every atom balances its moved bonds
  have hatom : ∀ i, (∑ k' ∈ Finset.range M,
      if ((w₁.bonds[k']! : WBond).touches i && D k') = true then δ k' else 0) = 0 := by
    intro i
    have hd := h.dsum i
    rw [← h.bondsOf] at hd
    simp only [Work.bondsOf, List.filter_filter, sum_map_filter, sum_range_eq_finset] at hd
    have hz := congrArg (fun x : ℕ ↦ (x : ℤ)) hd
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] at hz
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hz
    refine Eq.trans (Finset.sum_congr rfl fun k' _ ↦ ?_) hz
    simp only [δ, Bool.and_comm (D k')]
    split <;> simp
  have htotal : ∑ k' ∈ Finset.range M, g k' = 0 := by
    simp only [g]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    by_cases hS : S[i]! = true
    · simp only [hS, true_and]
      exact hatom i
    · simp [hS]
  -- a moved bond is counted at the ends of it that are marked
  have hg : ∀ k' < M, D k' = true →
      g k' = δ k' * ((if S[(w₁.bonds[k']! : WBond).src]! then 1 else 0) +
        (if S[(w₁.bonds[k']! : WBond).dst]! then 1 else 0)) := by
    intro k' hk' hD
    obtain ⟨hs, hd, hne⟩ := hwf k' hk'
    rw [← sum_touches N (fun i ↦ S[i]!) _ hs hd hne, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [hD, Bool.and_true]
    split <;> simp
  have hδ : ∀ k', D k' = true → δ k' = 2 ∨ δ k' = -2 := fun k' hD ↦
    halfOrder_sub_of_isSD (h.on k' hD).1 (h.on k' hD).2.1 (h.on k' hD).2.2
  have hrest : (4 : ℤ) ∣ ∑ k' ∈ (Finset.range M).erase k, g k' := by
    refine Finset.dvd_sum fun k' hk' ↦ ?_
    obtain ⟨hne, hk'M⟩ := Finset.mem_erase.mp hk'
    have hk'M := Finset.mem_range.mp hk'M
    cases hD : D k'
    · simp [g, hD]
    · rw [hg k' hk'M hD, hclosed k' hk'M hne]
      rcases hδ k' hD with e | e <;> rw [e] <;> split <;> omega
  have hgk : g k = δ k := by
    rw [hg k hkM hk, hsrc, hdst]
    simp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hkM), hgk] at htotal
  rcases hδ k hk with e | e <;> rw [e] at htotal <;> omega

end RelD

/-! ### `cleanUp` in lockstep

`cleanUp` rewrites bonds at a few hypervalent atoms (`cleanUpCenter`). When no moved bond touches
one, both sides make the same rewrites, on bonds that are not moved. -/

lemma any_congr {β : Type*} {l : List β} {p q : β → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.any_cons, h x List.mem_cons_self, ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

/-- Atom `i` looks the same in `w` and `w'`: its record, its bonds and their kinds. -/
structure SameAt (w w' : Work) (i : ℕ) : Prop where
  atom : w.atoms[i]! = w'.atoms[i]!
  bondsOf : w.bondsOf i = w'.bondsOf i
  kind : ∀ k ∈ w.bondsOf i, (w.bonds[k]! : WBond).kind = (w'.bonds[k]! : WBond).kind

lemma SameAt.isAromaticAtom {w w' : Work} {i : ℕ} (h : SameAt w w' i) :
    w.isAromaticAtom i = w'.isAromaticAtom i := by
  simp only [Work.isAromaticAtom, h.atom, ← h.bondsOf]
  congr 1
  exact any_congr fun k hk ↦ by rw [h.kind k hk]

lemma SameAt.explicitValence {w w' : Work} {i : ℕ} (h : SameAt w w' i) :
    w.explicitValence i = w'.explicitValence i := by
  have hs : w.bondHalfSum i = w'.bondHalfSum i := by
    simp only [Work.bondHalfSum, ← h.bondsOf]
    exact congrArg List.sum (List.map_congr_left fun k hk ↦ by rw [h.kind k hk])
  simp only [Work.explicitValence, hs, h.atom, h.isAromaticAtom]

/-- An atom `cleanUp` may rewrite: a neutral N or P of valence 5, or a neutral Cl, Br or I of
valence 3, 5 or 7. -/
def cleanUpCenter (w : Work) (i : ℕ) : Bool :=
  let a := w.atoms[i]!
  a.charge == 0 && (((a.z == 7 || a.z == 15) && w.explicitValence i == 5) ||
    ((a.z == 17 || a.z == 35 || a.z == 53) && [3, 5, 7].contains (w.explicitValence i)))

lemma SameAt.cleanUpCenter {w w' : Work} {i : ℕ} (h : SameAt w w' i) :
    w.cleanUpCenter i = w'.cleanUpCenter i := by
  simp only [Work.cleanUpCenter, h.atom, h.explicitValence]

lemma Sim.cleanUpCenter {w₁ w₂ : Work} (h : Sim w₁ w₂) : w₁.cleanUpCenter = w₂.cleanUpCenter := by
  funext i
  simp only [Work.cleanUpCenter, h.atoms, h.explicitValence]

/-- No bond of `D` touches atom `c`. -/
def OffD (D : ℕ → Bool) (w : Work) (c : ℕ) : Prop :=
  ∀ k : ℕ, D k = true → (w.bonds[k]! : WBond).touches c = false

/-- No bond of `D` touches an atom `cleanUp` may rewrite. -/
def AvoidsCenters (D : ℕ → Bool) (w : Work) : Prop :=
  ∀ c : ℕ, w.cleanUpCenter c = true → OffD D w c

lemma OffD.notD {D : ℕ → Bool} {w : Work} {c : ℕ} (h : OffD D w c) {k : ℕ} (hk : k ∈ w.bondsOf c) :
    D k = false := by
  by_contra hD
  have := h k (by simpa using hD)
  simp [Work.bondsOf, this] at hk

/-- What `cleanUp` keeps along the way: the lockstep, moved bonds away from the atoms it may
rewrite, no aromaticity, and the skeleton of the start `w₀`. -/
structure CleanInv (D : ℕ → Bool) (w₀ w₁ w₂ : Work) : Prop where
  rel : RelD D w₁ w₂
  avoid : AvoidsCenters D w₁
  noArom : NoAromatic w₁
  skel : SameSkel w₀ w₁

lemma touches_other {b : WBond} {c x : ℕ} (hc : b.touches c = true) (hx : b.touches x = true) :
    x = c ∨ x = b.other c := by
  simp only [WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq] at hc hx ⊢
  split <;> omega

/-- A rewrite near a rewritable atom `c`: bonds change only between `c` and `j`, atoms only at `c`
and `j`, `j` ends up charged unless it is `c`, nothing becomes aromatic. -/
structure Local (w w' : Work) (c j : ℕ) : Prop where
  skel : SameSkel w w'
  atom : ∀ i, i ≠ c → i ≠ j → w'.atoms[i]! = w.atoms[i]!
  charged : j ≠ c → (w'.atoms[j]! : WAtom).charge ≠ 0
  kind : ∀ k : ℕ, (w'.bonds[k]! : WBond).kind ≠ (w.bonds[k]! : WBond).kind →
    ∀ i, (w.bonds[k]! : WBond).touches i = true → i = c ∨ i = j
  arom : ∀ k : ℕ, (w'.bonds[k]! : WBond).kind ≠ (w.bonds[k]! : WBond).kind →
    (w'.bonds[k]! : WBond).kind ≠ .aromatic
  atomArom : ∀ i : ℕ, (w'.atoms[i]! : WAtom).aromatic = (w.atoms[i]! : WAtom).aromatic

lemma SameSkel.refl (w : Work) : SameSkel w w := ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

lemma SameSkel.trans {w₁ w₂ w₃ : Work} (h₁ : SameSkel w₁ w₂) (h₂ : SameSkel w₂ w₃) :
    SameSkel w₁ w₃ :=
  ⟨h₁.numAtoms.trans h₂.numAtoms, h₁.numBonds.trans h₂.numBonds,
    fun k ↦ (h₁.src k).trans (h₂.src k), fun k ↦ (h₁.dst k).trans (h₂.dst k)⟩

lemma SameSkel.touches' {w w' : Work} (h : SameSkel w w') (k i : ℕ) :
    (w.bonds[k]! : WBond).touches i = (w'.bonds[k]! : WBond).touches i := h.touches k i

lemma Local.avoid {D : ℕ → Bool} {w w' : Work} {c j : ℕ} (h : Local w w' c j)
    (hav : AvoidsCenters D w) (hc : OffD D w c) : AvoidsCenters D w' := by
  intro x hx k hk
  rw [← h.skel.touches]
  by_contra htx
  simp only [Bool.not_eq_false] at htx
  by_cases hxc : x = c
  · subst hxc
    simp [hc k hk] at htx
  by_cases hxj : x = j
  · subst hxj
    have := h.charged hxc
    simp [Work.cleanUpCenter, this] at hx
  -- `x` and its bonds are untouched
  have hsame : SameAt w w' x := by
    refine ⟨(h.atom x hxc hxj).symm, by rw [h.skel.bondsOf], fun k' hk' ↦ ?_⟩
    by_contra hne
    have htk : (w.bonds[k']! : WBond).touches x = true := by
      simpa [Work.bondsOf] using (List.mem_filter.mp hk').2
    rcases h.kind k' (Ne.symm hne) x htk with e | e
    · exact hxc e
    · exact hxj e
  rw [← hsame.cleanUpCenter] at hx
  have := hav x hx k hk
  simp [this] at htx

lemma Local.noArom {w w' : Work} {c j : ℕ} (h : Local w w' c j) (hn : NoAromatic w) :
    NoAromatic w' := by
  refine ⟨fun k ↦ ?_, fun i ↦ by rw [h.atomArom, hn.2]⟩
  by_cases hk : (w'.bonds[k]! : WBond).kind = (w.bonds[k]! : WBond).kind
  · rw [hk]
    exact hn.1 k
  · exact h.arom k hk

/-- Rewriting both sides alike near a rewritable atom `c` that no moved bond touches keeps the
invariant, provided the rewrite is the same composite of `setKind` and `modifyAtom` on both
sides. -/
lemma CleanInv.step {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂) {c j : ℕ}
    (hc : OffD D w₁ c) (F : Work → Work) (hrel : RelD D (F w₁) (F w₂))
    (hloc : Local w₁ (F w₁) c j) :
    CleanInv D w₀ (F w₁) (F w₂) :=
  ⟨hrel, hloc.avoid h.avoid hc, hloc.noArom h.noArom, h.skel.trans hloc.skel⟩

lemma SameSkel.wf {w w' : Work} (h : SameSkel w w') (hw : WF w) : WF w' := by
  intro k hk
  rw [← h.numBonds] at hk
  rw [← h.src, ← h.dst, ← h.numAtoms]
  exact hw k hk

lemma SameSkel.symm {w w' : Work} (h : SameSkel w w') : SameSkel w' w :=
  ⟨h.numAtoms.symm, h.numBonds.symm, fun k ↦ (h.src k).symm, fun k ↦ (h.dst k).symm⟩

lemma touches_of_mem_bondsOf {w : Work} {c k : ℕ} (hk : k ∈ w.bondsOf c) :
    (w.bonds[k]! : WBond).touches c = true := (List.mem_filter.mp hk).2

lemma lt_of_mem_bondsOf {w : Work} {c k : ℕ} (hk : k ∈ w.bondsOf c) : k < w.numBonds :=
  List.mem_range.mp (List.mem_filter.mp hk).1

lemma other_lt {w : Work} (hwf : WF w) {c k : ℕ} (hk : k ∈ w.bondsOf c) :
    (w.bonds[k]! : WBond).other c < w.atoms.size := by
  obtain ⟨hs, hd, -⟩ := hwf k (lt_of_mem_bondsOf hk)
  simp only [WBond.other]
  split <;> assumption

lemma mem_neighbors {w : Work} {c k j : ℕ} (h : (k, j) ∈ w.neighbors c) :
    k ∈ w.bondsOf c ∧ j = (w.bonds[k]! : WBond).other c := by
  obtain ⟨k', hk', e⟩ := List.mem_map.mp h
  simp only [Prod.mk.injEq] at e
  exact ⟨e.1 ▸ hk', e.1 ▸ e.2.symm⟩

lemma skel_setKind (w : Work) (k : ℕ) (o : BondKind) : SameSkel w (w.setKind k o) :=
  ⟨rfl, by simp, fun _ ↦ by simp, fun _ ↦ by simp⟩

lemma skel_modifyAtom (w : Work) (i : ℕ) (f : WAtom → WAtom) : SameSkel w (w.modifyAtom i f) :=
  ⟨by simp, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `setKind`, then `F` at `c`, then `G` at `j` (the nitrogen rewrites). -/
lemma local_kcj (w : Work) (hwf : WF w) {c k : ℕ} (hk : k ∈ w.bondsOf c) (o : BondKind)
    (ho : o ≠ .aromatic) (F G : WAtom → WAtom) (hF : ∀ a, (F a).aromatic = a.aromatic)
    (hG : ∀ a, (G a).aromatic = a.aromatic) (hGc : ∀ a, (G a).charge ≠ 0) :
    Local w (((w.setKind k o).modifyAtom c F).modifyAtom ((w.bonds[k]! : WBond).other c) G) c
      ((w.bonds[k]! : WBond).other c) where
  skel := ((skel_setKind w k o).trans (skel_modifyAtom _ c F)).trans (skel_modifyAtom _ _ G)
  atom i hc hj := by simp [atom_modifyAtom, Ne.symm hc, Ne.symm hj]
  charged _ := by
    rw [atom_modifyAtom, if_pos ⟨rfl, by simpa using other_lt hwf hk⟩]
    exact hGc _
  kind k' hk' i hi := by
    simp only [bonds_modifyAtom, kind_setKind] at hk'
    split at hk'
    · rename_i e
      obtain ⟨rfl, -⟩ := e
      exact touches_other (touches_of_mem_bondsOf hk) hi
    · exact absurd rfl hk'
  arom k' hk' := by
    simp only [bonds_modifyAtom, kind_setKind] at hk' ⊢
    by_cases e : k = k' ∧ k' < w.bonds.size
    · simpa [e] using ho
    · simp [e] at hk'
  atomArom i := by
    simp only [atom_modifyAtom, atoms_setKind, size_atoms_modifyAtom]
    split_ifs <;> simp [hF, hG]

/-- `setKind`, then `G` at `j`, then `F` at `c` (the phosphorus rewrite). -/
lemma local_kjc (w : Work) (hwf : WF w) {c k : ℕ} (hk : k ∈ w.bondsOf c) (o : BondKind)
    (ho : o ≠ .aromatic) (F G : WAtom → WAtom) (hF : ∀ a, (F a).aromatic = a.aromatic)
    (hG : ∀ a, (G a).aromatic = a.aromatic) (hGc : ∀ a, (G a).charge ≠ 0) :
    Local w (((w.setKind k o).modifyAtom ((w.bonds[k]! : WBond).other c) G).modifyAtom c F) c
      ((w.bonds[k]! : WBond).other c) where
  skel := ((skel_setKind w k o).trans (skel_modifyAtom _ _ G)).trans (skel_modifyAtom _ c F)
  atom i hc hj := by simp [atom_modifyAtom, Ne.symm hc, Ne.symm hj]
  charged hjc := by
    rw [atom_modifyAtom, if_neg fun e ↦ hjc e.1.symm, atom_modifyAtom,
      if_pos ⟨rfl, by simpa using other_lt hwf hk⟩]
    exact hGc _
  kind k' hk' i hi := by
    simp only [bonds_modifyAtom, kind_setKind] at hk'
    split at hk'
    · rename_i e
      obtain ⟨rfl, -⟩ := e
      exact touches_other (touches_of_mem_bondsOf hk) hi
    · exact absurd rfl hk'
  arom k' hk' := by
    simp only [bonds_modifyAtom, kind_setKind] at hk' ⊢
    by_cases e : k = k' ∧ k' < w.bonds.size
    · simpa [e] using ho
    · simp [e] at hk'
  atomArom i := by
    simp only [atom_modifyAtom, atoms_setKind, size_atoms_modifyAtom]
    split_ifs <;> simp [hF, hG]

/-- `setKind`, then `G` at `j` (one step of the halogen rewrite). -/
lemma local_kj (w : Work) (hwf : WF w) {c k : ℕ} (hk : k ∈ w.bondsOf c) (o : BondKind)
    (ho : o ≠ .aromatic) (G : WAtom → WAtom) (hG : ∀ a, (G a).aromatic = a.aromatic)
    (hGc : ∀ a, (G a).charge ≠ 0) :
    Local w ((w.setKind k o).modifyAtom ((w.bonds[k]! : WBond).other c) G) c
      ((w.bonds[k]! : WBond).other c) where
  skel := (skel_setKind w k o).trans (skel_modifyAtom _ _ G)
  atom i _ hj := by simp [atom_modifyAtom, Ne.symm hj]
  charged _ := by
    rw [atom_modifyAtom, if_pos ⟨rfl, by simpa using other_lt hwf hk⟩]
    exact hGc _
  kind k' hk' i hi := by
    simp only [bonds_modifyAtom, kind_setKind] at hk'
    split at hk'
    · rename_i e
      obtain ⟨rfl, -⟩ := e
      exact touches_other (touches_of_mem_bondsOf hk) hi
    · exact absurd rfl hk'
  arom k' hk' := by
    simp only [bonds_modifyAtom, kind_setKind] at hk' ⊢
    by_cases e : k = k' ∧ k' < w.bonds.size
    · simpa [e] using ho
    · simp [e] at hk'
  atomArom i := by
    simp only [atom_modifyAtom, atoms_setKind]
    split_ifs <;> simp [hG]

/-- `F` at `c` alone (the end of the halogen rewrite). -/
lemma local_c (w : Work) (c : ℕ) (F : WAtom → WAtom) (hF : ∀ a, (F a).aromatic = a.aromatic) :
    Local w (w.modifyAtom c F) c c where
  skel := skel_modifyAtom w c F
  atom i hc _ := by simp [atom_modifyAtom, Ne.symm hc]
  charged h := absurd rfl h
  kind k' hk' := absurd rfl hk'
  arom k' hk' := absurd rfl hk'
  atomArom i := by
    simp only [atom_modifyAtom]
    split_ifs <;> simp [hF]

/-! #### The steps of `cleanUp`, with their searches named

`Basic` writes the steps of `cleanUp` with their searches inline. The lockstep proofs take them
with the predicates of `Passes` (`nitroCand`, `nitroO`, `azideN`). -/

/-- What `nitroStep` does to the working copy at a `nitroCand` nitrogen `i`: the first neutral O
on a double bond becomes -O⁻ and `i` becomes N⁺. -/
def nitrogenOxideAt (w : Work) (i : ℕ) : Work :=
  match (w.neighbors i).find? w.nitroO with
  | some (k, j) =>
    ((w.setKind k .single).modifyAtom i ({ · with charge := 1 })).modifyAtom j
      ({ · with charge := -1 })
  | none => w

/-- `nitroStep` rewrites at the `nitroCand` nitrogens, and remembers them. -/
lemma nitroStep_eq (s : Work × List ℕ) (i : ℕ) :
    nitroStep s i = if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s := by
  obtain ⟨w, c⟩ := s
  unfold nitroStep nitroCand
  dsimp only
  split <;> rename_i h <;> simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  · rw [if_neg (by simp only [Bool.and_eq_true, beq_iff_eq]; tauto)]
  · rw [if_pos (by simp only [Bool.and_eq_true, beq_iff_eq]; tauto)]
    refine (congrArg (fun o : Option (ℕ × ℕ) ↦ (match o with
      | some (k, j) =>
        (((w.setKind k .single).modifyAtom i ({ · with charge := 1 })).modifyAtom j
          ({ · with charge := -1 }), c ++ [i])
      | none => (w, c ++ [i]) : Work × List ℕ))
      (find?_congr_mem (q := w.nitroO) fun ⟨_, _⟩ _ ↦ rfl)).trans ?_
    unfold nitrogenOxideAt
    cases (w.neighbors i).find? w.nitroO <;> rfl

/-- `azideStep`, with its search named. -/
lemma azideStep_eq (w : Work) (i : ℕ) :
    azideStep w i = match (w.neighbors i).find? w.azideN with
      | some (k, j) =>
        ((w.setKind k .double).modifyAtom i ({ · with charge := 1 })).modifyAtom j
          ({ · with charge := -1 })
      | none => w := by
  unfold azideStep
  exact congrArg (fun o : Option (ℕ × ℕ) ↦ (match o with
    | some (k, j) =>
      ((w.setKind k .double).modifyAtom i ({ · with charge := 1 })).modifyAtom j
        ({ · with charge := -1 })
    | none => w : Work)) (find?_congr_mem (q := w.azideN) fun ⟨_, _⟩ _ ↦ rfl)

/-- `nitrogensCleanup`: the first pass rewrites at the `nitroCand` nitrogens and remembers them,
the second revisits those. -/
lemma nitrogensCleanup_eq (w : Work) :
    w.nitrogensCleanup =
      ((List.range w.numAtoms).foldl (init := (w, ([] : List ℕ))) fun s i ↦
        if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s).2.foldl azideStep
      ((List.range w.numAtoms).foldl (init := (w, ([] : List ℕ))) fun s i ↦
        if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s).1 := by
  rw [← show nitroStep = (fun s i ↦
    if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s) from
      funext fun s ↦ funext fun i ↦ nitroStep_eq s i]
  rfl

/-- One neighbour `(bond, atom)` of `phosphorusScan`. -/
def phosphorusStep (w : Work) (s : Option (ℕ × ℕ) × Bool) (p : ℕ × ℕ) : Option (ℕ × ℕ) × Bool :=
  let b := w.atoms[p.2]!
  if b.z == 8 && b.charge == 0 && w.bonds[p.1]!.kind == .double then (some p, s.2)
  else if (b.z == 6 || b.z == 7) && 2 ≤ w.degree p.2 && w.bonds[p.1]!.kind == .double then
    (s.1, true)
  else s

/-- `phosphorusScan` is a fold of `phosphorusStep` over the neighbours. -/
lemma phosphorusScan_eq (w : Work) (i : ℕ) :
    w.phosphorusScan i = (w.neighbors i).foldl w.phosphorusStep (none, false) := by
  unfold phosphorusScan
  exact foldl_congr_mem (fun ⟨_, _⟩ ⟨_, _⟩ _ ↦ rfl) _

/-- One neighbour of `halogenCleanup`, on a pair it does not take apart. -/
lemma halogenStep_eq (s : Work × ℤ) (p : ℕ × ℕ) :
    halogenStep s p = if s.1.bonds[p.1]!.kind == .double then
      ((s.1.setKind p.1 .single).modifyAtom p.2 ({ · with charge := -1 }), s.2 + 1) else s := by
  obtain ⟨w, fc⟩ := s
  obtain ⟨k, j⟩ := p
  rfl

namespace CleanInv

variable {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂) (hwf : WF w₀)
include h

lemma wf₁ (hwf : WF w₀) : WF w₁ := h.skel.wf hwf

/-- At an atom no moved bond touches, the bonds have the same kinds on both sides. -/
lemma kind_at {c : ℕ} (hc : OffD D w₁ c) {k : ℕ} (hk : k ∈ w₁.bondsOf c) :
    (w₁.bonds[k]! : WBond).kind = (w₂.bonds[k]! : WBond).kind :=
  h.rel.off k (hc.notD hk)

lemma find?_eq {c : ℕ} {p₁ p₂ : Work → ℕ × ℕ → Bool}
    (hp : ∀ k j, k ∈ w₁.bondsOf c → p₁ w₁ (k, j) = p₂ w₂ (k, j)) :
    (w₁.neighbors c).find? (p₁ w₁) = (w₂.neighbors c).find? (p₂ w₂) := by
  rw [← h.rel.neighbors]
  exact find?_congr_mem fun ⟨k, j⟩ hkj ↦ hp k j (mem_neighbors hkj).1

include hwf in
lemma nitrogenOxideAt {i : ℕ} (hi : w₁.cleanUpCenter i = true) :
    CleanInv D w₀ (w₁.nitrogenOxideAt i) (w₂.nitrogenOxideAt i) := by
  have hc := h.avoid i hi
  have hfind := h.find?_eq (c := i) (p₁ := nitroO) (p₂ := nitroO) fun k j hk ↦ by
    simp only [Work.nitroO, h.rel.atoms, h.kind_at hc hk]
  unfold Work.nitrogenOxideAt
  rw [← hfind]
  rcases hf : (w₁.neighbors i).find? w₁.nitroO with _ | ⟨k, j⟩
  · exact h
  · obtain ⟨hk, rfl⟩ := mem_neighbors (List.mem_of_find?_eq_some hf)
    exact h.step hc (fun w ↦ ((w.setKind k .single).modifyAtom i ({ · with charge := 1 }))
        |>.modifyAtom ((w₁.bonds[k]! : WBond).other i) ({ · with charge := -1 }))
      (((h.rel.setKind k (hc.notD hk) _).modifyAtom _ _).modifyAtom _ _)
      (local_kcj w₁ (h.wf₁ hwf) hk .single (by decide) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ ↦ by simp))

include hwf in
lemma azideStep {i : ℕ} (hc : OffD D w₁ i) :
    CleanInv D w₀ (w₁.azideStep i) (w₂.azideStep i) := by
  have hfind := h.find?_eq (c := i) (p₁ := azideN) (p₂ := azideN) fun k j hk ↦ by
    simp only [Work.azideN, h.rel.atoms, h.kind_at hc hk]
  rw [azideStep_eq, azideStep_eq, ← hfind]
  rcases hf : (w₁.neighbors i).find? w₁.azideN with _ | ⟨k, j⟩
  · exact h
  · obtain ⟨hk, rfl⟩ := mem_neighbors (List.mem_of_find?_eq_some hf)
    exact h.step hc (fun w ↦ ((w.setKind k .double).modifyAtom i ({ · with charge := 1 }))
        |>.modifyAtom ((w₁.bonds[k]! : WBond).other i) ({ · with charge := -1 }))
      (((h.rel.setKind k (hc.notD hk) _).modifyAtom _ _).modifyAtom _ _)
      (local_kcj w₁ (h.wf₁ hwf) hk .double (by decide) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ ↦ by simp))

end CleanInv

lemma cleanUpCenter_of_nitroCand {w : Work} {i : ℕ} (h : w.nitroCand i = true) :
    w.cleanUpCenter i = true := by
  simp only [Work.nitroCand, Bool.and_eq_true, beq_iff_eq] at h
  simp [Work.cleanUpCenter, h.1.1, h.1.2, h.2]

lemma CleanInv.nitrogensCleanup {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂)
    (hwf : WF w₀) : CleanInv D w₀ w₁.nitrogensCleanup w₂.nitrogensCleanup := by
  rw [nitrogensCleanup_eq, nitrogensCleanup_eq, ← h.rel.numAtoms]
  -- the first pass: the same rewrites, and the same list of nitrogens, none on a moved bond
  let R : Work × List ℕ → Work × List ℕ → Prop := fun s t ↦
    CleanInv D w₀ s.1 t.1 ∧ s.2 = t.2 ∧ ∀ i ∈ s.2, OffD D s.1 i
  have hfirst : R ((List.range w₁.numAtoms).foldl (init := (w₁, ([] : List ℕ))) fun s i ↦
        if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s)
      ((List.range w₁.numAtoms).foldl (init := (w₂, ([] : List ℕ))) fun s i ↦
        if s.1.nitroCand i then (s.1.nitrogenOxideAt i, s.2 ++ [i]) else s) := by
    refine foldl_lockstep _ (fun s t i _ hst ↦ ?_) ⟨h, rfl, by simp⟩
    obtain ⟨hst, h2, hoff⟩ := hst
    have hn : s.1.nitroCand i = t.1.nitroCand i := by
      simp only [Work.nitroCand, hst.rel.atoms, hst.rel.sim.explicitValence]
    rw [← hn]
    split
    · rename_i hi
      have hc := cleanUpCenter_of_nitroCand hi
      have hnew := hst.nitrogenOxideAt hwf hc
      refine ⟨hnew, by rw [h2], fun j hj ↦ ?_⟩
      have hskel : SameSkel s.1 (s.1.nitrogenOxideAt i) := hst.skel.symm.trans hnew.skel
      have off : ∀ x, OffD D s.1 x → OffD D (s.1.nitrogenOxideAt i) x := fun x hx k hk ↦ by
        rw [← hskel.touches]
        exact hx k hk
      rcases List.mem_append.mp hj with hj | hj
      · exact off j (hoff j hj)
      · simp only [List.mem_singleton] at hj
        exact off j (hj ▸ hst.avoid i hc)
    · exact ⟨hst, h2, hoff⟩
  obtain ⟨hf, h2, hoff⟩ := hfirst
  rw [← h2]
  -- the second pass revisits those nitrogens
  have : ∀ (l : List ℕ) (s t : Work), CleanInv D w₀ s t → (∀ i ∈ l, OffD D s i) →
      CleanInv D w₀ (l.foldl Work.azideStep s) (l.foldl Work.azideStep t) := by
    intro l
    induction l with
    | nil => intro s t hst _; exact hst
    | cons i l ih =>
      intro s t hst hoff
      have hnew := hst.azideStep hwf (hoff i List.mem_cons_self)
      refine ih _ _ hnew fun j hj ↦ ?_
      have hskel : SameSkel s (s.azideStep i) := hst.skel.symm.trans hnew.skel
      intro k hk
      rw [← hskel.touches]
      exact hoff j (List.mem_cons_of_mem _ hj) k hk
  exact this _ _ _ hf hoff

lemma phosphorusScan_mem (w : Work) (l : List (ℕ × ℕ)) (s : Option (ℕ × ℕ) × Bool) {p : ℕ × ℕ}
    (h : (l.foldl w.phosphorusStep s).1 = some p) : s.1 = some p ∨ p ∈ l := by
  induction l generalizing s with
  | nil => exact Or.inl h
  | cons q l ih =>
    rcases ih _ h with e | e
    · unfold Work.phosphorusStep at e
      dsimp only at e
      split at e
      · simp only [Option.some.injEq] at e
        exact Or.inr (e ▸ List.mem_cons_self)
      · split at e <;> exact Or.inl e
    · exact Or.inr (List.mem_cons_of_mem _ e)

lemma CleanInv.phosphorusCleanup {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂)
    (hwf : WF w₀) {i : ℕ} (hz : (w₁.atoms[i]! : WAtom).z = 15) :
    CleanInv D w₀ (w₁.phosphorusCleanup i) (w₂.phosphorusCleanup i) := by
  unfold Work.phosphorusCleanup
  dsimp only
  rw [← h.rel.atoms, ← h.rel.sim.explicitValence, ← h.rel.degree]
  split
  · exact h
  rename_i hcond
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hcond
  have hc : OffD D w₁ i := h.avoid i (by simp [Work.cleanUpCenter, hz, hcond])
  have hscan : w₂.phosphorusScan i = w₁.phosphorusScan i := by
    rw [phosphorusScan_eq, phosphorusScan_eq, ← h.rel.neighbors]
    refine List.foldl_ext _ _ _ fun s ⟨k, j⟩ hkj ↦ ?_
    have hk := (mem_neighbors hkj).1
    simp only [Work.phosphorusStep, h.rel.atoms, h.rel.degree, h.kind_at hc hk]
  rw [hscan]
  rcases hs : w₁.phosphorusScan i with ⟨_ | ⟨k, j⟩, _ | _⟩
  · exact h
  · exact h
  · exact h
  · have hmem : (k, j) ∈ w₁.neighbors i := by
      rcases phosphorusScan_mem w₁ _ _ (congrArg Prod.fst ((phosphorusScan_eq w₁ i).symm.trans hs))
        with e | e
      · simp at e
      · exact e
    obtain ⟨hk, rfl⟩ := mem_neighbors hmem
    exact h.step hc (fun w ↦ ((w.setKind k .single).modifyAtom ((w₁.bonds[k]! : WBond).other i)
        ({ · with charge := -1 })).modifyAtom i ({ · with charge := 1 }))
      (((h.rel.setKind k (hc.notD hk) _).modifyAtom _ _).modifyAtom _ _)
      (local_kjc w₁ (h.wf₁ hwf) hk .single (by decide) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)
        (fun _ ↦ by simp))

lemma CleanInv.halogenCleanup {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂)
    (hwf : WF w₀) {i : ℕ} (hz : (w₁.atoms[i]! : WAtom).z = 17 ∨ (w₁.atoms[i]! : WAtom).z = 35 ∨
      (w₁.atoms[i]! : WAtom).z = 53) :
    CleanInv D w₀ (w₁.halogenCleanup i) (w₂.halogenCleanup i) := by
  unfold Work.halogenCleanup
  dsimp only
  rw [← h.rel.atoms, ← h.rel.sim.explicitValence, ← h.rel.neighbors]
  split
  · exact h
  rename_i hcond
  split
  · exact h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not, Bool.not_eq_true',
    Bool.not_eq_false] at hcond
  have hc : OffD D w₁ i := h.avoid i (by
    rcases hz with hz | hz | hz <;> simp [Work.cleanUpCenter, hcond.1, hz] <;> simpa using hcond.2)
  -- the halogen's neighbours, rewritten in turn
  let R : Work × ℤ → Work × ℤ → Prop := fun s t ↦
    CleanInv D w₀ s.1 t.1 ∧ s.2 = t.2 ∧ SameSkel w₁ s.1
  have hfold : R ((w₁.neighbors i).foldl halogenStep (w₁, 0))
      ((w₁.neighbors i).foldl halogenStep (w₂, 0)) := by
    refine foldl_lockstep _ (fun s t ⟨k, j⟩ hkj hst ↦ ?_) ⟨h, rfl, SameSkel.refl _⟩
    obtain ⟨hst, h2, hsk⟩ := hst
    obtain ⟨hk, rfl⟩ := mem_neighbors hkj
    have hk' : k ∈ s.1.bondsOf i := by rwa [← hsk.bondsOf]
    have hc' : OffD D s.1 i := fun k' hk'' ↦ by rw [← hsk.touches]; exact hc k' hk''
    have hother : (w₁.bonds[k]! : WBond).other i = (s.1.bonds[k]! : WBond).other i := hsk.other k i
    rw [halogenStep_eq, halogenStep_eq, ← hst.kind_at hc' hk', h2]
    split
    · rw [hother]
      have hnew := hst.step hc' (fun w ↦ (w.setKind k .single).modifyAtom
          ((s.1.bonds[k]! : WBond).other i) ({ · with charge := -1 }))
        ((hst.rel.setKind k (hc'.notD hk') _).modifyAtom _ _)
        (local_kj s.1 (hst.wf₁ hwf) hk' .single (by decide) _ (fun _ ↦ rfl) (fun _ ↦ by simp))
      exact ⟨hnew, rfl, hsk.trans (hst.skel.symm.trans hnew.skel)⟩
    · exact ⟨hst, h2, hsk⟩
  obtain ⟨hf, h2, hsk⟩ := hfold
  rw [← h2]
  have hc' : OffD D ((w₁.neighbors i).foldl halogenStep (w₁, 0)).1 i := fun k' hk'' ↦ by
    rw [← hsk.touches]; exact hc k' hk''
  exact hf.step hc' (fun w ↦ w.modifyAtom i _) (hf.rel.modifyAtom _ _) (local_c _ i _ fun _ ↦ rfl)

lemma CleanInv.cleanUp {D : ℕ → Bool} {w₀ w₁ w₂ : Work} (h : CleanInv D w₀ w₁ w₂)
    (hwf : WF w₀) : CleanInv D w₀ w₁.cleanUp w₂.cleanUp := by
  have hn := h.nitrogensCleanup hwf
  unfold Work.cleanUp
  dsimp only
  rw [← hn.rel.numAtoms]
  refine foldl_lockstep _ (fun s t i _ hst ↦ ?_) hn
  unfold Work.cleanUpStep
  dsimp only
  rw [← hst.rel.atoms]
  split
  · rename_i hz
    exact hst.phosphorusCleanup hwf (by simpa using hz)
  · split
    · rename_i _ hz
      exact hst.halogenCleanup hwf (by simpa [or_assoc] using hz)
    · exact hst

/-! ### The passes keep the skeleton, and keep a Kekulé structure Kekulé -/

lemma freezeHs_atom (w : Work) (i : ℕ) :
    w.freezeHs.atoms[i]! =
      if i < w.atoms.size then { w.atoms[i]! with frozenHs := some (w.totalHs i) }
      else w.atoms[i]! := by
  by_cases hi : i < w.atoms.size
  · rw [if_pos hi, getElem!_pos _ i (by simpa [Work.freezeHs, Work.numAtoms] using hi)]
    simp [Work.freezeHs, Work.numAtoms]
  · rw [if_neg hi, getElem!_neg _ i (by simpa [Work.freezeHs, Work.numAtoms] using hi),
      getElem!_neg _ i hi]

lemma cacheValences_atom (w : Work) (i : ℕ) :
    w.cacheValences.atoms[i]! =
      if i < w.atoms.size then
        { w.atoms[i]! with cachedValence := some (w.explicitValence i),
                           cachedImplicit := w.implicitHs i, adjustHs := w.isAromaticAtom i }
      else w.atoms[i]! := by
  by_cases hi : i < w.atoms.size
  · rw [if_pos hi, getElem!_pos _ i (by simpa [Work.cacheValences, Work.numAtoms] using hi)]
    simp [Work.cacheValences, Work.numAtoms]
  · rw [if_neg hi, getElem!_neg _ i (by simpa [Work.cacheValences, Work.numAtoms] using hi),
      getElem!_neg _ i hi]

lemma skel_of_bonds {w w' : Work} (hb : w'.bonds = w.bonds) (ha : w'.atoms.size = w.atoms.size) :
    SameSkel w w' :=
  ⟨by simp [Work.numAtoms, ha], by simp [Work.numBonds, hb], fun _ ↦ by rw [hb],
    fun _ ↦ by rw [hb]⟩

lemma skel_freezeHs (w : Work) : SameSkel w w.freezeHs :=
  skel_of_bonds rfl (by simp [Work.freezeHs, Work.numAtoms])

lemma skel_cacheValences (w : Work) : SameSkel w w.cacheValences :=
  skel_of_bonds rfl (by simp [Work.cacheValences, Work.numAtoms])

lemma size_atoms_assignRadicals (w : Work) : w.assignRadicals.atoms.size = w.atoms.size := by
  unfold Work.assignRadicals
  generalize List.range w.numAtoms = l
  induction l generalizing w with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih]
    unfold Work.radicalStep
    dsimp only
    split
    · rfl
    · simp

lemma skel_assignRadicals (w : Work) : SameSkel w w.assignRadicals :=
  skel_of_bonds (assignRadicals_bonds w) (size_atoms_assignRadicals w)

lemma aromatic_assignRadicals (w : Work) (i : ℕ) :
    (w.assignRadicals.atoms[i]! : WAtom).aromatic = (w.atoms[i]! : WAtom).aromatic := by
  unfold Work.assignRadicals
  generalize List.range w.numAtoms = l
  induction l generalizing w with
  | nil => rfl
  | cons j l ih =>
    rw [List.foldl_cons, ih]
    unfold Work.radicalStep
    dsimp only
    split
    · rfl
    · rw [atom_modifyAtom]
      split_ifs with h
      · obtain ⟨rfl, -⟩ := h
        rfl
      · rfl

lemma NoAromatic.freezeHs {w : Work} (h : NoAromatic w) : NoAromatic w.freezeHs :=
  ⟨h.1, fun i ↦ by rw [freezeHs_atom]; split <;> exact h.2 i⟩

lemma NoAromatic.cacheValences {w : Work} (h : NoAromatic w) : NoAromatic w.cacheValences :=
  ⟨h.1, fun i ↦ by rw [cacheValences_atom]; split <;> exact h.2 i⟩

lemma NoAromatic.assignRadicals {w : Work} (h : NoAromatic w) : NoAromatic w.assignRadicals :=
  ⟨fun k ↦ by rw [assignRadicals_bonds]; exact h.1 k, fun i ↦ by
    rw [aromatic_assignRadicals]; exact h.2 i⟩

lemma NoAromatic.isAromaticAtom {w : Work} (h : NoAromatic w) (i : ℕ) :
    w.isAromaticAtom i = false := by
  simp [Work.isAromaticAtom, h.2 i, h.1]

/-- `freezeHs` leaves what `cleanUp` looks at alone. -/
lemma explicitValence_freezeHs (w : Work) : w.freezeHs.explicitValence = w.explicitValence := by
  funext i
  have hz : (w.freezeHs.atoms[i]! : WAtom).z = (w.atoms[i]! : WAtom).z := by
    rw [freezeHs_atom]; split <;> rfl
  have hc : (w.freezeHs.atoms[i]! : WAtom).charge = (w.atoms[i]! : WAtom).charge := by
    rw [freezeHs_atom]; split <;> rfl
  have he : (w.freezeHs.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs := by
    rw [freezeHs_atom]; split <;> rfl
  have ha : (w.freezeHs.atoms[i]! : WAtom).aromatic = (w.atoms[i]! : WAtom).aromatic := by
    rw [freezeHs_atom]; split <;> rfl
  have hsum : w.freezeHs.bondHalfSum i = w.bondHalfSum i := rfl
  have harom : w.freezeHs.isAromaticAtom i = w.isAromaticAtom i := by
    simp only [Work.isAromaticAtom, ha]
    rfl
  simp only [Work.explicitValence, effectiveZ, hz, hc, he, hsum, harom]

lemma cleanUpCenter_freezeHs (w : Work) : w.freezeHs.cleanUpCenter = w.cleanUpCenter := by
  funext i
  have hz : (w.freezeHs.atoms[i]! : WAtom).z = (w.atoms[i]! : WAtom).z := by
    rw [freezeHs_atom]; split <;> rfl
  have hc : (w.freezeHs.atoms[i]! : WAtom).charge = (w.atoms[i]! : WAtom).charge := by
    rw [freezeHs_atom]; split <;> rfl
  simp only [Work.cleanUpCenter, hz, hc, explicitValence_freezeHs]

/-- Explicit valence of an atom no aromatic bond touches: bond orders plus written hydrogens. -/
lemma explicitValence_of_not_aromatic (w : Work) (i : ℕ) (h : w.isAromaticAtom i = false) :
    w.explicitValence i = (2 * (w.atoms[i]! : WAtom).explicitHs + w.bondHalfSum i + 1) / 2 := by
  simp only [Work.explicitValence, h, Bool.and_false]
  split <;> rfl

lemma bondsOf_eq_nil {w : Work} (hwf : WF w) {i : ℕ} (hi : w.numAtoms ≤ i) : w.bondsOf i = [] := by
  refine List.filter_eq_nil_iff.mpr fun k hk ↦ ?_
  obtain ⟨hs, hd, -⟩ := hwf k (List.mem_range.mp hk)
  simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq, not_or]
  omega

/-- The relation with no moved bonds relates a working copy to itself. -/
lemma RelD.rfl (w : Work) : RelD (fun _ ↦ false) w w :=
  ⟨SameSkel.refl w, _root_.rfl, fun _ _ ↦ _root_.rfl, fun _ h ↦ absurd h (by simp),
    fun _ ↦ _root_.rfl⟩

lemma CleanInv.rfl (w : Work) (h : NoAromatic w) : CleanInv (fun _ ↦ false) w w w :=
  ⟨RelD.rfl w, fun _ _ _ hk ↦ absurd hk (by simp), h, SameSkel.refl w⟩

/-- The lockstep, from equal bond-order sums at every atom. -/
lemma RelD.of_bondHalfSum {D : ℕ → Bool} {w₁ w₂ : Work} (hs : SameSkel w₁ w₂)
    (ha : w₁.atoms = w₂.atoms)
    (hoff : ∀ k : ℕ, D k = false → (w₁.bonds[k]! : WBond).kind = (w₂.bonds[k]! : WBond).kind)
    (hon : ∀ k : ℕ, D k = true → isSD (w₁.bonds[k]! : WBond).kind ∧
      isSD (w₂.bonds[k]! : WBond).kind ∧ (w₁.bonds[k]! : WBond).kind ≠ (w₂.bonds[k]! : WBond).kind)
    (hsum : ∀ i, w₁.bondHalfSum i = w₂.bondHalfSum i) : RelD D w₁ w₂ where
  toSameSkel := hs
  atoms := ha
  off := hoff
  on := hon
  dsum i := by
    have h := hsum i
    simp only [bondHalfSum, ← hs.bondsOf] at h
    rw [← hs.bondsOf]
    simp only [sum_map_filter]
    have e : ∀ f : ℕ → ℕ, ((w₁.bondsOf i).map f).sum =
        ((w₁.bondsOf i).map fun k ↦ if D k then f k else 0).sum +
          ((w₁.bondsOf i).map fun k ↦ if D k then 0 else f k).sum := fun f ↦ by
      rw [← List.sum_map_add]
      congr 1
      exact List.map_congr_left fun k _ ↦ by cases D k <;> simp
    rw [e, e (fun k ↦ halfOrder (w₂.bonds[k]! : WBond).kind)] at h
    have hrest : ((w₁.bondsOf i).map fun k ↦ if D k then 0 else halfOrder w₁.bonds[k]!.kind) =
        (w₁.bondsOf i).map fun k ↦ if D k then 0 else halfOrder w₂.bonds[k]!.kind :=
      List.map_congr_left fun k _ ↦ by
        cases hD : D k
        · simp [hoff k hD]
        · simp
    rw [hrest] at h
    omega

/-- The lockstep of this file is the swap of `Congruence`, over the moved bonds. -/
lemma RelD.swapped {D : ℕ → Bool} {w₁ w₂ : Work} (h : RelD D w₁ w₂) : Swapped D w₁ w₂ where
  atoms := h.atoms.symm
  size := by
    have := h.numBonds
    simpa [Work.numBonds] using this.symm
  ends k := by
    have hn : w₁.bonds.size = w₂.bonds.size := h.numBonds
    by_cases hk : k < w₁.bonds.size
    · have h1 := h.src k
      have h2 := h.dst k
      rw [getElem!_pos w₁.bonds k hk, getElem!_pos w₂.bonds k (hn ▸ hk)] at h1 h2
      simp [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem (hn ▸ hk), h1, h2]
    · simp [Array.getElem?_eq_none (Nat.le_of_not_lt hk),
        Array.getElem?_eq_none (Nat.le_of_not_lt (hn ▸ hk))]
  kind k hk := by
    have hn : w₁.bonds.size = w₂.bonds.size := h.numBonds
    by_cases hk' : k < w₁.bonds.size
    · have h1 := h.off k hk
      rw [getElem!_pos w₁.bonds k hk', getElem!_pos w₂.bonds k (hn ▸ hk')] at h1
      simp [Work.kind?, Array.getElem?_eq_getElem hk', Array.getElem?_eq_getElem (hn ▸ hk'), h1]
    · simp [Work.kind?, Array.getElem?_eq_none (Nat.le_of_not_lt hk'),
        Array.getElem?_eq_none (Nat.le_of_not_lt (hn ▸ hk'))]
  sd k hk := by
    have hn : w₁.bonds.size = w₂.bonds.size := h.numBonds
    have hk' : k < w₁.bonds.size := h.lt_of_D hk
    obtain ⟨h1, h2, -⟩ := h.on k hk
    rw [getElem!_pos w₁.bonds k hk'] at h1
    rw [getElem!_pos w₂.bonds k (hn ▸ hk')] at h2
    have sd : ∀ x : BondKind, isSD x = true → IsSD x := fun x hx ↦ by
      cases x <;> simp_all [isSD, IsSD]
    exact ⟨⟨_, by simp [Work.kind?, Array.getElem?_eq_getElem hk'], sd _ h1⟩,
      ⟨_, by simp [Work.kind?, Array.getElem?_eq_getElem (hn ▸ hk')], sd _ h2⟩⟩
  sum i := (h.sim.sum i).symm

/-- Partners in lockstep make the same bonds aromatic, when every moved bond is a bond of one of
the rings: `Swapped.aromaticBondList_eq`. A moved bond lies on a cycle (`RelD.onCycle_of_D`), but
that every bond on a cycle is a bond of one of the `relevantCycles` is not proved. -/
lemma RelD.aromaticBondList {D : ℕ → Bool} {w₁ w₂ : Work} (h : RelD D w₁ w₂)
    (rings : Array (List ℕ)) (hD : ∀ k, D k = true → k ∈ rings.toList.flatMap w₁.ringBonds) :
    w₁.aromaticBondList rings = w₂.aromaticBondList rings :=
  (h.swapped.aromaticBondList_eq rings hD).symm

end Work

end LeanSMILES.Aromaticity
