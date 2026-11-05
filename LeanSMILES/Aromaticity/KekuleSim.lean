/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Perceive
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# LeanSMILES.Aromaticity.KekuleSim

Two working copies that differ only in where their double bonds sit run through
`Molecule.aromatize` in lockstep.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A left fold that adds is the start plus the sum. -/
lemma foldl_add_eq_sum {β : Type*} (f : β → ℕ) (l : List β) (a : ℕ) :
    l.foldl (fun s k ↦ s + f k) a = a + (l.map f).sum := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp [ih, Nat.add_assoc]

lemma sum_map_two_mul {β : Type*} (l : List β) (f : β → ℕ) :
    (l.map fun k ↦ 2 * f k).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih, Nat.mul_add]

/-- A left fold carries any relation its step carries. -/
lemma foldl_rel {α β : Type*} {R : α → α → Prop} {f : α → β → α} (l : List β)
    (hf : ∀ a₁ a₂ b, b ∈ l → R a₁ a₂ → R (f a₁ b) (f a₂ b)) {a₁ a₂ : α} (h : R a₁ a₂) :
    R (l.foldl f a₁) (l.foldl f a₂) := by
  induction l generalizing a₁ a₂ with
  | nil => exact h
  | cons x l ih =>
    exact ih (fun a₁ a₂ b hb ↦ hf a₁ a₂ b (List.mem_cons_of_mem _ hb))
      (hf _ _ _ List.mem_cons_self h)

namespace Work

/-- Bond orders at atom `i`, in half units. -/
def halfSum (w : Work) (i : ℕ) : ℕ := ((w.bondsOf i).map fun k ↦ halfOrder w.bonds[k]!.kind).sum

/-- Explicit valence on the Kekulé graph, through `halfSum`. -/
lemma kekuleValence_eq (w : Work) (i : ℕ) :
    w.kekuleValence i = w.halfSum i / 2 + w.atoms[i]!.explicitHs := by
  simp [Work.kekuleValence, halfSum, foldl_add_eq_sum]

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
  unfold Work.relevantCycles Work.candidateCycles Work.bfs Work.allShortestPaths Work.cycleMask
  rw [h.numAtoms, h.neighbors, h.bondBetween?]

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
  sum : ∀ i : ℕ, w₁.halfSum i = w₂.halfSum i

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
  have hs := h.sum i
  simp only [halfSum, h.bondsOf] at hs
  simp only [Work.explicitValence, Id.run, pure_bind, List.forIn_pure_yield_eq_foldl,
    foldl_add_eq_sum, hs, h.atoms, h.isAromaticAtom, h.bondsOf]

lemma implicitHs : w₁.implicitHs = w₂.implicitHs := by
  funext i
  simp only [Work.implicitHs, h.atoms, h.explicitValence, h.isAromaticAtom]

lemma totalHs : w₁.totalHs = w₂.totalHs := by
  funext i
  simp only [Work.totalHs, h.atoms, h.implicitHs]

lemma kekuleValence : w₁.kekuleValence = w₂.kekuleValence := by
  funext i
  rw [kekuleValence_eq, kekuleValence_eq, h.sum, h.atoms]

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
  sum := by simpa [halfSum, Work.bondsOf, Work.numBonds, hb₁, hb₂] using h.sum

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
  refine foldl_rel _ (fun w₁ w₂ _ _ h ↦ ?_) h
  simp only [h.atoms, h.kekuleValence]
  split
  · exact h
  · exact h.modifyAtom _ _

/-! #### Multiple bonds at an atom -/

/-- Kinds that differ are single and double, so a bond's multiple-bond indicator moves with its
half order. -/
lemma two_mul_add (k : ℕ) (P : ℕ → Bool)
    (hP : w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → P k = true) :
    2 * (if isMultiple w₁.bonds[k]!.kind && P k then 1 else 0) + halfOrder w₂.bonds[k]!.kind =
      2 * (if isMultiple w₂.bonds[k]!.kind && P k then 1 else 0) + halfOrder w₁.bonds[k]!.kind := by
  by_cases hk : w₁.bonds[k]!.kind = w₂.bonds[k]!.kind
  · rw [hk]
  · have hp := hP hk
    obtain ⟨h₁, h₂⟩ := h.kind k hk
    revert hk h₁ h₂
    cases w₁.bonds[k]!.kind <;> cases w₂.bonds[k]!.kind <;> simp [isSD, isMultiple, halfOrder, hp]

/-- The number of multiple bonds at atom `i` that satisfy `P` is the same, when `P` holds on
every bond at `i` whose kind differs. -/
lemma countMultiple (i : ℕ) (P : ℕ → Bool)
    (hP : ∀ k ∈ w₁.bondsOf i, w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → P k = true) :
    ((w₁.bondsOf i).map fun k ↦ if isMultiple w₁.bonds[k]!.kind && P k then 1 else 0).sum =
      ((w₂.bondsOf i).map fun k ↦ if isMultiple w₂.bonds[k]!.kind && P k then 1 else 0).sum := by
  have hs := h.sum i
  simp only [halfSum, ← h.bondsOf] at hs
  have key : ((w₁.bondsOf i).map fun k ↦
        2 * (if isMultiple w₁.bonds[k]!.kind && P k then 1 else 0) + halfOrder w₂.bonds[k]!.kind) =
      (w₁.bondsOf i).map fun k ↦
        2 * (if isMultiple w₂.bonds[k]!.kind && P k then 1 else 0) + halfOrder w₁.bonds[k]!.kind :=
    List.map_congr_left fun k hk ↦ h.two_mul_add k P (hP k hk)
  have e := congrArg List.sum key
  simp only [List.sum_map_add, sum_map_two_mul] at e
  rw [← h.bondsOf]
  omega

end Sim

lemma any_eq_sum_pos {β : Type*} (l : List β) (p : β → Bool) :
    l.any p = decide (0 < (l.map fun k ↦ if p k then 1 else 0).sum) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases hx : p x
    · simp [hx, ih]
    · simp only [hx, List.any_cons, Bool.true_or, List.map_cons, if_true, List.sum_cons]
      simp [Nat.add_comm 1]

lemma length_filter_eq_sum {β : Type*} (l : List β) (p : β → Bool) :
    (l.filter p).length = (l.map fun k ↦ if p k then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih => cases hx : p x <;> simp [hx, ih, Nat.add_comm]

lemma find?_congr {β : Type*} {l : List β} {p q : β → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self,
      ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

namespace Sim

variable {w₁ w₂ : Work} (h : Sim w₁ w₂)
include h

lemma anyMultipleIn (inRing : ℕ → Bool)
    (hr : ∀ k, w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → inRing k = true) (i : ℕ) :
    ((w₁.bondsOf i).any fun k ↦ isMultiple w₁.bonds[k]!.kind && inRing k) =
      ((w₂.bondsOf i).any fun k ↦ isMultiple w₂.bonds[k]!.kind && inRing k) := by
  rw [any_eq_sum_pos, any_eq_sum_pos, h.countMultiple i inRing fun k _ ↦ hr k]

lemma anyMultiple (i : ℕ) :
    ((w₁.bondsOf i).any (isMultiple w₁.bonds[·]!.kind)) =
      ((w₂.bondsOf i).any (isMultiple w₂.bonds[·]!.kind)) := by
  have := h.anyMultipleIn (fun _ ↦ true) (fun _ _ ↦ rfl) i
  simpa using this

lemma numMultiple (i : ℕ) :
    ((w₁.bondsOf i).filter fun k ↦ isMultiple w₁.bonds[k]!.kind).length =
      ((w₂.bondsOf i).filter fun k ↦ isMultiple w₂.bonds[k]!.kind).length := by
  have := h.countMultiple i (fun _ ↦ true) fun _ _ _ ↦ rfl
  simpa [length_filter_eq_sum] using this

lemma exocyclicMultiple? (inRing : ℕ → Bool)
    (hr : ∀ k, w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → inRing k = true) :
    w₁.exocyclicMultiple? inRing = w₂.exocyclicMultiple? inRing := by
  funext i
  simp only [Work.exocyclicMultiple?, h.neighbors]
  congr 1
  refine find?_congr fun ⟨k, j⟩ _ ↦ ?_
  by_cases hk : w₁.bonds[k]!.kind = w₂.bonds[k]!.kind
  · simp [hk]
  · simp [hr k hk]

lemma countAtomElec : w₁.countAtomElec = w₂.countAtomElec := by
  funext i
  simp only [Work.countAtomElec, h.atoms, h.degree, h.cachedTotalHs, h.cachedValence]

lemma donorType (inRing : ℕ → Bool)
    (hr : ∀ k, w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → inRing k = true) :
    w₁.donorType inRing = w₂.donorType inRing := by
  funext i
  simp only [Work.donorType, h.atoms, h.countAtomElec, h.exocyclicMultiple? inRing hr,
    h.anyMultipleIn inRing hr, h.cachedValence, h.degree]

lemma ringDonor (inRing : ℕ → Bool)
    (hr : ∀ k, w₁.bonds[k]!.kind ≠ w₂.bonds[k]!.kind → inRing k = true) :
    w₁.ringDonor inRing = w₂.ringDonor inRing := by
  funext len i
  simp only [Work.ringDonor, h.donorType inRing hr, h.atoms, h.degree, h.anyMultiple]

lemma isAromaticCandidate : w₁.isAromaticCandidate = w₂.isAromaticCandidate := by
  funext i d
  simp only [Work.isAromaticCandidate, h.atoms, h.cachedValence, h.degree, h.numMultiple]

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
    (w.modifyAtom i f).atoms[j]! = if i = j ∧ j < w.atoms.size then f w.atoms[j]! else w.atoms[j]! :=
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

lemma sum_map_filter {β : Type*} (l : List β) (p : β → Bool) (f : β → ℕ) :
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
    simp only [halfSum, ← h.bondsOf, e, e₂, List.sum_map_add, hd]

/-- Rewriting a bond outside `D` the same way on both sides keeps the lockstep. -/
lemma setKind (k : ℕ) (hk : D k = false) (o : BondKind) : RelD D (w₁.setKind k o) (w₂.setKind k o) where
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
  refine foldl_rel _ (fun w₁ w₂ _ _ h ↦ ?_) h
  simp only [h.atoms, h.sim.kekuleValence]
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
  foldl_rel (f := Work.markAromatic) l (fun _ _ b _ h ↦ h.markAromatic b) h

@[simp] lemma size_markAromatic (w : Work) (b : ℕ) : (w.markAromatic b).bonds.size = w.bonds.size := by
  unfold Work.markAromatic
  dsimp only
  split <;> simp [Work.setKind]

/-- After marking the bonds of `l`, bond `k` is aromatic if it is in `l` and was single or double,
and has its old kind otherwise. -/
lemma kind_foldl_markAromatic (w : Work) (l : List ℕ) (k : ℕ) (hk : k < w.bonds.size) :
    ((l.foldl markAromatic w).bonds[k]! : WBond).kind =
      if k ∈ l ∧ isSD (w.bonds[k]! : WBond).kind then .aromatic else (w.bonds[k]! : WBond).kind := by
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

@[simp] lemma bonds_adjustHsAt (w : Work) (i : ℕ) : (w.adjustHsAt i).bonds = w.bonds := by
  simp only [Work.adjustHsAt]
  split_ifs <;> rfl

@[simp] lemma bonds_finalizeHs (w : Work) : w.finalizeHs.bonds = w.bonds := by
  have : ∀ l : List ℕ, ∀ w : Work, (l.foldl adjustHsAt w).bonds = w.bonds := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => intro w; simp [ih]
  simp [Work.finalizeHs, this]

/-- No aromatic atom and no aromatic bond: nothing to kekulize. -/
def NoAromatic (w : Work) : Prop :=
  (∀ k : ℕ, (w.bonds[k]! : WBond).kind ≠ .aromatic) ∧ ∀ i : ℕ, (w.atoms[i]! : WAtom).aromatic = false

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
  ∀ k < w.numBonds, (w.bonds[k]! : WBond).src < w.numAtoms ∧ (w.bonds[k]! : WBond).dst < w.numAtoms ∧
    (w.bonds[k]! : WBond).src ≠ (w.bonds[k]! : WBond).dst

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

end Work

end LeanSMILES.Aromaticity
