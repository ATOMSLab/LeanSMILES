/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Resonance
public import LeanSMILES.Aromaticity.KekuleSim
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# LeanSMILES.Aromaticity.ResonanceProofs

Proofs of properties 1 and 2 of `Molecule.aromatize` stated in
`LeanSMILES.Aromaticity.Resonance`, and the bridge with property 2 discharged.

A Kekulé structure needs no kekulizing (`Work.kekulize_of_noAromatic`), so
`aromatize` is `freezeHs`, `cleanUp`, `cacheValences`, `assignRadicals`,
`setAromaticity` and `finalizeHs`. The working copies of two Kekulé partners
start in lockstep (`relD_ofMolecule`): their half-unit bond-order sums are twice
the molecules' (`halfSum_ofMolecule`). They stay in lockstep through every pass
(`pipeline`). Property 1 reads the aromatic bonds off the result
(`Aromaticity.aromaticBondsKekuleInvariant`). Property 2 compares the results
bond by bond (`Aromaticity.aromatizeMergesExactlyResonance`).

Property 3 is not proved here; see the status in
`LeanSMILES.Aromaticity.Resonance`.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

open Work

variable {n : ℕ}

/-! ### A molecule and its working copy -/

/-- The working copy of a bond. -/
def toWBond (b : Bond n) : WBond := { src := b.src.val, dst := b.dst.val, kind := b.kind }

lemma ofMolecule_bonds (m : Molecule n) :
    (Work.ofMolecule m).bonds = m.bonds.toArray.map toWBond := rfl

lemma ofMolecule_numBonds (m : Molecule n) : (Work.ofMolecule m).numBonds = m.bonds.length := by
  simp [Work.numBonds, ofMolecule_bonds]

lemma ofMolecule_numAtoms (m : Molecule n) : (Work.ofMolecule m).numAtoms = n := by
  simp [Work.numAtoms, Work.ofMolecule]

lemma ofMolecule_bond (m : Molecule n) {k : ℕ} (hk : k < m.bonds.length) :
    (Work.ofMolecule m).bonds[k]! = toWBond m.bonds[k] := by
  rw [getElem!_pos _ k (by simpa [ofMolecule_bonds] using hk)]
  simp [ofMolecule_bonds]

lemma ofMolecule_bond_ge (m : Molecule n) {k : ℕ} (hk : m.bonds.length ≤ k) :
    (Work.ofMolecule m).bonds[k]! = default :=
  getElem!_neg _ k (by simpa [ofMolecule_bonds] using hk)

lemma ofMolecule_atom (m : Molecule n) (i : Fin n) :
    (Work.ofMolecule m).atoms[i.val]! =
      { z := (m.atom i).atomicNumber, aromatic := (m.atom i).aromatic,
        charge := (m.atom i).charge, explicitHs := (m.atom i).explicitH.getD 0,
        noImplicit := (m.atom i).explicitH.isSome || (m.atom i).element.isNone } := by
  rw [getElem!_pos _ i.val (by simp [Work.ofMolecule])]
  simp [Work.ofMolecule]

lemma ofMolecule_wf (m : Molecule n) : WF (Work.ofMolecule m) := by
  intro k hk
  rw [ofMolecule_numBonds] at hk
  rw [ofMolecule_bond m hk, ofMolecule_numAtoms]
  exact ⟨m.bonds[k].src.isLt, m.bonds[k].dst.isLt, fun h ↦ m.bonds[k].ne (Fin.ext h)⟩

lemma halfOrder_eq (k : BondKind) : (halfOrder k : ℚ) = 2 * k.order := by
  cases k <;> simp [halfOrder, BondKind.order] <;> norm_num

lemma val_beq_val (x y : Fin n) : ((x : ℕ) == (y : ℕ)) = (x == y) := by
  cases h : x == y
  · simpa [Fin.val_inj] using h
  · simpa [Fin.val_inj] using h

lemma toWBond_touches (b : Bond n) (i : Fin n) : (toWBond b).touches i.val = b.touches i := by
  simp only [toWBond, WBond.touches, Bond.touches, val_beq_val]

/-- A sum over the bond indices of the working copy is a sum over the bonds. -/
lemma sum_range_bonds {M : Type*} [AddMonoid M] (m : Molecule n) (g : WBond → M) :
    ((List.range (Work.ofMolecule m).numBonds).map fun k ↦ g (Work.ofMolecule m).bonds[k]!).sum =
      (m.bonds.map fun b ↦ g (toWBond b)).sum := by
  congr 1
  apply List.ext_getElem
  · simp [ofMolecule_numBonds]
  · intro k h₁ h₂
    simp only [List.getElem_map, List.getElem_range]
    rw [ofMolecule_bond m (by simpa using h₂)]

/-- The half-unit bond orders at an atom of the working copy add up to twice its bond-order sum. -/
lemma halfSum_ofMolecule (m : Molecule n) (i : Fin n) :
    ((Work.ofMolecule m).halfSum i.val : ℚ) = 2 * m.bondOrderSum i := by
  have h := sum_range_bonds m fun b ↦ if b.touches i.val then halfOrder b.kind else 0
  simp only [Work.halfSum, Work.bondsOf, sum_map_filter] at h ⊢
  rw [h, Molecule.bondOrderSum, Molecule.bondsAt, sum_map_filter, Nat.cast_list_sum,
    List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun b _ ↦ ?_
  simp only [Function.comp_apply, toWBond_touches]
  split <;> simp [halfOrder_eq, toWBond]

lemma noAromatic_ofMolecule (m : Molecule n) (hk : m.IsKekule) :
    NoAromatic (Work.ofMolecule m) := by
  refine ⟨fun k ↦ ?_, fun i ↦ ?_⟩
  · by_cases hlt : k < m.bonds.length
    · rw [ofMolecule_bond m hlt]
      exact hk.2 _ (List.getElem_mem hlt)
    · rw [ofMolecule_bond_ge m (by omega)]
      decide
  · by_cases hlt : i < n
    · rw [ofMolecule_atom m ⟨i, hlt⟩]
      exact hk.1 _
    · rw [getElem!_neg _ i (by simpa [Work.ofMolecule] using hlt)]
      rfl

lemma even_halfSum {w : Work} (h : NoAromatic w) (i : ℕ) : 2 ∣ w.halfSum i := by
  refine List.dvd_sum fun x hx ↦ ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  have := h.1 k
  revert this
  cases (w.bonds[k]! : WBond).kind <;> simp [halfOrder]

/-- What `cleanUp` rewrites in the working copy of a Kekulé structure is `CleanUpTarget`. -/
lemma cleanUpTarget_of_center (m : Molecule n) (hk : m.IsKekule) (i : Fin n)
    (h : (Work.ofMolecule m).cleanUpCenter i.val = true) : m.CleanUpTarget i := by
  have hn := noAromatic_ofMolecule m hk
  have hev := explicitValence_of_not_aromatic _ i.val (hn.isAromaticAtom i.val)
  have hs := halfSum_ofMolecule m i
  obtain ⟨t, ht⟩ := even_halfSum hn i.val
  rw [ofMolecule_atom] at hev
  simp only at hev
  have hv : ((Work.ofMolecule m).explicitValence i.val : ℚ) =
      m.bondOrderSum i + ((m.atom i).explicitH.getD 0 : ℚ) := by
    rw [hev, ht]
    rw [ht] at hs
    have : (2 * (m.atom i).explicitH.getD 0 + 2 * t + 1) / 2 = (m.atom i).explicitH.getD 0 + t := by
      omega
    rw [this]
    push_cast at hs ⊢
    linarith
  simp only [Work.cleanUpCenter, ofMolecule_atom, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    List.contains_cons, List.contains_nil, Bool.or_false] at h
  obtain ⟨hch, h⟩ := h
  refine ⟨hch, ?_⟩
  rcases h with ⟨hz, he⟩ | ⟨hz, he⟩
  · refine Or.inl ⟨hz, ?_⟩
    rw [← hv, he]
    norm_num
  · refine Or.inr ⟨or_assoc.mp hz, ?_⟩
    rw [← hv]
    rcases he with he | he | he <;> rw [he] <;> norm_num

/-! ### Kekulé partners in lockstep -/

namespace KP

variable {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂)
include h

lemma atoms : m₁.atoms = m₂.atoms := by
  simp only [Molecule.KekulePartner, Molecule.kekuleData, Prod.mk.injEq] at h
  exact h.1

lemma map_forget : m₁.bonds.map Bond.forgetDouble = m₂.bonds.map Bond.forgetDouble := by
  simp only [Molecule.KekulePartner, Molecule.kekuleData, Prod.mk.injEq] at h
  exact h.2.1

lemma length : m₁.bonds.length = m₂.bonds.length := by
  simpa using congrArg List.length (map_forget h)

lemma forget (k : ℕ) (h₁ : k < m₁.bonds.length) :
    m₁.bonds[k].forgetDouble = (m₂.bonds[k]'(length h ▸ h₁)).forgetDouble := by
  have := congrArg (·[k]?) (map_forget h)
  simpa [h₁, (length h ▸ h₁ : k < m₂.bonds.length)] using this

lemma bondOrderSum (i : Fin n) : m₁.bondOrderSum i = m₂.bondOrderSum i := by
  simp only [Molecule.KekulePartner, Molecule.kekuleData, Prod.mk.injEq] at h
  simpa using congrArg (·[i]) h.2.2

lemma src (k : ℕ) (h₁ : k < m₁.bonds.length) :
    m₁.bonds[k].src = (m₂.bonds[k]'(length h ▸ h₁)).src := by
  simpa [Bond.forgetDouble] using congrArg Bond.src (forget h k h₁)

lemma dst (k : ℕ) (h₁ : k < m₁.bonds.length) :
    m₁.bonds[k].dst = (m₂.bonds[k]'(length h ▸ h₁)).dst := by
  simpa [Bond.forgetDouble] using congrArg Bond.dst (forget h k h₁)

lemma with_kind (k : ℕ) (h₁ : k < m₁.bonds.length) (o : BondKind) :
    { m₁.bonds[k] with kind := o } = { m₂.bonds[k]'(length h ▸ h₁) with kind := o } := by
  calc { m₁.bonds[k] with kind := o } = { m₁.bonds[k].forgetDouble with kind := o } := rfl
    _ = { (m₂.bonds[k]'(length h ▸ h₁)).forgetDouble with kind := o } := by rw [forget h k h₁]
    _ = { m₂.bonds[k]'(length h ▸ h₁) with kind := o } := rfl

lemma kind_forget (k : ℕ) (h₁ : k < m₁.bonds.length) :
    m₁.bonds[k].kind.forgetDouble = (m₂.bonds[k]'(length h ▸ h₁)).kind.forgetDouble := by
  simpa [Bond.forgetDouble] using congrArg Bond.kind (forget h k h₁)

end KP

lemma isSD_of_forget {a b : BondKind} (h : a.forgetDouble = b.forgetDouble) (hab : a ≠ b) :
    isSD a = true ∧ isSD b = true ∧ a ≠ b := by
  revert h hab
  cases a <;> cases b <;> simp [BondKind.forgetDouble, isSD]

/-- The bonds where two molecules' working copies differ in kind. -/
def movedD (m₁ m₂ : Molecule n) (k : ℕ) : Bool :=
  (Work.ofMolecule m₁).bonds[k]!.kind != (Work.ofMolecule m₂).bonds[k]!.kind

lemma movedD_lt {m₁ m₂ : Molecule n} (hp : m₁.KekulePartner m₂) {k : ℕ}
    (hk : movedD m₁ m₂ k = true) : k < m₁.bonds.length := by
  by_contra hlt
  rw [movedD, ofMolecule_bond_ge m₁ (by omega),
    ofMolecule_bond_ge m₂ (by rw [← KP.length hp]; omega)] at hk
  simp at hk

lemma relD_ofMolecule {m₁ m₂ : Molecule n} (hp : m₁.KekulePartner m₂) :
    RelD (movedD m₁ m₂) (Work.ofMolecule m₁) (Work.ofMolecule m₂) := by
  have hsk : SameSkel (Work.ofMolecule m₁) (Work.ofMolecule m₂) := by
    refine ⟨by simp [ofMolecule_numAtoms], by simp [ofMolecule_numBonds, KP.length hp],
      fun k ↦ ?_, fun k ↦ ?_⟩ <;>
    · by_cases hlt : k < m₁.bonds.length
      · rw [ofMolecule_bond m₁ hlt, ofMolecule_bond m₂ (KP.length hp ▸ hlt)]
        simp [toWBond, KP.src hp k hlt, KP.dst hp k hlt]
      · rw [ofMolecule_bond_ge m₁ (by omega), ofMolecule_bond_ge m₂ (by rw [← KP.length hp]; omega)]
  refine RelD.of_halfSum hsk ?_ (fun k hk ↦ by simpa [movedD] using hk) (fun k hk ↦ ?_) (fun i ↦ ?_)
  · simp only [Work.ofMolecule, Molecule.atom, KP.atoms hp]
  · have hlt := movedD_lt hp hk
    simp only [movedD, bne_iff_ne, ne_eq] at hk
    rw [ofMolecule_bond m₁ hlt, ofMolecule_bond m₂ (KP.length hp ▸ hlt)] at hk ⊢
    exact isSD_of_forget (KP.kind_forget hp k hlt) hk
  · by_cases hi : i < n
    · have h₁ := halfSum_ofMolecule m₁ ⟨i, hi⟩
      have h₂ := halfSum_ofMolecule m₂ ⟨i, hi⟩
      rw [KP.bondOrderSum hp, ← h₂] at h₁
      exact_mod_cast h₁
    · have h₁ : (Work.ofMolecule m₁).numAtoms ≤ i := by rw [ofMolecule_numAtoms]; omega
      have h₂ : (Work.ofMolecule m₂).numAtoms ≤ i := by rw [ofMolecule_numAtoms]; omega
      rw [Work.halfSum, Work.halfSum, bondsOf_eq_nil (ofMolecule_wf m₁) h₁,
        bondsOf_eq_nil (ofMolecule_wf m₂) h₂]
      rfl

/-- The hypothesis on molecules, as the working copies need it. -/
lemma avoidsCenters {m₁ m₂ : Molecule n} (hk : m₁.IsKekule) (hp : m₁.KekulePartner m₂)
    (hc : m₁.MovesAvoidCleanUp m₂) :
    AvoidsCenters (movedD m₁ m₂) (Work.ofMolecule m₁).freezeHs := by
  intro c hcen k hD
  rw [cleanUpCenter_freezeHs] at hcen
  have hlt := movedD_lt hp hD
  have hlt₂ : k < m₂.bonds.length := KP.length hp ▸ hlt
  rw [bonds_freezeHs, ofMolecule_bond m₁ hlt]
  have hmem : (m₁.bonds[k], m₂.bonds[k]) ∈ m₁.bonds.zip m₂.bonds := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simp [hlt, hlt₂], by simp⟩
  have hne : m₁.bonds[k].kind ≠ m₂.bonds[k].kind := by
    simpa [movedD, ofMolecule_bond m₁ hlt, ofMolecule_bond m₂ hlt₂, toWBond] using hD
  obtain ⟨hs, hd⟩ := hc _ hmem hne
  by_contra htc
  simp only [Bool.not_eq_false, toWBond, WBond.touches, Bool.or_eq_true, beq_iff_eq] at htc
  rcases htc with e | e
  · exact hs (cleanUpTarget_of_center m₁ hk _ (e ▸ hcen))
  · exact hd (cleanUpTarget_of_center m₁ hk _ (e ▸ hcen))

/-! ### Through `aromatize` -/

/-- The working copy `aromatize` kekulizes: after `freezeHs`, `cleanUp` and `cacheValences`. -/
def prep (m : Molecule n) : Work := (Work.ofMolecule m).freezeHs.cleanUp.cacheValences

lemma aromatize_eq_of_noAromatic (m : Molecule n) (h : NoAromatic (prep m)) :
    m.aromatize =
      .ok (writeBack m
        ((prep m).assignRadicals.setAromaticity (prep m).relevantCycles).finalizeHs) := by
  unfold Molecule.aromatize
  unfold prep at h
  dsimp only
  rw [kekulize_of_noAromatic _ h]
  rfl

lemma Work.RelD.noAromatic {D : ℕ → Bool} {w₁ w₂ : Work} (h : RelD D w₁ w₂) (hn : NoAromatic w₁) :
    NoAromatic w₂ := by
  refine ⟨fun k hk ↦ ?_, fun i ↦ by rw [← h.atoms]; exact hn.2 i⟩
  have := h.sim.kind_aromatic k
  rw [hk] at this
  simp only [beq_self_eq_true, beq_iff_eq] at this
  exact hn.1 k this

/-- Kekulé partners whose moved bonds avoid `cleanUp`'s atoms run through `aromatize` in lockstep
up to the marking of aromatic bonds. -/
structure Pipeline (m₁ m₂ : Molecule n) (w₁ w₂ : Work) (rings : Array (List ℕ)) : Prop where
  rel : RelD (movedD m₁ m₂) w₁ w₂
  noArom : NoAromatic w₁
  wf : WF w₁
  size : w₁.bonds.size = m₁.bonds.length
  arom₁ : m₁.aromatize = .ok (writeBack m₁ (w₁.setAromaticity rings).finalizeHs)
  arom₂ : m₂.aromatize = .ok (writeBack m₂ (w₂.setAromaticity rings).finalizeHs)

lemma pipeline {m₁ m₂ : Molecule n} (hk : m₁.IsKekule) (hp : m₁.KekulePartner m₂)
    (hc : m₁.MovesAvoidCleanUp m₂) :
    Pipeline m₁ m₂ (prep m₁).assignRadicals (prep m₂).assignRadicals (prep m₁).relevantCycles := by
  have h0 := relD_ofMolecule hp
  have hwf0 : WF (Work.ofMolecule m₁).freezeHs := (skel_freezeHs _).wf (ofMolecule_wf m₁)
  have inv : CleanInv (movedD m₁ m₂) (Work.ofMolecule m₁).freezeHs (Work.ofMolecule m₁).freezeHs
      (Work.ofMolecule m₂).freezeHs :=
    ⟨h0.freezeHs, avoidsCenters hk hp hc, (noAromatic_ofMolecule m₁ hk).freezeHs, SameSkel.refl _⟩
  have inv2 := inv.cleanUp hwf0
  have h3 : RelD (movedD m₁ m₂) (prep m₁) (prep m₂) := inv2.rel.cacheValences
  have hn1 : NoAromatic (prep m₁) := inv2.noArom.cacheValences
  have hn2 : NoAromatic (prep m₂) := h3.noAromatic hn1
  have hsk : SameSkel (Work.ofMolecule m₁) (prep m₁).assignRadicals :=
    (((skel_freezeHs _).trans inv2.skel).trans (skel_cacheValences _)).trans
      (skel_assignRadicals _)
  refine ⟨h3.assignRadicals, hn1.assignRadicals, hsk.wf (ofMolecule_wf m₁), ?_,
    aromatize_eq_of_noAromatic m₁ hn1, ?_⟩
  · have := hsk.numBonds
    simp only [Work.numBonds, ofMolecule_bonds, Array.size_map, List.size_toArray] at this
    exact this.symm
  · rw [aromatize_eq_of_noAromatic m₂ hn2, h3.toSameSkel.relevantCycles]

lemma length_withKinds (m : Molecule n) (w : Work) : (withKinds m w).length = m.bonds.length := by
  simp [withKinds]

lemma getElem_withKinds (m : Molecule n) (w : Work) {k : ℕ} {hk : k < (withKinds m w).length}
    (hw : k < w.bonds.size) :
    (withKinds m w)[k]'hk =
      { m.bonds[k]'(by simpa [length_withKinds] using hk) with
        kind := (w.bonds[k]! : WBond).kind } := by
  simp [withKinds, hw]

lemma aromaticBonds_writeBack (m : Molecule n) (w : Work) (hw : w.bonds.size = m.bonds.length) :
    (writeBack m w).aromaticBonds =
      (List.range m.bonds.length).map fun k ↦ (w.bonds[k]! : WBond).kind == .aromatic := by
  apply List.ext_getElem
  · simp [Molecule.aromaticBonds, writeBack, length_withKinds]
  · intro k h₁ h₂
    have hk : k < m.bonds.length := by simpa using h₂
    simp only [Molecule.aromaticBonds, writeBack, List.getElem_map, List.getElem_range]
    rw [getElem_withKinds m w (by omega)]

lemma size_foldl_markAromatic (w : Work) (L : List ℕ) :
    (L.foldl markAromatic w).bonds.size = w.bonds.size := by
  induction L generalizing w with
  | nil => rfl
  | cons b L ih => rw [List.foldl_cons, ih, size_markAromatic]

lemma size_final (w : Work) (L : List ℕ) :
    (L.foldl markAromatic w).finalizeHs.bonds.size = w.bonds.size := by
  rw [bonds_finalizeHs]
  induction L generalizing w with
  | nil => rfl
  | cons b L ih => rw [List.foldl_cons, ih, size_markAromatic]

/-- The kind of bond `k` once the bonds of `L` are marked and hydrogens finalized. -/
lemma kind_final (w : Work) (L : List ℕ) (k : ℕ) (hk : k < w.bonds.size) :
    ((L.foldl markAromatic w).finalizeHs.bonds[k]! : WBond).kind =
      if k ∈ L ∧ isSD (w.bonds[k]! : WBond).kind then .aromatic
      else (w.bonds[k]! : WBond).kind := by
  rw [bonds_finalizeHs, kind_foldl_markAromatic w L k hk]

lemma wbond_ext {a b : WBond} (h₁ : a.src = b.src) (h₂ : a.dst = b.dst) (h₃ : a.kind = b.kind) :
    a = b := by
  cases a
  cases b
  simp_all

lemma work_ext {w w' : Work} (ha : w.atoms = w'.atoms) (hs : w.bonds.size = w'.bonds.size)
    (hb : ∀ k < w.bonds.size, w.bonds[k]! = w'.bonds[k]!) : w = w' := by
  cases w
  cases w'
  simp only [Work.mk.injEq]
  refine ⟨ha, Array.ext hs fun k h₁ h₂ ↦ ?_⟩
  have := hb k h₁
  rwa [getElem!_pos _ k h₁, getElem!_pos _ k h₂] at this

/-- `differOnlyOn`, bond by bond. -/
lemma differOnlyOn_iff {m₁ m₂ : Molecule n} (mask : List Bool)
    (hl : m₁.bonds.length = m₂.bonds.length) (hm : mask.length = m₁.bonds.length) :
    m₁.differOnlyOn m₂ mask = true ↔ ∀ k (h : k < m₁.bonds.length),
      m₁.bonds[k].kind = (m₂.bonds[k]'(hl ▸ h)).kind ∨ mask[k]'(hm ▸ h) = true := by
  unfold Molecule.differOnlyOn
  rw [List.all_eq_true]
  constructor
  · intro H k h
    have hmem : ((m₁.bonds[k], m₂.bonds[k]'(hl ▸ h)), mask[k]'(hm ▸ h)) ∈
        (m₁.bonds.zip m₂.bonds).zip mask :=
      List.mem_iff_getElem.mpr ⟨k, by simp [h, ← hl, hm], by simp⟩
    simpa using H _ hmem
  · intro H x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_zip] at hk
    have hk₁ : k < m₁.bonds.length := by omega
    simpa using H k hk₁

/-- Partners write back one working copy to one molecule. -/
lemma writeBack_partner {m₁ m₂ : Molecule n} (hp : m₁.KekulePartner m₂) (w : Work)
    (hw : w.bonds.size = m₁.bonds.length) : writeBack m₁ w = writeBack m₂ w := by
  refine Molecule.ext ?_ ?_
  · simp only [writeBack, Molecule.atom, KP.atoms hp]
  · apply List.ext_getElem
    · simp [writeBack, length_withKinds, KP.length hp]
    · intro k h₁ h₂
      have hk : k < m₁.bonds.length := by simpa [writeBack, length_withKinds] using h₁
      simp only [writeBack]
      rw [getElem_withKinds m₁ w (by omega), getElem_withKinds m₂ w (by omega)]
      exact KP.with_kind hp k hk _

/-! ### Properties 1 and 2 -/

/-- **Property 1.** Kekulé partners whose moved bonds avoid the atoms `cleanUp` rewrites get the
same aromatic bonds. -/
theorem aromaticBondsKekuleInvariant : AromaticBondsKekuleInvariant := by
  intro n m₁ m₂ hk hp hc
  have P := pipeline hk hp hc
  set rings := (prep m₁).relevantCycles
  set w₁ := (prep m₁).assignRadicals
  set w₂ := (prep m₂).assignRadicals
  have hL := P.rel.aromaticBondList P.wf rings
  have hsize₂ : w₂.bonds.size = m₂.bonds.length := by
    have := P.rel.numBonds
    simp only [Work.numBonds] at this
    rw [← this, P.size, KP.length hp]
  rw [P.arom₁, P.arom₂]
  simp only [Except.map, Except.toOption, Option.some.injEq, Work.setAromaticity, ← hL]
  rw [aromaticBonds_writeBack _ _ (by rw [size_final, P.size]),
    aromaticBonds_writeBack _ _ (by rw [size_final, hsize₂]), ← KP.length hp]
  refine List.map_congr_left fun k hk' ↦ ?_
  have hk₁ : k < w₁.bonds.size := by rw [P.size]; exact List.mem_range.mp hk'
  have hk₂ : k < w₂.bonds.size := by rw [hsize₂, ← KP.length hp]; exact List.mem_range.mp hk'
  rw [kind_final w₁ _ k hk₁, kind_final w₂ _ k hk₂, P.rel.sim.markRel.isSD k]
  have n₁ := P.noArom.1 k
  have n₂ := (P.rel.noAromatic P.noArom).1 k
  split <;> simp [n₁, n₂]

/-- **Property 2.** Kekulé partners whose moved bonds avoid the atoms `cleanUp` rewrites aromatize
to one molecule exactly when they differ only on bonds the model makes aromatic. -/
theorem aromatizeMergesExactlyResonance : AromatizeMergesExactlyResonance := by
  intro n m₁ m₂ a hk hp hc ha
  have P := pipeline hk hp hc
  set rings := (prep m₁).relevantCycles
  set w₁ := (prep m₁).assignRadicals
  set w₂ := (prep m₂).assignRadicals
  have hL := P.rel.aromaticBondList P.wf rings
  set L := w₁.aromaticBondList rings
  have hlen := KP.length hp
  have hsize₂ : w₂.bonds.size = m₂.bonds.length := by
    have := P.rel.numBonds
    simp only [Work.numBonds] at this
    rw [← this, P.size, hlen]
  set F₁ := (L.foldl markAromatic w₁).finalizeHs
  set F₂ := (L.foldl markAromatic w₂).finalizeHs
  have e₂ : m₂.aromatize = .ok (writeBack m₂ F₂) := by
    rw [P.arom₂]
    simp only [Work.setAromaticity, ← hL, F₂]
  have e₁ : m₁.aromatize = .ok (writeBack m₁ F₁) := P.arom₁
  rw [e₁] at ha
  cases ha
  rw [e₂]
  have hF₁ : F₁.bonds.size = m₁.bonds.length := by rw [size_final, P.size]
  have hF₂ : F₂.bonds.size = m₁.bonds.length := by rw [size_final, hsize₂, hlen]
  -- bond by bond
  have hK : ∀ k < m₁.bonds.length, ((F₁.bonds[k]! : WBond).kind = (F₂.bonds[k]! : WBond).kind ↔
      (movedD m₁ m₂ k = true → k ∈ L)) := by
    intro k hk'
    rw [kind_final w₁ L k (by rw [P.size]; exact hk'),
      kind_final w₂ L k (by rw [hsize₂, ← hlen]; exact hk')]
    cases hD : movedD m₁ m₂ k
    · rw [P.rel.off k hD]
      simp
    · obtain ⟨h₁, h₂, hne⟩ := P.rel.on k hD
      by_cases hkL : k ∈ L <;> simp [hkL, h₁, h₂, hne]
  have hmask : ∀ k (h : k < m₁.bonds.length),
      ((writeBack m₁ F₁).aromaticBonds[k]'(by
        rw [aromaticBonds_writeBack _ _ hF₁]; simpa using h) = true ↔
        k ∈ L ∧ isSD (w₁.bonds[k]! : WBond).kind = true) := by
    intro k hk'
    simp only [aromaticBonds_writeBack _ _ hF₁, List.getElem_map, List.getElem_range]
    rw [kind_final w₁ L k (by rw [P.size]; exact hk')]
    have := P.noArom.1 k
    split <;> simp_all
  have hD : ∀ k (h : k < m₁.bonds.length),
      movedD m₁ m₂ k = true ↔ m₁.bonds[k].kind ≠ (m₂.bonds[k]'(hlen ▸ h)).kind := by
    intro k hk'
    simp [movedD, ofMolecule_bond m₁ hk', ofMolecule_bond m₂ (hlen ▸ hk'), toWBond]
  rw [differOnlyOn_iff _ hlen (by simp [aromaticBonds_writeBack _ _ hF₁])]
  constructor
  · intro heq k hk'
    have hb := congrArg Molecule.bonds (Except.ok.inj heq)
    simp only [writeBack] at hb
    have hkk := congrArg (fun l ↦ (l[k]? ).map Bond.kind) hb
    simp only [List.getElem?_eq_getElem (by simpa [length_withKinds, hlen] using hk' :
        k < (withKinds m₂ F₂).length),
      List.getElem?_eq_getElem
        (by simpa [length_withKinds] using hk' : k < (withKinds m₁ F₁).length),
      Option.map_some, Option.some.injEq] at hkk
    rw [getElem_withKinds _ _ (by rw [hF₂]; exact hk'),
      getElem_withKinds _ _ (by rw [hF₁]; exact hk')] at hkk
    by_cases hkind : m₁.bonds[k].kind = (m₂.bonds[k]'(hlen ▸ hk')).kind
    · exact Or.inl hkind
    · right
      have hDk := (hD k hk').mpr hkind
      exact (hmask k hk').mpr ⟨(hK k hk').mp hkk.symm hDk, (P.rel.on k hDk).1⟩
  · intro H
    have hFF : F₁ = F₂ := by
      have hfold : L.foldl markAromatic w₁ = L.foldl markAromatic w₂ := by
        have hm := P.rel.sim.markRel.foldl_markAromatic L
        refine work_ext hm.atoms ?_ fun k hk' ↦ wbond_ext (hm.src k) (hm.dst k) ?_
        · have := hm.numBonds
          simpa [Work.numBonds] using this
        · have hk'' : k < m₁.bonds.length := by
            rw [size_foldl_markAromatic, P.size] at hk'
            exact hk'
          have := (hK k hk'').mpr fun hDk ↦ ?_
          · simpa [F₁, F₂, bonds_finalizeHs] using this
          · rcases H k hk'' with h | h
            · exact absurd h ((hD k hk'').mp hDk)
            · exact ((hmask k hk'').mp h).1
      simp only [F₁, F₂, hfold]
    rw [← hFF, writeBack_partner hp F₁ hF₁]

end LeanSMILES.Aromaticity

namespace LeanSMILES.Molecule

open Aromaticity

variable {n : ℕ}

/-! ### The bridge, with property 2 proved -/

/-- Resonance structures have one aromatic canonical SMILES. -/
theorem aromaticCanonicalSmiles_eq_of_resonance {m₁ m₂ : Molecule n} (hk : m₁.IsKekule)
    (hr : m₁.ResonanceStructure m₂) :
    m₂.aromaticCanonicalSmiles = m₁.aromaticCanonicalSmiles :=
  aromaticCanonicalSmiles_eq_of_resonanceStructure aromatizeMergesExactlyResonance hk hr

/-- Any two Kekulé structures related by resonance moves, in any order and either direction, have
one aromatic canonical SMILES. -/
theorem aromaticCanonicalSmiles_eq_of_eqvGen_resonance {m₁ m₂ : Molecule n} (hk : m₁.IsKekule)
    (h : Relation.EqvGen ResonanceStructure m₁ m₂) :
    m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles := by
  suffices H : (m₁.IsKekule ↔ m₂.IsKekule) ∧
      (m₁.IsKekule → m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles) from H.2 hk
  clear hk
  induction h with
  | rel x y hr =>
    exact ⟨⟨hr.1.isKekule, (kekulePartner_equivalence.symm hr.1).isKekule⟩,
      fun hx ↦ (aromaticCanonicalSmiles_eq_of_resonance hx hr).symm⟩
  | refl x => exact ⟨Iff.rfl, fun _ ↦ rfl⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy ↦ (ih.2 (ih.1.mpr hy)).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
    exact ⟨ih₁.1.trans ih₂.1, fun hx ↦ (ih₁.2 hx).trans (ih₂.2 (ih₁.1.mp hx))⟩

/-- **The bridge**, with property 2 discharged: given property 3, any two Kekulé structures
related by renumbering and resonance moves have one aromatic canonical SMILES, as long as the atoms
`cleanUp` rewrites are apart. -/
theorem aromaticCanonicalSmiles_eq_of_eqvGen' (h₃ : AromatizeRelabelKekule) {m₁ m₂ : Molecule n}
    (hk : m₁.IsKekule) (ha : m₁.CleanUpTargetsApart) (h : Relation.EqvGen Redraw m₁ m₂) :
    m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles :=
  aromaticCanonicalSmiles_eq_of_eqvGen aromatizeMergesExactlyResonance h₃ hk ha h

end LeanSMILES.Molecule
