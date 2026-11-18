/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeCompose
public import LeanSMILES.Aromaticity.HsLocal

/-!
# LeanSMILES.Aromaticity.KekulizeAtoms

**What kekulization does to an atom** (`Work.kekulize_atom`): it clears the aromatic flag, and
nothing else, except at an aromatic neutral nitrogen or phosphorus with one written hydrogen
(`[nH]`, `[pH]`), which it rewrites into a bare atom whose cached valence is its Kekulé bond-order
sum and whose cached implicit hydrogens are counted on the Kekulé bonds (`Work.branchRec`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- The record `clearAromatic` gives an aromatic `[nH]` or `[pH]` with record `a`, bond half-order
sum `h` and aromatic bonds or not (`arom`). -/
def branchRec (a : WAtom) (h : ℕ) (arom : Bool) : WAtom :=
  let a1 : WAtom :=
    { a with aromatic := false, noImplicit := false, explicitHs := 0,
             cachedValence := some (h / 2) }
  { a1 with cachedImplicit := Loc.impl a1 h arom }

/-- The `[nH]`/`[pH]` case of `clearAromatic`. -/
def IsBranch (a : WAtom) : Prop :=
  a.aromatic = true ∧ (a.z = 7 ∨ a.z = 15) ∧ a.charge = 0 ∧ a.explicitHs = 1

/-- What atom `i` of `w` may be while `clearAromatic` runs over the atoms of a copy with record
`a0` there and bonds `bs`. -/
def ClearOk (a0 : WAtom) (bs : Array WBond) (w : Work) (i : ℕ) : Prop :=
  w.bonds = bs ∧ ((w.atoms[i]! : WAtom) = a0 ∨
    (w.atoms[i]! : WAtom) = { a0 with aromatic := false } ∨
    (IsBranch a0 ∧ (w.atoms[i]! : WAtom) =
      branchRec a0 (({ atoms := #[], bonds := bs } : Work).bondHalfSum i)
        ((({ atoms := #[], bonds := bs } : Work).kindsAt i).any (· == .aromatic))))

lemma clearAromatic_clearOk {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} {w w' : Work} {j : ℕ}
    (hw : clearAromatic ra w j = .ok w') (i : ℕ) (h : ClearOk a0 bs w i) : ClearOk a0 bs w' i := by
  obtain ⟨hb, ha⟩ := h
  have hbh : ∀ x : Work, x.bonds = bs → x.bondHalfSum i =
      ({ atoms := #[], bonds := bs } : Work).bondHalfSum i := fun x hx ↦ by
    simp only [bondHalfSum, bondsOf, numBonds, hx]
  have hka : ∀ x : Work, x.bonds = bs → x.kindsAt i =
      ({ atoms := #[], bonds := bs } : Work).kindsAt i := fun x hx ↦ by
    simp only [kindsAt, bondsOf, numBonds, hx]
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · cases hw; exact ⟨hb, ha⟩
  split at hw
  · cases hw
  split at hw
  · rename_i hnar _ hbr
    cases hw
    refine ⟨hb, ?_⟩
    by_cases hji : j = i
    · subst hji
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hnar
      by_cases hjs : j < w.atoms.size
      · -- the rewrite happens here: the atom was `a0` (the others are not aromatic)
        have ha0 : (w.atoms[j]! : WAtom) = a0 := by
          rcases ha with h | h | ⟨-, h⟩
          · exact h
          · rw [h] at hnar; cases hnar
          · rw [h] at hnar; cases hnar
        rw [modifyAtom_atom_self, if_pos (by simpa [modifyAtom] using hjs)]
        right; right
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_cons,
          List.not_mem_nil, or_false] at hbr
        refine ⟨⟨by rw [← ha0]; exact hnar, by rw [← ha0]; omega, by rw [← ha0]; exact hbr.1.2,
          by rw [← ha0]; exact hbr.2⟩, ?_⟩
        rw [modifyAtom_atom_self, if_pos hjs, ha0, implicitHs_eq_loc, modifyAtom_atom_self,
          if_pos hjs, ha0]
        unfold branchRec
        rw [foldl_halfOrder, Nat.zero_add, ← bondHalfSum, hbh w hb, hbh _ (by simp),
          isAromaticAtom_eq_loc, modifyAtom_atom_self, if_pos hjs, hka _ (by simp [hb])]
        simp [bondHalfSum, bondsOf, numBonds, hb]
      · rw [modifyAtom_atom_self, if_neg (by simpa [modifyAtom] using hjs), modifyAtom_atom_self,
          if_neg hjs]
        refine ha.imp id (Or.imp id fun h ↦ ⟨h.1, ?_⟩)
        exact h.2
    · rw [modifyAtom_atom_of_ne _ hji, modifyAtom_atom_of_ne _ hji]
      refine ha.imp id (Or.imp id fun h ↦ ⟨h.1, ?_⟩)
      exact h.2
  · cases hw
    refine ⟨hb, ?_⟩
    by_cases hji : j = i
    · subst hji
      rename_i hnar _ _
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hnar
      rw [modifyAtom_atom_self]
      split
      · rcases ha with h | h | ⟨-, h⟩
        · right; left; rw [h]
        · right; left; rw [h]
        · rw [h] at hnar; cases hnar
      · exact ha
    · rw [modifyAtom_atom_of_ne _ hji]
      exact ha

lemma foldlM_clearAromatic_clearOk {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} (i : ℕ) :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ra) w = .ok w' →
      ClearOk a0 bs w i → ClearOk a0 bs w' i
  | [], w, w', hw, h => by cases hw; exact h
  | x :: l, w, w', hw, h => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ra w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      exact foldlM_clearAromatic_clearOk i l v w' hw (clearAromatic_clearOk hx i h)

/-- **What kekulization does to an atom**: clears its aromatic flag, or rewrites an aromatic
`[nH]`/`[pH]` into a bare atom (`branchRec`, over the Kekulé bonds). -/
theorem kekulize_atom {m K : Work} {rings : Array (List ℕ)} (hK : m.kekulize rings = .ok K)
    (i : ℕ) :
    (K.atoms[i]! : WAtom) = { (m.atoms[i]! : WAtom) with aromatic := false } ∨
      (IsBranch m.atoms[i]! ∧
        (K.atoms[i]! : WAtom) = branchRec m.atoms[i]! (K.bondHalfSum i)
          ((K.kindsAt i).any (· == .aromatic))) := by
  have hna := kekulize_noArom hK
  have hfl : (K.atoms[i]! : WAtom).aromatic = false := by
    by_cases hi : i < K.atoms.size
    · rw [getElem!_pos K.atoms i hi]
      exact hna.1 _ (Array.getElem_mem hi)
    · rw [getElem!_neg K.atoms i hi]; rfl
  have hfin : ClearOk m.atoms[i]! K.bonds K i := by
    unfold kekulize at hK
    dsimp only at hK
    split at hK
    · cases hK; exact ⟨rfl, .inl rfl⟩
    · simp only [pure, Except.pure, bind, Except.bind] at hK
      split at hK
      · cases hK
      · rename_i out1 h1
        have q1 := foldlM_except_of (fun w ↦ w.atoms = m.atoms) _
          (fun _ _ _ hq hx ↦ kekulizeSystem_m (Q := fun w ↦ w.atoms = m.atoms)
            (fun _ _ _ h ↦ h) hq hx) _ _ _ rfl h1
        split at hK
        · cases hK
        · rename_i out2 h2
          split at hK
          · cases hK
          · cases hK
            have hb := foldlM_clearAromatic_bonds _ h2
            refine foldlM_clearAromatic_clearOk i _ _ _ h2 ⟨hb.symm, .inl ?_⟩
            simp only at q1
            rw [q1]
  obtain ⟨-, h | h | ⟨hbr, h⟩⟩ := hfin
  · left
    rw [h] at hfl ⊢
    cases hm : (m.atoms[i]! : WAtom)
    rw [hm] at hfl
    simp_all
  · exact .inl h
  · right
    refine ⟨hbr, ?_⟩
    rw [h]
    rfl

end LeanSMILES.Aromaticity.Work
