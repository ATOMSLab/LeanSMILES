/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RelabelPipeline

/-!
# LeanSMILES.Aromaticity.KekulizeRelabel

Two kekulizations of one copy, up to renumbering

Kekulization picks its double bonds by a walk whose order depends on the numbering, but every
atom ends with the same sum of bond orders: each candidate atom gets exactly one double bond
(`Work.kekulize_prepare_correct`). So the kekulization of a relabeled copy is the relabeled
kekulization with some single and double bonds swapped (`Work.kekulize_relabel_swapped`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- After `clearAromatic`, an aromatic `[nH]`/`[pH]` is never merely unflagged. -/
def NotCleared (a0 : WAtom) (w : Work) (i : ℕ) : Prop :=
  IsBranch a0 → (w.atoms[i]! : WAtom) ≠ { a0 with aromatic := false }

lemma clearAromatic_notCleared {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} {w w' : Work}
    {j : ℕ} (hw : clearAromatic ra w j = .ok w') (i : ℕ) (hok : ClearOk a0 bs w i)
    (h : NotCleared a0 w i) : NotCleared a0 w' i := by
  intro hbr
  have he1 : ({ a0 with aromatic := false } : WAtom).explicitHs = 1 := hbr.2.2.2
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · cases hw; exact h hbr
  split at hw
  · cases hw
  split at hw
  · cases hw
    by_cases hji : j = i
    · subst hji
      rw [modifyAtom_atom_self]
      split
      · rename_i hpos
        rw [modifyAtom_atom_self, if_pos (by simpa [modifyAtom] using hpos)]
        intro e
        have := congrArg WAtom.explicitHs e
        rw [he1] at this
        simp at this
      · rename_i hneg
        rw [modifyAtom_atom_self, if_neg (by simpa [modifyAtom] using hneg)]
        exact h hbr
    · rw [modifyAtom_atom_of_ne _ hji, modifyAtom_atom_of_ne _ hji]
      exact h hbr
  · cases hw
    by_cases hji : j = i
    · subst hji
      rename_i hnar _ hbr'
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hnar
      rw [modifyAtom_atom_self]
      split
      · -- the atom was `a0`, aromatic, and its branch test failed: impossible
        exfalso
        obtain ⟨-, ha⟩ := hok
        have ha0 : (w.atoms[j]! : WAtom) = a0 := by
          rcases ha with h' | h' | ⟨-, h'⟩
          · exact h'
          · rw [h'] at hnar; cases hnar
          · rw [h'] at hnar; cases hnar
        apply hbr'
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_cons,
          List.not_mem_nil, or_false, ha0]
        obtain ⟨-, hz, hc, he⟩ := hbr
        exact ⟨⟨hz, hc⟩, he⟩
      · exact h hbr
    · rw [modifyAtom_atom_of_ne _ hji]
      exact h hbr

lemma foldlM_clearAromatic_notCleared {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} (i : ℕ) :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ra) w = .ok w' →
      ClearOk a0 bs w i → NotCleared a0 w i → NotCleared a0 w' i
  | [], w, w', hw, _, h => by cases hw; exact h
  | x :: l, w, w', hw, hok, h => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ra w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      exact foldlM_clearAromatic_notCleared i l v w' hw (clearAromatic_clearOk hx i hok)
        (clearAromatic_notCleared hx i hok h)

/-- **Kekulization rewrites an aromatic `[nH]`/`[pH]`** (`branchRec`). -/
theorem kekulize_atom_branch {m K : Work} {rings : Array (List ℕ)}
    (hK : m.kekulize rings = .ok K) {i : ℕ} (hbr : IsBranch m.atoms[i]!) :
    (K.atoms[i]! : WAtom) = branchRec m.atoms[i]! (K.bondHalfSum i)
      ((K.kindsAt i).any (· == .aromatic)) := by
  have hnc : NotCleared m.atoms[i]! K i := by
    unfold kekulize at hK
    dsimp only at hK
    split at hK
    · rename_i hnone
      exfalso
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hnone
      have := hnone.2
      have hi : i < m.atoms.size := by
        by_contra hi
        rw [getElem!_neg m.atoms i hi] at hbr
        exact absurd hbr.1 (by decide)
      rw [Array.any_eq_false] at this
      exact absurd hbr.1 (by
        have := this i hi
        rw [← getElem!_pos m.atoms i hi] at this
        simpa using this)
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
            simp only at q1
            refine foldlM_clearAromatic_notCleared i _ _ _ h2 ⟨hb.symm, .inl (by rw [q1])⟩ ?_
            intro hbr' e
            rw [q1] at e
            have := congrArg WAtom.aromatic e
            rw [hbr'.1] at this
            cases this
  rcases kekulize_atom hK i with h | ⟨-, h⟩
  · exact absurd h (hnc hbr)
  · exact h

end LeanSMILES.Aromaticity.Work
