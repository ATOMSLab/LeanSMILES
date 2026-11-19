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

/-! ### Bond-order sums after kekulization -/

/-- An atom's bond-order sum with the bonds written aromatic made single. -/
def kekBase (m : Work) (x : ℕ) : ℕ :=
  ((m.bondsOf x).map fun k ↦ if m.kekWa k then 2 else halfOrder (m.bonds[k]! : WBond).kind).sum

lemma bondsOf_of_kindsRel {o w : Work} (h : KindsRel o w) : w.bondsOf = o.bondsOf := by
  have hs : w.bonds.size = o.bonds.size := by
    have := h.bonds
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := this w.bonds.size
      rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
      simp at this
    · have := this o.bonds.size
      rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
      simp at this
  funext x
  unfold bondsOf
  rw [show w.numBonds = o.numBonds from hs]
  apply List.filter_congr
  intro k hk
  have hk' : k < o.bonds.size := List.mem_range.1 hk
  have := h.bonds k
  rw [Array.getElem?_eq_getElem (hs ▸ hk'), Array.getElem?_eq_getElem hk'] at this
  simp only [Option.map_some, Option.some.injEq, WBond.mk.injEq] at this
  rw [getElem!_pos _ k (hs ▸ hk'), getElem!_pos _ k hk']
  simp only [WBond.touches, this.1, this.2.1]

lemma sum_ite_two (l : List ℕ) (D : ℕ → Bool) :
    (l.map fun k ↦ if D k = true then 2 else 0).sum = 2 * (l.filter D).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    split <;> simp [*] <;> omega

/-- **An atom's bond-order sum after kekulization**: the base, plus one double bond if it is a
candidate. -/
theorem bondHalfSum_of_matching {m K : Work} (hwf : WF m) (hKR : KindsRel m K) {D : ℕ → Bool}
    (hkind : ∀ k, (K.bonds[k]! : WBond).kind = if D k = true then .double else
        if m.kekWa k = true then .single else (m.bonds[k]! : WBond).kind)
    (hdok : ∀ k, D k = true → k < m.bonds.size ∧ m.kekWa k = true ∧
        ∀ x, (m.bonds[k]! : WBond).touches x = true → candOf m m.kekWa m.kekEv0 x = true)
    (hmatch : ∀ k₁ k₂ x, D k₁ = true → D k₂ = true → (m.bonds[k₁]! : WBond).touches x = true →
        (m.bonds[k₂]! : WBond).touches x = true → k₁ = k₂)
    (hcover : ∀ x < m.atoms.size, candOf m m.kekWa m.kekEv0 x = true →
        ∃ k, D k = true ∧ (m.bonds[k]! : WBond).touches x = true) (x : ℕ) :
    K.bondHalfSum x = kekBase m x +
      if x < m.atoms.size ∧ candOf m m.kekWa m.kekEv0 x = true then 2 else 0 := by
  unfold bondHalfSum kekBase
  rw [bondsOf_of_kindsRel hKR]
  have e : ∀ k ∈ m.bondsOf x, halfOrder (K.bonds[k]! : WBond).kind =
      (if m.kekWa k = true then 2 else halfOrder (m.bonds[k]! : WBond).kind) +
        if D k = true then 2 else 0 := fun k _ ↦ by
    rw [hkind k]
    by_cases hD : D k = true
    · rw [if_pos hD, if_pos (hdok k hD).2.1, if_pos hD]; rfl
    · rw [if_neg hD, if_neg hD]
      split <;> rfl
  rw [List.map_congr_left e, List.sum_map_add, sum_ite_two]
  congr 1
  have hmem : ∀ k, k ∈ m.bondsOf x ↔ k < m.bonds.size ∧ (m.bonds[k]! : WBond).touches x = true :=
    fun k ↦ by simp [bondsOf, numBonds]
  split
  · rename_i hc
    obtain ⟨k, hk, ht⟩ := hcover x hc.1 hc.2
    rw [length_filter_eq_one (show (m.bondsOf x).Nodup from List.nodup_range.filter _)
      (fun a ha b hb hpa hpb ↦ hmatch a b x hpa hpb ((hmem a).1 ha).2 ((hmem b).1 hb).2)
      ⟨k, (hmem k).2 ⟨(hdok k hk).1, ht⟩, hk⟩]
  · rename_i hc
    suffices ((m.bondsOf x).filter D).length = 0 by rw [this]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro k hk hD
    obtain ⟨hks, ht⟩ := (hmem k).1 hk
    apply hc
    refine ⟨?_, (hdok k hD).2.2 x ht⟩
    have := hwf k hks
    simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with rfl | rfl
    · exact this.1
    · exact this.2.1

end LeanSMILES.Aromaticity.Work
