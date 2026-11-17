/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Passes

/-!
# LeanSMILES.Aromaticity.KekulizeFacts

What kekulization keeps, for any input it succeeds on (not only one with nothing aromatic, as in
`Work.kekulize_of_noArom`).

* `Work.kekulize_m`: a property of the working copy kept by setting a bond's kind, and by editing
  an atom without touching its element or charge, is kept by `Work.kekulize`.  The walk
  (`Work.kekulizeStep`, `Work.kekulizeLoop`) changes the molecule only through `Work.setKind`,
  and clearing the aromatic flags only through such atom edits.
* `Work.kekulize_kindsRel`: kekulization keeps every atom's element and charge and every bond's
  ends; only bond kinds and the atoms' bookkeeping change.
* `Work.kekulize_noArom`: nothing in the result is aromatic.

These need the walk to be a structural recursion: written as RDKit writes it, a `while` loop,
it would be a `partial` function, and nothing about what it returns could be proved.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

variable {Q : Work → Prop}

/-! ### A property kept by setting bond kinds -/

lemma undoAdds_fst (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (keep : List ℕ)
    (p : Work × Array Bool × Array Bool) (k : ℕ) (h : Q p.1) : Q (undoAdds keep p k).1 := by
  obtain ⟨m, adds, cands⟩ := p
  unfold undoAdds
  dsimp only
  split
  · split
    · exact hQ _ _ _ h
    · exact h
  · exact h

lemma foldl_undoAdds_fst (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (keep : List ℕ) :
    ∀ (l : List ℕ) (p : Work × Array Bool × Array Bool), Q p.1 →
      Q (l.foldl (undoAdds keep) p).1
  | [], _, h => h
  | k :: l, p, h => foldl_undoAdds_fst hQ keep l _ (undoAdds_fst hQ keep p k h)

lemma KekState.backTrack_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (s : KekState) (lo : ℕ)
    (h : Q s.m) : Q (s.backTrack lo).m := by
  unfold KekState.backTrack
  exact foldl_undoAdds_fst hQ _ _ (s.m, s.adds, s.cands) h

@[simp] lemma KekState.placeDouble_m (s : KekState) (curr n k : ℕ) (rest : List ℕ) :
    (s.placeDouble curr n k rest).m = s.m.setKind k .double := rfl

/-- What a step's result says about the molecule: the molecule it ends with, or the one it goes
on with, has `Q`; a failure says nothing. -/
def StepQ (Q : Work → Prop) : Option Work ⊕ KekState → Prop
  | .inl (some w) => Q w
  | .inl none => True
  | .inr s => Q s.m

/-- One step of the walk keeps a property kept by setting bond kinds. -/
theorem kekulizeStep_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (wasAromatic : ℕ → Bool)
    (atoms sorted : List ℕ) (s : KekState) (h : Q s.m) :
    StepQ Q (kekulizeStep wasAromatic atoms sorted s) := by
  unfold kekulizeStep
  split
  · exact h
  · split
    all_goals
      dsimp only
      split
      · exact h
      · split
        · split
          · exact hQ _ _ _ h
          · trivial
        · split
          · split
            · trivial
            · exact KekState.backTrack_m hQ _ _ h
          · trivial

/-- The walk keeps a property kept by setting bond kinds. -/
theorem kekulizeLoop_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (wasAromatic : ℕ → Bool)
    (atoms sorted : List ℕ) :
    ∀ (fuel : ℕ) (s : KekState), Q s.m → ∀ w,
      kekulizeLoop wasAromatic atoms sorted fuel s = some w → Q w
  | 0, _, _, _, hw => by simp [kekulizeLoop] at hw
  | fuel + 1, s, hs, w, hw => by
    unfold kekulizeLoop at hw
    split at hw
    · have hst := kekulizeStep_m hQ wasAromatic atoms sorted s hs
      split at hw
      · rename_i r hr
        rw [hr] at hst
        subst hw
        exact hst
      · rename_i s' hs'
        rw [hs'] at hst
        exact kekulizeLoop_m hQ wasAromatic atoms sorted fuel s' hst w hw
    · cases hw
      exact hs

theorem kekulizeWorker_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) {m w : Work}
    {wasAromatic : ℕ → Bool} {atoms : List ℕ} {cands : Array Bool} {done : List ℕ} (h : Q m)
    (hw : m.kekulizeWorker wasAromatic atoms cands done = some w) : Q w :=
  kekulizeLoop_m hQ wasAromatic atoms _ _ _ h w hw

lemma foldl_setKind_of (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (g : ℕ → Bool) (t : BondKind) :
    ∀ (l : List ℕ) (o : Work), Q o → Q (l.foldl (fun o k ↦ if g k then o.setKind k t else o) o)
  | [], _, h => h
  | k :: l, o, h => by
    refine foldl_setKind_of hQ g t l _ ?_
    dsimp only
    split
    · exact hQ _ _ _ h
    · exact h

lemma singleAromaticBonds_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) (wasAromatic : ℕ → Bool)
    (out : Work) (i : ℕ) (h : Q out) : Q (singleAromaticBonds wasAromatic out i) := by
  unfold singleAromaticBonds
  split
  · exact foldl_setKind_of hQ wasAromatic .single _ _ h
  · exact h

lemma foldl_singleAromaticBonds_m (hQ : ∀ w k t, Q w → Q (w.setKind k t))
    (wasAromatic : ℕ → Bool) : ∀ (l : List ℕ) (out : Work), Q out →
      Q (l.foldl (singleAromaticBonds wasAromatic) out)
  | [], _, h => h
  | i :: l, out, h =>
    foldl_singleAromaticBonds_m hQ wasAromatic l _ (singleAromaticBonds_m hQ wasAromatic out i h)

/-- One fused system keeps a property kept by setting bond kinds. -/
theorem kekulizeSystem_m (hQ : ∀ w k t, Q w → Q (w.setKind k t)) {wasAromatic : ℕ → Bool}
    {ev0 : List ℕ} {rings : Array (List ℕ)} {out w : Work} {system : List ℕ} (h : Q out)
    (hw : kekulizeSystem wasAromatic ev0 rings out system = .ok w) : Q w := by
  unfold kekulizeSystem at hw
  dsimp only at hw
  split at hw
  · cases hw
    exact h
  · split at hw
    · cases hw
      exact kekulizeWorker_m hQ (foldl_singleAromaticBonds_m hQ wasAromatic _ _ h) ‹_›
    · cases hw

/-- A property kept by every step of a monadic left fold that may fail holds of its result. -/
theorem foldlM_except_of {α : Type} (P : Work → Prop) (f : Work → α → Except String Work)
    (hf : ∀ w x w', P w → f w x = .ok w' → P w') :
    ∀ (l : List α) (w w' : Work), P w → l.foldlM f w = .ok w' → P w'
  | [], w, w', h, hw => by
    cases hw
    exact h
  | x :: l, w, w', h, hw => by
    rw [List.foldlM_cons] at hw
    cases hx : f w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      exact foldlM_except_of P f hf l v w' (hf w x v h hx) hw

/-- Clearing an atom's aromatic flag keeps a property kept by editing an atom's bookkeeping. -/
theorem clearAromatic_m
    (hA : ∀ w i (f : WAtom → WAtom), (∀ a, (f a).z = a.z ∧ (f a).charge = a.charge) →
      Q w → Q (w.modifyAtom i f))
    {ringAtoms : List ℕ} {out w : Work} {i : ℕ} (h : Q out)
    (hw : clearAromatic ringAtoms out i = .ok w) : Q w := by
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · cases hw; exact h
  · split at hw
    · cases hw
    · split at hw
      · cases hw
        exact hA _ _ _ (fun _ ↦ ⟨rfl, rfl⟩) (hA _ _ _ (fun _ ↦ ⟨rfl, rfl⟩) h)
      · cases hw
        exact hA _ _ _ (fun _ ↦ ⟨rfl, rfl⟩) h

/-- **Kekulization keeps a property kept by setting bond kinds and by editing an atom's
bookkeeping** (anything but its element and charge). -/
theorem kekulize_m (hQ : ∀ w k t, Q w → Q (w.setKind k t))
    (hA : ∀ w i (f : WAtom → WAtom), (∀ a, (f a).z = a.z ∧ (f a).charge = a.charge) →
      Q w → Q (w.modifyAtom i f))
    {m w : Work} {rings : Array (List ℕ)} (h : Q m) (hw : m.kekulize rings = .ok w) : Q w := by
  unfold kekulize at hw
  dsimp only at hw
  split at hw
  · cases hw; exact h
  · simp only [pure, Except.pure, bind, Except.bind] at hw
    split at hw
    · cases hw
    · rename_i out1 h1
      have q1 := foldlM_except_of Q _ (fun _ _ _ hq hx ↦ kekulizeSystem_m hQ hq hx) _ _ _ h h1
      split at hw
      · cases hw
      · rename_i out2 h2
        have q2 := foldlM_except_of Q _ (fun _ _ _ hq hx ↦ clearAromatic_m hA hq hx) _ _ _ q1 h2
        split at hw
        · simp at hw
        · cases hw; exact q2

/-! ### What kekulization keeps -/

/-- `w` is `o` but for its bond kinds and its atoms' bookkeeping: as many atoms, with the same
elements and charges, and the same bonds but for their kinds. -/
structure KindsRel (o w : Work) : Prop where
  /-- As many atoms. -/
  atoms_size : w.atoms.size = o.atoms.size
  /-- The same elements. -/
  z : ∀ j : ℕ, w.atoms[j]?.map (·.z) = o.atoms[j]?.map (·.z)
  /-- The same charges. -/
  charge : w.charge? = o.charge?
  /-- The same bonds but for their kinds. -/
  bonds : ∀ k : ℕ, w.bonds[k]?.map (fun b : WBond ↦ { b with kind := .single }) =
    o.bonds[k]?.map (fun b : WBond ↦ { b with kind := .single })

lemma KindsRel.refl (o : Work) : KindsRel o o := ⟨rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl⟩

lemma KindsRel.setKind {o w : Work} (h : KindsRel o w) (k : ℕ) (t : BondKind) :
    KindsRel o (w.setKind k t) where
  atoms_size := h.atoms_size
  z := h.z
  charge := h.charge
  bonds j := by
    rw [← h.bonds j, getElem?_setKind_bonds]
    split <;> simp [Option.map_map, Function.comp_def]

lemma KindsRel.modifyAtom {o w : Work} (h : KindsRel o w) (i : ℕ) (f : WAtom → WAtom)
    (hf : ∀ a, (f a).z = a.z ∧ (f a).charge = a.charge) : KindsRel o (w.modifyAtom i f) where
  atoms_size := by simp [h.atoms_size]
  z j := by
    rw [← h.z j, getElem?_modifyAtom_atoms]
    split <;> simp [Option.map_map, Function.comp_def, hf]
  charge := by
    rw [← h.charge]
    funext j
    simp only [charge?, getElem?_modifyAtom_atoms]
    split <;> simp [Option.map_map, Function.comp_def, hf]
  bonds := h.bonds

/-- As many bonds. -/
lemma KindsRel.bonds_size {o w : Work} (h : KindsRel o w) : w.bonds.size = o.bonds.size := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := h.bonds w.bonds.size
    rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
    simp at this
  · have := h.bonds o.bonds.size
    rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
    simp at this

/-- **Kekulization keeps the atoms' elements and charges and the bonds' ends**: only bond kinds
and the atoms' bookkeeping change. -/
theorem kekulize_kindsRel {m w : Work} {rings : Array (List ℕ)}
    (hw : m.kekulize rings = .ok w) : KindsRel m w :=
  kekulize_m (Q := KindsRel m) (fun _ k t h ↦ h.setKind k t)
    (fun _ i f hf h ↦ h.modifyAtom i f hf) (.refl m) hw

/-! ### Nothing aromatic comes out -/

/-- Clearing atom `i`'s flag keeps the number of atoms and every other atom's flag, and leaves
atom `i` not aromatic. -/
lemma clearAromatic_spec {ringAtoms : List ℕ} {out w : Work} {i : ℕ}
    (hw : clearAromatic ringAtoms out i = .ok w) :
    w.atoms.size = out.atoms.size ∧
      (∀ j, j ≠ i → w.atoms[j]?.map (·.aromatic) = out.atoms[j]?.map (·.aromatic)) ∧
      ∀ a, w.atoms[i]? = some a → a.aromatic = false := by
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · rename_i ha
    cases hw
    refine ⟨rfl, fun _ _ ↦ rfl, fun a hai ↦ ?_⟩
    simpa [getElem!_def, hai] using ha
  · split at hw
    · cases hw
    · split at hw
      · cases hw
        refine ⟨by simp, fun j hj ↦ ?_, fun a hai ↦ ?_⟩
        · simp only [getElem?_modifyAtom_atoms, if_neg (Ne.symm hj)]
        · simp only [getElem?_modifyAtom_atoms, ↓reduceIte] at hai
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hai
          obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hb
          rfl
      · cases hw
        refine ⟨by simp, fun j hj ↦ ?_, fun a hai ↦ ?_⟩
        · simp only [getElem?_modifyAtom_atoms, if_neg (Ne.symm hj)]
        · simp only [getElem?_modifyAtom_atoms, ↓reduceIte] at hai
          obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.mp hai
          rfl

/-- Clearing the flags of the atoms in `l`: as many atoms, the flags of atoms not in `l` kept,
and no atom of `l` aromatic. -/
lemma foldlM_clearAromatic_spec {ringAtoms : List ℕ} :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ringAtoms) w = .ok w' →
      w'.atoms.size = w.atoms.size ∧
        (∀ j, j ∉ l → w'.atoms[j]?.map (·.aromatic) = w.atoms[j]?.map (·.aromatic)) ∧
        ∀ j ∈ l, ∀ a, w'.atoms[j]? = some a → a.aromatic = false
  | [], w, w', hw => by cases hw; exact ⟨rfl, fun _ _ ↦ rfl, by simp⟩
  | x :: l, w, w', hw => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ringAtoms w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      obtain ⟨hs, hother, hself⟩ := clearAromatic_spec hx
      obtain ⟨hs', hother', hl⟩ := foldlM_clearAromatic_spec l v w' hw
      refine ⟨hs'.trans hs, fun j hj ↦ ?_, fun j hj a ha ↦ ?_⟩
      · rw [List.mem_cons, not_or] at hj
        rw [hother' j hj.2, hother j hj.1]
      · by_cases hjl : j ∈ l
        · exact hl j hjl a ha
        · have hjx : j = x := by
            rcases List.mem_cons.mp hj with h | h
            · exact h
            · exact absurd h hjl
          subst hjx
          have e := hother' j hjl
          rw [ha] at e
          obtain ⟨b, hb, hba⟩ := Option.map_eq_some_iff.mp e.symm
          simp only at hba
          rw [← hba]
          exact hself b hb

/-- **Nothing comes out of kekulization aromatic**: no atom flagged, no bond of kind aromatic. -/
theorem kekulize_noArom {m w : Work} {rings : Array (List ℕ)} (hw : m.kekulize rings = .ok w) :
    w.NoArom := by
  unfold kekulize at hw
  dsimp only at hw
  split at hw
  · rename_i hnone
    cases hw
    rw [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, List.filter_eq_nil_iff] at hnone
    refine ⟨fun a ha ↦ ?_, fun b hb hbk ↦ ?_⟩
    · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
      have := hnone.2
      rw [Array.any_eq_false] at this
      simpa using this i hi
    · obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hb
      have := hnone.1 k (List.mem_range.mpr hk)
      simp [getElem!_def, Array.getElem?_eq_getElem hk, hbk] at this
  · simp only [pure, Except.pure, bind, Except.bind] at hw
    split at hw
    · cases hw
    · rename_i out1 h1
      split at hw
      · cases hw
      · rename_i out2 h2
        obtain ⟨hs, -, hl⟩ := foldlM_clearAromatic_spec _ _ _ h2
        split at hw
        · simp at hw
        · rename_i hb
          cases hw
          refine ⟨fun a ha ↦ ?_, fun b hb' hbk ↦ ?_⟩
          · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
            exact hl i (List.mem_range.mpr (by simpa [numAtoms, ← hs] using hi)) _
              (Array.getElem?_eq_getElem hi)
          · rw [Bool.not_eq_true, Array.any_eq_false] at hb
            obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp hb'
            simpa [hbk] using hb k hk

end LeanSMILES.Aromaticity.Work
