/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Congruence
public import LeanSMILES.Aromaticity.PerceiveFacts

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

/-- Bonds that agree but for their kinds join the same atoms. -/
lemma ends_of_single {x y : Option WBond}
    (h : x.map (fun b : WBond ↦ { b with kind := .single }) =
      y.map (fun b : WBond ↦ { b with kind := .single })) :
    x.map (fun b : WBond ↦ (b.src, b.dst)) = y.map (fun b : WBond ↦ (b.src, b.dst)) := by
  have := congrArg (Option.map fun b : WBond ↦ (b.src, b.dst)) h
  simpa [Option.map_map, Function.comp_def] using this

/-- `KindsRel` keeps which atoms each bond joins. -/
lemma KindsRel.ends {o w : Work} (h : KindsRel o w) (k : ℕ) :
    w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      o.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) :=
  ends_of_single (h.bonds k)

/-- **Ring perception reads only how many atoms there are and which atoms the bonds join.** -/
lemma relevantCycles_eq_of_ends {w w' : Work} (hn : w'.atoms.size = w.atoms.size)
    (hs : w'.bonds.size = w.bonds.size)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) :
    w'.relevantCycles = w.relevantCycles := by
  have hsrc : ∀ k, (w'.bonds[k]! : WBond).src = (w.bonds[k]! : WBond).src :=
    fun k ↦ (ends_getElem! hs he k).1
  have hdst : ∀ k, (w'.bonds[k]! : WBond).dst = (w.bonds[k]! : WBond).dst :=
    fun k ↦ (ends_getElem! hs he k).2
  have hN : w'.numAtoms = w.numAtoms := hn
  have hB : w'.numBonds = w.numBonds := hs
  have hbo : w'.bondsOf = w.bondsOf := by
    funext i
    simp only [bondsOf, hB, WBond.touches, hsrc, hdst]
  have hnb : w'.neighbors = w.neighbors := by
    funext i
    simp only [neighbors, hbo, WBond.other, hsrc, hdst]
  have hbb : w'.bondBetween? = w.bondBetween? := by
    funext i j
    simp only [bondBetween?, hB, hsrc, hdst]
  exact relevantCycles_congr hnb hbb hN hB

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

/-! ### Only bonds written aromatic change -/

/-- Setting a bond's kind keeps which atoms each bond joins. -/
lemma bondBetween?_setKind (w : Work) (k : ℕ) (t : BondKind) :
    (w.setKind k t).bondBetween? = w.bondBetween? := by
  have hs : (w.setKind k t).bonds.size = w.bonds.size := by simp
  have he : ∀ k' : ℕ, (w.setKind k t).bonds[k']?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k']?.map (fun b : WBond ↦ (b.src, b.dst)) := by
    intro k'
    rw [getElem?_setKind_bonds]
    split <;> simp [Option.map_map, Function.comp_def]
  have hsrc : ∀ k', ((w.setKind k t).bonds[k']! : WBond).src = (w.bonds[k']! : WBond).src :=
    fun k' ↦ (ends_getElem! hs he k').1
  have hdst : ∀ k', ((w.setKind k t).bonds[k']! : WBond).dst = (w.bonds[k']! : WBond).dst :=
    fun k' ↦ (ends_getElem! hs he k').2
  funext i j
  simp only [bondBetween?, numBonds, hs, hsrc, hdst]

/-- A pair found by `lookup` is in the list. -/
lemma mem_of_lookup {α β : Type*} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, l.lookup a = some b → (a, b) ∈ l
  | [], h => by simp at h
  | (x, y) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hx
      cases h
      rw [beq_iff_eq] at hx
      subst hx
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup h)

/-- An option the scan finds is joined to the current atom by a bond written aromatic. -/
lemma mem_foldl_scanStep (wa : ℕ → Bool) (m : Work) (cands : Array Bool) (curr : ℕ)
    (ccand : Bool) (queue : List ℕ) :
    ∀ (l : List ℕ) (p : List ℕ × List ℕ) (j : ℕ),
      j ∈ (l.foldl (scanStep m wa cands curr ccand queue) p).2 →
        j ∈ p.2 ∨ ∃ k, m.bondBetween? curr j = some k ∧ wa k = true
  | [], _, _, h => .inl h
  | x :: l, p, j, h => by
    rw [List.foldl_cons] at h
    rcases mem_foldl_scanStep wa m cands curr ccand queue l _ j h with h | h
    · unfold scanStep at h
      dsimp only at h
      split at h
      · rename_i k hk
        split at h
        · rename_i hc
          rcases List.mem_append.mp h with h | h
          · exact .inl h
          · rw [List.mem_singleton] at h
            subst h
            simp only [Bool.and_eq_true] at hc
            exact .inr ⟨k, hk, hc.2⟩
        · exact .inl h
      · exact .inl h
    · exact .inr h

/-- The walk's bookkeeping only ever points at bonds written aromatic (`wa`): every option kept
for an atom is joined to it by such a bond, and every bond the walk made double is one. -/
structure KekState.OnlyArom (wa : ℕ → Bool) (s : KekState) : Prop where
  /-- Kept options lie across bonds written aromatic. -/
  options : ∀ a o, (a, o) ∈ s.options → ∀ j ∈ o, ∀ k,
    s.m.bondBetween? a j = some k → wa k = true
  /-- Bonds made double were written aromatic. -/
  adds : ∀ k, s.adds[k]! = true → wa k = true

/-- What a step's result says, for a property `P` kept by setting the kinds of bonds written
aromatic: the molecule it ends with has `P`; the state it goes on from keeps the bookkeeping
invariant, `P` and the bonds' ends. -/
def StepR (wa : ℕ → Bool) (P : Work → Prop) (s : KekState) : Option Work ⊕ KekState → Prop
  | .inl (some w) => P w
  | .inl none => True
  | .inr s' => s'.OnlyArom wa ∧ P s'.m ∧ s'.m.bondBetween? = s.m.bondBetween?

section OnlyArom

variable {wa : ℕ → Bool} {P : Work → Prop}

lemma KekState.OnlyArom.placeDouble (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    {s₀ s : KekState} (hm : s.m = s₀.m) (hi : s.OnlyArom wa) (hp : P s.m) {curr n k : ℕ}
    {rest : List ℕ} (hk : s.m.bondBetween? curr n = some k)
    (hopts : ∀ j ∈ n :: rest, ∀ k, s.m.bondBetween? curr j = some k → wa k = true) :
    StepR wa P s₀ (.inr (s.placeDouble curr n k rest)) := by
  have hwk : wa k = true := hopts n List.mem_cons_self k hk
  have hbb := bondBetween?_setKind s.m k .double
  refine ⟨⟨fun a o hmem j hj k' hk' ↦ ?_, fun k' hk' ↦ ?_⟩, hP _ _ _ hwk hp, hbb.trans (by rw [hm])⟩
  · simp only [KekState.placeDouble_m, hbb] at hk'
    have hrest : ∀ j ∈ rest, ∀ k, s.m.bondBetween? curr j = some k → wa k = true :=
      fun j hj ↦ hopts j (List.mem_cons_of_mem _ hj)
    unfold KekState.placeDouble at hmem
    dsimp only at hmem
    split at hmem <;> (try split at hmem) <;> simp only at hmem
    · obtain ⟨hm, -⟩ := List.mem_filter.mp hmem
      exact hi.options a o hm j hj k' hk'
    · obtain ⟨q, hm, he⟩ := List.mem_map.mp hmem
      obtain ⟨a', o'⟩ := q
      simp only at he
      split at he
      · rename_i ha'
        cases he
        rw [beq_iff_eq] at ha'
        subst ha'
        exact hrest j hj k' hk'
      · cases he
        exact hi.options _ _ hm j hj k' hk'
    · rcases List.mem_append.mp hmem with hm | hm
      · exact hi.options a o hm j hj k' hk'
      · rw [List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        exact hrest j hj k' hk'
    · exact hi.options a o hmem j hj k' hk'
  · have e : (s.placeDouble curr n k rest).adds = s.adds.set! k true := by
      unfold KekState.placeDouble
      split <;> (try split) <;> rfl
    rw [e, getElem!_set!_bool] at hk'
    split at hk'
    · rename_i h
      rw [← h.1]
      exact hwk
    · exact hi.adds k' hk'

lemma foldl_undoAdds_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    (keep : List ℕ) : ∀ (l : List ℕ) (p : Work × Array Bool × Array Bool),
      (∀ k, p.2.1[k]! = true → wa k = true) → P p.1 →
      let q := l.foldl (undoAdds keep) p
      (∀ k, q.2.1[k]! = true → wa k = true) ∧ P q.1 ∧ q.1.bondBetween? = p.1.bondBetween?
  | [], _, ha, hp => ⟨ha, hp, rfl⟩
  | k :: l, ⟨m, adds, cands⟩, ha, hp => by
    simp only [List.foldl_cons]
    have step : (∀ k', (undoAdds keep (m, adds, cands) k).2.1[k']! = true → wa k' = true) ∧
        P (undoAdds keep (m, adds, cands) k).1 ∧
        (undoAdds keep (m, adds, cands) k).1.bondBetween? = m.bondBetween? := by
      unfold undoAdds
      dsimp only
      split
      · rename_i hk
        split
        · refine ⟨fun k' hk' ↦ ?_, hP _ _ _ (ha k hk) hp, bondBetween?_setKind _ _ _⟩
          simp only at hk'
          rw [getElem!_set!_bool] at hk'
          split at hk'
          · cases hk'
          · exact ha k' hk'
        · exact ⟨ha, hp, rfl⟩
      · exact ⟨ha, hp, rfl⟩
    obtain ⟨h1, h2, h3⟩ := foldl_undoAdds_onlyArom hP keep l _ step.1 step.2.1
    exact ⟨h1, h2, h3.trans step.2.2⟩

lemma KekState.OnlyArom.backTrack (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    {s₀ s : KekState} (hm : s.m = s₀.m) (hi : s.OnlyArom wa) (hp : P s.m) (lo : ℕ) :
    StepR wa P s₀ (.inr (s.backTrack lo)) := by
  obtain ⟨h1, h2, h3⟩ := foldl_undoAdds_onlyArom hP (s.done.take (s.done.idxOf lo))
    (List.range s.m.numBonds) (s.m, s.adds, s.cands) hi.adds hp
  unfold KekState.backTrack
  exact ⟨⟨fun a o hm' j hj k hk ↦ hi.options a o hm' j hj k (by rwa [h3] at hk), h1⟩, h2,
    h3.trans (by rw [hm])⟩

/-- **One step of the walk sets the kind only of bonds written aromatic.** -/
theorem kekulizeStep_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    (atoms sorted : List ℕ) {s : KekState} (hi : s.OnlyArom wa) (hp : P s.m) :
    StepR wa P s (kekulizeStep wa atoms sorted s) := by
  unfold kekulizeStep
  split
  · exact hp
  · rename_i curr queue _
    split
    all_goals
      rename_i hopt
      dsimp only
      split
      · exact ⟨⟨hi.options, hi.adds⟩, hp, rfl⟩
      · split
        · rename_i n rest hnr
          split
          · rename_i k hk
            apply KekState.OnlyArom.placeDouble hP ?_ ?_ ?_ ?_ ?_
            · rfl
            · exact ⟨hi.options, hi.adds⟩
            · exact hp
            · exact hk
            intro j hj k' hk'
            first
              | (have hmem := mem_of_lookup hopt
                 exact hi.options _ _ hmem j hj k' hk')
              | (rcases mem_foldl_scanStep wa s.m _ curr _ _ _ ([], []) j (by rw [hnr]; exact hj)
                   with h | h
                 · cases h
                 · obtain ⟨k'', hk'', hw⟩ := h
                   rw [hk''] at hk'
                   cases hk'
                   exact hw)
          · trivial
        · split
          · split
            · trivial
            · apply KekState.OnlyArom.backTrack hP ?_ ?_ ?_
              · rfl
              · exact ⟨hi.options, hi.adds⟩
              · exact hp
          · trivial

theorem kekulizeLoop_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    (atoms sorted : List ℕ) :
    ∀ (fuel : ℕ) (s : KekState), s.OnlyArom wa → P s.m → ∀ w,
      kekulizeLoop wa atoms sorted fuel s = some w → P w
  | 0, _, _, _, _, hw => by simp [kekulizeLoop] at hw
  | fuel + 1, s, hi, hp, w, hw => by
    unfold kekulizeLoop at hw
    split at hw
    · have hst := kekulizeStep_onlyArom hP atoms sorted hi hp
      split at hw
      · rename_i r hr
        rw [hr] at hst
        subst hw
        exact hst
      · rename_i s' hs'
        rw [hs'] at hst
        exact kekulizeLoop_onlyArom hP atoms sorted fuel s' hst.1 hst.2.1 w hw
    · cases hw
      exact hp

theorem kekulizeWorker_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    {m w : Work} {atoms : List ℕ} {cands : Array Bool} {done : List ℕ} (hp : P m)
    (hw : m.kekulizeWorker wa atoms cands done = some w) : P w :=
  kekulizeLoop_onlyArom hP atoms _ _ _
    ⟨fun _ _ h ↦ by simp at h, fun k h ↦ by simp [getElem!_replicate_false] at h⟩ hp w hw

lemma foldl_single_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t)) :
    ∀ (l : List ℕ) (o : Work), P o →
      P (l.foldl (fun o k ↦ if wa k then o.setKind k .single else o) o)
  | [], _, hp => hp
  | k :: l, o, hp => by
    rw [List.foldl_cons]
    refine foldl_single_onlyArom hP l _ ?_
    dsimp only
    split
    · exact hP _ _ _ ‹_› hp
    · exact hp

lemma singleAromaticBonds_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    (out : Work) (i : ℕ) (hp : P out) : P (singleAromaticBonds wa out i) := by
  unfold singleAromaticBonds
  split
  · exact foldl_single_onlyArom hP _ _ hp
  · exact hp

lemma foldl_singleAromaticBonds_onlyArom
    (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t)) :
    ∀ (l : List ℕ) (out : Work), P out → P (l.foldl (singleAromaticBonds wa) out)
  | [], _, hp => hp
  | i :: l, out, hp =>
    foldl_singleAromaticBonds_onlyArom hP l _ (singleAromaticBonds_onlyArom hP out i hp)

theorem kekulizeSystem_onlyArom (hP : ∀ w k t, wa k = true → P w → P (w.setKind k t))
    {ev0 : List ℕ} {rings : Array (List ℕ)} {out w : Work} {system : List ℕ} (hp : P out)
    (hw : kekulizeSystem wa ev0 rings out system = .ok w) : P w := by
  unfold kekulizeSystem at hw
  dsimp only at hw
  split at hw
  · cases hw
    exact hp
  · split at hw
    · cases hw
      exact kekulizeWorker_onlyArom hP (foldl_singleAromaticBonds_onlyArom hP _ _ hp) ‹_›
    · cases hw

end OnlyArom

/-- **Kekulization changes only bonds written aromatic**: every other bond keeps its kind. -/
theorem kekulize_kind_of_not_aromatic {m w : Work} {rings : Array (List ℕ)}
    (hw : m.kekulize rings = .ok w) {k : ℕ} (hk : m.kind? k ≠ some .aromatic) :
    w.kind? k = m.kind? k := by
  let P : Work → Prop := fun w ↦ ∀ k, m.kind? k ≠ some .aromatic → w.kind? k = m.kind? k
  suffices h : P w from h k hk
  unfold kekulize at hw
  dsimp only at hw
  split at hw
  · cases hw
    exact fun _ _ ↦ rfl
  · simp only [pure, Except.pure, bind, Except.bind] at hw
    split at hw
    · cases hw
    · rename_i out1 h1
      have hP : ∀ (w : Work) (k : ℕ) (t : BondKind),
          ((List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)).contains k = true →
          P w → P (w.setKind k t) := by
        intro w k t hwk hpw k' hk'
        rw [kind?, getElem?_setKind_bonds]
        split
        · rename_i hkk
          subst hkk
          exfalso
          apply hk'
          simp only [List.contains_iff_mem, List.mem_filter, List.mem_range, beq_iff_eq,
            numBonds] at hwk
          obtain ⟨hlt, hkind⟩ := hwk
          rw [getElem!_pos m.bonds k hlt] at hkind
          rw [kind?, Array.getElem?_eq_getElem hlt, Option.map_some, hkind]
        · exact hpw k' hk'
      have q1 : P out1 := by
        refine foldlM_except_of P _ ?_ _ _ _ (fun _ _ ↦ rfl) h1
        intro _ _ _ hq hx
        exact kekulizeSystem_onlyArom hP hq hx
      split at hw
      · cases hw
      · rename_i out2 h2
        have q2 : P out2 := by
          refine foldlM_except_of P _ ?_ _ _ _ q1 h2
          intro _ _ _ hq hx
          exact clearAromatic_m (Q := P) (fun _ _ _ _ h ↦ h) hq hx
        split at hw
        · simp at hw
        · cases hw
          exact q2


end LeanSMILES.Aromaticity.Work
