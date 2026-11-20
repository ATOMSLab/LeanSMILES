/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekuleSim

/-!
# LeanSMILES.Aromaticity.CleanFacts

What `cleanUp` can do to an atom and a bond, beyond `Work.CleanRel`: it never makes a bond
aromatic or not (each rewrite turns a double or triple bond into a single or double one), and
every charge it sets is `+1`, or `-1` on nitrogen or oxygen, or any charge on Cl, Br or I
(`Work.CleanFine`, `Work.cleanFine_cleanUp`).

## Main definitions

* `CleanCharge`: the charges `cleanUp` sets on an atom of a given element.
* `Work.CleanFine`: `CleanRel`, with aromatic bonds unchanged and every changed charge a
  `CleanCharge`.

## Main statements

* `Work.cleanFine_cleanUp`: `cleanUp` relates its input and output by `CleanFine`.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- The charges `cleanUp` sets on an atom of element `z`: `+1` (nitro and azide nitrogens,
phosphorus), `-1` on nitrogen (azide) or oxygen, anything on a halogen (perchlorate). -/
def CleanCharge (z : ℕ) (c : ℤ) : Prop :=
  c = 1 ∨ (c = -1 ∧ (z = 7 ∨ z = 8)) ∨ z = 17 ∨ z = 35 ∨ z = 53

namespace Work

/-- `cleanUp`'s changes, in detail: as `CleanRel`, with every bond aromatic exactly when it was,
and every changed charge one `cleanUp` sets (`CleanCharge`). -/
structure CleanFine (o w : Work) : Prop where
  /-- The coarse relation. -/
  rel : CleanRel o w
  /-- Aromatic bonds stay, and no other bond becomes one. -/
  arom : ∀ k : ℕ, (w.bonds[k]! : WBond).kind = .aromatic ↔ (o.bonds[k]! : WBond).kind = .aromatic
  /-- Each charge is `o`'s or one `cleanUp` sets. -/
  charge : ∀ j : ℕ, (w.atoms[j]! : WAtom).charge = (o.atoms[j]! : WAtom).charge ∨
    CleanCharge (o.atoms[j]! : WAtom).z (w.atoms[j]! : WAtom).charge

/-- `CleanRel` keeps every element. -/
lemma CleanRel.z_getElem! {o w : Work} (h : CleanRel o w) (j : ℕ) :
    (w.atoms[j]! : WAtom).z = (o.atoms[j]! : WAtom).z := by
  have := h.atoms j
  simp only [getElem!_def]
  cases h1 : w.atoms[j]? <;> cases h2 : o.atoms[j]? <;> simp_all

/-- Every copy is related to itself by `CleanFine`. -/
lemma CleanFine.refl (o : Work) : CleanFine o o :=
  ⟨.refl o, fun _ ↦ Iff.rfl, fun _ ↦ .inl rfl⟩

/-- `CleanFine` composes: two such steps in a row are one. -/
lemma CleanFine.trans {o w w' : Work} (h : CleanFine o w) (h' : CleanFine w w') :
    CleanFine o w' where
  rel := h.rel.trans h'.rel
  arom k := (h'.arom k).trans (h.arom k)
  charge j := by
    rcases h'.charge j with e | e
    · rw [e]; exact h.charge j
    · rw [h.rel.z_getElem! j] at e
      exact .inr e

/-- Making a bond that is not aromatic single or double. -/
lemma cleanFine_setKind (w : Work) {k : ℕ} {t : BondKind} (ht : t = .single ∨ t = .double)
    (hk : (w.bonds[k]! : WBond).kind ≠ .aromatic) : CleanFine w (w.setKind k t) where
  rel := cleanRel_setKind w k t ht
  arom j := by
    rw [kind_setKind]
    split
    · rename_i h
      obtain ⟨rfl, -⟩ := h
      rcases ht with rfl | rfl <;> simp [hk]
    · exact Iff.rfl
  charge _ := .inl rfl

/-- Setting a charge `cleanUp` sets. -/
lemma cleanFine_modifyAtom_charge (w : Work) {i : ℕ} {c : ℤ}
    (hc : CleanCharge (w.atoms[i]! : WAtom).z c) (hc0 : c ≠ 0) :
    CleanFine w (w.modifyAtom i ({ · with charge := c })) where
  rel := cleanRel_modifyAtom_charge w i c hc0
  arom _ := Iff.rfl
  charge j := by
    rw [atom_modifyAtom]
    split
    · rename_i h
      obtain ⟨rfl, -⟩ := h
      exact .inr hc
    · exact .inl rfl

/-- What `find?` picks out of `neighbors` satisfies the test and is a neighbor pair of the atom. -/
lemma find?_neighbors_spec {w : Work} {i k j : ℕ} {p : ℕ × ℕ → Bool}
    (h : (w.neighbors i).find? p = some (k, j)) : p (k, j) = true ∧ (k, j) ∈ w.neighbors i :=
  ⟨List.find?_some h, List.mem_of_find?_eq_some h⟩

/-- One step of `nitrogensCleanup`'s first pass changes its copy only as `CleanFine` allows. -/
lemma cleanFine_nitroStep (p : Work × List ℕ) (i : ℕ) : CleanFine p.1 (nitroStep p i).1 := by
  obtain ⟨w, consider⟩ := p
  unfold nitroStep
  dsimp only
  split
  · exact .refl w
  · split
    · rename_i k j hf
      have hp := (find?_neighbors_spec hf).1
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      obtain ⟨⟨hz, -⟩, hd⟩ := hp
      have h1 := w.cleanFine_setKind (k := k) (.inl rfl) (by rw [hd]; decide)
      have h2 := (w.setKind k .single).cleanFine_modifyAtom_charge (i := i) (c := 1)
        (.inl rfl) one_ne_zero
      have h3 := Work.cleanFine_modifyAtom_charge ((w.setKind k .single).modifyAtom i
        ({ · with charge := 1 })) (i := j) (c := -1) ?_ (by decide)
      · exact (h1.trans h2).trans h3
      · refine .inr (.inl ⟨rfl, .inr ?_⟩)
        rw [atom_modifyAtom]
        split <;> simp [hz]
    · exact .refl w

/-- One step of `nitrogensCleanup`'s second pass changes the copy only as `CleanFine` allows. -/
lemma cleanFine_azideStep (w : Work) (i : ℕ) : CleanFine w (azideStep w i) := by
  unfold azideStep
  dsimp only
  split
  · rename_i k j hf
    have hp := (find?_neighbors_spec hf).1
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨hz, -⟩, hd⟩ := hp
    have h1 := w.cleanFine_setKind (k := k) (.inr rfl) (by rw [hd]; decide)
    have h2 := (w.setKind k .double).cleanFine_modifyAtom_charge (i := i) (c := 1)
      (.inl rfl) one_ne_zero
    have h3 := Work.cleanFine_modifyAtom_charge ((w.setKind k .double).modifyAtom i
        ({ · with charge := 1 })) (i := j) (c := -1) ?_ (by decide)
    · exact (h1.trans h2).trans h3
    · refine .inr (.inl ⟨rfl, .inl ?_⟩)
      rw [atom_modifyAtom]
      split <;> simp [hz]
  · exact .refl w

/-- The `=O` `phosphorusScan` finds is a double bond to an oxygen. -/
lemma phosphorusScan_spec (w : Work) (i : ℕ) {k j : ℕ}
    (h : (w.phosphorusScan i).1 = some (k, j)) :
    (w.bonds[k]! : WBond).kind = .double ∧ (w.atoms[j]! : WAtom).z = 8 := by
  unfold phosphorusScan at h
  have key : ∀ (l : List (ℕ × ℕ)) (s : Option (ℕ × ℕ) × Bool),
      (∀ k j, s.1 = some (k, j) → (w.bonds[k]! : WBond).kind = .double ∧
        (w.atoms[j]! : WAtom).z = 8) →
      ∀ k j, (l.foldl (fun (st : Option (ℕ × ℕ) × Bool) (kj : ℕ × ℕ) ↦
          let b := w.atoms[kj.2]!
          if b.z == 8 && b.charge == 0 && w.bonds[kj.1]!.kind == .double then
            (some (kj.1, kj.2), st.2)
          else if (b.z == 6 || b.z == 7) && 2 ≤ w.degree kj.2 &&
              w.bonds[kj.1]!.kind == .double then (st.1, true)
          else (st.1, st.2)) s).1 = some (k, j) →
        (w.bonds[k]! : WBond).kind = .double ∧ (w.atoms[j]! : WAtom).z = 8 := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons kj l ih =>
      intro s hs
      rw [List.foldl_cons]
      apply ih
      intro k j hkj
      dsimp only at hkj
      split at hkj
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hkj
        obtain ⟨rfl, rfl⟩ := hkj
        exact ⟨hc.2, hc.1.1⟩
      · split at hkj
        · exact hs k j hkj
        · exact hs k j hkj
  exact key _ (none, false) (fun _ _ h ↦ by simp at h) k j h

/-- `phosphorusCleanup` at any atom changes the copy only as `CleanFine` allows. -/
lemma cleanFine_phosphorusCleanup (w : Work) (i : ℕ) :
    CleanFine w (w.phosphorusCleanup i) := by
  unfold phosphorusCleanup
  dsimp only
  split
  · exact .refl w
  · split
    · rename_i k j hs
      split
      · obtain ⟨hd, hz⟩ := w.phosphorusScan_spec i hs
        have h1 := w.cleanFine_setKind (k := k) (.inl rfl) (by rw [hd]; decide)
        have h2 := (w.setKind k .single).cleanFine_modifyAtom_charge (i := j) (c := -1)
          (.inr (.inl ⟨rfl, .inr (by simpa using hz)⟩)) (by decide)
        have h3 := Work.cleanFine_modifyAtom_charge ((w.setKind k .single).modifyAtom j
        ({ · with charge := -1 })) (i := i) (c := 1) (.inl rfl) one_ne_zero
        exact (h1.trans h2).trans h3
      · exact .refl w
    · exact .refl w

/-- `halogenCleanup` at a Cl, Br or I atom changes the copy only as `CleanFine` allows. -/
lemma cleanFine_halogenCleanup (w : Work) (i : ℕ) (hz : (w.atoms[i]! : WAtom).z = 17 ∨
    (w.atoms[i]! : WAtom).z = 35 ∨ (w.atoms[i]! : WAtom).z = 53) :
    CleanFine w (w.halogenCleanup i) := by
  unfold halogenCleanup
  dsimp only
  split
  · exact .refl w
  · split
    · exact .refl w
    · rename_i hO
      have hO' : ∀ kj ∈ w.neighbors i, (w.atoms[kj.2]! : WAtom).z = 8 := by simpa using hO
      have key : ∀ (l : List (ℕ × ℕ)), (∀ kj ∈ l, (w.atoms[kj.2]! : WAtom).z = 8) →
          ∀ p : Work × ℤ, CleanFine w p.1 ∧ (p.2 = 0 ∧ p.1 = w ∨ 0 < p.2) →
            CleanFine w (l.foldl halogenStep p).1 ∧
              ((l.foldl halogenStep p).2 = 0 ∧ (l.foldl halogenStep p).1 = w ∨
                0 < (l.foldl halogenStep p).2) := by
        intro l hl
        induction l with
        | nil => intro p hp; exact hp
        | cons kj l ih =>
          intro p hp
          rw [List.foldl_cons]
          refine ih (fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)) _ ?_
          obtain ⟨w', fc⟩ := p
          obtain ⟨hp, hp2⟩ := hp
          obtain ⟨k, j⟩ := kj
          unfold halogenStep
          dsimp only at hp2 ⊢
          split
          · rename_i hd
            simp only [beq_iff_eq] at hd
            have hz8 : (w'.atoms[j]! : WAtom).z = 8 := by
              rw [hp.rel.z_getElem! j]; exact hl _ List.mem_cons_self
            have h1 := w'.cleanFine_setKind (k := k) (.inl rfl) (by rw [hd]; decide)
            have h2 := (w'.setKind k .single).cleanFine_modifyAtom_charge (i := j) (c := -1)
              (.inr (.inl ⟨rfl, .inr (by simpa using hz8)⟩)) (by decide)
            refine ⟨hp.trans (h1.trans h2), .inr ?_⟩
            rcases hp2 with ⟨rfl, -⟩ | h <;> omega
          · exact ⟨hp, hp2⟩
      obtain ⟨hf, hf2⟩ := key (w.neighbors i) hO' (w, 0)
        ⟨.refl w, .inl ⟨rfl, rfl⟩⟩
      generalize (w.neighbors i).foldl halogenStep (w, 0) = p at hf hf2
      obtain ⟨w', fc⟩ := p
      dsimp only at hf hf2 ⊢
      rcases hf2 with ⟨rfl, rfl⟩ | hpos
      · rename_i hch
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at hch
        rw [modifyAtom_charge_self _ hch.1]
        exact .refl _
      · refine hf.trans (w'.cleanFine_modifyAtom_charge ?_ (by omega))
        rw [hf.rel.z_getElem! i]
        rcases hz with h | h | h <;> rw [h] <;> simp [CleanCharge]

/-- One step of `cleanUp`'s second pass changes the copy only as `CleanFine` allows. -/
lemma cleanFine_cleanUpStep (w : Work) (i : ℕ) : CleanFine w (cleanUpStep w i) := by
  unfold cleanUpStep
  dsimp only
  split
  · exact w.cleanFine_phosphorusCleanup i
  · split
    · rename_i h
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact w.cleanFine_halogenCleanup i (by omega)
    · exact .refl w

/-- `nitrogensCleanup` changes the copy only as `CleanFine` allows. -/
lemma cleanFine_nitrogensCleanup (w : Work) : CleanFine w w.nitrogensCleanup := by
  unfold nitrogensCleanup
  have h1 := foldl_induction (fun p : Work × List ℕ ↦ CleanFine w p.1) nitroStep
    (List.range w.numAtoms) (w, []) (.refl w) fun p i _ hp ↦ hp.trans (cleanFine_nitroStep p i)
  generalize (List.range w.numAtoms).foldl nitroStep (w, []) = p at h1
  obtain ⟨w', consider⟩ := p
  exact foldl_induction (CleanFine w) azideStep consider w' h1
    fun w'' i _ h ↦ h.trans (cleanFine_azideStep w'' i)

/-- **What `cleanUp` does, in detail.** -/
theorem cleanFine_cleanUp (w : Work) : CleanFine w w.cleanUp := by
  unfold cleanUp
  have h := w.cleanFine_nitrogensCleanup
  exact foldl_induction (CleanFine w) cleanUpStep (List.range w.nitrogensCleanup.numAtoms) _ h
    fun w' i _ h' ↦ h'.trans (cleanFine_cleanUpStep w' i)

end Work

end LeanSMILES.Aromaticity
