/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekuleSim

/-!
# LeanSMILES.Aromaticity.RingOrder

**Perception reads only the set of rings.**  `Work.setAromaticity` takes the ring set as an array
of atom lists; what it computes does not depend on the order of rings of equal size, or on where
each ring's atom list starts and which way it runs.  This file proves the first part: marking the
aromatic bonds depends only on the set of bonds marked (`Work.foldl_markAromatic_congr`), since
marking a bond is idempotent and markings of two bonds commute.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- **A fold of a self-commuting, idempotent step depends only on the set of its inputs.** -/
lemma foldl_congr_of_comm_idem {α β : Type*} (f : β → α → β)
    (hc : ∀ w a b, f (f w a) b = f (f w b) a) (hi : ∀ w a, f (f w a) a = f w a) :
    ∀ {l l' : List α}, (∀ x, x ∈ l ↔ x ∈ l') → ∀ w, l.foldl f w = l'.foldl f w := by
  classical
  -- a step already in the list is absorbed by it
  have absorb : ∀ (l : List α) (x : α), x ∈ l → ∀ w, l.foldl f (f w x) = l.foldl f w := by
    intro l
    induction l with
    | nil => intro x hx; cases hx
    | cons y l ih =>
      intro x hx w
      rw [List.foldl_cons, List.foldl_cons]
      by_cases hxy : x = y
      · subst hxy; rw [hi]
      · have hxl : x ∈ l := (List.mem_cons.1 hx).resolve_left hxy
        rw [hc, ih x hxl]
  have dedup : ∀ (l : List α) w, l.foldl f w = l.dedup.foldl f w := by
    intro l
    induction l with
    | nil => intro w; rfl
    | cons a l ih =>
      intro w
      by_cases ha : a ∈ l
      · rw [List.dedup_cons_of_mem ha, List.foldl_cons, absorb l a ha, ih]
      · rw [List.dedup_cons_of_notMem ha, List.foldl_cons, List.foldl_cons, ih]
  intro l l' h w
  rw [dedup l, dedup l']
  have hp : l.dedup.Perm l'.dedup :=
    (List.perm_ext_iff_of_nodup (List.nodup_dedup l) (List.nodup_dedup l')).2 fun x ↦ by
      rw [List.mem_dedup, List.mem_dedup]; exact h x
  exact hp.foldl_eq' (fun x _ y _ z ↦ hc z x y) w

namespace Work

/-- The flag `markAromatic` sets. -/
abbrev setArom : WAtom → WAtom := ({ · with aromatic := true })

lemma getElem?_markAromatic_bonds' (w : Work) (a k : ℕ) :
    (w.markAromatic a).bonds[k]? =
      if k = a ∧ isSD (w.bonds[a]! : WBond).kind = true then
        w.bonds[k]?.map ({ · with kind := .aromatic }) else w.bonds[k]? := by
  unfold markAromatic
  dsimp only
  by_cases hsd : isSD (w.bonds[a]! : WBond).kind = true
  · have hsd' : ((w.bonds[a]! : WBond).kind == .single ||
        (w.bonds[a]! : WBond).kind == .double) = true := hsd
    rw [if_pos hsd']
    simp only [modifyAtom, setKind, Array.getElem?_modify]
    by_cases hk : k = a
    · subst hk; simp [hsd]
    · simp [hk, Ne.symm hk]
  · rw [if_neg (show ¬ ((w.bonds[a]! : WBond).kind == .single ||
        (w.bonds[a]! : WBond).kind == .double) = true from hsd)]
    simp [hsd]

lemma getElem?_markAromatic_atoms' (w : Work) (a j : ℕ) :
    (w.markAromatic a).atoms[j]? =
      if isSD (w.bonds[a]! : WBond).kind = true ∧
          ((w.bonds[a]! : WBond).src = j ∨ (w.bonds[a]! : WBond).dst = j) then
        w.atoms[j]?.map setArom else w.atoms[j]? := by
  unfold markAromatic
  dsimp only
  by_cases hsd : isSD (w.bonds[a]! : WBond).kind = true
  · have hsd' : ((w.bonds[a]! : WBond).kind == .single ||
        (w.bonds[a]! : WBond).kind == .double) = true := hsd
    rw [if_pos hsd']
    simp only [modifyAtom, setKind, Array.getElem?_modify]
    split_ifs <;> simp_all [Option.map_map, Function.comp_def]
  · rw [if_neg (show ¬ ((w.bonds[a]! : WBond).kind == .single ||
        (w.bonds[a]! : WBond).kind == .double) = true from hsd)]
    simp [hsd]

/-- Marking bond `a` leaves bond `b ≠ a` alone. -/
lemma markAromatic_bond_of_ne (w : Work) {a b : ℕ} (h : b ≠ a) :
    ((w.markAromatic a).bonds[b]! : WBond) = w.bonds[b]! := by
  simp only [getElem!_def, getElem?_markAromatic_bonds', h, false_and, if_false]

lemma ext_getElem? {w w' : Work} (ha : ∀ j : ℕ, w'.atoms[j]? = w.atoms[j]?)
    (hb : ∀ k : ℕ, w'.bonds[k]? = w.bonds[k]?) : w' = w := by
  cases w; cases w'
  simp only [Work.mk.injEq]
  exact ⟨Array.ext_getElem? ha, Array.ext_getElem? hb⟩

/-- **Markings of two bonds commute.** -/
lemma markAromatic_comm (w : Work) (a b : ℕ) :
    (w.markAromatic a).markAromatic b = (w.markAromatic b).markAromatic a := by
  by_cases hab : a = b
  · subst hab; rfl
  have e1 := markAromatic_bond_of_ne w (Ne.symm hab)
  have e2 := markAromatic_bond_of_ne w hab
  apply ext_getElem?
  · intro j
    rw [getElem?_markAromatic_atoms' (w.markAromatic a) b j,
      getElem?_markAromatic_atoms' (w.markAromatic b) a j, e1, e2,
      getElem?_markAromatic_atoms' w a j, getElem?_markAromatic_atoms' w b j]
    split_ifs <;> simp [Option.map_map, Function.comp_def]
  · intro k
    rw [getElem?_markAromatic_bonds' (w.markAromatic a) b k,
      getElem?_markAromatic_bonds' (w.markAromatic b) a k, e1, e2,
      getElem?_markAromatic_bonds' w a k, getElem?_markAromatic_bonds' w b k]
    split_ifs <;> simp_all

/-- **Marking a bond twice is marking it once.** -/
lemma markAromatic_idem (w : Work) (a : ℕ) :
    (w.markAromatic a).markAromatic a = w.markAromatic a := by
  apply ext_getElem?
  · intro j
    rw [getElem?_markAromatic_atoms' (w.markAromatic a) a j, getElem?_markAromatic_atoms' w a j]
    by_cases ha : a < w.bonds.size
    · have hb : ((w.markAromatic a).bonds[a]! : WBond) =
          if isSD (w.bonds[a]! : WBond).kind = true then
            { (w.bonds[a]! : WBond) with kind := .aromatic } else w.bonds[a]! := by
        simp only [getElem!_def, getElem?_markAromatic_bonds', true_and,
          Array.getElem?_eq_getElem ha]
        split_ifs <;> rfl
      rw [hb]
      split_ifs <;> simp_all [isSD]
    · have hb : ((w.markAromatic a).bonds[a]! : WBond) = w.bonds[a]! := by
        simp only [getElem!_def, getElem?_markAromatic_bonds', Array.getElem?_eq_none
          (Nat.le_of_not_lt ha)]
        split_ifs <;> rfl
      rw [hb]
      split_ifs <;> simp_all [Option.map_map, Function.comp_def]
  · intro k
    rw [getElem?_markAromatic_bonds' (w.markAromatic a) a k, getElem?_markAromatic_bonds' w a k]
    by_cases hk : k = a
    · subst hk
      by_cases ha : k < w.bonds.size
      · simp only [getElem!_def, getElem?_markAromatic_bonds', true_and,
          Array.getElem?_eq_getElem ha]
        split_ifs <;> simp_all [isSD]
      · simp [Array.getElem?_eq_none (Nat.le_of_not_lt ha)]
    · simp [hk]

/-- **Marking the aromatic bonds depends only on the set of bonds marked.** -/
lemma foldl_markAromatic_congr {l l' : List ℕ} (h : ∀ b, b ∈ l ↔ b ∈ l') (w : Work) :
    l.foldl markAromatic w = l'.foldl markAromatic w :=
  foldl_congr_of_comm_idem markAromatic markAromatic_comm markAromatic_idem h w

end Work

end LeanSMILES.Aromaticity
