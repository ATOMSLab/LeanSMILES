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

/-! ### A ring's bonds do not depend on where its atom list starts or which way it runs -/

lemma bondBetween?_comm (w : Work) (i j : ℕ) : w.bondBetween? i j = w.bondBetween? j i := by
  unfold bondBetween?
  congr 1
  funext k
  rw [Bool.or_comm]

lemma ringBonds_eq_filterMap (w : Work) (r : List ℕ) :
    w.ringBonds r = (List.range r.length).filterMap fun t ↦
      w.bondBetween? r[t]! r[(t + 1) % r.length]! := rfl

/-- A self-map of `[0, n)` that is injective there permutes it. -/
lemma map_range_perm {n : ℕ} (f : ℕ → ℕ) (hf : ∀ t < n, f t < n)
    (hinj : ∀ a < n, ∀ b < n, f a = f b → a = b) :
    ((List.range n).map f).Perm (List.range n) := by
  have hnd : ((List.range n).map f).Nodup :=
    (List.nodup_range).map_on fun a ha b hb h ↦
      hinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) h
  have hsub : (List.range n).map f ⊆ List.range n := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (hf t (List.mem_range.1 ht))
  exact (List.subperm_of_subset hnd hsub).perm_of_length_le (by simp)

lemma getElem!_rotate {r : List ℕ} (k : ℕ) {t : ℕ} (ht : t < r.length) :
    (r.rotate k)[t]! = r[(t + k) % r.length]! := by
  have hlt : (t + k) % r.length < r.length := Nat.mod_lt _ (by omega)
  rw [getElem!_pos (r.rotate k) t (by rw [List.length_rotate]; exact ht),
    getElem!_pos r _ hlt, List.getElem_rotate]

lemma getElem!_reverse' {r : List ℕ} {t : ℕ} (ht : t < r.length) :
    r.reverse[t]! = r[r.length - 1 - t]! := by
  rw [getElem!_pos r.reverse t (by rw [List.length_reverse]; exact ht),
    getElem!_pos r _ (by omega), List.getElem_reverse]

/-- Reducing a number below `2 n` mod `n`. -/
lemma mod_of_lt_two_mul {x n : ℕ} (hx : x < 2 * n) : x % n = if x < n then x else x - n := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **Rotating a ring permutes its bonds.** -/
lemma ringBonds_rotate (w : Work) (r : List ℕ) (k : ℕ) :
    (w.ringBonds (r.rotate k)).Perm (w.ringBonds r) := by
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.length_rotate]
  generalize hn : r.length = n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  have e : (List.range n).filterMap (fun t ↦
      w.bondBetween? (r.rotate k)[t]! (r.rotate k)[(t + 1) % n]!) =
      ((List.range n).map fun t ↦ (t + k) % n).filterMap fun t ↦
        w.bondBetween? r[t]! r[(t + 1) % n]! := by
    rw [List.filterMap_map]
    apply List.filterMap_congr
    intro t ht
    have ht' := List.mem_range.1 ht
    simp only [Function.comp_apply]
    rw [getElem!_rotate k (by omega), getElem!_rotate k (by rw [hn]; exact Nat.mod_lt _ hpos), hn,
      Nat.mod_add_mod (t + 1) n k, Nat.mod_add_mod (t + k) n 1, show t + 1 + k = t + k + 1 by omega]
  rw [e]
  refine List.Perm.filterMap _ (map_range_perm _ (fun t _ ↦ Nat.mod_lt _ hpos) ?_)
  intro a ha b hb hab
  have hk := Nat.mod_lt k hpos
  change (a + k) % n = (b + k) % n at hab
  rw [← Nat.add_mod_mod a k n, ← Nat.add_mod_mod b k n,
    mod_of_lt_two_mul (x := a + k % n) (n := n) (by omega),
    mod_of_lt_two_mul (x := b + k % n) (n := n) (by omega)] at hab
  split_ifs at hab <;> omega

/-- **Reversing a ring permutes its bonds.** -/
lemma ringBonds_reverse (w : Work) (r : List ℕ) :
    (w.ringBonds r.reverse).Perm (w.ringBonds r) := by
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.length_reverse]
  generalize hn : r.length = n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  have e : (List.range n).filterMap (fun t ↦
      w.bondBetween? r.reverse[t]! r.reverse[(t + 1) % n]!) =
      ((List.range n).map fun t ↦ (n - 1 - t + (n - 1)) % n).filterMap fun t ↦
        w.bondBetween? r[t]! r[(t + 1) % n]! := by
    rw [List.filterMap_map]
    apply List.filterMap_congr
    intro t ht
    have ht' := List.mem_range.1 ht
    simp only [Function.comp_apply]
    rw [getElem!_reverse' (by omega), getElem!_reverse' (by rw [hn]; exact Nat.mod_lt _ hpos), hn,
      bondBetween?_comm]
    have hu : (n - 1 - t + (n - 1)) % n = if t + 1 < n then n - 2 - t else n - 1 := by
      rw [mod_of_lt_two_mul (by omega)]
      split_ifs <;> omega
    have hs : (t + 1) % n = if t + 1 < n then t + 1 else 0 := by
      rw [mod_of_lt_two_mul (by omega)]
      split_ifs <;> omega
    rw [hu, hs]
    split_ifs with h
    · rw [show (n - 2 - t + 1) % n = n - 1 - t by rw [Nat.mod_eq_of_lt (by omega)]; omega]
      congr 2
      omega
    · rw [show (n - 1 + 1) % n = 0 by rw [show n - 1 + 1 = n by omega, Nat.mod_self]]
      congr 2; omega
  rw [e]
  refine List.Perm.filterMap _ (map_range_perm _ (fun t _ ↦ Nat.mod_lt _ hpos) ?_)
  intro a ha b hb hab
  rw [mod_of_lt_two_mul (by omega), mod_of_lt_two_mul (by omega)] at hab
  split_ifs at hab <;> omega

/-! ### The same ring set -/

lemma forall₂_exists_left {α β : Type*} {P : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ P l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, P a b := by
  induction h with
  | nil => cases ha
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, hxy⟩
    · obtain ⟨b, hb, h⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

lemma forall₂_exists_right {α β : Type*} {P : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ P l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, P a b := by
  induction h with
  | nil => cases hb
  | @cons x y _ _ hxy _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨x, List.mem_cons_self, hxy⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- `r'` is the ring `r` with its atom list started elsewhere, run either way. -/
def RingEq (r r' : List ℕ) : Prop := ∃ k, r' = r.rotate k ∨ r' = (r.rotate k).reverse

/-- `R'` lists the rings of `R`, each started anywhere and run either way, in any order. -/
def RingsEquiv (R R' : List (List ℕ)) : Prop :=
  ∃ L, List.Forall₂ RingEq R L ∧ L.Perm R'

lemma RingEq.length {r r' : List ℕ} (h : RingEq r r') : r'.length = r.length := by
  obtain ⟨k, rfl | rfl⟩ := h <;> simp

lemma RingEq.mem {r r' : List ℕ} (h : RingEq r r') (i : ℕ) : i ∈ r' ↔ i ∈ r := by
  obtain ⟨k, rfl | rfl⟩ := h <;> simp [List.mem_rotate]

lemma RingEq.ringBonds (w : Work) {r r' : List ℕ} (h : RingEq r r') :
    (w.ringBonds r').Perm (w.ringBonds r) := by
  obtain ⟨k, rfl | rfl⟩ := h
  · exact ringBonds_rotate w r k
  · exact (ringBonds_reverse w _).trans (ringBonds_rotate w r k)

/-- What a property of rings that reads only their atoms and lengths says of equivalent lists. -/
lemma RingsEquiv.forall_exists {R R' : List (List ℕ)} (h : RingsEquiv R R') :
    ∀ r' ∈ R', ∃ r ∈ R, RingEq r r' := by
  obtain ⟨L, hf, hp⟩ := h
  intro r' hr'
  obtain ⟨r, hr, hrr⟩ := forall₂_exists_right hf (hp.mem_iff.2 hr')
  exact ⟨r, hr, hrr⟩

lemma RingsEquiv.exists_forall {R R' : List (List ℕ)} (h : RingsEquiv R R') :
    ∀ r ∈ R, ∃ r' ∈ R', RingEq r r' := by
  obtain ⟨L, hf, hp⟩ := h
  intro r hr
  obtain ⟨r', hr', hrr⟩ := forall₂_exists_left hf hr
  exact ⟨r', hp.mem_iff.1 hr', hrr⟩

lemma RingsEquiv.filter {R R' : List (List ℕ)} (h : RingsEquiv R R') (p : List ℕ → Bool)
    (hp : ∀ r r', RingEq r r' → p r' = p r) : RingsEquiv (R.filter p) (R'.filter p) := by
  obtain ⟨L, hf, hperm⟩ := h
  refine ⟨L.filter p, ?_, hperm.filter p⟩
  clear hperm
  induction hf with
  | nil => exact .nil
  | @cons r r' _ _ hrr _ ih =>
    simp only [List.filter_cons, hp r r' hrr]
    split
    · exact .cons hrr ih
    · exact ih

/-- The bonds of a list of rings, as a set, do not depend on how it is written. -/
lemma RingsEquiv.mem_flatMap_ringBonds (w : Work) {R R' : List (List ℕ)} (h : RingsEquiv R R')
    (k : ℕ) : k ∈ R'.flatMap w.ringBonds ↔ k ∈ R.flatMap w.ringBonds := by
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨r', hr', hk⟩
    obtain ⟨r, hr, hrr⟩ := h.forall_exists r' hr'
    exact ⟨r, hr, (hrr.ringBonds w).mem_iff.1 hk⟩
  · rintro ⟨r, hr, hk⟩
    obtain ⟨r', hr', hrr⟩ := h.exists_forall r hr
    exact ⟨r', hr', (hrr.ringBonds w).mem_iff.2 hk⟩

/-! ### Donor types and candidate rings -/

/-- The donor step reads the ring-bond set only through membership. -/
lemma donorType_congr (w : Work) {B B' : List ℕ} (h : ∀ k, k ∈ B ↔ k ∈ B') (i : ℕ) :
    w.donorType B' i = w.donorType B i := by
  have hc : List.contains B' = List.contains B := funext fun k ↦ by
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]; exact (h k).symm
  unfold donorType exocyclicMultiple?
  rw [hc]

lemma ringDonor_congr (w : Work) {B B' : List ℕ} (h : ∀ k, k ∈ B ↔ k ∈ B') (len i : ℕ) :
    w.ringDonor B' len i = w.ringDonor B len i := by
  simp only [ringDonor, donorType_congr w h]

/-- The donor type the first ring of `L` containing `i` gives it. -/
def firstDonor (w : Work) (B : List ℕ) (L : List (List ℕ)) (i : ℕ) : Donor :=
  match L.find? (·.contains i) with
  | some r => w.ringDonor B r.length i
  | none => .none

/-- Whether the first ring of `L` containing `i` makes it a candidate. -/
def firstCand (w : Work) (B : List ℕ) (L : List (List ℕ)) (i : ℕ) : Bool :=
  match L.find? (·.contains i) with
  | some r => w.isAromaticCandidate i (w.ringDonor B r.length i)
  | none => false

/-- What `donorData`'s first pass has done after the rings `L`. -/
structure DonorInv (w : Work) (B : List ℕ) (L : List (List ℕ)) (s : DonorState) : Prop where
  seen_size : s.seen.size = w.numAtoms
  cand_size : s.cand.size = w.numAtoms
  donor_size : s.donor.size = w.numAtoms
  seen : ∀ i < w.numAtoms, s.seen[i]! = L.any (·.contains i)
  donor : ∀ i < w.numAtoms, s.donor[i]! = firstDonor w B L i
  cand : ∀ i < w.numAtoms, s.cand[i]! = firstCand w B L i
  candRings : s.candRings.toList =
    L.filter fun r ↦ r.all fun i ↦ decide (i < w.numAtoms) && firstCand w B L i

lemma find?_append_singleton_of_any {L : List (List ℕ)} {r : List ℕ} {i : ℕ}
    (h : L.any (·.contains i) = true) :
    (L ++ [r]).find? (·.contains i) = L.find? (·.contains i) := by
  rw [List.find?_append]
  obtain ⟨x, hx, hxi⟩ := List.any_eq_true.1 h
  cases hf : L.find? (·.contains i) with
  | none => rw [List.find?_eq_none] at hf; exact absurd hxi (by simpa using hf x hx)
  | some y => rfl

lemma find?_append_singleton_of_not_any {L : List (List ℕ)} {r : List ℕ} {i : ℕ}
    (h : L.any (·.contains i) = false) :
    (L ++ [r]).find? (·.contains i) = if r.contains i then some r else none := by
  rw [List.find?_append]
  have : L.find? (·.contains i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.any_eq_false] at h
    simpa using h x hx
  rw [this]
  simp only [List.find?_cons, List.find?_nil, Option.none_or]
  cases r.contains i <;> rfl

lemma firstCand_append_of_mem {L : List (List ℕ)} {r : List ℕ} {w : Work} {B : List ℕ} {i : ℕ}
    (hi : i ∈ r) (L' : List (List ℕ)) :
    firstCand w B (L ++ r :: L') i = firstCand w B (L ++ [r]) i := by
  unfold firstCand
  rw [show L ++ r :: L' = (L ++ [r]) ++ L' by simp, List.find?_append]
  have : ((L ++ [r]).find? (·.contains i)).isSome := by
    rw [List.find?_isSome]
    exact ⟨r, by simp, by simpa using hi⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 this
  rw [hy]
  rfl

/-- What the first pass has done partway through ring `r`, after its atoms `rp`. -/
structure DonorInnerInv (w : Work) (B : List ℕ) (L : List (List ℕ)) (r rp : List ℕ)
    (s : DonorState) (a : Bool) : Prop where
  seen_size : s.seen.size = w.numAtoms
  cand_size : s.cand.size = w.numAtoms
  donor_size : s.donor.size = w.numAtoms
  seen : ∀ i < w.numAtoms, s.seen[i]! = (L.any (·.contains i) || rp.contains i)
  donor : ∀ i < w.numAtoms, s.donor[i]! =
    if (L.any (·.contains i) || rp.contains i) = true then firstDonor w B (L ++ [r]) i else .none
  cand : ∀ i < w.numAtoms, s.cand[i]! =
    if (L.any (·.contains i) || rp.contains i) = true then firstCand w B (L ++ [r]) i else false
  allCand : a = rp.all fun i ↦ decide (i < w.numAtoms) && firstCand w B (L ++ [r]) i
  candRings : s.candRings.toList =
    L.filter fun r ↦ r.all fun i ↦ decide (i < w.numAtoms) && firstCand w B L i

lemma getElem!_set!_gen {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ j < a.size then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj]
    simp [Array.set!, Array.getElem_setIfInBounds, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    simp [hj]

lemma firstDonor_of_not_any {w : Work} {B : List ℕ} {L : List (List ℕ)} {r : List ℕ} {i : ℕ}
    (hL : L.any (·.contains i) = false) (hr : i ∈ r) :
    firstDonor w B (L ++ [r]) i = w.ringDonor B r.length i := by
  unfold firstDonor
  rw [find?_append_singleton_of_not_any hL, if_pos (by simpa using hr)]

lemma firstCand_of_not_any {w : Work} {B : List ℕ} {L : List (List ℕ)} {r : List ℕ} {i : ℕ}
    (hL : L.any (·.contains i) = false) (hr : i ∈ r) :
    firstCand w B (L ++ [r]) i = w.isAromaticCandidate i (w.ringDonor B r.length i) := by
  unfold firstCand
  rw [find?_append_singleton_of_not_any hL, if_pos (by simpa using hr)]

lemma donorAtomStep_inv {w : Work} {B : List ℕ} {L : List (List ℕ)} {r rp : List ℕ}
    {s : DonorState} {a : Bool} {x : ℕ} (hx : x ∈ r) (hi : DonorInnerInv w B L r rp s a) :
    DonorInnerInv w B L r (rp ++ [x]) (w.donorAtomStep B r.length (s, a) x).1
      (w.donorAtomStep B r.length (s, a) x).2 := by
  have hne : ∀ i, i ≠ x → (L.any (·.contains i) || (rp ++ [x]).contains i) =
      (L.any (·.contains i) || rp.contains i) := fun i h ↦ by
    simp [h]
  have hxx : (L.any (·.contains x) || (rp ++ [x]).contains x) = true := by
    simp
  have hall : ∀ f : ℕ → Bool, (rp ++ [x]).all f = (rp.all f && f x) := fun f ↦ by
    simp [List.all_append]
  unfold donorAtomStep
  dsimp only
  by_cases hsx : s.seen[x]! = true
  · rw [if_pos hsx]
    have hxn : x < w.numAtoms := by
      by_contra h
      rw [getElem!_neg s.seen x (by rw [hi.seen_size]; exact h)] at hsx
      cases hsx
    have hcond : (L.any (·.contains x) || rp.contains x) = true := by
      rw [← hi.seen x hxn]; exact hsx
    refine ⟨hi.seen_size, hi.cand_size, hi.donor_size, fun i hin ↦ ?_, fun i hin ↦ ?_,
      fun i hin ↦ ?_, ?_, hi.candRings⟩
    · by_cases h : i = x
      · subst h; rw [hi.seen i hin, hcond, hxx]
      · rw [hne i h]; exact hi.seen i hin
    · by_cases h : i = x
      · subst h; rw [hi.donor i hin, if_pos hcond, if_pos hxx]
      · rw [hne i h]; exact hi.donor i hin
    · by_cases h : i = x
      · subst h; rw [hi.cand i hin, if_pos hcond, if_pos hxx]
      · rw [hne i h]; exact hi.cand i hin
    · rw [hi.allCand, hall, hi.cand x hxn, if_pos hcond]
      simp [hxn]
  · rw [if_neg hsx]
    by_cases hxn : x < w.numAtoms
    · have hcond : (L.any (·.contains x) || rp.contains x) = false := by
        rw [← hi.seen x hxn]; simpa using hsx
      have hL : L.any (·.contains x) = false := by
        rw [Bool.or_eq_false_iff] at hcond; exact hcond.1
      refine ⟨by simp [hi.seen_size], by simp [hi.cand_size], by simp [hi.donor_size],
        fun i hin ↦ ?_, fun i hin ↦ ?_, fun i hin ↦ ?_, ?_, hi.candRings⟩
      · by_cases h : i = x
        · subst h
          rw [getElem!_set!_gen, if_pos ⟨rfl, by rw [hi.seen_size]; exact hin⟩, hxx]
        · rw [getElem!_set!_gen, if_neg (by omega), hne i h]; exact hi.seen i hin
      · by_cases h : i = x
        · subst h
          rw [getElem!_set!_gen, if_pos ⟨rfl, by rw [hi.donor_size]; exact hin⟩, if_pos hxx,
            firstDonor_of_not_any hL hx]
        · rw [getElem!_set!_gen, if_neg (by omega), hne i h]; exact hi.donor i hin
      · by_cases h : i = x
        · subst h
          rw [getElem!_set!_gen, if_pos ⟨rfl, by rw [hi.cand_size]; exact hin⟩, if_pos hxx,
            firstCand_of_not_any hL hx]
        · rw [getElem!_set!_gen, if_neg (by omega), hne i h]; exact hi.cand i hin
      · have hc : x < s.cand.size := by rw [hi.cand_size]; exact hxn
        rw [hi.allCand, hall, getElem!_set!_gen, if_pos ⟨rfl, hc⟩, firstCand_of_not_any hL hx]
        simp [hxn]
    · refine ⟨by simp [hi.seen_size], by simp [hi.cand_size], by simp [hi.donor_size],
        fun i hin ↦ ?_, fun i hin ↦ ?_, fun i hin ↦ ?_, ?_, hi.candRings⟩
      · rw [getElem!_set!_gen, if_neg (by omega), hne i (by omega)]; exact hi.seen i hin
      · rw [getElem!_set!_gen, if_neg (by omega), hne i (by omega)]; exact hi.donor i hin
      · rw [getElem!_set!_gen, if_neg (by omega), hne i (by omega)]; exact hi.cand i hin
      · have hz : (s.cand.set! x (w.isAromaticCandidate x (w.ringDonor B r.length x)))[x]! =
            false := by
          rw [getElem!_set!_gen, if_neg (by rw [hi.cand_size]; omega),
            getElem!_neg s.cand x (by rw [hi.cand_size]; exact hxn)]
          rfl
        rw [hz, hall, hi.allCand]
        simp [hxn]

lemma donorAtoms_inv (w : Work) (B : List ℕ) (L : List (List ℕ)) (r : List ℕ) :
    ∀ (rest rp : List ℕ) (s : DonorState) (a : Bool), rp ++ rest = r →
      DonorInnerInv w B L r rp s a →
      DonorInnerInv w B L r r (rest.foldl (w.donorAtomStep B r.length) (s, a)).1
        (rest.foldl (w.donorAtomStep B r.length) (s, a)).2 := by
  intro rest
  induction rest with
  | nil => intro rp s a h hi; simp only [List.append_nil] at h; subst h; exact hi
  | cons x rest ih =>
    intro rp s a h hi
    have hx : x ∈ r := by rw [← h]; simp
    rw [List.foldl_cons]
    exact ih (rp ++ [x]) _ _ (by rw [← h]; simp) (donorAtomStep_inv hx hi)

lemma donorRingStep_inv {w : Work} {B : List ℕ} {L : List (List ℕ)} {r : List ℕ}
    {s : DonorState} (hi : DonorInv w B L s) :
    DonorInv w B (L ++ [r]) (w.donorRingStep B s r) := by
  have h0 : DonorInnerInv w B L r [] s true := by
    refine ⟨hi.seen_size, hi.cand_size, hi.donor_size, fun i hin ↦ ?_, fun i hin ↦ ?_,
      fun i hin ↦ ?_, by simp, hi.candRings⟩
    · rw [hi.seen i hin]; simp
    · rw [hi.donor i hin]
      simp only [List.contains_nil, Bool.or_false]
      split
      · rename_i h
        unfold firstDonor
        rw [find?_append_singleton_of_any h]
      · rename_i h
        unfold firstDonor
        simp only [Bool.not_eq_true] at h
        have : L.find? (·.contains i) = none := by
          rw [List.find?_eq_none]
          intro x hx
          rw [List.any_eq_false] at h
          simpa using h x hx
        rw [this]
    · rw [hi.cand i hin]
      simp only [List.contains_nil, Bool.or_false]
      split
      · rename_i h
        unfold firstCand
        rw [find?_append_singleton_of_any h]
      · rename_i h
        unfold firstCand
        simp only [Bool.not_eq_true] at h
        have : L.find? (·.contains i) = none := by
          rw [List.find?_eq_none]
          intro x hx
          rw [List.any_eq_false] at h
          simpa using h x hx
        rw [this]
  have hf := donorAtoms_inv w B L r r [] s true (by simp) h0
  unfold donorRingStep
  dsimp only
  set st := r.foldl (w.donorAtomStep B r.length) (s, true) with hst
  -- every condition is decided by the rings so far, now including `r`
  have hany : ∀ i, (L.any (·.contains i) || r.contains i) = (L ++ [r]).any (·.contains i) :=
    fun i ↦ by simp [List.any_append]
  have hnone : ∀ i, (L ++ [r]).any (·.contains i) = false →
      (L ++ [r]).find? (·.contains i) = none := fun i h ↦ by
    rw [List.find?_eq_none]
    intro x hx
    rw [List.any_eq_false] at h
    simpa using h x hx
  have hold : ∀ r₀ ∈ L, ∀ i ∈ r₀, firstCand w B (L ++ [r]) i = firstCand w B L i :=
    fun r₀ hr₀ i hi₀ ↦ by
      unfold firstCand
      rw [find?_append_singleton_of_any (List.any_eq_true.2 ⟨r₀, hr₀, by simpa using hi₀⟩)]
  have hfilt : (L.filter fun r₀ ↦ r₀.all fun i ↦ decide (i < w.numAtoms) &&
      firstCand w B (L ++ [r]) i) =
      L.filter fun r₀ ↦ r₀.all fun i ↦ decide (i < w.numAtoms) && firstCand w B L i := by
    apply List.filter_congr
    intro r₀ hr₀
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact forall₂_congr fun i hi₀ ↦ by rw [hold r₀ hr₀ i hi₀]
  have hcr : ∀ st' : DonorState, st'.seen = st.1.seen → st'.cand = st.1.cand →
      st'.donor = st.1.donor → DonorInv w B (L ++ [r]) st' ∨ True := fun _ _ _ _ ↦ .inr trivial
  clear hcr
  split
  · rename_i hA
    refine ⟨hf.seen_size, hf.cand_size, hf.donor_size, fun i hin ↦ ?_, fun i hin ↦ ?_,
      fun i hin ↦ ?_, ?_⟩
    · rw [hf.seen i hin, hany]
    · rw [hf.donor i hin, hany]
      split
      · rfl
      · rename_i h
        unfold firstDonor
        rw [hnone i (by simpa using h)]
    · rw [hf.cand i hin, hany]
      split
      · rfl
      · rename_i h
        unfold firstCand
        rw [hnone i (by simpa using h)]
    · simp only [Array.toList_push, hf.candRings, List.filter_append, hfilt]
      rw [hf.allCand] at hA
      simp [hA]
  · rename_i hA
    refine ⟨hf.seen_size, hf.cand_size, hf.donor_size, fun i hin ↦ ?_, fun i hin ↦ ?_,
      fun i hin ↦ ?_, ?_⟩
    · rw [hf.seen i hin, hany]
    · rw [hf.donor i hin, hany]
      split
      · rfl
      · rename_i h
        unfold firstDonor
        rw [hnone i (by simpa using h)]
    · rw [hf.cand i hin, hany]
      split
      · rfl
      · rename_i h
        unfold firstCand
        rw [hnone i (by simpa using h)]
    · rw [hf.candRings, List.filter_append, hfilt]
      rw [hf.allCand] at hA
      simp [hA]

/-- **`donorData`, characterized**: each atom's donor type and candidacy are those the first
ring containing it gives, and a ring is a candidate when all its atoms are. -/
lemma donorData_inv (w : Work) (R : Array (List ℕ)) :
    DonorInv w ((R.toList.flatMap w.ringBonds).eraseDups) R.toList (w.donorData R) := by
  unfold donorData
  dsimp only
  have key : ∀ (l L : List (List ℕ)) (s : DonorState),
      DonorInv w ((R.toList.flatMap w.ringBonds).eraseDups) L s →
      DonorInv w ((R.toList.flatMap w.ringBonds).eraseDups) (L ++ l)
        (l.foldl (w.donorRingStep ((R.toList.flatMap w.ringBonds).eraseDups)) s) := by
    intro l
    induction l with
    | nil => intro L s h; simpa using h
    | cons r l ih =>
      intro L s h
      rw [List.foldl_cons, show L ++ r :: l = (L ++ [r]) ++ l by simp]
      exact ih _ _ (donorRingStep_inv h)
  have := key R.toList []
    (⟨Array.replicate w.numAtoms false, Array.replicate w.numAtoms false,
      Array.replicate w.numAtoms Donor.none, #[]⟩ : DonorState)
    ⟨by simp [numAtoms], by simp [numAtoms], by simp [numAtoms],
      fun i hin ↦ by simp [hin], fun i hin ↦ by simp [hin, firstDonor],
      fun i hin ↦ by simp [hin, firstCand], by simp⟩
  simpa using this

end Work

end LeanSMILES.Aromaticity
