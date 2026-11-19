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

/-- In a list sorted by length, the first ring containing `i` is as short as any. -/
lemma find?_length_le {L : List (List ℕ)} (hs : L.Pairwise (·.length ≤ ·.length)) {i : ℕ}
    {r : List ℕ} (hr : L.find? (·.contains i) = some r) :
    ∀ r₀ ∈ L, i ∈ r₀ → r.length ≤ r₀.length := by
  obtain ⟨-, as, bs, rfl, has⟩ := List.find?_eq_some_iff_append.1 hr
  intro r₀ hr₀ hi
  rw [List.mem_append, List.mem_cons] at hr₀
  rcases hr₀ with hr₀ | rfl | hr₀
  · exact absurd (by simpa using hi) (by simpa using has r₀ hr₀)
  · exact le_rfl
  · rw [List.pairwise_append, List.pairwise_cons] at hs
    exact hs.2.1.1 r₀ hr₀

/-- Equivalent ring lists sorted by length: the first ring containing an atom has the same
length in both. -/
lemma RingsEquiv.find?_length {R R' : List (List ℕ)} (h : RingsEquiv R R')
    (hs : R.Pairwise (·.length ≤ ·.length)) (hs' : R'.Pairwise (·.length ≤ ·.length)) (i : ℕ) :
    (R'.find? (·.contains i)).map List.length = (R.find? (·.contains i)).map List.length := by
  cases hf : R.find? (·.contains i) with
  | none =>
    rw [List.find?_eq_none] at hf
    have : R'.find? (·.contains i) = none := by
      rw [List.find?_eq_none]
      intro r' hr' hc
      obtain ⟨r, hr, hrr⟩ := h.forall_exists r' hr'
      exact hf r hr (by simpa [hrr.mem] using hc)
    rw [this]
  | some r =>
    have hri : i ∈ r := by simpa using List.find?_some hf
    obtain ⟨r', hr', hrr⟩ := h.exists_forall r (List.mem_of_find?_eq_some hf)
    cases hf' : R'.find? (·.contains i) with
    | none =>
      rw [List.find?_eq_none] at hf'
      exact absurd (by simpa using (hrr.mem i).2 hri) (hf' r' hr')
    | some q =>
      have hqi : i ∈ q := by simpa using List.find?_some hf'
      obtain ⟨q₀, hq₀, hqq⟩ := h.forall_exists q (List.mem_of_find?_eq_some hf')
      have h1 := find?_length_le hs hf q₀ hq₀ ((hqq.mem i).1 hqi)
      have h2 := find?_length_le hs' hf' r' hr' ((hrr.mem i).2 hri)
      rw [← hqq.length] at h1
      rw [hrr.length] at h2
      have : q.length = r.length := by omega
      simp [this]

lemma firstDonor_eq_of_length {w : Work} {B B' : List ℕ} {L L' : List (List ℕ)} {i : ℕ}
    (hB : ∀ k, k ∈ B ↔ k ∈ B')
    (hl : (L'.find? (·.contains i)).map List.length = (L.find? (·.contains i)).map List.length) :
    firstDonor w B' L' i = firstDonor w B L i ∧ firstCand w B' L' i = firstCand w B L i := by
  unfold firstDonor firstCand
  cases h1 : L'.find? (·.contains i) with
  | none =>
    cases h2 : L.find? (·.contains i) with
    | none => exact ⟨rfl, rfl⟩
    | some r => rw [h1, h2] at hl; cases hl
  | some r' =>
    cases h2 : L.find? (·.contains i) with
    | none => rw [h1, h2] at hl; cases hl
    | some r =>
      rw [h1, h2] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      dsimp only
      rw [hl, ringDonor_congr w hB]
      exact ⟨rfl, rfl⟩

lemma array_ext_of_getElem! {α : Type} [Inhabited α] {a b : Array α} {n : ℕ} (ha : a.size = n)
    (hb : b.size = n) (h : ∀ i < n, a[i]! = b[i]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i hi hi'
  have := h i (by omega)
  rwa [getElem!_pos a i hi, getElem!_pos b i hi'] at this

/-- **The first pass of perception reads only the ring set**: for two ring lists sorted by
length that list the same rings, each written any way, the donor types and candidacies agree,
and the candidate rings are again the same rings. -/
theorem donorData_equiv (w : Work) {R R' : Array (List ℕ)} (h : RingsEquiv R.toList R'.toList)
    (hs : R.toList.Pairwise (·.length ≤ ·.length))
    (hs' : R'.toList.Pairwise (·.length ≤ ·.length)) :
    (w.donorData R').seen = (w.donorData R).seen ∧ (w.donorData R').cand = (w.donorData R).cand ∧
      (w.donorData R').donor = (w.donorData R).donor ∧
      RingsEquiv (w.donorData R).candRings.toList (w.donorData R').candRings.toList := by
  have I := donorData_inv w R
  have I' := donorData_inv w R'
  have hB : ∀ k, k ∈ (R.toList.flatMap w.ringBonds).eraseDups ↔
      k ∈ (R'.toList.flatMap w.ringBonds).eraseDups := fun k ↦ by
    rw [List.mem_eraseDups, List.mem_eraseDups]
    exact (h.mem_flatMap_ringBonds w k).symm
  have hfc : ∀ i, firstDonor w ((R'.toList.flatMap w.ringBonds).eraseDups) R'.toList i =
        firstDonor w ((R.toList.flatMap w.ringBonds).eraseDups) R.toList i ∧
      firstCand w ((R'.toList.flatMap w.ringBonds).eraseDups) R'.toList i =
        firstCand w ((R.toList.flatMap w.ringBonds).eraseDups) R.toList i := fun i ↦
    firstDonor_eq_of_length hB (h.find?_length hs hs' i)
  have hany : ∀ i, R'.toList.any (·.contains i) = R.toList.any (·.contains i) := fun i ↦ by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨r', hr', hc⟩
      obtain ⟨r, hr, hrr⟩ := h.forall_exists r' hr'
      exact ⟨r, hr, by simpa [hrr.mem] using hc⟩
    · rintro ⟨r, hr, hc⟩
      obtain ⟨r', hr', hrr⟩ := h.exists_forall r hr
      exact ⟨r', hr', by simpa [hrr.mem] using hc⟩
  refine ⟨array_ext_of_getElem! I'.seen_size I.seen_size fun i hi ↦ ?_,
    array_ext_of_getElem! I'.cand_size I.cand_size fun i hi ↦ ?_,
    array_ext_of_getElem! I'.donor_size I.donor_size fun i hi ↦ ?_, ?_⟩
  · rw [I'.seen i hi, I.seen i hi, hany]
  · rw [I'.cand i hi, I.cand i hi, (hfc i).2]
  · rw [I'.donor i hi, I.donor i hi, (hfc i).1]
  · rw [I.candRings, I'.candRings]
    have hp : (fun r : List ℕ ↦ r.all fun i ↦ decide (i < w.numAtoms) &&
        firstCand w ((R'.toList.flatMap w.ringBonds).eraseDups) R'.toList i) =
        fun r : List ℕ ↦ r.all fun i ↦ decide (i < w.numAtoms) &&
          firstCand w ((R.toList.flatMap w.ringBonds).eraseDups) R.toList i := by
      funext r; simp only [(hfc _).2]
    rw [hp]
    refine h.filter _ fun r r' hrr ↦ ?_
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact ⟨fun H i hi ↦ H i ((hrr.mem i).2 hi), fun H i hi ↦ H i ((hrr.mem i).1 hi)⟩

/-! ### Fused systems: rings written another way, in the same order -/

lemma eraseDups_nodup : ∀ l : List ℕ, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
    rw [List.eraseDups_cons]
    exact List.Nodup.cons (by simp [List.mem_eraseDups]) (eraseDups_nodup _)
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

lemma perm_eraseDups {l l' : List ℕ} (h : l.Perm l') : l.eraseDups.Perm l'.eraseDups :=
  (List.perm_ext_iff_of_nodup (eraseDups_nodup l) (eraseDups_nodup l')).2 fun x ↦ by
    rw [List.mem_eraseDups, List.mem_eraseDups]; exact h.mem_iff

lemma mergeSort_eraseDups_perm {l l' : List ℕ} (h : l.Perm l') :
    l.eraseDups.mergeSort (· ≤ ·) = l'.eraseDups.mergeSort (· ≤ ·) := by
  refine List.Perm.eq_of_pairwise (le := fun a b : ℕ ↦ decide (a ≤ b) = true)
    (fun a b _ _ h1 h2 ↦ by simp at h1 h2; omega)
    (List.pairwise_mergeSort (fun a b c ↦ by simp; omega) (fun a b ↦ by simp; omega) _)
    (List.pairwise_mergeSort (fun a b c ↦ by simp; omega) (fun a b ↦ by simp; omega) _) ?_
  exact ((List.mergeSort_perm _ _).trans (perm_eraseDups h)).trans (List.mergeSort_perm _ _).symm

/-- Counting atoms over a ring does not depend on how the ring is written. -/
lemma foldl_count_perm {l l' : List ℕ} (h : l.Perm l') (acc : Array ℕ) :
    l.foldl (fun acc a ↦ acc.modify a (· + 1)) acc =
      l'.foldl (fun acc a ↦ acc.modify a (· + 1)) acc := by
  refine h.foldl_eq' (fun x _ y _ z ↦ ?_) acc
  apply Array.ext_getElem?
  intro j
  simp only [Array.getElem?_modify]
  split_ifs <;> simp_all [Option.map_map, Function.comp_def]

lemma groupBonds_ringEq {numAtoms : ℕ} {rb rb' C C' : Array (List ℕ)} {d : Array Donor}
    {nbrs : Array (List ℕ)} (hC : ∀ r : ℕ, (C'[r]!).Perm (C[r]!))
    (hR : ∀ r : ℕ, (rb'[r]!).Perm (rb[r]!)) (cur : List ℕ) :
    groupBonds numAtoms rb' C' d nbrs cur = groupBonds numAtoms rb C d nbrs cur := by
  unfold groupBonds
  have hcount : ∀ (acc : Array ℕ) (r : ℕ),
      C'[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc =
        C[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc := fun acc r ↦
    foldl_count_perm (hC r) acc
  have hall : (cur.flatMap (rb'[·]!)).Perm (cur.flatMap (rb[·]!)) :=
    List.Perm.flatMap_left _ fun r _ ↦ hR r
  simp only [hcount, mergeSort_eraseDups_perm hall, hall.count_eq]

lemma fusedNbrs_ringEq {rb rb' : Array (List ℕ)} (hs : rb'.size = rb.size)
    (hR : ∀ r : ℕ, (rb'[r]!).Perm (rb[r]!)) : fusedNbrs rb' = fusedNbrs rb := by
  have hc : ∀ i j : ℕ, ((rb'[i]!).filter (rb'[j]!).contains).length =
      ((rb[i]!).filter (rb[j]!).contains).length := fun i j ↦ by
    have e : (rb'[j]!).contains = (rb[j]!).contains := funext fun k ↦ by
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]; exact (hR j).mem_iff
    rw [e]
    exact ((hR i).filter _).length_eq
  have hl : ∀ i : ℕ, (rb'[i]!).length = (rb[i]!).length := fun i ↦ (hR i).length_eq
  unfold fusedNbrs
  simp only [hs, hc, hl]

lemma systemBonds_ringEq {numAtoms : ℕ} {rb rb' C C' : Array (List ℕ)} {d : Array Donor}
    {nbrs : Array (List ℕ)} (hC : ∀ r : ℕ, (C'[r]!).Perm (C[r]!))
    (hR : ∀ r : ℕ, (rb'[r]!).Perm (rb[r]!)) (fused : List ℕ) :
    systemBonds numAtoms rb' C' d nbrs fused = systemBonds numAtoms rb C d nbrs fused := by
  have hlen : (fused.flatMap (rb'[·]!)).eraseDups.length =
      (fused.flatMap (rb[·]!)).eraseDups.length :=
    (perm_eraseDups (List.Perm.flatMap_left _ fun r _ ↦ hR r)).length_eq
  unfold systemBonds
  simp only [hlen, groupBonds_ringEq hC hR]

/-- **Fused systems read each candidate ring only up to rotation and reversal.** -/
theorem fusedBonds_ringEq {numAtoms : ℕ} {w : Work} {C C' : Array (List ℕ)} {d : Array Donor}
    (h : List.Forall₂ RingEq C.toList C'.toList) :
    fusedBonds numAtoms (C'.map w.ringBonds) C' d =
      fusedBonds numAtoms (C.map w.ringBonds) C d := by
  have hs : C'.size = C.size := by
    rw [← Array.length_toList, ← Array.length_toList]; exact h.length_eq.symm
  have hge : ∀ r < C.size, RingEq C[r]! C'[r]! := by
    intro r hr
    rw [getElem!_pos C r hr, getElem!_pos C' r (by omega)]
    have := List.forall₂_iff_get.1 h
    simpa using this.2 r (by simpa using hr) (by simpa [hs] using hr)
  have hC : ∀ r : ℕ, (C'[r]!).Perm (C[r]!) := fun r ↦ by
    by_cases hr : r < C.size
    · obtain ⟨k, e | e⟩ := hge r hr
      · rw [e]; exact List.rotate_perm _ _
      · rw [e]; exact (List.reverse_perm _).trans (List.rotate_perm _ _)
    · rw [getElem!_neg C r hr, getElem!_neg C' r (by omega)]
  have hR : ∀ r : ℕ, ((C'.map w.ringBonds)[r]!).Perm ((C.map w.ringBonds)[r]!) := fun r ↦ by
    by_cases hr : r < C.size
    · rw [getElem!_pos _ r (by simpa [hs] using hr), getElem!_pos _ r (by simpa using hr)]
      simp only [Array.getElem_map]
      rw [← getElem!_pos C r hr, ← getElem!_pos C' r (by omega)]
      exact (hge r hr).ringBonds w
    · rw [getElem!_neg _ r (by simpa [hs] using hr), getElem!_neg _ r (by simpa using hr)]
  have hsz : (C'.map w.ringBonds).size = (C.map w.ringBonds).size := by simp [hs]
  unfold fusedBonds
  dsimp only
  rw [fusedNbrs_ringEq hsz hR, hs]
  have e : systemBonds numAtoms (C'.map w.ringBonds) C' d (fusedNbrs (C.map w.ringBonds)) =
      systemBonds numAtoms (C.map w.ringBonds) C d (fusedNbrs (C.map w.ringBonds)) :=
    funext fun F ↦ systemBonds_ringEq hC hR F
  rw [e]

/-! ### Fused systems: rings reordered -/

/-- Whether candidate rings `i` and `j` are fused (`fusedNbrs`). -/
def fusedPair (rb : Array (List ℕ)) (i j : ℕ) : Bool :=
  (rb[i]!).length ≤ 24 && (rb[j]!).length ≤ 24 && ((rb[i]!).filter (rb[j]!).contains).length == 1

lemma forIn_ite_yield {β : Type} (l : List ℕ) (b : β) (c : ℕ → Prop) [DecidablePred c]
    (g : ℕ → β → β) :
    (forIn l b (fun a r ↦ if c a then pure (ForInStep.yield (g a r))
      else pure (ForInStep.yield r)) : Id β) = l.foldl (fun r a ↦ if c a then g a r else r) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases hc : c x
    · simp only [if_pos hc]; exact ih _
    · simp only [if_neg hc]; exact ih _

lemma forIn_ite_yield' {β : Type} (l : List ℕ) (b : β) (c : ℕ → β → Bool)
    (g : ℕ → β → β) :
    (forIn l b (fun a r ↦ if c a r = true then pure (ForInStep.yield (g a r))
      else pure (ForInStep.yield r)) : Id β) =
      l.foldl (fun r a ↦ if c a r = true then g a r else r) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih =>
    rw [List.forIn_cons, List.foldl_cons]
    by_cases hc : c x b = true
    · simp only [if_pos hc]; exact ih _
    · simp only [if_neg hc]; exact ih _

lemma foldlM_id {β : Type} (l : List ℕ) (b : β) (f : β → ℕ → Id β) :
    (l.foldlM f b).run = l.foldl (fun r a ↦ (f r a).run) b := by
  induction l generalizing b with
  | nil => rfl
  | cons x l ih => rw [List.foldlM_cons, List.foldl_cons]; exact ih _

lemma fusedNbrs_eq_foldl (rb : Array (List ℕ)) :
    fusedNbrs rb = (List.range rb.size).foldl (fun nbrs i ↦
      (List.range' (i + 1) (rb.size - (i + 1))).foldl (fun nbrs j ↦
        if fusedPair rb i j then (nbrs.modify i (· ++ [j])).modify j (· ++ [i]) else nbrs) nbrs)
      (Array.replicate rb.size []) := by
  simp only [fusedNbrs, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bind_pure_comp,
    map_pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    add_tsub_cancel_right, Nat.div_one, tsub_zero, List.forIn_yield_eq_foldlM, id_map', bind_pure,
    fusedPair, List.range_eq_range']
  rw [foldlM_id]
  congr 1
  funext nbrs i
  exact forIn_ite_yield _ _ _ _

/-- One step of `fusedNbrs` on the pair `(i, j)`. -/
def fusedStep (rb : Array (List ℕ)) (nbrs : Array (List ℕ)) (p : ℕ × ℕ) : Array (List ℕ) :=
  if fusedPair rb p.1 p.2 then (nbrs.modify p.1 (· ++ [p.2])).modify p.2 (· ++ [p.1]) else nbrs

/-- The pairs `fusedNbrs` visits: `(i, j)` with `i < j < n`. -/
def fusedPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ (List.range' (i + 1) (n - (i + 1))).map fun j ↦ (i, j)

lemma mem_fusedPairs {n : ℕ} {p : ℕ × ℕ} : p ∈ fusedPairs n ↔ p.1 < p.2 ∧ p.2 < n := by
  obtain ⟨a, b⟩ := p
  simp only [fusedPairs, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_range'_1,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i, hi, j, ⟨hj1, hj2⟩, rfl, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨a, by omega, b, ⟨by omega, by omega⟩, rfl, rfl⟩

lemma getElem!_modify_list (a : Array (List ℕ)) (k : ℕ) (f : List ℕ → List ℕ) {i : ℕ}
    (hi : i < a.size) : (a.modify k f)[i]! = if k = i then f a[i]! else a[i]! := by
  rw [getElem!_pos (a.modify k f) i (by simpa using hi), getElem!_pos a i hi,
    Array.getElem_modify]

lemma fusedNbrs_eq_pairs (rb : Array (List ℕ)) :
    fusedNbrs rb = (fusedPairs rb.size).foldl (fusedStep rb) (Array.replicate rb.size []) := by
  rw [fusedNbrs_eq_foldl, fusedPairs, List.foldl_flatMap]
  congr 1
  funext nbrs i
  rw [List.foldl_map]
  rfl

lemma size_foldl_fusedStep (rb : Array (List ℕ)) :
    ∀ (P : List (ℕ × ℕ)) (nbrs : Array (List ℕ)), (P.foldl (fusedStep rb) nbrs).size = nbrs.size
  | [], _ => rfl
  | p :: P, nbrs => by
    rw [List.foldl_cons, size_foldl_fusedStep rb P]
    unfold fusedStep; split <;> simp

lemma mem_foldl_fusedStep (rb : Array (List ℕ)) {n : ℕ} :
    ∀ (P : List (ℕ × ℕ)) (nbrs : Array (List ℕ)), nbrs.size = n →
      (∀ p ∈ P, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) → ∀ i < n, ∀ j,
        j ∈ (P.foldl (fusedStep rb) nbrs)[i]! ↔ j ∈ nbrs[i]! ∨
          ∃ p ∈ P, fusedPair rb p.1 p.2 = true ∧ ((p.1 = i ∧ p.2 = j) ∨ (p.2 = i ∧ p.1 = j))
  | [], nbrs, _, _, i, _, j => by simp
  | p :: P, nbrs, hn, hP, i, hi, j => by
    rw [List.foldl_cons]
    obtain ⟨hp1, hp2, hp12⟩ := hP p List.mem_cons_self
    have hstep : ∀ i < n, ∀ j, j ∈ (fusedStep rb nbrs p)[i]! ↔ j ∈ nbrs[i]! ∨
        (fusedPair rb p.1 p.2 = true ∧ ((p.1 = i ∧ p.2 = j) ∨ (p.2 = i ∧ p.1 = j))) := by
      intro i hi j
      unfold fusedStep
      split
      · rename_i hf
        rw [getElem!_modify_list _ _ _ (by simpa [hn] using hi),
          getElem!_modify_list _ _ _ (by omega)]
        by_cases h1 : p.1 = i <;> by_cases h2 : p.2 = i
        · omega
        · simp only [if_pos h1, if_neg h2, List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | rfl)
            · exact .inl (h1 ▸ h)
            · exact .inr ⟨hf, .inl ⟨h1, rfl⟩⟩
          · rintro (h | ⟨-, ⟨-, rfl⟩ | ⟨h, -⟩⟩)
            · exact .inl (h1 ▸ h)
            · exact .inr rfl
            · exact absurd h h2
        · simp only [if_neg h1, if_pos h2, List.mem_append, List.mem_singleton]
          constructor
          · rintro (h | rfl)
            · exact .inl (h2 ▸ h)
            · exact .inr ⟨hf, .inr ⟨h2, rfl⟩⟩
          · rintro (h | ⟨-, ⟨h, -⟩ | ⟨-, rfl⟩⟩)
            · exact .inl (h2 ▸ h)
            · exact absurd h h1
            · exact .inr rfl
        · simp only [if_neg h1, if_neg h2]
          constructor
          · exact .inl
          · rintro (h | ⟨-, ⟨h, -⟩ | ⟨h, -⟩⟩)
            · exact h
            · exact absurd h h1
            · exact absurd h h2
      · rename_i hf
        simp [hf]
    rw [mem_foldl_fusedStep rb P _ (by unfold fusedStep; split <;> simp [hn])
      (fun q hq ↦ hP q (List.mem_cons_of_mem _ hq)) i hi j, hstep i hi j]
    constructor
    · rintro ((h | h) | ⟨q, hq, hq'⟩)
      · exact .inl h
      · exact .inr ⟨p, List.mem_cons_self, h⟩
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, hq'⟩
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact .inl (.inl h)
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact .inl (.inr hq')
        · exact .inr ⟨q, hq, hq'⟩

/-- **The fused-neighbour graph**: `j` neighbours `i` when both are rings, different, and fused
(read from the smaller index). -/
lemma mem_fusedNbrs (rb : Array (List ℕ)) (i j : ℕ) :
    j ∈ (fusedNbrs rb)[i]! ↔ i < rb.size ∧ j < rb.size ∧
      ((i < j ∧ fusedPair rb i j = true) ∨ (j < i ∧ fusedPair rb j i = true)) := by
  rw [fusedNbrs_eq_pairs]
  by_cases hi : i < rb.size
  · rw [mem_foldl_fusedStep rb (fusedPairs rb.size) _ (by simp)
      (fun p hp ↦ by rw [mem_fusedPairs] at hp; omega) i hi j]
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate]
    simp only [List.not_mem_nil, false_or, mem_fusedPairs]
    constructor
    · rintro ⟨⟨a, b⟩, ⟨hab, hb⟩, hf, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
      · exact ⟨hi, hb, .inl ⟨hab, hf⟩⟩
      · exact ⟨hi, by omega, .inr ⟨hab, hf⟩⟩
    · rintro ⟨-, hj, (⟨hij, hf⟩ | ⟨hji, hf⟩)⟩
      · exact ⟨(i, j), ⟨hij, hj⟩, hf, .inl ⟨rfl, rfl⟩⟩
      · exact ⟨(j, i), ⟨hji, hi⟩, hf, .inr ⟨rfl, rfl⟩⟩
  · rw [getElem!_neg _ i (by rw [size_foldl_fusedStep]; simpa using hi)]
    simp only [hi, false_and, iff_false]
    exact List.not_mem_nil

/-! ### The connectivity test of a group of rings -/

/-- One sweep of `isConnectedSet`: every neighbour in `S` of the rings seen at its start is
added once. -/
def connRound (S : List ℕ) (nbrs : Array (List ℕ)) (seen : List ℕ) : List ℕ :=
  seen.foldl (fun sn r ↦ (nbrs[r]!).foldl (fun sn v ↦
    if S.contains v && !sn.contains v then sn ++ [v] else sn) sn) seen

lemma isConnectedSet_eq (rids : List ℕ) (nbrs : Array (List ℕ)) :
    isConnectedSet rids nbrs = match rids.head? with
      | none => true
      | some first => (rids.foldl (fun sn _ ↦ connRound rids nbrs sn) [first]).length ==
          rids.length := by
  unfold isConnectedSet
  cases h : rids.head? with
  | none => rfl
  | some first =>
    simp only [Id.run, bind_pure_comp, map_pure, List.forIn_yield_eq_foldlM, id_map']
    change ((List.foldlM _ [first] rids : Id (List ℕ)).run.length == rids.length) = _
    rw [foldlM_id]
    congr 2
    congr 1
    funext sn _
    rw [foldlM_id]
    unfold connRound
    congr 1
    funext sn' r
    exact forIn_ite_yield' _ _ (fun v sn ↦ rids.contains v && !sn.contains v) (fun v sn ↦ sn ++ [v])

/-- One ring's neighbours in a sweep. -/
def connInner (S : List ℕ) (vs sn : List ℕ) : List ℕ :=
  vs.foldl (fun sn v ↦ if S.contains v && !sn.contains v then sn ++ [v] else sn) sn

lemma connInner_spec (S : List ℕ) :
    ∀ (vs sn : List ℕ), sn.Nodup →
      (∃ e, connInner S vs sn = sn ++ e) ∧ (connInner S vs sn).Nodup ∧
      (∀ v ∈ connInner S vs sn, v ∈ sn ∨ (v ∈ S ∧ v ∈ vs)) ∧
      ∀ v ∈ vs, v ∈ S → v ∈ connInner S vs sn
  | [], sn, hn => ⟨⟨[], by simp [connInner]⟩, hn, fun v hv ↦ .inl hv, by simp⟩
  | x :: vs, sn, hn => by
    have hstep : ∃ sn', (if S.contains x && !sn.contains x then sn ++ [x] else sn) = sn' ∧
        (∃ e, sn' = sn ++ e) ∧ sn'.Nodup ∧ (∀ v ∈ sn', v ∈ sn ∨ (v ∈ S ∧ v = x)) ∧
        (x ∈ S → x ∈ sn') := by
      split
      · rename_i hc
        rw [Bool.and_eq_true] at hc
        have hxS : x ∈ S := List.contains_iff_mem.1 hc.1
        have hxn : x ∉ sn := fun h ↦ by
          have := List.contains_iff_mem.2 h
          rw [this] at hc
          simp at hc
        refine ⟨_, rfl, ⟨[x], rfl⟩, ?_, fun v hv ↦ ?_, fun _ ↦ by simp⟩
        · refine List.nodup_append.2 ⟨hn, by simp, fun a ha b hb ↦ ?_⟩
          rw [List.mem_singleton] at hb
          subst hb
          exact fun h ↦ hxn (h ▸ ha)
        · rcases List.mem_append.1 hv with h | h
          · exact .inl h
          · rw [List.mem_singleton] at h
            subst h
            exact .inr ⟨hxS, rfl⟩
      · rename_i hc
        refine ⟨_, rfl, ⟨[], by simp⟩, hn, fun v hv ↦ .inl hv, fun hx ↦ ?_⟩
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and,
          Bool.not_eq_false, List.contains_eq_mem, decide_eq_true_eq] at hc
        by_contra h
        exact absurd (hc hx) (by simpa using h)
    obtain ⟨sn', hsn', ⟨e1, he1⟩, hnd', hmem', hx'⟩ := hstep
    have hc : connInner S (x :: vs) sn = connInner S vs sn' := by
      unfold connInner; rw [List.foldl_cons, hsn']
    obtain ⟨⟨e2, he2⟩, hnd, hmem, hall⟩ := connInner_spec S vs sn' hnd'
    rw [hc]
    refine ⟨⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, hnd, fun v hv ↦ ?_, fun v hv hvS ↦ ?_⟩
    · rcases hmem v hv with h | ⟨h1, h2⟩
      · rcases hmem' v h with h | ⟨h1, rfl⟩
        · exact .inl h
        · exact .inr ⟨h1, List.mem_cons_self⟩
      · exact .inr ⟨h1, List.mem_cons_of_mem _ h2⟩
    · rcases List.mem_cons.1 hv with rfl | hv
      · rw [he2]; exact List.mem_append_left _ (hx' hvS)
      · exact hall v hv hvS

lemma connOuter_spec (S : List ℕ) (nbrs : Array (List ℕ)) :
    ∀ (L sn : List ℕ), sn.Nodup →
      (∃ e, L.foldl (fun sn r ↦ connInner S (nbrs[r]!) sn) sn = sn ++ e) ∧
      (L.foldl (fun sn r ↦ connInner S (nbrs[r]!) sn) sn).Nodup ∧
      (∀ v ∈ L.foldl (fun sn r ↦ connInner S (nbrs[r]!) sn) sn,
        v ∈ sn ∨ (v ∈ S ∧ ∃ r ∈ L, v ∈ nbrs[r]!)) ∧
      ∀ r ∈ L, ∀ v ∈ nbrs[r]!, v ∈ S → v ∈ L.foldl (fun sn r ↦ connInner S (nbrs[r]!) sn) sn
  | [], sn, hn => ⟨⟨[], by simp⟩, hn, fun v hv ↦ .inl hv, by simp⟩
  | r :: L, sn, hn => by
    obtain ⟨⟨e1, he1⟩, hnd1, hmem1, hall1⟩ := connInner_spec S (nbrs[r]!) sn hn
    obtain ⟨⟨e2, he2⟩, hnd2, hmem2, hall2⟩ := connOuter_spec S nbrs L _ hnd1
    rw [List.foldl_cons]
    refine ⟨⟨e1 ++ e2, by rw [he2, he1, List.append_assoc]⟩, hnd2, fun v hv ↦ ?_,
      fun r' hr' v hv hvS ↦ ?_⟩
    · rcases hmem2 v hv with h | ⟨h1, r', hr', h2⟩
      · rcases hmem1 v h with h | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨h1, r, List.mem_cons_self, h2⟩
      · exact .inr ⟨h1, r', List.mem_cons_of_mem _ hr', h2⟩
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · rw [he2]; exact List.mem_append_left _ (hall1 v hv hvS)
      · exact hall2 r' hr' v hv hvS

lemma connRound_eq (S : List ℕ) (nbrs : Array (List ℕ)) (seen : List ℕ) :
    connRound S nbrs seen = seen.foldl (fun sn r ↦ connInner S (nbrs[r]!) sn) seen := rfl

/-- **One sweep of the connectivity test**: it appends, adds no repeat, adds only neighbours in
`S` of the rings seen at its start, and adds all of them. -/
lemma connRound_spec (S : List ℕ) (nbrs : Array (List ℕ)) {seen : List ℕ} (hn : seen.Nodup) :
    (∃ e, connRound S nbrs seen = seen ++ e) ∧ (connRound S nbrs seen).Nodup ∧
      (∀ v ∈ connRound S nbrs seen, v ∈ seen ∨ (v ∈ S ∧ ∃ r ∈ seen, v ∈ nbrs[r]!)) ∧
      ∀ r ∈ seen, ∀ v ∈ nbrs[r]!, v ∈ S → v ∈ connRound S nbrs seen := by
  rw [connRound_eq]
  exact connOuter_spec S nbrs seen seen hn

/-- `v` is reached from `a` through rings of `S`, by neighbour steps. -/
def GroupReach (S : List ℕ) (nbrs : Array (List ℕ)) (a v : ℕ) : Prop :=
  Relation.ReflTransGen (fun x y ↦ y ∈ S ∧ y ∈ nbrs[x]!) a v

/-- What `k` sweeps from `[first]` have: no repeat, all in `S`, all reached, `first` kept, and
either nothing more to add or at least `k + 1` rings. -/
lemma connRounds_spec (S : List ℕ) (nbrs : Array (List ℕ)) {first : ℕ} (hf : first ∈ S) :
    ∀ k : ℕ, let seen := (List.range k).foldl (fun sn _ ↦ connRound S nbrs sn) [first]
      seen.Nodup ∧ (∀ v ∈ seen, v ∈ S ∧ GroupReach S nbrs first v) ∧ first ∈ seen ∧
      ((∀ r ∈ seen, ∀ v ∈ nbrs[r]!, v ∈ S → v ∈ seen) ∨ k + 1 ≤ seen.length)
  | 0 => by
    simp only [List.range_zero, List.foldl_nil, List.nodup_singleton, List.mem_singleton,
      forall_eq, List.length_singleton, zero_add, le_refl, or_true, and_true, true_and]
    exact ⟨hf, .refl⟩
  | k + 1 => by
    intro seen
    obtain ⟨hnd, hin, hfirst, hclo⟩ := connRounds_spec S nbrs hf k
    set s0 := (List.range k).foldl (fun sn _ ↦ connRound S nbrs sn) [first] with hs0
    have hseen : seen = connRound S nbrs s0 := by
      simp only [seen, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hs0]
    rw [hseen]
    obtain ⟨⟨e, he⟩, hnd', hmem', hall'⟩ := connRound_spec S nbrs hnd
    refine ⟨hnd', fun v hv ↦ ?_, by rw [he]; exact List.mem_append_left _ hfirst, ?_⟩
    · rcases hmem' v hv with h | ⟨hvS, r, hr, hv'⟩
      · exact hin v h
      · exact ⟨hvS, (hin r hr).2.tail ⟨hvS, hv'⟩⟩
    · by_cases he0 : e = []
      · subst he0
        rw [List.append_nil] at he
        left
        intro r hr v hv hvS
        exact hall' r (he ▸ hr) v hv hvS
      · rcases hclo with hc | hc
        · -- closed already: nothing could be added
          exfalso
          obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil e he0
          have hxr : x ∈ connRound S nbrs s0 := by rw [he]; exact List.mem_append_right _ hx
          have hxs : x ∈ s0 := by
            rcases hmem' x hxr with h | ⟨hxS, r, hr, h⟩
            · exact h
            · exact hc r hr x h hxS
          rw [he] at hnd'
          exact (List.nodup_append.1 hnd').2.2 x hxs x hx rfl
        · right
          rw [he, List.length_append]
          have : 1 ≤ e.length := List.length_pos_iff.2 he0
          omega

/-- **The connectivity test of a group of rings**: it passes exactly when the group has no
repeat and every ring of it is reached from the first through rings of the group. -/
theorem isConnectedSet_iff (rids : List ℕ) (nbrs : Array (List ℕ)) :
    isConnectedSet rids nbrs = true ↔ ∀ first, rids.head? = some first →
      rids.Nodup ∧ ∀ v ∈ rids, GroupReach rids nbrs first v := by
  rw [isConnectedSet_eq]
  cases h : rids.head? with
  | none => simp
  | some first =>
    have hf : first ∈ rids := List.mem_of_mem_head? h
    have hk : List.foldl (fun sn _ ↦ connRound rids nbrs sn) [first] rids =
        (List.range rids.length).foldl (fun sn _ ↦ connRound rids nbrs sn) [first] := by
      have : ∀ (l l' : List ℕ), l.length = l'.length → ∀ s : List ℕ,
          l.foldl (fun sn _ ↦ connRound rids nbrs sn) s =
            l'.foldl (fun sn _ ↦ connRound rids nbrs sn) s := by
        intro l
        induction l with
        | nil => intro l' hl s; rw [List.length_eq_zero_iff.1 hl.symm]
        | cons x l ih =>
          intro l' hl s
          obtain ⟨y, l'', rfl⟩ := List.exists_cons_of_length_eq_add_one hl.symm
          rw [List.foldl_cons, List.foldl_cons]
          exact ih l'' (by simpa using hl) _
      exact this _ _ (by simp) _
    dsimp only
    rw [hk]
    obtain ⟨hnd, hin, hfirst, hclo⟩ := connRounds_spec rids nbrs hf rids.length
    set seen := (List.range rids.length).foldl (fun sn _ ↦ connRound rids nbrs sn) [first]
      with hseen
    have hsub : seen ⊆ rids := fun v hv ↦ (hin v hv).1
    have hle : seen.length ≤ rids.length := by
      have := (List.subperm_of_subset hnd hsub).length_le
      exact this
    have hclosed : ∀ r ∈ seen, ∀ v ∈ nbrs[r]!, v ∈ rids → v ∈ seen := by
      rcases hclo with hc | hc
      · exact hc
      · omega
    have hreach : ∀ v, GroupReach rids nbrs first v → v ∈ seen := by
      intro v hv
      induction hv with
      | refl => exact hfirst
      | tail _ hstep ih => exact hclosed _ ih _ hstep.2 hstep.1
    simp only [beq_iff_eq, Option.some.injEq, forall_eq']
    constructor
    · intro hlen
      have hp : seen.Perm rids := (List.subperm_of_subset hnd hsub).perm_of_length_le (by omega)
      refine ⟨hp.nodup_iff.1 hnd, fun v hv ↦ (hin v (hp.mem_iff.2 hv)).2⟩
    · rintro ⟨hrn, hall⟩
      have hp : rids.Perm seen :=
        (List.subperm_of_subset hrn fun v hv ↦ hreach v (hall v hv)).perm_of_length_le hle
      exact hp.length_eq.symm

/-! ### A group of rings, in any order -/

lemma GroupReach.mem {S : List ℕ} {nbrs : Array (List ℕ)} {a v : ℕ} (ha : a ∈ S)
    (h : GroupReach S nbrs a v) : v ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hs _ => exact hs.1

lemma GroupReach.congr {S S' : List ℕ} {nbrs : Array (List ℕ)} (hS : ∀ x, x ∈ S ↔ x ∈ S')
    {a v : ℕ} (h : GroupReach S nbrs a v) : GroupReach S' nbrs a v := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨(hS _).1 hs.1, hs.2⟩

/-- With symmetric neighbours, a path inside `S` from a ring of `S` runs back. -/
lemma GroupReach.symm {S : List ℕ} {nbrs : Array (List ℕ)}
    (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) {a v : ℕ} (ha : a ∈ S)
    (h : GroupReach S nbrs a v) : GroupReach S nbrs v a := by
  induction h with
  | refl => exact .refl
  | @tail x y hxy hs ih =>
    exact Relation.ReflTransGen.head ⟨GroupReach.mem ha hxy, hsym _ _ hs.2⟩ ih

/-- **Connectivity does not depend on where the test starts**, with symmetric neighbours. -/
lemma isConnectedSet_perm {rids rids' : List ℕ} {nbrs : Array (List ℕ)}
    (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) (hp : rids.Perm rids') :
    isConnectedSet rids' nbrs = isConnectedSet rids nbrs := by
  have hS : ∀ x, x ∈ rids ↔ x ∈ rids' := fun x ↦ hp.mem_iff
  -- connected from one ring of the group means connected from any
  have key : ∀ {L L' : List ℕ}, L.Perm L' → isConnectedSet L nbrs = true →
      isConnectedSet L' nbrs = true := by
    intro L L' hLL h
    rw [isConnectedSet_iff] at h ⊢
    intro f' hf'
    cases hL : L.head? with
    | none =>
      rw [List.head?_eq_none_iff] at hL
      subst hL
      rw [List.nil_perm] at hLL
      subst hLL
      cases hf'
    | some f =>
      obtain ⟨hnd, hall⟩ := h f hL
      have hfL : f ∈ L := List.mem_of_mem_head? hL
      have hf'L : f' ∈ L := hLL.mem_iff.2 (List.mem_of_mem_head? hf')
      refine ⟨hLL.nodup_iff.1 hnd, fun v hv ↦ ?_⟩
      have h1 : GroupReach L nbrs f' f := (hall f' hf'L).symm hsym hfL
      have h2 : GroupReach L nbrs f v := hall v (hLL.mem_iff.2 hv)
      exact GroupReach.congr (fun x ↦ hLL.mem_iff) (Relation.ReflTransGen.trans h1 h2)
  cases h1 : isConnectedSet rids nbrs <;> cases h2 : isConnectedSet rids' nbrs
  · rfl
  · exact absurd (key hp.symm h2) (by simp [h1])
  · exact absurd (key hp h1) (by simp [h2])
  · rfl

/-- **A group of fused rings makes the same bonds aromatic in any order.** -/
lemma groupBonds_perm {numAtoms : ℕ} {rb C : Array (List ℕ)} {d : Array Donor}
    {nbrs : Array (List ℕ)} (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) {cur cur' : List ℕ}
    (hp : cur.Perm cur') :
    groupBonds numAtoms rb C d nbrs cur' = groupBonds numAtoms rb C d nbrs cur := by
  unfold groupBonds
  rw [isConnectedSet_perm hsym hp]
  have hcount : cur'.foldl (fun acc r ↦ C[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)
      (Array.replicate numAtoms 0) =
      cur.foldl (fun acc r ↦ C[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)
      (Array.replicate numAtoms 0) := by
    refine (hp.symm.foldl_eq' (fun x _ y _ z ↦ ?_) _)
    rw [← List.foldl_append, ← List.foldl_append]
    exact foldl_count_perm List.perm_append_comm z
  have hall : (cur'.flatMap (rb[·]!)).Perm (cur.flatMap (rb[·]!)) := hp.symm.flatMap_right _
  simp only [hcount, mergeSort_eraseDups_perm hall, hall.count_eq]

/-! ### Groups of rings of one size -/

lemma pairwise_lt_range_n (n : ℕ) : (List.range n).Pairwise (· < ·) := by
  rw [List.range_eq_range']
  exact List.pairwise_lt_range' 1 (by omega)

/-- A list is a sublist of `[0, n)` exactly when it is strictly increasing with entries below
`n`. -/
lemma sublist_range_iff {n : ℕ} {l : List ℕ} :
    l.Sublist (List.range n) ↔ l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < n := by
  constructor
  · intro h
    exact ⟨(pairwise_lt_range_n n).sublist h, fun x hx ↦ List.mem_range.1 (h.subset hx)⟩
  · rintro ⟨hp, hl⟩
    refine List.sublist_of_subperm_of_pairwise (r := (· < ·)) ?_ hp (pairwise_lt_range_n n)
    exact List.subperm_of_subset (hp.imp Nat.ne_of_lt) fun x hx ↦ List.mem_range.2 (hl x hx)

/-- **`combinations n k` lists the strictly increasing lists of `k` entries below `n`.** -/
lemma mem_combinations {n : ℕ} : ∀ {k : ℕ} {c : List ℕ},
    c ∈ combinations n k ↔ c.length = k ∧ c.Pairwise (· < ·) ∧ ∀ x ∈ c, x < n
  | 0, c => by
    simp only [combinations, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -, -⟩; exact List.eq_nil_of_length_eq_zero h
  | k + 1, c => by
    simp only [combinations, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨c0, hc0, d, hd, rfl⟩
      obtain ⟨hl, hp, hlt⟩ := mem_combinations.1 hc0
      -- the new entry is past every entry of `c0`
      have hgt : ∀ y ∈ c0, y < (match c0.getLast? with | some x => x + 1 | none => 0) + d := by
        intro y hy
        cases hlast : c0.getLast? with
        | none => rw [List.getLast?_eq_none_iff] at hlast; subst hlast; cases hy
        | some z =>
          have hz : z ∈ c0 := List.mem_of_getLast? hlast
          have hyz : y ≤ z := by
            obtain ⟨c1, rfl⟩ := List.getLast?_eq_some_iff.1 hlast
            rcases List.mem_append.1 hy with hy | hy
            · exact Nat.le_of_lt (List.pairwise_append.1 hp |>.2.2 y hy z (by simp))
            · simp at hy; omega
          simp only
          omega
      refine ⟨by simp [hl], List.pairwise_append.2 ⟨hp, by simp, fun a ha b hb ↦ ?_⟩,
        fun x hx ↦ ?_⟩
      · rw [List.mem_singleton] at hb; subst hb; exact hgt a ha
      · rcases List.mem_append.1 hx with hx | hx
        · exact hlt x hx
        · rw [List.mem_singleton] at hx; subst hx
          cases hlast : c0.getLast? <;> simp only [hlast] at hd ⊢ <;> omega
    · rintro ⟨hl, hp, hlt⟩
      obtain ⟨c0, x, rfl⟩ : ∃ c0 x, c = c0 ++ [x] := by
        rcases List.eq_nil_or_concat c with h | ⟨c0, x, h⟩
        · subst h; simp at hl
        · exact ⟨c0, x, by rw [h, List.concat_eq_append]⟩
      rw [List.pairwise_append] at hp
      have hx : x < n := hlt x (by simp)
      refine ⟨c0, mem_combinations.2 ⟨by simpa using hl, hp.1,
        fun y hy ↦ hlt y (by simp [hy])⟩, ?_⟩
      cases hlast : c0.getLast? with
      | none =>
        refine ⟨x, by simp only; omega, by simp⟩
      | some z =>
        have hzx : z < x := hp.2.2 z (List.mem_of_getLast? hlast) x (by simp)
        refine ⟨x - (z + 1), by simp only; omega, ?_⟩
        simp only
        congr 2
        omega

/-- Picking positions out of `F` by a sublist of `[0, |F|)`, and every sublist of `F` so. -/
lemma sublist_iff_positions (F : List ℕ) (G : List ℕ) :
    G.Sublist F ↔ ∃ c : List ℕ, c.Sublist (List.range F.length) ∧ c.map (F[·]!) = G := by
  constructor
  · intro h
    induction h with
    | slnil => exact ⟨[], by simp, rfl⟩
    | @cons l₁ l₂ a _ ih =>
      obtain ⟨c, hc, hcG⟩ := ih
      refine ⟨c.map (· + 1), ?_, ?_⟩
      · rw [List.length_cons, List.range_succ_eq_map]
        exact (hc.map _).cons _
      · rw [List.map_map, ← hcG]
        apply List.map_congr_left
        intro x _
        simp
    | @cons_cons l₁ l₂ a _ ih =>
      obtain ⟨c, hc, hcG⟩ := ih
      refine ⟨0 :: c.map (· + 1), ?_, ?_⟩
      · rw [List.length_cons, List.range_succ_eq_map]
        exact (hc.map _).cons_cons _
      · rw [List.map_cons, List.map_map, ← hcG]
        simp only [getElem!_pos (a :: l₂) 0 (by simp), List.getElem_cons_zero, List.cons.injEq,
          true_and]
        apply List.map_congr_left
        intro x _
        simp
  · rintro ⟨c, hc, rfl⟩
    have hF : (List.range F.length).map (F[·]!) = F := by
      apply List.ext_getElem (by simp)
      intro i h1 h2
      simp [getElem!_def, List.getElem?_eq_getElem h2]
    have := hc.map (F[·]!)
    rwa [hF] at this

end Work

end LeanSMILES.Aromaticity
