/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Passes

/-! # LeanSMILES.Aromaticity.PerceiveFacts

Where the bonds `setAromaticity` makes aromatic come from. -/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-! ### Reading arrays -/

/-- Reading a `Bool` array after `set!`: an out-of-range write changes nothing. -/
lemma getElem!_set!_bool (a : Array Bool) (i j : ℕ) (v : Bool) :
    (a.set! i v)[j]! = if i = j ∧ j < a.size then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj]
    simp [Array.set!, Array.getElem_setIfInBounds, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    simp [hj]

/-- Reading an all-`false` array. -/
lemma getElem!_replicate_false (n j : ℕ) : (Array.replicate n false)[j]! = false := by
  by_cases hj : j < n
  · rw [getElem!_pos _ j (by simpa using hj)]
    simp
  · rw [getElem!_neg _ j (by simpa using hj)]
    rfl

/-! ### `markAromatic` -/

/-- `markAromatic` at `b` leaves every other bond as it was. -/
lemma getElem?_markAromatic_bonds (w : Work) {b k : ℕ} (h : b ≠ k) :
    (w.markAromatic b).bonds[k]? = w.bonds[k]? := by
  unfold markAromatic
  dsimp only
  split
  · simp only [modifyAtom_bonds, getElem?_setKind_bonds, if_neg h]
  · rfl

/-- A fold of `markAromatic` over `l` leaves every bond not in `l` as it was. -/
lemma getElem?_foldl_markAromatic_bonds (l : List ℕ) (w : Work) {k : ℕ} (hk : k ∉ l) :
    (l.foldl markAromatic w).bonds[k]? = w.bonds[k]? := by
  induction l generalizing w with
  | nil => rfl
  | cons a l ih =>
    rw [List.mem_cons, not_or] at hk
    rw [List.foldl_cons, ih _ hk.2, getElem?_markAromatic_bonds _ (Ne.symm hk.1)]

/-- A bond `setAromaticity` makes aromatic is in `aromaticBondList`. -/
lemma mem_aromaticBondList_of_kind? (w : Work) (rings : Array (List ℕ)) {b : ℕ}
    (h : (w.setAromaticity rings).kind? b = some .aromatic) (h0 : w.kind? b ≠ some .aromatic) :
    b ∈ w.aromaticBondList rings := by
  by_contra hb
  apply h0
  rw [← h]
  simp only [kind?, setAromaticity, getElem?_foldl_markAromatic_bonds _ _ hb]

/-! ### `fusedBonds` -/

/-- A bond of `groupBonds` is a bond of one of the rings. -/
lemma mem_groupBonds {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {donor : Array Donor}
    {nbrs : Array (List ℕ)} {cur : List ℕ} {b : ℕ}
    (h : b ∈ groupBonds numAtoms rbonds candRings donor nbrs cur) : ∃ r : ℕ, b ∈ rbonds[r]! := by
  unfold groupBonds at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rw [List.mem_filter, List.mem_mergeSort, List.mem_eraseDups, List.mem_flatMap] at h
      obtain ⟨⟨r, -, hr⟩, -⟩ := h
      exact ⟨r, hr⟩
    · simp at h

/-- A bond of `systemBonds` is a bond of one of the rings. -/
lemma mem_systemBonds {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {donor : Array Donor}
    {nbrs : Array (List ℕ)} {fused : List ℕ} {b : ℕ}
    (h : b ∈ systemBonds numAtoms rbonds candRings donor nbrs fused) :
    ∃ r : ℕ, b ∈ rbonds[r]! := by
  unfold systemBonds at h
  dsimp only at h
  refine foldl_induction (fun st : List ℕ × List ℕ × Bool ↦ ∀ b ∈ st.1, ∃ r : ℕ, b ∈ rbonds[r]!)
    _ _ _ (by simp) ?_ b h
  rintro ⟨out, done, stop⟩ size - hst
  dsimp only at hst ⊢
  split
  · exact hst
  · intro b hb
    rw [List.mem_append, List.mem_flatMap] at hb
    rcases hb with hb | ⟨comb, -, hb⟩
    · exact hst b hb
    · exact mem_groupBonds hb

/-- A bond of `fusedBonds` is a bond of one of the rings. -/
lemma mem_fusedBonds {numAtoms : ℕ} {rbonds candRings : Array (List ℕ)} {donor : Array Donor}
    {b : ℕ} (h : b ∈ fusedBonds numAtoms rbonds candRings donor) : ∃ r : ℕ, b ∈ rbonds[r]! := by
  unfold fusedBonds at h
  obtain ⟨fused, -, hb⟩ := List.mem_flatMap.1 h
  exact mem_systemBonds hb

/-! ### `ringBonds` -/

/-- The bond `bondBetween?` finds joins its two atoms. -/
lemma bondBetween?_eq_some {w : Work} {i j k : ℕ} (h : w.bondBetween? i j = some k) :
    ∃ hk : k < w.bonds.size, (w.bonds[k].src = i ∧ w.bonds[k].dst = j) ∨
      (w.bonds[k].src = j ∧ w.bonds[k].dst = i) := by
  unfold bondBetween? at h
  have hk : k < w.bonds.size := List.mem_range.1 (List.mem_of_find?_eq_some h)
  have hp := List.find?_some h
  rw [getElem!_pos w.bonds k hk] at hp
  refine ⟨hk, ?_⟩
  simpa using hp

/-- Both atoms of a bond of `ringBonds ring` are in `ring`. -/
lemma mem_ringBonds {w : Work} {ring : List ℕ} {k : ℕ} (h : k ∈ w.ringBonds ring) :
    ∃ hk : k < w.bonds.size, w.bonds[k].src ∈ ring ∧ w.bonds[k].dst ∈ ring := by
  unfold ringBonds at h
  obtain ⟨t, ht, hb⟩ := List.mem_filterMap.1 h
  rw [List.mem_range] at ht
  obtain ⟨hk, hsd⟩ := bondBetween?_eq_some hb
  have h1 : ring[t]! ∈ ring := by
    rw [getElem!_pos ring t ht]
    exact List.getElem_mem ht
  have h2 : ring[(t + 1) % ring.length]! ∈ ring := by
    have h' : (t + 1) % ring.length < ring.length := Nat.mod_lt _ (by omega)
    rw [getElem!_pos ring _ h']
    exact List.getElem_mem h'
  refine ⟨hk, ?_⟩
  rcases hsd with ⟨hs, hd⟩ | ⟨hs, hd⟩
  · rw [hs, hd]
    exact ⟨h1, h2⟩
  · rw [hs, hd]
    exact ⟨h2, h1⟩

/-! ### `donorData` -/

/-- What every step of `donorData` keeps: `cand` and `seen` have the same size, and a candidate
atom has been seen and is an aromatic candidate for some donor type. -/
def DonorInv (w : Work) (s : DonorState) : Prop :=
  s.cand.size = s.seen.size ∧
    ∀ j : ℕ, s.cand[j]! = true → s.seen[j]! = true ∧ ∃ d, w.isAromaticCandidate j d = true

/-- One `donorAtomStep` keeps `DonorInv`, keeps every candidate a candidate and the candidate
rings, and its flag is true only if it was and atom `i` is a candidate. -/
lemma donorAtomStep_spec (w : Work) (rbs : List ℕ) (len : ℕ) (s : DonorState) (a : Bool)
    (i : ℕ) (hs : w.DonorInv s) :
    w.DonorInv (w.donorAtomStep rbs len (s, a) i).1 ∧
      (∀ j : ℕ, s.cand[j]! = true → (w.donorAtomStep rbs len (s, a) i).1.cand[j]! = true) ∧
      (w.donorAtomStep rbs len (s, a) i).1.candRings = s.candRings ∧
      ((w.donorAtomStep rbs len (s, a) i).2 = true →
        a = true ∧ (w.donorAtomStep rbs len (s, a) i).1.cand[i]! = true) := by
  obtain ⟨hsize, hc⟩ := hs
  unfold donorAtomStep
  dsimp only
  split
  · refine ⟨⟨hsize, hc⟩, fun _ h ↦ h, rfl, ?_⟩
    simp
  · rename_i hseen
    refine ⟨⟨?_, ?_⟩, ?_, rfl, ?_⟩
    · simp [hsize]
    · intro j hj
      rw [getElem!_set!_bool] at hj ⊢
      split at hj
      · obtain ⟨rfl, hj'⟩ := ‹i = j ∧ j < s.cand.size›
        rw [if_pos ⟨rfl, hsize ▸ hj'⟩]
        exact ⟨rfl, _, hj⟩
      · obtain ⟨h1, h2⟩ := hc j hj
        refine ⟨?_, h2⟩
        split <;> simp_all
    · intro j hj
      rw [getElem!_set!_bool]
      split
      · obtain ⟨rfl, -⟩ := ‹i = j ∧ j < s.cand.size›
        exact absurd (hc _ hj).1 hseen
      · exact hj
    · intro h
      simp only [Bool.and_eq_true] at h
      exact h

/-- A fold of `donorAtomStep` over `l` keeps `DonorInv`, keeps every candidate a candidate and
the candidate rings, and its flag is true only if it was and every atom of `l` is a candidate. -/
lemma foldl_donorAtomStep_spec (w : Work) (rbs : List ℕ) (len : ℕ) (l : List ℕ)
    (s : DonorState) (a : Bool) (hs : w.DonorInv s) :
    w.DonorInv (l.foldl (w.donorAtomStep rbs len) (s, a)).1 ∧
      (∀ j : ℕ, s.cand[j]! = true → (l.foldl (w.donorAtomStep rbs len) (s, a)).1.cand[j]! = true) ∧
      (l.foldl (w.donorAtomStep rbs len) (s, a)).1.candRings = s.candRings ∧
      ((l.foldl (w.donorAtomStep rbs len) (s, a)).2 = true →
        a = true ∧ ∀ i ∈ l, (l.foldl (w.donorAtomStep rbs len) (s, a)).1.cand[i]! = true) := by
  induction l generalizing s a with
  | nil => exact ⟨hs, fun _ h ↦ h, rfl, fun h ↦ ⟨h, by simp⟩⟩
  | cons i l ih =>
    obtain ⟨h1, h2, h3, h4⟩ := w.donorAtomStep_spec rbs len s a i hs
    obtain ⟨g1, g2, g3, g4⟩ := ih _ _ h1
    refine ⟨g1, fun j hj ↦ g2 j (h2 j hj), g3.trans h3, fun hp ↦ ?_⟩
    obtain ⟨ha, hl⟩ := g4 hp
    obtain ⟨ha', hi⟩ := h4 ha
    refine ⟨ha', fun j hj ↦ ?_⟩
    rcases List.mem_cons.1 hj with rfl | hj
    · exact g2 _ hi
    · exact hl j hj

/-- What `donorData`'s fold over the rings keeps: `DonorInv`, and every candidate ring is one of
`rings` with every atom a candidate. -/
def RingInv (w : Work) (rings : Array (List ℕ)) (s : DonorState) : Prop :=
  w.DonorInv s ∧ ∀ r ∈ s.candRings, r ∈ rings.toList ∧ ∀ i ∈ r, s.cand[i]! = true

/-- `donorData` satisfies `RingInv`. -/
lemma ringInv_donorData (w : Work) (rings : Array (List ℕ)) :
    w.RingInv rings (w.donorData rings) := by
  unfold donorData
  refine foldl_induction _ _ _ _ ?_ ?_
  · refine ⟨⟨by simp, fun j hj ↦ ?_⟩, by simp⟩
    rw [getElem!_replicate_false] at hj
    exact absurd hj Bool.false_ne_true
  · intro s ring hring ⟨hs, hr⟩
    unfold donorRingStep
    obtain ⟨g1, g2, g3, g4⟩ := w.foldl_donorAtomStep_spec
      (rings.toList.flatMap w.ringBonds).eraseDups ring.length ring s true hs
    generalize ring.foldl _ (s, true) = p at g1 g2 g3 g4 ⊢
    obtain ⟨s1, ac⟩ := p
    dsimp only at g1 g2 g3 g4 ⊢
    split
    · refine ⟨g1, fun r hr' ↦ ?_⟩
      rcases Array.mem_push.1 hr' with hr' | rfl
      · rw [g3] at hr'
        obtain ⟨hr1, hr2⟩ := hr r hr'
        exact ⟨hr1, fun i hi ↦ g2 i (hr2 i hi)⟩
      · exact ⟨hring, (g4 ‹_›).2⟩
    · refine ⟨g1, fun r hr' ↦ ?_⟩
      rw [g3] at hr'
      obtain ⟨hr1, hr2⟩ := hr r hr'
      exact ⟨hr1, fun i hi ↦ g2 i (hr2 i hi)⟩

/-! ### `setAromaticity` -/

/-- A bond `setAromaticity` makes aromatic is a bond of one of the rings, and both its atoms are
aromatic candidates. -/
theorem of_kind?_setAromaticity (w : Work) (rings : Array (List ℕ)) {b : ℕ}
    (h : (w.setAromaticity rings).kind? b = some .aromatic) (h0 : w.kind? b ≠ some .aromatic) :
    ∃ bd, w.bonds[b]? = some bd ∧ b ∈ rings.toList.flatMap w.ringBonds ∧
      (∃ d, w.isAromaticCandidate bd.src d = true) ∧
        ∃ d, w.isAromaticCandidate bd.dst d = true := by
  have hb := mem_aromaticBondList_of_kind? w rings h h0
  unfold aromaticBondList at hb
  obtain ⟨r, hr⟩ := mem_fusedBonds hb
  have hr' : r < (w.donorData rings).candRings.size := by
    by_contra hlt
    rw [getElem!_neg _ r (by simpa using hlt)] at hr
    exact List.not_mem_nil hr
  rw [getElem!_pos _ r (by simpa using hr'), Array.getElem_map] at hr
  obtain ⟨hk, hsrc, hdst⟩ := mem_ringBonds hr
  obtain ⟨⟨-, hc⟩, hcr⟩ := ringInv_donorData w rings
  have hmem : (w.donorData rings).candRings[r] ∈ (w.donorData rings).candRings :=
    Array.getElem_mem hr'
  obtain ⟨hring, hall⟩ := hcr _ hmem
  exact ⟨w.bonds[b], getElem?_pos w.bonds b hk, List.mem_flatMap.2 ⟨_, hring, hr⟩,
    (hc _ (hall _ hsrc)).2, (hc _ (hall _ hdst)).2⟩

end LeanSMILES.Aromaticity.Work
