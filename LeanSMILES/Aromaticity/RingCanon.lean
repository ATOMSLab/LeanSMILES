/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingOrder
public import LeanSMILES.Aromaticity.RingBasis

/-!
# LeanSMILES.Aromaticity.RingCanon

Rings as bond sets

A ring (`Work.IsRing`) has one bond per atom and repeats none (`IsRing.ringBonds_nodup`,
`IsRing.ringBonds_length`); its bond mask has exactly those bits (`testBit_cycleMask`), so the
mask's popcount is the ring's length (`IsRing.popcount_cycleMask`). Two rings with the same bonds
are one ring, started elsewhere or run the other way (`IsRing.ringEq_of_ringBonds`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

lemma getElem!_inj {c : List ℕ} (hnd : c.Nodup) {i j : ℕ} (hi : i < c.length)
    (hj : j < c.length) (e : c[i]! = c[j]!) : i = j := by
  rw [getElem!_pos c i hi, getElem!_pos c j hj] at e
  exact (hnd.getElem_inj_iff).1 e

/-- The bond `bondBetween?` finds joins the two atoms. -/
lemma bondBetween?_ends {m : Work} {u v k : ℕ} (h : m.bondBetween? u v = some k) :
    ((m.bonds[k]! : WBond).src = u ∧ (m.bonds[k]! : WBond).dst = v) ∨
      ((m.bonds[k]! : WBond).src = v ∧ (m.bonds[k]! : WBond).dst = u) := by
  unfold bondBetween? at h
  have hp := List.find?_some h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
  exact hp

/-- A bond joins one pair of atoms. -/
lemma pair_of_bondBetween? {m : Work} {u v u' v' k : ℕ} (h : m.bondBetween? u v = some k)
    (h' : m.bondBetween? u' v' = some k) : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  have := bondBetween?_ends h
  have := bondBetween?_ends h'
  omega

/-- **A ring repeats no bond.** -/
lemma IsRing.ringBonds_nodup {m : Work} {c : List ℕ} (hc : m.IsRing c) :
    (m.ringBonds c).Nodup := by
  rw [ringBonds_eq_filterMap]
  have h3 := hc.three
  have hp : (List.range c.length).Pairwise fun t t' ↦ t < c.length ∧ t' < c.length ∧ t ≠ t' :=
    (List.nodup_range).imp_of_mem fun ht ht' hne ↦
      ⟨List.mem_range.1 ht, List.mem_range.1 ht', hne⟩
  refine List.Pairwise.filterMap _ (fun t t' ⟨ht, ht', hne⟩ k hk k' hk' e ↦ ?_) hp
  subst e
  rcases pair_of_bondBetween? hk hk' with ⟨e1, -⟩ | ⟨e1, e2⟩
  · exact hne (getElem!_inj hc.nodup ht' ht e1).symm
  · have h1 := getElem!_inj hc.nodup ht' (Nat.mod_lt _ (by omega)) e1
    have h2 := getElem!_inj hc.nodup (Nat.mod_lt _ (by omega)) ht e2
    rw [succ_mod ht] at h1
    rw [succ_mod ht'] at h2
    split_ifs at h1 h2 <;> omega

lemma length_filterMap_of_isSome {α β : Type} (f : α → Option β) :
    ∀ {l : List α}, (∀ a ∈ l, (f a).isSome) → (l.filterMap f).length = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h a List.mem_cons_self)
    rw [List.filterMap_cons, hb, List.length_cons, List.length_cons,
      length_filterMap_of_isSome f fun x hx ↦ h x (List.mem_cons_of_mem _ hx)]

/-- **A ring has one bond per atom.** -/
lemma IsRing.ringBonds_length {m : Work} {c : List ℕ} (hc : m.IsRing c) :
    (m.ringBonds c).length = c.length := by
  rw [ringBonds_eq_filterMap, length_filterMap_of_isSome, List.length_range]
  intro t ht
  obtain ⟨k, hk⟩ := bondBetween?_of_adj (hc.adj_get (List.mem_range.1 ht))
  rw [hk]
  rfl

/-- **A cycle's mask has exactly its ring bonds set.** -/
lemma testBit_cycleMask (m : Work) (c : List ℕ) (j : ℕ) :
    (m.cycleMask c).testBit j = decide (j ∈ m.ringBonds c) := by
  have key : ∀ (L : List ℕ) (init : ℕ),
      (L.foldl (fun acc t ↦ match m.bondBetween? (c[t]!) (c[(t + 1) % c.length]!) with
        | some k => acc ||| (1 <<< k)
        | none => acc) init).testBit j =
      (init.testBit j || decide (j ∈ L.filterMap fun t ↦
        m.bondBetween? (c[t]!) (c[(t + 1) % c.length]!))) := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih =>
      intro init
      rw [List.foldl_cons, ih, List.filterMap_cons]
      cases hk : m.bondBetween? (c[t]!) (c[(t + 1) % c.length]!) with
      | none => rfl
      | some k =>
        simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.mem_cons]
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h | rfl) | h)
          · exact .inl h
          · exact .inr (.inl rfl)
          · exact .inr (.inr h)
        · rintro (h | rfl | h)
          · exact .inl (.inl h)
          · exact .inl (.inr rfl)
          · exact .inr h
  exact (key _ 0).trans (by rw [ringBonds_eq_filterMap, Nat.zero_testBit, Bool.false_or])

/-- The popcount of a number is the count of its set bits. -/
lemma popcount_eq_length {v : ℕ} {S : List ℕ} (hS : S.Nodup)
    (h : ∀ j, v.testBit j = true ↔ j ∈ S) : popcount v = S.length := by
  unfold popcount
  rw [List.countP_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup (List.nodup_range.filter _) hS]
  intro j
  rw [List.mem_filter, List.mem_range, ← h j]
  constructor
  · exact fun h ↦ h.2
  · intro hj
    refine ⟨?_, hj⟩
    have h0 : v ≠ 0 := by rintro rfl; simp at hj
    have := (Nat.le_log2 h0).2 (Nat.ge_two_pow_of_testBit hj)
    omega

/-- **A ring's mask counts its atoms.** -/
lemma IsRing.popcount_cycleMask {m : Work} {c : List ℕ} (hc : m.IsRing c) :
    popcount (m.cycleMask c) = c.length := by
  rw [popcount_eq_length hc.ringBonds_nodup (fun j ↦ by rw [testBit_cycleMask]; simp),
    hc.ringBonds_length]

/-- `u` then `v` are consecutive in the ring `c` (the last atom followed by the first). -/
def REdge (c : List ℕ) (u v : ℕ) : Prop :=
  ∃ t < c.length, c[t]! = u ∧ c[(t + 1) % c.length]! = v

lemma REdge.mem_left {c : List ℕ} {u v : ℕ} (h : REdge c u v) : u ∈ c := by
  obtain ⟨t, ht, rfl, -⟩ := h
  rw [getElem!_pos c t ht]
  exact List.getElem_mem _

lemma REdge.mem_right {c : List ℕ} {u v : ℕ} (h : REdge c u v) : v ∈ c := by
  obtain ⟨t, ht, -, rfl⟩ := h
  rw [getElem!_pos c _ (Nat.mod_lt _ (by omega))]
  exact List.getElem_mem _

/-- Consecutive atoms of a ring whose bonds are among another ring's are consecutive there. -/
lemma IsRing.redge_of_sub {m : Work} {c c' : List ℕ} (hc' : m.IsRing c')
    (hsub : ∀ k ∈ m.ringBonds c', k ∈ m.ringBonds c) {u v : ℕ} (h : REdge c' u v) :
    REdge c u v ∨ REdge c v u := by
  obtain ⟨t, ht, rfl, rfl⟩ := h
  obtain ⟨k, hk⟩ := bondBetween?_of_adj (hc'.adj_get ht)
  have := hsub k (mem_ringBonds_of ht hk)
  rw [ringBonds_eq_filterMap, List.mem_filterMap] at this
  obtain ⟨t', ht', hk'⟩ := this
  rw [List.mem_range] at ht'
  rcases pair_of_bondBetween? hk' hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact .inl ⟨t', ht', e1.symm, e2.symm⟩
  · exact .inr ⟨t', ht', e2.symm, e1.symm⟩

/-- The atoms next to atom `t` of a ring are atoms `t + 1` and `t - 1` (cyclically). -/
lemma IsRing.nbr {m : Work} {c : List ℕ} (hc : m.IsRing c) {t : ℕ} (ht : t < c.length) {v : ℕ}
    (h : REdge c (c[t]!) v ∨ REdge c v (c[t]!)) :
    v = c[(t + 1) % c.length]! ∨ v = c[(t + c.length - 1) % c.length]! := by
  set n := c.length with hn
  rcases h with ⟨t', ht', e1, rfl⟩ | ⟨t', ht', rfl, e2⟩
  · rw [getElem!_inj hc.nodup ht' ht e1]
    exact .inl rfl
  · right
    have h1 := getElem!_inj hc.nodup (Nat.mod_lt _ (by omega)) ht e2
    rw [succ_mod ht'] at h1
    congr 1
    split_ifs at h1
    · have : t + n - 1 = t' + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht']
    · have : t + n - 1 = t' := by omega
      rw [this, Nat.mod_eq_of_lt ht']

/-- A ring whose consecutive pairs are among `c`'s, of the same length and starting like
`c.rotate s`, is `c.rotate s`. -/
lemma IsRing.eq_rotate {m : Work} {c c' : List ℕ} (hc : m.IsRing c) (hc' : m.IsRing c')
    (hsub : ∀ u v, REdge c' u v → REdge c u v ∨ REdge c v u) (hlen : c'.length = c.length)
    {s : ℕ} (hs : s < c.length) (h0 : c'[0]! = c[s]!) (h1 : c'[1]! = c[(s + 1) % c.length]!) :
    c' = c.rotate s := by
  set n := c.length with hn
  have h3 := hc.three
  have key : ∀ i, i + 1 < n → c'[i]! = c[(i + s) % n]! ∧ c'[i + 1]! = c[(i + 1 + s) % n]! := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [Nat.zero_add, Nat.zero_add, Nat.mod_eq_of_lt hs, Nat.add_comm 1 s]
      exact ⟨h0, h1⟩
    | succ i ih =>
      intro hi
      obtain ⟨a, b⟩ := ih (by omega)
      refine ⟨b, ?_⟩
      have he : REdge c' (c'[i + 1]!) (c'[i + 1 + 1]!) :=
        ⟨i + 1, by omega, rfl, by rw [hlen, Nat.mod_eq_of_lt (by omega)]⟩
      have hm : (i + 1 + s) % n < n := Nat.mod_lt _ (by omega)
      have := hc.nbr hm (b ▸ hsub _ _ he)
      rcases this with e | e
      · rw [e, Nat.mod_add_mod]
        congr 2
        omega
      · exfalso
        have e2 : ((i + 1 + s) % n + n - 1) % n = (i + s) % n := by
          rw [Nat.add_sub_assoc (by omega), Nat.mod_add_mod]
          have : i + 1 + s + (n - 1) = i + s + n := by omega
          rw [this, Nat.add_mod_right]
        rw [e2, ← a] at e
        have := getElem!_inj hc'.nodup (by omega) (by omega) e
        omega
  apply List.ext_getElem (by rw [List.length_rotate, hlen])
  intro i hi1 hi2
  rw [List.getElem_rotate, ← getElem!_pos c' i hi1, ← getElem!_pos c _ (Nat.mod_lt _ (by omega))]
  by_cases hi : i + 1 < n
  · exact (key i hi).1
  · have hi' : i = n - 2 + 1 := by rw [hlen] at hi1; omega
    have := (key (n - 2) (by omega)).2
    rw [← hi'] at this
    exact this

/-- **Two rings with the same bonds are one ring**, started elsewhere or run the other way. -/
theorem IsRing.ringEq_of_ringBonds {m : Work} {c c' : List ℕ} (hc : m.IsRing c)
    (hc' : m.IsRing c') (h : ∀ k, k ∈ m.ringBonds c ↔ k ∈ m.ringBonds c') : RingEq c c' := by
  have hsub : ∀ u v, REdge c' u v → REdge c u v ∨ REdge c v u :=
    fun u v ↦ hc'.redge_of_sub fun k hk ↦ (h k).2 hk
  have hsub' : ∀ u v, REdge c u v → REdge c' u v ∨ REdge c' v u :=
    fun u v ↦ hc.redge_of_sub fun k hk ↦ (h k).1 hk
  have hv : ∀ {c c' : List ℕ}, m.IsRing c' →
      (∀ u v, REdge c' u v → REdge c u v ∨ REdge c v u) → ∀ x ∈ c', x ∈ c := by
    intro c c' hc' hs x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have : REdge c' c'[t] (c'[(t + 1) % c'.length]!) := ⟨t, ht, getElem!_pos c' t ht, rfl⟩
    rcases hs _ _ this with e | e
    · exact e.mem_left
    · exact e.mem_right
  have hlen : c'.length = c.length := le_antisymm
    (List.subperm_of_subset hc'.nodup (hv hc' hsub)).length_le
    (List.subperm_of_subset hc.nodup (hv hc hsub')).length_le
  set n := c.length with hn
  have h3 := hc.three
  have h0mem : c'[0]! ∈ c := hv hc' hsub _ (by
    rw [getElem!_pos c' 0 (by omega)]; exact List.getElem_mem _)
  obtain ⟨s, hs, hs0⟩ := List.getElem_of_mem h0mem
  rw [← getElem!_pos c s hs] at hs0
  have he : REdge c' (c'[0]!) (c'[1]!) := ⟨0, by omega, rfl, by rw [Nat.mod_eq_of_lt (by omega)]⟩
  rcases hc.nbr hs (hs0 ▸ hsub _ _ he) with e | e
  · exact ⟨s, .inl (hc.eq_rotate hc' hsub hlen hs hs0.symm e)⟩
  · -- the other direction: `c'` follows `c.reverse`
    have hcr : m.IsRing c.reverse := by
      refine ⟨List.nodup_reverse.2 hc.nodup, by simpa using hc.three,
        isChain_reverse_of_symm hc.chain, ?_⟩
      intro a ha b hb
      rw [List.getLast?_reverse] at ha
      rw [List.head?_reverse] at hb
      exact (hc.close b hb a ha).symm
    have hsubr : ∀ u v, REdge c' u v → REdge c.reverse u v ∨ REdge c.reverse v u := by
      refine fun u v ↦ hc'.redge_of_sub fun k hk ↦ ?_
      exact (ringBonds_reverse m c).mem_iff.2 ((h k).2 hk)
    have hrev : ∀ i < n, c.reverse[i]! = c[n - 1 - i]! := fun i hi ↦ by
      rw [getElem!_pos _ i (by simpa using hi), getElem!_pos c _ (by omega), List.getElem_reverse]
    have hlr : c.reverse.length = n := by simp [hn]
    have hs' : n - 1 - s < c.reverse.length := by omega
    have e0 : c'[0]! = c.reverse[n - 1 - s]! := by
      rw [hrev _ (by omega), show n - 1 - (n - 1 - s) = s by omega, hs0]
    have e1 : c'[1]! = c.reverse[(n - 1 - s + 1) % c.reverse.length]! := by
      rw [e, hlr, hrev _ (Nat.mod_lt _ (by omega)), ← hn]
      congr 1
      by_cases hs0' : s = 0
      · subst hs0'
        rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega),
          show n - 1 - 0 + 1 = n by omega, Nat.mod_self, Nat.sub_zero]
      · rw [show s + n - 1 = (s - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (show s - 1 < n by omega),
          Nat.mod_eq_of_lt (show n - 1 - s + 1 < n by omega)]
        omega
    have := hcr.eq_rotate hc' hsubr (by rw [hlen, hlr]) hs' e0 e1
    rw [List.rotate_reverse] at this
    exact ⟨_, .inr this⟩

/-- **Perception reads only the ring set**, for rings (`setAromaticity_equiv`). -/
theorem setAromaticity_equiv_of_isRing (w : Work) {R R' : Array (List ℕ)}
    (h : RingsEquiv R.toList R'.toList) (hs : R.toList.Pairwise (·.length ≤ ·.length))
    (hs' : R'.toList.Pairwise (·.length ≤ ·.length)) (hr : ∀ r ∈ R.toList, w.IsRing r) :
    w.setAromaticity R' = w.setAromaticity R :=
  setAromaticity_equiv w h hs hs' fun r hr' ↦ (hr r hr').ringBonds_nodup

end Work

end LeanSMILES.Aromaticity
