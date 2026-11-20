/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingSearch

/-!
# LeanSMILES.Aromaticity.RingCands

The candidate cycles from a root, described without the numbering

`Work.cyclesFrom r` lists two kinds of cycle (`Work.Cand`): two shortest paths from `r` to bonded
atoms at the same distance, closed by their bond (`Work.OddCand`), and two shortest paths to two
different atoms one step nearer than an atom `x`, closed through `x` (`Work.EvenCand`); the paths
share only `r`. Every cycle it lists is one of these (`Work.cand_of_mem_cyclesFrom`), and every
such cycle is listed, perhaps started elsewhere and run the other way
(`Work.exists_mem_cyclesFrom_of_cand`): which way round depends on the numbering, through the test
`x < y` and the order of the neighbour list.

## Main definitions

* `Work.OddCand`, `Work.EvenCand`: the two kinds of candidate cycle from a root.
* `Work.Cand`: a candidate cycle from a root, odd or even.

## Main statements

* `Work.cand_of_mem_cyclesFrom`: every cycle `cyclesFrom` lists is a candidate.
* `Work.exists_mem_cyclesFrom_of_cand`: every candidate is listed, up to `RingEq`.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

/-- A shortest path to `w` at distance `d ≥ 1` has `w` after the root. -/
lemma PathOK.mem_tail {m : Work} {dist : Array (Option ℕ)} {r w d : ℕ} {p : List ℕ}
    (h : m.PathOK dist r w d p) (hd : 1 ≤ d) : w ∈ p.tail := by
  obtain ⟨pt, rfl, hpt⟩ := h.cons
  have hpt0 : pt ≠ [] := by rintro rfl; simp at hpt; omega
  have := h.last
  rw [getLast?_cons_of_ne_nil hpt0] at this
  exact List.mem_of_getLast? this

/-- `disjointTails` is symmetric in its two paths. -/
lemma disjointTails_comm {p q : List ℕ} : disjointTails p q = disjointTails q p := by
  rw [Bool.eq_iff_iff]
  simp only [disjointTails, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not]
  exact ⟨fun h a ha hq ↦ h a hq ha, fun h a ha hq ↦ h a hq ha⟩

/-- An odd candidate: shortest paths to bonded `x` and `y` at one distance, closed by the
bond. -/
def OddCand (m : Work) (r : ℕ) (c : List ℕ) : Prop :=
  ∃ x y dx p q, (m.bfs r).1[x]! = some dx ∧ dx ≠ 0 ∧ (m.bfs r).1[y]! = some dx ∧ m.Adj x y ∧
    m.PathOK (m.bfs r).1 r x dx p ∧ m.PathOK (m.bfs r).1 r y dx q ∧ disjointTails p q = true ∧
    c = p ++ q.reverse.dropLast

/-- An even candidate: shortest paths to two different neighbours `u₁`, `u₂` of `x`, one step
nearer, closed through `x`. -/
def EvenCand (m : Work) (r : ℕ) (c : List ℕ) : Prop :=
  ∃ x u₁ u₂ dx p q, (m.bfs r).1[x]! = some dx ∧ 2 ≤ dx ∧ m.Adj x u₁ ∧ m.Adj x u₂ ∧ u₁ ≠ u₂ ∧
    (m.bfs r).1[u₁]! = some (dx - 1) ∧ (m.bfs r).1[u₂]! = some (dx - 1) ∧
    m.PathOK (m.bfs r).1 r u₁ (dx - 1) p ∧ m.PathOK (m.bfs r).1 r u₂ (dx - 1) q ∧
    disjointTails p q = true ∧ c = p ++ [x] ++ q.reverse.dropLast

/-- A candidate cycle from `r`. -/
def Cand (m : Work) (r : ℕ) (c : List ℕ) : Prop := m.OddCand r c ∨ m.EvenCand r c

/-- **Every cycle `cyclesFrom` lists is a candidate.** -/
theorem cand_of_mem_cyclesFrom (m : Work) {r : ℕ} (hr : r < m.numAtoms) {c : List ℕ}
    (hc : c ∈ m.cyclesFrom r) : m.Cand r c := by
  have hp := pathsOK_allShortestPaths m (zeroAt_bfs m hr) (m.bfs r).2
  unfold cyclesFrom at hc
  obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
  unfold cyclesAt at hc
  split at hc
  · cases hc
  rename_i dx hx
  split at hc
  · cases hc
  rename_i hdx
  simp only [beq_iff_eq] at hdx
  rcases List.mem_append.1 hc with hc | hc
  · left
    unfold oddCycles at hc
    obtain ⟨⟨k, y⟩, hky, hc⟩ := List.mem_flatMap.1 hc
    dsimp only at hc
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      obtain ⟨p, hpm, hc⟩ := List.mem_flatMap.1 hc
      obtain ⟨q, hqm, hc⟩ := List.mem_filterMap.1 hc
      split at hc
      · rename_i hdis
        cases hc
        exact ⟨x, y, dx, p, q, hx, hdx, hcond.2, adj_of_mem_neighbors hky, hp x dx hx p hpm,
          hp y dx hcond.2 q hqm, hdis, rfl⟩
      · cases hc
    · cases hc
  · right
    split at hc
    swap
    · cases hc
    rename_i hdx2
    unfold evenCycles at hc
    dsimp only at hc
    generalize hP : (m.neighbors x).filterMap (fun (e : ℕ × ℕ) ↦
      if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none) = preds at hc
    have hpre : ∀ i < preds.length,
        m.Adj x preds[i]! ∧ (m.bfs r).1[preds[i]!]! = some (dx - 1) := by
      intro i hi
      rw [getElem!_pos preds i hi]
      generalize preds[i] = u0, (List.getElem_mem hi : preds[i] ∈ preds) = hm
      rw [← hP] at hm
      obtain ⟨⟨k, u⟩, hku, hu⟩ := List.mem_filterMap.1 hm
      dsimp only at hu
      split at hu
      · rename_i hdu
        cases hu
        exact ⟨adj_of_mem_neighbors hku, by simpa using hdu⟩
      · cases hu
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨b, hb, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨p, hpm, hc⟩ := List.mem_flatMap.1 hc
    obtain ⟨q, hqm, hc⟩ := List.mem_filterMap.1 hc
    split at hc
    · rename_i hdis
      cases hc
      rw [List.mem_range] at ha
      rw [List.mem_range'_1] at hb
      obtain ⟨hxa, hda⟩ := hpre a ha
      obtain ⟨hxb, hdb⟩ := hpre b (by omega)
      have hp' := hp _ _ hda p hpm
      have hq' := hp _ _ hdb q hqm
      refine ⟨x, _, _, dx, p, q, hx, hdx2, hxa, hxb, fun e ↦ ?_, hda, hdb, hp', hq', hdis, rfl⟩
      have h1 := hp'.mem_tail (by omega)
      have h2 := hq'.mem_tail (by omega)
      rw [e] at h1
      exact not_mem_tail_of_disjointTails hdis _ h1 h2
    · cases hc

/-- The same cycle closed from the other side: started at the root, run the other way. -/
lemma ringEq_swap (r : ℕ) (A B : List ℕ) : RingEq (r :: (A ++ B.reverse)) (r :: (B ++ A.reverse)) :=
  ⟨1, .inr (by simp [List.rotate_cons_succ])⟩

/-- Every atom list is `RingEq` to itself. -/
lemma RingEq.refl (c : List ℕ) : RingEq c c := ⟨0, .inl (by simp)⟩

/-- **Every candidate is listed**, perhaps started elsewhere and run the other way. -/
theorem exists_mem_cyclesFrom_of_cand {m : Work} (hwf : m.WF) {r : ℕ} (hr : r < m.numAtoms)
    {c : List ℕ} (hc : m.Cand r c) : ∃ c' ∈ m.cyclesFrom r, RingEq c c' := by
  have I := bfs_inv hwf hr
  have hlt : ∀ x e, (m.bfs r).1[x]! = some e → x < m.numAtoms := fun x e hx ↦ by
    by_contra h
    rw [getElem!_neg _ x (by rw [I.size]; exact h)] at hx
    cases hx
  have hnoloop : ∀ x, ¬ m.Adj x x := fun x ⟨k, hk⟩ ↦ by
    obtain ⟨k', hk', e⟩ := List.mem_map.mp hk
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, he⟩ := e
    simp only [bondsOf, List.mem_filter, List.mem_range, WBond.touches, Bool.or_eq_true,
      beq_iff_eq] at hk'
    have := (hwf k' hk'.1).2.2
    simp only [WBond.other, beq_iff_eq] at he
    split at he <;> omega
  have hmem : ∀ x c', c' ∈ m.cyclesAt (m.bfs r).1 (m.allShortestPaths (m.bfs r).1 (m.bfs r).2 r) x →
      x < m.numAtoms → c' ∈ m.cyclesFrom r := fun x c' h hx ↦ by
    unfold cyclesFrom
    exact List.mem_flatMap.2 ⟨x, List.mem_range.2 hx, h⟩
  rcases hc with ⟨x, y, dx, p, q, hx, hdx, hy, hxy, hp, hq, hdis, rfl⟩ |
    ⟨x, u₁, u₂, dx, p, q, hx, hdx, hx1, hx2, hne, hd1, hd2, hp, hq, hdis, rfl⟩
  · -- odd: listed from the smaller of `x` and `y`
    obtain ⟨pt, rfl, -⟩ := hp.cons
    obtain ⟨qt, rfl, -⟩ := hq.cons
    have hodd : ∀ x y p q, (m.bfs r).1[x]! = some dx → (m.bfs r).1[y]! = some dx →
        m.Adj x y → x < y → m.PathOK (m.bfs r).1 r x dx p → m.PathOK (m.bfs r).1 r y dx q →
        disjointTails p q = true → p ++ q.reverse.dropLast ∈ m.cyclesFrom r := by
      intro x y p q hx hy hxy hlt' hp hq hdis
      refine hmem x _ ?_ (hlt x dx hx)
      unfold cyclesAt
      rw [hx]
      simp only [beq_iff_eq, hdx, if_false]
      apply List.mem_append_left
      unfold oddCycles
      obtain ⟨k, hk⟩ := hxy
      refine List.mem_flatMap.2 ⟨(k, y), hk, ?_⟩
      dsimp only
      rw [if_pos (by simp [hlt', hy])]
      exact List.mem_flatMap.2 ⟨p, mem_allShortestPaths hwf hr hx hp,
        List.mem_filterMap.2 ⟨q, mem_allShortestPaths hwf hr hy hq, by rw [if_pos hdis]⟩⟩
    rcases lt_trichotomy x y with h | rfl | h
    · exact ⟨_, hodd x y _ _ hx hy hxy h hp hq hdis, .refl _⟩
    · exact absurd hxy (hnoloop x)
    · refine ⟨_, hodd y x _ _ hy hx hxy.symm h hq hp (disjointTails_comm.trans hdis), ?_⟩
      simp only [List.reverse_cons, List.dropLast_concat, List.cons_append]
      exact ringEq_swap r pt qt
  · -- even: listed with the two nearer neighbours in the order of the neighbour list
    have hdx0 : dx ≠ 0 := by omega
    have heven : ∀ (a b : ℕ) (p q : List ℕ), a < b →
        b < ((m.neighbors x).filterMap fun (e : ℕ × ℕ) ↦
          if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none).length →
        p ∈ (m.allShortestPaths (m.bfs r).1 (m.bfs r).2 r)[((m.neighbors x).filterMap
          fun (e : ℕ × ℕ) ↦ if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none)[a]!]! →
        q ∈ (m.allShortestPaths (m.bfs r).1 (m.bfs r).2 r)[((m.neighbors x).filterMap
          fun (e : ℕ × ℕ) ↦ if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none)[b]!]! →
        disjointTails p q = true → p ++ [x] ++ q.reverse.dropLast ∈ m.cyclesFrom r := by
      intro a b p q hab hb hp hq hdis
      refine hmem x _ ?_ (hlt x dx hx)
      unfold cyclesAt
      rw [hx]
      simp only [beq_iff_eq, hdx0, if_false, if_pos hdx]
      apply List.mem_append_right
      unfold evenCycles
      dsimp only
      refine List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), List.mem_flatMap.2 ⟨b,
        List.mem_range'_1.2 ⟨hab, by omega⟩, List.mem_flatMap.2 ⟨p, hp,
          List.mem_filterMap.2 ⟨q, hq, by rw [if_pos hdis]⟩⟩⟩⟩
    have hpred : ∀ u, m.Adj x u → (m.bfs r).1[u]! = some (dx - 1) →
        ∃ i, ∃ hi : i < ((m.neighbors x).filterMap fun (e : ℕ × ℕ) ↦
          if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none).length,
          ((m.neighbors x).filterMap fun (e : ℕ × ℕ) ↦
            if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none)[i]! = u := by
      intro u ⟨k, hk⟩ hu
      have : u ∈ (m.neighbors x).filterMap fun (e : ℕ × ℕ) ↦
          if (m.bfs r).1[e.2]! == some (dx - 1) then some e.2 else none :=
        List.mem_filterMap.2 ⟨(k, u), hk, by simp [hu]⟩
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem this
      exact ⟨i, hi, by rw [getElem!_pos _ i hi]; exact e⟩
    obtain ⟨i₁, hi₁, e₁⟩ := hpred u₁ hx1 hd1
    obtain ⟨i₂, hi₂, e₂⟩ := hpred u₂ hx2 hd2
    have hpm := mem_allShortestPaths hwf hr hd1 hp
    have hqm := mem_allShortestPaths hwf hr hd2 hq
    rcases lt_trichotomy i₁ i₂ with h | rfl | h
    · exact ⟨_, heven i₁ i₂ p q h hi₂ (e₁ ▸ hpm) (e₂ ▸ hqm) hdis, .refl _⟩
    · exact absurd (e₁.symm.trans e₂) hne
    · refine ⟨_, heven i₂ i₁ q p h hi₁ (e₂ ▸ hqm) (e₁ ▸ hpm) (disjointTails_comm.trans hdis), ?_⟩
      obtain ⟨pt, rfl, -⟩ := hp.cons
      obtain ⟨qt, rfl, -⟩ := hq.cons
      have := ringEq_swap r (pt ++ [x]) qt
      simp only [List.reverse_cons, List.dropLast_concat, List.cons_append, List.append_assoc,
        List.reverse_append, List.reverse_nil, List.nil_append]
        at this ⊢
      exact this

end Work

end LeanSMILES.Aromaticity
