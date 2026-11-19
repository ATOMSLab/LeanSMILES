/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingCanon

/-!
# LeanSMILES.Aromaticity.RingSearch

What the breadth-first search of `Work.relevantCycles` computes

On a copy whose bonds join atoms in range (`Work.WF`, from `KekuleSim`), `Work.bfs r` gives
every atom its
distance from `r` (`Work.bfs_dist`): `some d` exactly when the shortest walk from `r` has `d`
bonds, `none` when there is no walk. Its visiting order lists the reached atoms once each, by
nondecreasing distance (`Work.bfs_order`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

lemma Adj.lt {m : Work} (hwf : m.WF) {u v : ℕ} (h : m.Adj u v) :
    u < m.numAtoms ∧ v < m.numAtoms := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk', e⟩ := List.mem_map.mp hk
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [bondsOf, List.mem_filter, List.mem_range, WBond.touches, Bool.or_eq_true,
    beq_iff_eq] at hk'
  have := hwf k' hk'.1
  simp only [WBond.other, beq_iff_eq]
  split <;> omega

/-- A walk of `d` bonds from `r` to `v`. -/
inductive Walk (m : Work) (r : ℕ) : ℕ → ℕ → Prop
  | refl : Walk m r r 0
  | step {u v d : ℕ} : Walk m r u d → m.Adj u v → Walk m r v (d + 1)

/-- `v` is `d` bonds from `r`: a walk of `d` bonds, and none shorter. -/
def IsDist (m : Work) (r v d : ℕ) : Prop := m.Walk r v d ∧ ∀ e, m.Walk r v e → d ≤ e

lemma IsDist.unique {m : Work} {r v d e : ℕ} (h : m.IsDist r v d) (h' : m.IsDist r v e) :
    d = e :=
  le_antisymm (h.2 e h'.1) (h'.2 d h.1)

/-- One neighbour of a visit, the visited atom at distance `du`. -/
def visitStep (du : ℕ) (p : Array (Option ℕ) × Array ℕ) (e : ℕ × ℕ) :
    Array (Option ℕ) × Array ℕ :=
  if p.1[e.2]!.isNone then (p.1.set! e.2 (some (du + 1)), p.2.push e.2) else p

lemma bfsVisit_eq (m : Work) (u : ℕ) (p : Array (Option ℕ) × Array ℕ) :
    m.bfsVisit u p = (m.neighbors u).foldl (visitStep ((p.1[u]!).getD 0)) p := by
  unfold bfsVisit
  dsimp only
  congr 1

/-- The neighbour loop of a visit. -/
lemma foldl_visitStep (N du : ℕ) : ∀ (L : List (ℕ × ℕ)) (dist : Array (Option ℕ)) (q : Array ℕ),
    (∀ e ∈ L, e.2 < N) → dist.size = N → (∀ x : ℕ, (dist[x]!).isSome ↔ x ∈ q.toList) →
    q.toList.Nodup →
    (L.foldl (visitStep du) (dist, q)).1.size = N ∧
      (∀ x : ℕ, (dist[x]!).isSome → (L.foldl (visitStep du) (dist, q)).1[x]! = dist[x]!) ∧
      (∃ new, (L.foldl (visitStep du) (dist, q)).2.toList = q.toList ++ new ∧
        ∀ x ∈ new, (L.foldl (visitStep du) (dist, q)).1[x]! = some (du + 1) ∧
          dist[x]! = none ∧ ∃ k, (k, x) ∈ L) ∧
      (∀ x : ℕ, ((L.foldl (visitStep du) (dist, q)).1[x]!).isSome ↔
        x ∈ (L.foldl (visitStep du) (dist, q)).2.toList) ∧
      (L.foldl (visitStep du) (dist, q)).2.toList.Nodup ∧
      ∀ e ∈ L, ((L.foldl (visitStep du) (dist, q)).1[e.2]!).isSome
  | [], dist, q, _, hsz, hseen, hnd =>
    ⟨hsz, fun _ _ ↦ rfl, ⟨[], by simp, by simp⟩, hseen, hnd, by simp⟩
  | (k, v) :: L, dist, q, hL, hsz, hseen, hnd => by
    have hL' : ∀ e ∈ L, e.2 < N := fun e he ↦ hL e (List.mem_cons_of_mem _ he)
    rw [List.foldl_cons]
    by_cases hv : dist[v]!.isNone = true
    · have hvN : v < N := hL _ List.mem_cons_self
      have hvn : dist[v]! = none := Option.isNone_iff_eq_none.1 hv
      have hvq : v ∉ q.toList := fun h ↦ by
        have := (hseen v).2 h
        rw [hvn] at this
        cases this
      have e1 : visitStep du (dist, q) (k, v) = (dist.set! v (some (du + 1)), q.push v) := by
        simp [visitStep, hv]
      have hset : ∀ x, (dist.set! v (some (du + 1)))[x]! =
          if x = v then some (du + 1) else dist[x]! := fun x ↦ by
        rw [getElem!_set!_any]
        by_cases hx : x = v
        · subst hx; simp [hsz, hvN]
        · simp [hx, Ne.symm hx]
      rw [e1]
      obtain ⟨c1, c2, ⟨new, c3a, c3b⟩, c4, c5, c6⟩ :=
        foldl_visitStep N du L (dist.set! v (some (du + 1))) (q.push v) hL'
        (by rw [size_set!_any, hsz]) (fun x ↦ by
          rw [hset, Array.toList_push, List.mem_append, List.mem_singleton]
          by_cases hx : x = v
          · subst hx; simp
          · simp [hx, hseen x])
        (by rw [Array.toList_push]; exact List.nodup_append.2 ⟨hnd, List.nodup_singleton _,
          fun a ha b hb e ↦ by rw [List.mem_singleton] at hb; subst hb e; exact hvq ha⟩)
      have hsv : ((dist.set! v (some (du + 1)))[v]!).isSome := by rw [hset]; simp
      refine ⟨c1, fun x hx ↦ ?_, ⟨v :: new, ?_, fun x hx ↦ ?_⟩, c4, c5, fun e he ↦ ?_⟩
      · have hxv : x ≠ v := by rintro rfl; rw [hvn] at hx; cases hx
        rw [c2 x (by rw [hset, if_neg hxv]; exact hx), hset, if_neg hxv]
      · rw [c3a, Array.toList_push, List.append_assoc]
        rfl
      · rcases List.mem_cons.1 hx with rfl | hx
        · refine ⟨by rw [c2 _ hsv, hset, if_pos rfl], hvn, k, List.mem_cons_self⟩
        · obtain ⟨d1, d2, k', hk'⟩ := c3b x hx
          have hxv : x ≠ v := by rintro rfl; rw [hset, if_pos rfl] at d2; cases d2
          refine ⟨d1, by rw [hset, if_neg hxv] at d2; exact d2, k', List.mem_cons_of_mem _ hk'⟩
      · rcases List.mem_cons.1 he with rfl | he
        · rw [c2 _ hsv]; exact hsv
        · exact c6 e he
    · have e1 : visitStep du (dist, q) (k, v) = (dist, q) := by simp [visitStep, hv]
      rw [e1]
      obtain ⟨c1, c2, ⟨new, c3a, c3b⟩, c4, c5, c6⟩ :=
        foldl_visitStep N du L dist q hL' hsz hseen hnd
      have hsv : (dist[v]!).isSome := Option.isSome_iff_ne_none.2 (by
        simpa [Option.isNone_iff_eq_none] using hv)
      refine ⟨c1, c2, ⟨new, c3a, fun x hx ↦ ?_⟩, c4, c5, fun e he ↦ ?_⟩
      · obtain ⟨d1, d2, k', hk'⟩ := c3b x hx
        exact ⟨d1, d2, k', List.mem_cons_of_mem _ hk'⟩
      · rcases List.mem_cons.1 he with rfl | he
        · rw [c2 _ hsv]; exact hsv
        · exact c6 e he

/-- What the search has after visiting `h` atoms of its queue `q`: the seen atoms are the queued
ones, each with the length of a walk to it, the queue is ordered by distance and spans at most one
step from its head, and every visited atom's neighbours are seen at most one step further. -/
structure BfsInv (m : Work) (r h : ℕ) (dist : Array (Option ℕ)) (q : Array ℕ) : Prop where
  size : dist.size = m.numAtoms
  seen : ∀ x : ℕ, (dist[x]!).isSome ↔ x ∈ q.toList
  nodup : q.toList.Nodup
  walk : ∀ x d : ℕ, dist[x]! = some d → m.Walk r x d
  sorted : q.toList.Pairwise fun a b ↦ (dist[a]!).getD 0 ≤ (dist[b]!).getD 0
  head : h ≤ q.toList.length
  spread : h < q.toList.length →
    ∀ x ∈ q.toList, (dist[x]!).getD 0 ≤ (dist[q.toList[h]!]!).getD 0 + 1
  closed : ∀ i < h, ∀ v, m.Adj q.toList[i]! v →
    (dist[v]!).isSome ∧ (dist[v]!).getD 0 ≤ (dist[q.toList[i]!]!).getD 0 + 1
  root : dist[r]! = some 0

lemma getElem!_append_left' {l l' : List ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ l')[i]! = l[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos l i h, List.getElem_append_left h]

/-- **One visit keeps the invariant**, one more atom visited. -/
lemma BfsInv.visit {m : Work} (hwf : m.WF) {r h : ℕ} {dist : Array (Option ℕ)} {q : Array ℕ}
    (I : m.BfsInv r h dist q) (hh : h < q.toList.length) :
    m.BfsInv r (h + 1) (m.bfsVisit q.toList[h]! (dist, q)).1
      (m.bfsVisit q.toList[h]! (dist, q)).2 := by
  set u := q.toList[h]! with hu
  have huq : u ∈ q.toList := by rw [hu, getElem!_pos _ h hh]; exact List.getElem_mem _
  obtain ⟨du, hdu⟩ := Option.isSome_iff_exists.1 ((I.seen u).2 huq)
  have hL : ∀ e ∈ m.neighbors u, e.2 < m.numAtoms :=
    fun e he ↦ (Adj.lt hwf (adj_of_mem_neighbors (k := e.1) he)).2
  rw [bfsVisit_eq]
  dsimp only
  rw [hdu, Option.getD_some]
  obtain ⟨c1, c2, ⟨new, c3a, c3b⟩, c4, c5, c6⟩ :=
    foldl_visitStep m.numAtoms du (m.neighbors u) dist q hL I.size I.seen I.nodup
  generalize (m.neighbors u).foldl (visitStep du) (dist, q) = res at c1 c2 c3a c3b c4 c5 c6
  obtain ⟨dist', q'⟩ := res
  dsimp only at c1 c2 c3a c3b c4 c5 c6 ⊢
  have hold : ∀ x ∈ q.toList, dist'[x]! = dist[x]! := fun x hx ↦ c2 x ((I.seen x).2 hx)
  have hDold : ∀ x ∈ q.toList, (dist'[x]!).getD 0 = (dist[x]!).getD 0 :=
    fun x hx ↦ by rw [hold x hx]
  have hDnew : ∀ x ∈ new, (dist'[x]!).getD 0 = du + 1 := fun x hx ↦ by rw [(c3b x hx).1]; rfl
  have hDu : (dist[u]!).getD 0 = du := by rw [hdu]; rfl
  have hspread : ∀ x ∈ q.toList, (dist[x]!).getD 0 ≤ du + 1 := fun x hx ↦ hDu ▸ I.spread hh x hx
  have hnewQ : ∀ x ∈ new, x ∉ q.toList := fun x hx hq ↦ by
    have := (I.seen x).2 hq
    rw [(c3b x hx).2.1] at this
    cases this
  have hidx : ∀ i < q.toList.length, q'.toList[i]! = q.toList[i]! := fun i hi ↦ by
    rw [c3a, getElem!_append_left' hi]
  have hsorted : q'.toList.Pairwise fun a b ↦ (dist'[a]!).getD 0 ≤ (dist'[b]!).getD 0 := by
    rw [c3a, List.pairwise_append]
    refine ⟨I.sorted.imp_of_mem fun ha hb hab ↦ ?_, ?_, fun a ha b hb ↦ ?_⟩
    · rw [hDold _ ha, hDold _ hb]; exact hab
    · exact (List.pairwise_of_forall (R := fun _ _ ↦ True) fun _ _ ↦ trivial).imp_of_mem
        fun ha hb _ ↦ by rw [hDnew _ ha, hDnew _ hb]
    · rw [hDold _ ha, hDnew _ hb]; exact hspread a ha
  have hlen : q.toList.length ≤ q'.toList.length := by rw [c3a]; simp
  have hD' : ∀ x ∈ q'.toList, (dist'[x]!).getD 0 ≤ du + 1 := fun x hx ↦ by
    rw [c3a, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hDold _ hx]; exact hspread x hx
    · rw [hDnew _ hx]
  have hseen' : ∀ x, (dist'[x]!).isSome → x ∈ q.toList ∨ x ∈ new := fun x hx ↦ by
    have := (c4 x).1 hx
    rwa [c3a, List.mem_append] at this
  refine ⟨c1, c4, c5, fun x d hx ↦ ?_, hsorted, by omega, fun hh' x hx ↦ ?_, fun i hi v hv ↦ ?_,
    by rw [hold r ((I.seen r).1 (by rw [I.root]; rfl)), I.root]⟩
  · rcases hseen' x (by rw [hx]; rfl) with hq | hn
    · rw [hold x hq] at hx; exact I.walk x d hx
    · obtain ⟨d1, -, hadj⟩ := c3b x hn
      rw [d1] at hx
      cases hx
      exact .step (I.walk u du hdu) hadj
  · refine (hD' x hx).trans (Nat.add_le_add_right ?_ 1)
    have := List.pairwise_iff_getElem.1 hsorted h (h + 1) (by omega) hh' (by omega)
    rw [← getElem!_pos _ h (by omega), ← getElem!_pos _ (h + 1) hh', hidx h hh, ← hu,
      hDold u huq, hDu] at this
    exact this
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hidx i (by omega)] at hv ⊢
      have hiq : q.toList[i]! ∈ q.toList := by
        rw [getElem!_pos _ i (by omega)]; exact List.getElem_mem _
      obtain ⟨g1, g2⟩ := I.closed i hi v hv
      have hvq := (I.seen v).1 g1
      rw [hold v hvq, hDold _ hiq]
      exact ⟨g1, g2⟩
    · rw [hidx i hh, ← hu] at hv ⊢
      obtain ⟨k, hk⟩ := hv
      have hs := c6 (k, v) hk
      refine ⟨hs, ?_⟩
      rw [hDold u huq, hDu]
      rcases hseen' v hs with hq | hn
      · rw [hDold v hq]; exact hspread v hq
      · rw [hDnew v hn]

lemma BfsInv.length_le {m : Work} {r h : ℕ} {dist : Array (Option ℕ)} {q : Array ℕ}
    (I : m.BfsInv r h dist q) : q.toList.length ≤ m.numAtoms := by
  have hlt : ∀ x ∈ q.toList, x < m.numAtoms := fun x hx ↦ by
    by_contra hx'
    have := (I.seen x).2 hx
    rw [getElem!_neg dist x (by rw [I.size]; exact hx')] at this
    cases this
  simpa using (List.subperm_of_subset I.nodup fun x hx ↦ List.mem_range.2 (hlt x hx)).length_le

/-- **The loop ends with every queued atom visited.** -/
lemma bfsLoop_inv {m : Work} (hwf : m.WF) {r : ℕ} : ∀ (fuel head : ℕ)
    (p : Array (Option ℕ) × Array ℕ), m.BfsInv r head p.1 p.2 → m.numAtoms < fuel + head →
    m.BfsInv r (m.bfsLoop fuel head p).2.toList.length (m.bfsLoop fuel head p).1
      (m.bfsLoop fuel head p).2
  | 0, head, p, I, hf => absurd (I.head.trans I.length_le) (by omega)
  | fuel + 1, head, p, I, hf => by
    unfold bfsLoop
    split
    · rename_i hh
      have e : p.2[head] = p.2.toList[head]! := by
        rw [getElem!_pos _ head (by simpa using hh), Array.getElem_toList]
      rw [e]
      exact bfsLoop_inv hwf fuel (head + 1) _ (I.visit hwf (by simpa using hh)) (by omega)
    · rename_i hh
      have : head = p.2.toList.length := le_antisymm I.head (by simpa using hh)
      rw [← this]
      exact I

/-- The search's final state: everything queued is visited. -/
lemma bfs_inv {m : Work} (hwf : m.WF) {r : ℕ} (hr : r < m.numAtoms) :
    m.BfsInv r (m.bfs r).2.toList.length (m.bfs r).1 (m.bfs r).2 := by
  unfold bfs
  apply bfsLoop_inv hwf _ 0 _ _ (by omega)
  dsimp only
  have hd : ∀ x, ((Array.replicate m.numAtoms (none : Option ℕ)).set! r (some 0))[x]! =
      if x = r then some 0 else none := fun x ↦ by
    rw [getElem!_set!_any, Array.size_replicate]
    by_cases hx : x = r
    · subst hx; simp [hr]
    · rw [if_neg (fun h ↦ hx h.1.symm), if_neg hx]
      by_cases hxn : x < m.numAtoms
      · rw [getElem!_pos _ x (by simpa using hxn)]; simp
      · rw [getElem!_neg _ x (by simpa using hxn)]; rfl
  refine ⟨by simp, fun x ↦ ?_, by simp, fun x d hx ↦ ?_, by simp, by simp, fun _ x hx ↦ ?_,
    fun i hi ↦ absurd hi (Nat.not_lt_zero _), by rw [hd, if_pos rfl]⟩
  · rw [hd]
    by_cases hx : x = r <;> simp [hx]
  · rw [hd] at hx
    split at hx
    · rename_i hx'
      subst hx'
      cases hx
      exact .refl
    · cases hx
  · simp only [List.mem_singleton] at hx
    subst hx
    simp

/-- In the final state, a walk reaches a seen atom, and no farther than the walk. -/
lemma BfsInv.reach {m : Work} {r : ℕ} {dist : Array (Option ℕ)} {q : Array ℕ}
    (I : m.BfsInv r q.toList.length dist q) {x e : ℕ} (h : m.Walk r x e) :
    (dist[x]!).isSome ∧ (dist[x]!).getD 0 ≤ e := by
  induction h with
  | refl => rw [I.root]; exact ⟨rfl, le_refl _⟩
  | @step u v e _ hadj ih =>
    obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem ((I.seen u).1 ih.1)
    have hu : q.toList[i]! = u := by rw [getElem!_pos _ i hi]; exact hiu
    obtain ⟨g1, g2⟩ := I.closed i hi v (hu ▸ hadj)
    rw [hu] at g2
    exact ⟨g1, by omega⟩

/-- **The search finds distances**: atom `v` gets `some d` exactly when it is `d` bonds from the
root. -/
theorem bfs_dist {m : Work} (hwf : m.WF) {r : ℕ} (hr : r < m.numAtoms) (v d : ℕ) :
    (m.bfs r).1[v]! = some d ↔ m.IsDist r v d := by
  have I := bfs_inv hwf hr
  constructor
  · intro h
    refine ⟨I.walk v d h, fun e he ↦ ?_⟩
    have := (I.reach he).2
    rwa [h] at this
  · intro hd
    obtain ⟨d0, h0⟩ := Option.isSome_iff_exists.1 (I.reach hd.1).1
    have : m.IsDist r v d0 := ⟨I.walk v d0 h0, fun e he ↦ by
      have := (I.reach he).2; rwa [h0] at this⟩
    rw [h0, this.unique hd]

/-- An atom no walk reaches gets no distance. -/
theorem bfs_dist_none {m : Work} (hwf : m.WF) {r : ℕ} (hr : r < m.numAtoms) (v : ℕ) :
    (m.bfs r).1[v]! = none ↔ ∀ d, ¬ m.Walk r v d := by
  have I := bfs_inv hwf hr
  constructor
  · intro h d hw
    have := (I.reach hw).1
    rw [h] at this
    cases this
  · intro h
    cases hv : (m.bfs r).1[v]! with
    | none => rfl
    | some d => exact absurd (I.walk v d hv) (h d)

/-- **The search's order**: the reached atoms, once each, by nondecreasing distance. -/
theorem bfs_order {m : Work} (hwf : m.WF) {r : ℕ} (hr : r < m.numAtoms) :
    (m.bfs r).2.toList.Nodup ∧ (∀ x, x ∈ (m.bfs r).2.toList ↔ ∃ d, m.Walk r x d) ∧
      (m.bfs r).2.toList.Pairwise
        fun a b ↦ ((m.bfs r).1[a]!).getD 0 ≤ ((m.bfs r).1[b]!).getD 0 := by
  have I := bfs_inv hwf hr
  refine ⟨I.nodup, fun x ↦ ?_, I.sorted⟩
  rw [← I.seen]
  constructor
  · intro h
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 h
    exact ⟨d, I.walk x d hd⟩
  · rintro ⟨d, hd⟩
    exact (I.reach hd).1

end Work

end LeanSMILES.Aromaticity
