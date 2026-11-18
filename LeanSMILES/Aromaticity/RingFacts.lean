/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Rings

/-!
# LeanSMILES.Aromaticity.RingFacts

Every ring of the ring set (`Work.relevantCycles`) is a genuine cycle of the bond graph: its atoms
are distinct, there are at least three, and consecutive atoms (the last and the first included)
are bonded (`Work.IsRing`).

The proof follows the construction.  The breadth-first search gives distance `0` to the root and
to no other atom; the paths `allShortestPaths` builds to an atom at distance `d` then have `d + 1`
atoms, the `i`-th at distance `i`, consecutive ones bonded (`Work.PathOK`).  A candidate cycle
joins two such paths that share only the root, by a bond (odd cycles) or through a common
neighbour (even cycles); the distances keep its atoms distinct.  Choosing among the candidates
(`candidateCycles`, `relevantCycles`) only keeps some of them.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- Reading an array after `set!`: an out-of-range write changes nothing. -/
lemma getElem!_set!_any {α : Type} [Inhabited α] (a : Array α) (i j : ℕ) (v : α) :
    (a.set! i v)[j]! = if i = j ∧ j < a.size then v else a[j]! := by
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj]
    simp [Array.set!, Array.getElem_setIfInBounds, hj]
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    simp [hj]

namespace Work

/-! ### Adjacency -/

/-- Atoms `u` and `v` are joined by a bond. -/
def Adj (m : Work) (u v : ℕ) : Prop := ∃ k, (k, v) ∈ m.neighbors u

lemma Adj.symm {m : Work} {u v : ℕ} (h : m.Adj u v) : m.Adj v u := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk', e⟩ := List.mem_map.mp hk
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [bondsOf, List.mem_filter, List.mem_range] at hk'
  refine ⟨k', List.mem_map.mpr ⟨k', ?_, ?_⟩⟩
  · simp only [bondsOf, List.mem_filter, List.mem_range]
    refine ⟨hk'.1, ?_⟩
    simp only [WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq] at hk' ⊢
    split <;> simp_all
  · simp only [WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq, Prod.mk.injEq,
      true_and] at hk' ⊢
    split <;> split <;> simp_all

lemma adj_of_mem_neighbors {m : Work} {u v k : ℕ} (h : (k, v) ∈ m.neighbors u) : m.Adj u v :=
  ⟨k, h⟩

/-! ### Breadth-first distances -/

/-- Distance `0` belongs to the root alone. -/
def ZeroAt (dist : Array (Option ℕ)) (r : ℕ) : Prop := ∀ v, dist[v]! = some 0 ↔ v = r

lemma zeroAt_bfsVisit (m : Work) {r u : ℕ} {p : Array (Option ℕ) × Array ℕ}
    (h : ZeroAt p.1 r) : ZeroAt (m.bfsVisit u p).1 r := by
  unfold bfsVisit
  generalize (p.1[u]!).getD 0 = du
  induction m.neighbors u generalizing p with
  | nil => exact h
  | cons e l ih =>
    rw [List.foldl_cons]
    apply ih
    obtain ⟨dist, queue⟩ := p
    obtain ⟨k, v⟩ := e
    dsimp only
    split
    · rename_i hn
      intro w
      rw [getElem!_set!_any]
      split
      · rename_i hw
        obtain ⟨rfl, -⟩ := hw
        constructor
        · intro e; cases e
        · intro e
          have := (h _).2 e
          simp_all
      · exact h w
    · exact h

lemma zeroAt_bfsLoop (m : Work) {r : ℕ} :
    ∀ (fuel head : ℕ) (p : Array (Option ℕ) × Array ℕ), ZeroAt p.1 r →
      ZeroAt (m.bfsLoop fuel head p).1 r
  | 0, _, _, h => h
  | fuel + 1, head, p, h => by
    unfold bfsLoop
    split
    · exact zeroAt_bfsLoop m fuel _ _ (zeroAt_bfsVisit m h)
    · exact h

lemma zeroAt_bfs (m : Work) {r : ℕ} (hr : r < m.numAtoms) : ZeroAt (m.bfs r).1 r := by
  unfold bfs
  apply zeroAt_bfsLoop
  intro v
  dsimp only
  rw [getElem!_set!_any]
  simp only [Array.size_replicate]
  split
  · rename_i hv
    simp [hv.1]
  · rename_i hv
    constructor
    · intro e
      by_cases hvn : v < m.numAtoms
      · rw [getElem!_pos _ v (by simpa using hvn)] at e
        simp at e
      · rw [getElem!_neg _ v (by simpa using hvn)] at e
        cases e
    · rintro rfl
      exact absurd ⟨rfl, hr⟩ hv

/-! ### Shortest paths -/

/-- A path from the root `r` to `w` at distance `d`: `d + 1` atoms, starting at `r` and ending at
`w`, consecutive ones bonded, the `i`-th at distance `i`. -/
structure PathOK (m : Work) (dist : Array (Option ℕ)) (r w d : ℕ) (p : List ℕ) : Prop where
  length : p.length = d + 1
  head : p.head? = some r
  last : p.getLast? = some w
  chain : p.IsChain m.Adj
  dist : ∀ i (h : i < p.length), dist[p[i]]! = some i

/-- Every path stored for an atom at distance `d` is a `PathOK` path. -/
def PathsOK (m : Work) (dist : Array (Option ℕ)) (r : ℕ) (paths : Array (List (List ℕ))) :
    Prop :=
  ∀ w d, dist[w]! = some d → ∀ p ∈ paths[w]!, m.PathOK dist r w d p

lemma pathsOK_step (m : Work) {dist : Array (Option ℕ)} {r : ℕ} (hz : ZeroAt dist r)
    {paths : Array (List (List ℕ))} (h : m.PathsOK dist r paths) (v : ℕ) :
    m.PathsOK dist r (m.shortestPathsStep dist r paths v) := by
  unfold shortestPathsStep
  split
  · exact h
  rename_i hvr
  simp only [beq_iff_eq] at hvr
  intro w d hw p hp
  rw [getElem!_set!_any] at hp
  split at hp
  · rename_i hwv
    obtain ⟨rfl, -⟩ := hwv
    obtain ⟨u, hu, q, hq, rfl⟩ : ∃ u ∈ m.shortestPreds dist v, ∃ q ∈ paths[u]!, q ++ [v] = p := by
      simpa using hp
    unfold shortestPreds at hu
    obtain ⟨⟨k, u'⟩, hku, hu'⟩ := List.mem_filterMap.1 hu
    simp only [hw, Option.getD_some] at hu'
    split at hu'
    · rename_i hdu
      cases hu'
      have hd0 : d ≠ 0 := fun e ↦ hvr ((hz v).1 (e ▸ hw))
      have hdu' : dist[u]! = some (d - 1) := by simpa using hdu
      have hq' := h u (d - 1) hdu' q hq
      have hlen : q.length = d := by rw [hq'.length]; omega
      refine ⟨by simp [hlen], ?_, by simp, ?_, ?_⟩
      · obtain ⟨a, l, rfl⟩ := List.exists_cons_of_length_pos (by omega : 0 < q.length)
        simpa using hq'.head
      · refine hq'.chain.append (.singleton _) ?_
        intro x hx y hy
        rw [hq'.last] at hx
        simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
        subst hx hy
        exact (adj_of_mem_neighbors hku).symm
      · intro i hi
        by_cases hiq : i < q.length
        · rw [List.getElem_append_left hiq]
          exact hq'.dist i hiq
        · have : i = q.length := by simp at hi; omega
          subst this
          simp [hw, hlen]
    · cases hu'
  · exact h w d hw p hp

lemma pathsOK_allShortestPaths (m : Work) {dist : Array (Option ℕ)} {r : ℕ} (hz : ZeroAt dist r)
    (order : Array ℕ) :
    m.PathsOK dist r (m.allShortestPaths dist order r) := by
  unfold allShortestPaths
  suffices ∀ (l : List ℕ) (paths : Array (List (List ℕ))), m.PathsOK dist r paths →
      m.PathsOK dist r (l.foldl (m.shortestPathsStep dist r) paths) by
    apply this
    intro w d hw p hp
    rw [getElem!_set!_any] at hp
    simp only [Array.size_replicate] at hp
    split at hp
    · rename_i hwr
      obtain ⟨rfl, -⟩ := hwr
      have hd : d = 0 := by
        have := (hz r).2 rfl
        rw [this] at hw
        exact (Option.some.inj hw).symm
      subst hd
      simp only [List.mem_singleton] at hp
      subst hp
      refine ⟨rfl, rfl, rfl, .singleton _, ?_⟩
      intro i hi
      simp only [List.length_singleton, Nat.lt_one_iff] at hi
      subst hi
      exact (hz r).2 rfl
    · by_cases hwn : w < m.numAtoms
      · rw [getElem!_pos _ w (by simpa using hwn)] at hp
        simp at hp
      · rw [getElem!_neg _ w (by simpa using hwn)] at hp
        exact absurd hp List.not_mem_nil
  intro l
  induction l with
  | nil => exact fun _ h ↦ h
  | cons v l ih => exact fun paths h ↦ ih _ (pathsOK_step m hz h v)

/-- The atoms of a `PathOK` path are distinct: their distances are. -/
lemma PathOK.nodup {m : Work} {dist : Array (Option ℕ)} {r w d : ℕ} {p : List ℕ}
    (h : m.PathOK dist r w d p) : p.Nodup := by
  have hmap : p.map (fun a ↦ dist[a]!) = (List.range p.length).map some := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact h.dist i (by simpa using h1)
  apply List.Nodup.of_map (fun a ↦ dist[a]!)
  rw [hmap]
  exact (List.nodup_range).map (Option.some_injective _)

/-- An atom of a `PathOK` path to an atom at distance `d` is at distance at most `d`. -/
lemma PathOK.dist_le {m : Work} {dist : Array (Option ℕ)} {r w d : ℕ} {p : List ℕ}
    (h : m.PathOK dist r w d p) {a : ℕ} (ha : a ∈ p) : ∃ i ≤ d, dist[a]! = some i := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨i, by have := h.length; omega, h.dist i hi⟩

/-! ### Candidate cycles -/

/-- A ring: distinct atoms, at least three, consecutive ones bonded, the last to the first. -/
structure IsRing (m : Work) (c : List ℕ) : Prop where
  nodup : c.Nodup
  three : 3 ≤ c.length
  chain : c.IsChain m.Adj
  close : ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, m.Adj a b

lemma isChain_reverse_of_symm {m : Work} {l : List ℕ} (h : l.IsChain m.Adj) :
    l.reverse.IsChain m.Adj := by
  rw [List.isChain_reverse]
  exact h.imp fun _ _ h ↦ h.symm

/-- Two paths from `r` that share only `r`, the first extended by `mid`, closed into a ring by a
bond between their ends. -/
lemma isRing_join {m : Work} {r : ℕ} {p qt : List ℕ}
    (hpc : p.IsChain m.Adj) (hpn : p.Nodup) (hph : p.head? = some r)
    (hqc : (r :: qt).IsChain m.Adj) (hqn : (r :: qt).Nodup) (hqt : qt ≠ [])
    (hdis : ∀ a ∈ p, a ∉ qt)
    (hj : ∀ a ∈ p.getLast?, ∀ b ∈ qt.getLast?, m.Adj a b) (hlen : 3 ≤ p.length + qt.length) :
    m.IsRing (p ++ (r :: qt).reverse.dropLast) := by
  have hrev : (r :: qt).reverse.dropLast = qt.reverse := by
    simp [List.reverse_cons]
  rw [hrev]
  obtain ⟨b, qt', rfl⟩ := List.exists_cons_of_ne_nil hqt
  refine ⟨?_, by simpa using hlen, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hpn, (List.nodup_reverse).2 (List.Nodup.of_cons hqn), ?_⟩
    intro a ha c hc e
    subst e
    exact hdis a ha (List.mem_reverse.1 hc)
  · refine hpc.append (isChain_reverse_of_symm (List.IsChain.tail hqc)) ?_
    intro x hx y hy
    rw [List.head?_reverse] at hy
    exact hj x hx y hy
  · intro x hx y hy
    have hp0 : p ≠ [] := by rintro rfl; simp at hph
    rw [List.getLast?_append, List.getLast?_reverse] at hx
    simp only [List.head?_cons, Option.some_or, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_append, hph] at hy
    simp only [Option.some_or, Option.mem_def, Option.some.injEq] at hy
    subst hx hy
    have := List.IsChain.rel_head hqc
    exact this.symm

lemma PathOK.cons {m : Work} {dist : Array (Option ℕ)} {r w d : ℕ} {p : List ℕ}
    (h : m.PathOK dist r w d p) : ∃ pt, p = r :: pt ∧ pt.length = d := by
  obtain ⟨a, pt, rfl⟩ := List.exists_cons_of_length_pos (by rw [h.length]; omega : 0 < p.length)
  have := h.head
  simp only [List.head?_cons, Option.some.injEq] at this
  subst this
  exact ⟨pt, rfl, by have := h.length; simp at this; omega⟩

lemma not_mem_tail_of_disjointTails {p q : List ℕ} (h : disjointTails p q = true) :
    ∀ a ∈ p.tail, a ∉ q.tail := by
  simp only [disjointTails, List.all_eq_true] at h
  intro a ha hq
  have := h a ha
  have hc : q.tail.contains a = true := List.contains_iff_mem.2 hq
  rw [hc] at this
  cases this

/-- An atom at distance `dx` is on no path to an atom at a smaller distance. -/
lemma PathOK.not_mem {m : Work} {dist : Array (Option ℕ)} {r w d x dx : ℕ} {p : List ℕ}
    (h : m.PathOK dist r w d p) (hx : dist[x]! = some dx) (hd : d < dx) : x ∉ p := by
  intro hm
  obtain ⟨i, hi, e⟩ := h.dist_le hm
  rw [hx] at e
  cases e
  omega

lemma isRing_of_mem_oddCycles (m : Work) {dist : Array (Option ℕ)} {r : ℕ}
    {paths : Array (List (List ℕ))} (hp : m.PathsOK dist r paths) {x dx : ℕ}
    (hx : dist[x]! = some dx) (hdx : dx ≠ 0) {c : List ℕ} (hc : c ∈ m.oddCycles dist paths x dx) :
    m.IsRing c := by
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
      have hp' := hp x dx hx p hpm
      have hq' := hp y dx hcond.2 q hqm
      obtain ⟨pt, rfl, hpt⟩ := hp'.cons
      obtain ⟨qt, rfl, hqt⟩ := hq'.cons
      have hd := not_mem_tail_of_disjointTails hdis
      simp only [List.tail_cons] at hd
      apply isRing_join hp'.chain hp'.nodup rfl hq'.chain hq'.nodup
        (by rintro rfl; simp at hqt; omega)
      · intro a ha
        rcases List.mem_cons.1 ha with rfl | ha
        · exact (List.nodup_cons.1 hq'.nodup).1
        · exact hd a ha
      · intro a ha b hb
        have h1 := hp'.last
        have h2 := hq'.last
        have hqt0 : qt ≠ [] := by rintro rfl; simp at hqt; omega
        rw [h1] at ha
        obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 hqt0)
        rw [List.getLast?_cons, hz] at h2
        simp only [Option.getD_some, Option.some.injEq] at h2
        rw [hz, h2] at hb
        cases ha
        cases hb
        exact adj_of_mem_neighbors hky
      · simp only [List.length_cons]; omega
    · cases hc
  · cases hc

lemma getLast?_cons_of_ne_nil {r : ℕ} {qt : List ℕ} (h : qt ≠ []) :
    (r :: qt).getLast? = qt.getLast? := by
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (mt List.getLast?_eq_none_iff.1 h)
  rw [List.getLast?_cons, hz]
  rfl

lemma isRing_of_mem_evenCycles (m : Work) {dist : Array (Option ℕ)} {r : ℕ}
    {paths : Array (List (List ℕ))} (hp : m.PathsOK dist r paths) {x dx : ℕ}
    (hx : dist[x]! = some dx) (hdx : 2 ≤ dx) {c : List ℕ}
    (hc : c ∈ m.evenCycles dist paths x dx) : m.IsRing c := by
  unfold evenCycles at hc
  dsimp only at hc
  generalize hP : (m.neighbors x).filterMap (fun (e : ℕ × ℕ) ↦
    if dist[e.2]! == some (dx - 1) then some e.2 else none) = preds at hc
  have hpre : ∀ i < preds.length, m.Adj x preds[i]! ∧ dist[preds[i]!]! = some (dx - 1) := by
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
    obtain ⟨pt, rfl, hpt⟩ := hp'.cons
    obtain ⟨qt, rfl, hqt⟩ := hq'.cons
    have hd := not_mem_tail_of_disjointTails hdis
    simp only [List.tail_cons] at hd
    have hqt0 : qt ≠ [] := by rintro rfl; simp at hqt; omega
    have hxp : x ∉ r :: pt := hp'.not_mem hx (by omega)
    have hxq : x ∉ r :: qt := hq'.not_mem hx (by omega)
    apply isRing_join (p := r :: pt ++ [x]) _ _ (by simp) hq'.chain hq'.nodup hqt0
    · intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact (List.nodup_cons.1 hq'.nodup).1
        · exact hd y hy
      · rw [List.mem_singleton] at hy
        subst hy
        exact fun h ↦ hxq (List.mem_cons_of_mem _ h)
    · intro y hy z hz
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_def, Option.some.injEq] at hy
      have h2 := hq'.last
      rw [getLast?_cons_of_ne_nil hqt0] at h2
      rw [h2] at hz
      cases hz
      subst hy
      exact hxb
    · simp only [List.length_append, List.length_cons]; omega
    · refine hp'.chain.append (.singleton _) ?_
      intro y hy z hz
      rw [hp'.last] at hy
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy hz
      subst hy hz
      exact hxa.symm
    · rw [List.nodup_append]
      exact ⟨hp'.nodup, List.nodup_singleton _, by
        intro y hy z hz e
        rw [List.mem_singleton] at hz
        subst e hz
        exact hxp hy⟩
  · cases hc

lemma isRing_of_mem_cyclesAt (m : Work) {dist : Array (Option ℕ)} {r : ℕ}
    {paths : Array (List (List ℕ))} (hp : m.PathsOK dist r paths) {x : ℕ} {c : List ℕ}
    (hc : c ∈ m.cyclesAt dist paths x) : m.IsRing c := by
  unfold cyclesAt at hc
  split at hc
  · cases hc
  · rename_i dx hx
    split at hc
    · cases hc
    · rename_i hdx
      simp only [beq_iff_eq] at hdx
      rcases List.mem_append.1 hc with hc | hc
      · exact isRing_of_mem_oddCycles m hp hx hdx hc
      · split at hc
        · exact isRing_of_mem_evenCycles m hp hx (by omega) hc
        · cases hc

lemma isRing_of_mem_cyclesFrom (m : Work) {r : ℕ} (hr : r < m.numAtoms) {c : List ℕ}
    (hc : c ∈ m.cyclesFrom r) : m.IsRing c := by
  unfold cyclesFrom at hc
  obtain ⟨x, -, hc⟩ := List.mem_flatMap.1 hc
  exact isRing_of_mem_cyclesAt m
    (pathsOK_allShortestPaths m (zeroAt_bfs m hr) (m.bfs r).2) hc

lemma isRing_of_mem_candidateCycles (m : Work) {e : ℕ × List ℕ}
    (he : e ∈ m.candidateCycles) : m.IsRing e.2 := by
  unfold candidateCycles at he
  suffices ∀ (l : List ℕ) (cands : Array (ℕ × List ℕ)), (∀ r ∈ l, r < m.numAtoms) →
      (∀ e ∈ cands, m.IsRing e.2) →
      ∀ e ∈ l.foldl (fun cands r ↦ (m.cyclesFrom r).foldl m.addCandidate cands) cands,
        m.IsRing e.2 from
    this _ _ (fun r hr ↦ List.mem_range.1 hr) (fun e he ↦ by simp at he) e he
  intro l
  induction l with
  | nil => exact fun _ _ h ↦ h
  | cons r l ih =>
    intro cands hl hc
    rw [List.foldl_cons]
    apply ih _ (fun r hr ↦ hl r (List.mem_cons_of_mem _ hr))
    have hr := hl r List.mem_cons_self
    suffices ∀ (cs : List (List ℕ)) (cands : Array (ℕ × List ℕ)), (∀ c ∈ cs, m.IsRing c) →
        (∀ e ∈ cands, m.IsRing e.2) → ∀ e ∈ cs.foldl m.addCandidate cands, m.IsRing e.2 from
      this _ _ (fun c hc ↦ isRing_of_mem_cyclesFrom m hr hc) hc
    intro cs
    induction cs with
    | nil => exact fun _ _ h ↦ h
    | cons c cs ih' =>
      intro cands hcs hc
      rw [List.foldl_cons]
      apply ih' _ (fun c hc ↦ hcs c (List.mem_cons_of_mem _ hc))
      unfold addCandidate
      dsimp only
      split
      · intro e he
        rcases Array.mem_push.1 he with he | rfl
        · exact hc e he
        · exact hcs c List.mem_cons_self
      · exact hc

/-- **Every ring of the ring set is a genuine cycle** of the bond graph. -/
theorem isRing_of_mem_relevantCycles (m : Work) {c : List ℕ} (hc : c ∈ m.relevantCycles) :
    m.IsRing c := by
  unfold relevantCycles at hc
  dsimp only at hc
  generalize hs : List.mergeSort _ _ = sorted at hc
  have hsorted : ∀ e ∈ sorted, m.IsRing e.2 := by
    intro e he
    rw [← hs, List.mem_mergeSort, Array.mem_toList_iff] at he
    exact isRing_of_mem_candidateCycles m he
  suffices ∀ (l : List ℕ) (st : List (ℕ × ℕ) × Array (List ℕ)), (∀ c ∈ st.2, m.IsRing c) →
      ∀ c ∈ (l.foldl (relevantStep sorted) st).2, m.IsRing c from
    this _ _ (fun c hc ↦ by simp at hc) c hc
  intro l
  induction l with
  | nil => exact fun _ h ↦ h
  | cons size l ih =>
    intro st hst
    rw [List.foldl_cons]
    apply ih
    obtain ⟨basis, result⟩ := st
    intro c hc
    simp only [relevantStep, Array.mem_append, List.mem_toArray, List.mem_map,
      List.mem_filter] at hc
    rcases hc with hc | ⟨e, ⟨⟨he, -⟩, -⟩, rfl⟩
    · exact hst c hc
    · exact hsorted e he

/-! ### Ring bonds at an atom -/

lemma bondBetween?_comm (m : Work) (u v : ℕ) : m.bondBetween? u v = m.bondBetween? v u := by
  unfold bondBetween?
  congr 1
  funext k
  exact Bool.or_comm _ _

/-- The bond `bondBetween?` finds is at both atoms and touches no other. -/
lemma bondBetween?_spec {m : Work} {u v k : ℕ} (h : m.bondBetween? u v = some k) :
    k ∈ m.bondsOf u ∧ k ∈ m.bondsOf v ∧
      ∀ y, (m.bonds[k]! : WBond).touches y = true → y = u ∨ y = v := by
  unfold bondBetween? at h
  have hk := List.mem_range.1 (List.mem_of_find?_eq_some h)
  have hp := List.find?_some h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
  simp only [bondsOf, List.mem_filter, List.mem_range, WBond.touches, Bool.or_eq_true,
    beq_iff_eq]
  refine ⟨⟨hk, by omega⟩, ⟨hk, by omega⟩, fun y hy ↦ by omega⟩

lemma bondBetween?_of_adj {m : Work} {u v : ℕ} (h : m.Adj u v) :
    ∃ k, m.bondBetween? u v = some k := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk', e⟩ := List.mem_map.mp hk
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  simp only [bondsOf, List.mem_filter, List.mem_range] at hk'
  apply Option.isSome_iff_exists.1
  unfold bondBetween?
  refine List.find?_isSome.2 ⟨k', List.mem_range.2 hk'.1, ?_⟩
  have h2 := hk'.2
  simp only [WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h2 ⊢
  split <;> omega

lemma succ_mod {t n : ℕ} (ht : t < n) : (t + 1) % n = if t + 1 < n then t + 1 else 0 := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · have : t + 1 = n := by omega
    rw [this, Nat.mod_self]

/-- Consecutive atoms of a ring, the last and the first included, are bonded. -/
lemma IsRing.adj_get {m : Work} {c : List ℕ} (h : m.IsRing c) {t : ℕ} (ht : t < c.length) :
    m.Adj c[t]! c[(t + 1) % c.length]! := by
  rw [succ_mod ht]
  split
  · rename_i h1
    rw [getElem!_pos c t ht, getElem!_pos c (t + 1) h1]
    exact List.isChain_iff_getElem.1 h.chain t h1
  · have ht' : t = c.length - 1 := by omega
    have h0 : 0 < c.length := by omega
    rw [getElem!_pos c t ht, getElem!_pos c 0 h0]
    apply h.close
    · rw [List.getLast?_eq_getElem?, ← ht', List.getElem?_eq_getElem ht]; rfl
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]; rfl

lemma mem_ringBonds_of {m : Work} {c : List ℕ} {t k : ℕ} (ht : t < c.length)
    (hk : m.bondBetween? c[t]! c[(t + 1) % c.length]! = some k) : k ∈ m.ringBonds c :=
  List.mem_filterMap.2 ⟨t, List.mem_range.2 ht, hk⟩

/-- An atom of a ring has two different bonds of the ring. -/
lemma IsRing.two_bonds {m : Work} {c : List ℕ} (h : m.IsRing c) {x : ℕ} (hx : x ∈ c) :
    ∃ k₁ k₂, k₁ ≠ k₂ ∧ k₁ ∈ m.ringBonds c ∧ k₂ ∈ m.ringBonds c ∧ k₁ ∈ m.bondsOf x ∧
      k₂ ∈ m.bondsOf x := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
  have h3 := h.three
  set n := c.length with hn
  set s := if t = 0 then n - 1 else t - 1 with hs
  have hsn : s < n := by rw [hs]; split <;> omega
  have hst : (s + 1) % n = t := by
    rw [succ_mod hsn]
    rw [hs]
    split <;> split <;> omega
  obtain ⟨k₁, hk₁⟩ := bondBetween?_of_adj (h.adj_get ht)
  obtain ⟨k₂, hk₂⟩ := bondBetween?_of_adj (h.adj_get hsn)
  have e : c[t]! = c[t] := getElem!_pos c t ht
  have r₁ := mem_ringBonds_of ht hk₁
  have r₂ := mem_ringBonds_of hsn hk₂
  obtain ⟨a₁, -, t₁⟩ := bondBetween?_spec hk₁
  rw [hst] at hk₂
  obtain ⟨b₂, a₂, -⟩ := bondBetween?_spec hk₂
  rw [e] at a₁ a₂
  refine ⟨k₁, k₂, ?_, r₁, r₂, a₁, a₂⟩
  rintro rfl
  have htt : (t + 1) % n < n := Nat.mod_lt _ (by omega)
  have hb := (List.mem_filter.1 b₂).2
  rcases t₁ _ hb with e' | e'
  · rw [getElem!_pos c s hsn, getElem!_pos c t ht] at e'
    have := (List.Nodup.getElem_inj_iff h.nodup).1 e'
    rw [hs] at this
    split at this <;> omega
  · rw [getElem!_pos c s hsn, getElem!_pos c _ htt] at e'
    have := (List.Nodup.getElem_inj_iff h.nodup).1 e'
    rw [succ_mod ht, hs] at this
    split at this <;> split at this <;> omega

/-- **Two rings at an atom with at most three bonds share a bond**: each takes two of its
bonds. -/
theorem IsRing.shared_bond {m : Work} {A B : List ℕ} (hA : m.IsRing A) (hB : m.IsRing B) {x : ℕ}
    (hxA : x ∈ A) (hxB : x ∈ B) (hd : (m.bondsOf x).length ≤ 3) :
    ∃ k ∈ m.ringBonds A, k ∈ m.ringBonds B := by
  obtain ⟨k₁, k₂, h12, r₁, r₂, a₁, a₂⟩ := hA.two_bonds hxA
  obtain ⟨k₃, k₄, h34, r₃, r₄, a₃, a₄⟩ := hB.two_bonds hxB
  by_contra hno
  push Not at hno
  have hnd : [k₁, k₂, k₃, k₄].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true]
    refine ⟨?_, ?_, h34, by simp⟩
    · rintro (e | e | e)
      · exact h12 e
      · exact hno _ r₁ (e ▸ r₃)
      · exact hno _ r₁ (e ▸ r₄)
    · rintro (e | e)
      · exact hno _ r₂ (e ▸ r₃)
      · exact hno _ r₂ (e ▸ r₄)
  have hsub : [k₁, k₂, k₃, k₄].toFinset ⊆ (m.bondsOf x).toFinset := by
    intro k hk
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    rcases hk with rfl | rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  have := List.toFinset_card_le (m.bondsOf x)
  simp at *
  omega

end Work

/-! ### Connected components -/

lemma count_false_set! (sn : Array Bool) {v : ℕ} (hv : v < sn.size) (h : sn[v]! = false) :
    (sn.set! v true).toList.count false + 1 = sn.toList.count false := by
  rw [getElem!_pos sn v hv] at h
  have hv' : v < sn.toList.length := by simpa using hv
  have hpos : 0 < sn.toList.count false :=
    List.count_pos_iff.2 (by rw [← h, ← Array.getElem_toList hv']; exact List.getElem_mem hv')
  rw [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.count_set hv',
    Array.getElem_toList hv', h]
  simp only [BEq.rfl, ↓reduceIte, Bool.true_beq, Bool.false_eq_true, Nat.add_zero]
  omega

lemma size_set!_any {α : Type} (a : Array α) (i : ℕ) (v : α) : (a.set! i v).size = a.size := by
  simp

/-- Pushing the neighbours `L`: the ones not seen yet are marked and go on the stack. -/
lemma foldl_pushNbr (L : List ℕ) (sn : Array Bool) (st : List ℕ)
    (hL : ∀ v ∈ L, v < sn.size) :
    ∃ sn' new, L.foldl pushNbr (sn, st) = (sn', new ++ st) ∧ sn'.size = sn.size ∧
      (∀ x, sn'[x]! = true ↔ sn[x]! = true ∨ x ∈ L) ∧
      (∀ x ∈ new, x ∈ L ∧ sn[x]! = false) ∧
      (∀ x ∈ L, sn[x]! = false → x ∈ new) ∧
      sn'.toList.count false + new.length = sn.toList.count false := by
  induction L generalizing sn st with
  | nil => exact ⟨sn, [], rfl, rfl, by simp, by simp, by simp, rfl⟩
  | cons v L ih =>
    have hv := hL v List.mem_cons_self
    rw [List.foldl_cons]
    have hstep : pushNbr (sn, st) v =
        (if !sn[v]! then (sn.set! v true, v :: st) else (sn, st)) := rfl
    rw [hstep]
    split
    · rename_i hsv
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hsv
      obtain ⟨sn', new, he, hs, hi, hn, hn', hc⟩ := ih (sn.set! v true) (v :: st)
        (fun w hw ↦ by rw [size_set!_any]; exact hL w (List.mem_cons_of_mem _ hw))
      refine ⟨sn', new ++ [v], by rw [he]; simp, by rw [hs, size_set!_any], ?_, ?_, ?_, ?_⟩
      · intro x
        rw [hi, getElem!_set!_any]
        constructor
        · rintro (h | h)
          · split at h
            · rename_i hx; exact .inr (hx.1 ▸ List.mem_cons_self)
            · exact .inl h
          · exact .inr (List.mem_cons_of_mem _ h)
        · rintro (h | h)
          · left
            split
            · rfl
            · exact h
          · rcases List.mem_cons.1 h with rfl | h
            · left; simp [hv]
            · exact .inr h
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · obtain ⟨h1, h2⟩ := hn x hx
          refine ⟨List.mem_cons_of_mem _ h1, ?_⟩
          rw [getElem!_set!_any] at h2
          split at h2
          · cases h2
          · exact h2
        · rw [List.mem_singleton] at hx
          subst hx
          exact ⟨List.mem_cons_self, hsv⟩
      · intro x hx hxs
        by_cases hxv : x = v
        · subst hxv; simp
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact absurd rfl hxv
          · refine List.mem_append_left _ (hn' x hx ?_)
            rw [getElem!_set!_any]
            split
            · rename_i h; exact absurd h.1.symm hxv
            · exact hxs
      · have := count_false_set! sn hv hsv
        simp only [List.length_append, List.length_singleton]
        omega
    · rename_i hsv
      have hsv' : sn[v]! = true := by simpa using hsv
      obtain ⟨sn', new, he, hs, hi, hn, hn', hc⟩ := ih sn st
        (fun w hw ↦ hL w (List.mem_cons_of_mem _ hw))
      refine ⟨sn', new, he, hs, ?_, fun x hx ↦ ⟨List.mem_cons_of_mem _ (hn x hx).1,
        (hn x hx).2⟩, ?_, hc⟩
      swap
      · intro x hx hxs
        rcases List.mem_cons.1 hx with rfl | hx
        · rw [hxs] at hsv'; cases hsv'
        · exact hn' x hx hxs
      intro x
      rw [hi]
      constructor
      · rintro (h | h)
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rintro (h | h)
        · exact .inl h
        · rcases List.mem_cons.1 h with rfl | h
          · exact .inl hsv'
          · exact .inr h

/-- The state of the search of one component, the atoms of earlier components being `O`. -/
structure DfsInv (n : ℕ) (nbrs : Array (List ℕ)) (O : ℕ → Prop) (seen : Array Bool)
    (comp stack : List ℕ) : Prop where
  size : seen.size = n
  seenIff : ∀ x, seen[x]! = true ↔ x < n ∧ (O x ∨ x ∈ comp ∨ x ∈ stack)
  lt : ∀ x, x ∈ comp ∨ x ∈ stack → x < n
  notOld : ∀ x, x ∈ comp ∨ x ∈ stack → ¬ O x
  closed : ∀ i ∈ comp, ∀ j ∈ nbrs[i]!, seen[j]! = true

lemma dfsComp_inv {n : ℕ} {nbrs : Array (List ℕ)} (hlt : ∀ i : ℕ, ∀ j ∈ nbrs[i]!, j < n)
    {O : ℕ → Prop} :
    ∀ (fuel : ℕ) (seen : Array Bool) (comp stack : List ℕ), DfsInv n nbrs O seen comp stack →
      stack.length + seen.toList.count false ≤ fuel →
      DfsInv n nbrs O (dfsComp nbrs fuel (seen, comp, stack)).1
        (dfsComp nbrs fuel (seen, comp, stack)).2 [] ∧
      ∀ x : ℕ, seen[x]! = true → (dfsComp nbrs fuel (seen, comp, stack)).1[x]! = true
  | 0, seen, comp, stack, h, hf => by
    have : stack = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨h, fun _ h ↦ h⟩
  | fuel + 1, seen, comp, [], h, _ => ⟨h, fun _ h ↦ h⟩
  | fuel + 1, seen, comp, u :: rest, h, hf => by
    unfold dfsComp
    obtain ⟨sn', new, he, hs, hi, hn, hn', hc⟩ := foldl_pushNbr nbrs[u]! seen rest
      (fun v hv ↦ h.size ▸ hlt u v hv)
    rw [he]
    dsimp only
    have hu : u < n := h.lt u (.inr List.mem_cons_self)
    have hnew : ∀ x ∈ new, x < n ∧ ¬ O x := by
      intro x hx
      obtain ⟨h1, h2⟩ := hn x hx
      have hxn := hlt u x h1
      refine ⟨hxn, fun ho ↦ ?_⟩
      have := (h.seenIff x).2 ⟨hxn, .inl ho⟩
      rw [this] at h2
      cases h2
    have inv : DfsInv n nbrs O sn' (u :: comp) (new ++ rest) := by
      refine ⟨hs.trans h.size, ?_, ?_, ?_, ?_⟩
      · intro x
        rw [hi, h.seenIff x]
        constructor
        · rintro (⟨hx, ho | hcx | hsx⟩ | hx)
          · exact ⟨hx, .inl ho⟩
          · exact ⟨hx, .inr (.inl (List.mem_cons_of_mem _ hcx))⟩
          · rcases List.mem_cons.1 hsx with rfl | hsx
            · exact ⟨hx, .inr (.inl List.mem_cons_self)⟩
            · exact ⟨hx, .inr (.inr (List.mem_append_right _ hsx))⟩
          · by_cases hsx : seen[x]! = true
            · rw [h.seenIff x] at hsx
              rcases hsx with ⟨hx', ho | hcx | hsx⟩
              · exact ⟨hx', .inl ho⟩
              · exact ⟨hx', .inr (.inl (List.mem_cons_of_mem _ hcx))⟩
              · rcases List.mem_cons.1 hsx with rfl | hsx
                · exact ⟨hx', .inr (.inl List.mem_cons_self)⟩
                · exact ⟨hx', .inr (.inr (List.mem_append_right _ hsx))⟩
            · have hxw : x ∈ new := hn' x hx (by simpa using hsx)
              exact ⟨hlt u x hx, .inr (.inr (List.mem_append_left _ hxw))⟩
        · rintro ⟨hx, ho | hcx | hsx⟩
          · exact .inl ⟨hx, .inl ho⟩
          · rcases List.mem_cons.1 hcx with rfl | hcx
            · exact .inl ⟨hx, .inr (.inr List.mem_cons_self)⟩
            · exact .inl ⟨hx, .inr (.inl hcx)⟩
          · rcases List.mem_append.1 hsx with hsx | hsx
            · exact .inr (hn x hsx).1
            · exact .inl ⟨hx, .inr (.inr (List.mem_cons_of_mem _ hsx))⟩
      · intro x hx
        rcases hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hu
          · exact h.lt x (.inl hx)
        · rcases List.mem_append.1 hx with hx | hx
          · exact (hnew x hx).1
          · exact h.lt x (.inr (List.mem_cons_of_mem _ hx))
      · intro x hx
        rcases hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact h.notOld _ (.inr List.mem_cons_self)
          · exact h.notOld x (.inl hx)
        · rcases List.mem_append.1 hx with hx | hx
          · exact (hnew x hx).2
          · exact h.notOld x (.inr (List.mem_cons_of_mem _ hx))
      · intro i hi' j hj
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact (hi j).2 (.inr hj)
        · exact (hi j).2 (.inl (h.closed i hi' j hj))
    obtain ⟨h1, h2⟩ := dfsComp_inv hlt fuel sn' (u :: comp) (new ++ rest) inv
      (by simp only [List.length_append, List.length_cons] at hf ⊢; omega)
    exact ⟨h1, fun x hx ↦ h2 x ((hi x).2 (.inl hx))⟩

/-- The state of `components` after some start atoms: the components found so far. -/
structure CompInv (n : ℕ) (nbrs : Array (List ℕ)) (seen : Array Bool) (comps : List (List ℕ)) :
    Prop where
  size : seen.size = n
  seenIff : ∀ x, seen[x]! = true ↔ ∃ C ∈ comps, x ∈ C
  lt : ∀ C ∈ comps, ∀ x ∈ C, x < n
  pairwise : comps.Pairwise fun C D ↦ ∀ x ∈ C, x ∉ D
  closed : ∀ C ∈ comps, ∀ i ∈ C, ∀ j ∈ nbrs[i]!, j ∈ C

lemma componentsStep_inv {n : ℕ} {nbrs : Array (List ℕ)} (hlt : ∀ i : ℕ, ∀ j ∈ nbrs[i]!, j < n)
    (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) {s : ℕ} (hs : s < n)
    {seen : Array Bool} {comps : List (List ℕ)} (h : CompInv n nbrs seen comps) :
    CompInv n nbrs (componentsStep n nbrs (seen, comps) s).1
        (componentsStep n nbrs (seen, comps) s).2 ∧
      (componentsStep n nbrs (seen, comps) s).1[s]! = true ∧
      ∀ x : ℕ, seen[x]! = true → (componentsStep n nbrs (seen, comps) s).1[x]! = true := by
  unfold componentsStep
  dsimp only
  split
  · rename_i hss
    exact ⟨h, hss, fun _ h ↦ h⟩
  rename_i hss
  simp only [Bool.not_eq_true] at hss
  have hsn : s < seen.size := h.size ▸ hs
  let O : ℕ → Prop := fun x ↦ ∃ C ∈ comps, x ∈ C
  have hO : ∀ x, O x → x < n := fun x ⟨C, hC, hx⟩ ↦ h.lt C hC x hx
  have hinit : DfsInv n nbrs O (seen.set! s true) [] [s] := by
    refine ⟨by rw [size_set!_any, h.size], ?_, ?_, ?_, by simp⟩
    · intro x
      rw [getElem!_set!_any, h.size]
      constructor
      · intro hx
        split at hx
        · rename_i e; exact ⟨e.2, .inr (.inr (by simp [e.1]))⟩
        · have := (h.seenIff x).1 hx
          exact ⟨hO x this, .inl this⟩
      · rintro ⟨hx, ho | hx' | hx'⟩
        · split
          · rfl
          · exact (h.seenIff x).2 ho
        · simp at hx'
        · simp only [List.mem_singleton] at hx'
          subst hx'
          simp [hx]
    · intro x hx
      simp only [List.not_mem_nil, List.mem_singleton, false_or] at hx
      exact hx ▸ hs
    · intro x hx ho
      simp only [List.not_mem_nil, List.mem_singleton, false_or] at hx
      subst hx
      rw [(h.seenIff _).2 ho] at hss
      cases hss
  have hcount : [s].length + (seen.set! s true).toList.count false ≤ n := by
    have := count_false_set! seen hsn hss
    have := List.count_le_length (a := false) (l := seen.toList)
    simp only [Array.length_toList, h.size] at this
    simp only [List.length_singleton]
    omega
  obtain ⟨hd, hmono⟩ := dfsComp_inv hlt n _ _ _ hinit hcount
  generalize dfsComp nbrs n (seen.set! s true, [], [s]) = res at hd hmono
  obtain ⟨seen', comp'⟩ := res
  dsimp only at hd hmono ⊢
  have hm : ∀ x : ℕ, seen[x]! = true → seen'[x]! = true := by
    intro x hx
    apply hmono
    rw [getElem!_set!_any]
    split
    · rfl
    · exact hx
  refine ⟨⟨hd.size, ?_, ?_, ?_, ?_⟩, hmono s (by simp [hsn]), hm⟩
  · intro x
    rw [hd.seenIff x]
    simp only [List.not_mem_nil, or_false, List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨-, ⟨C, hC, hx⟩ | hx⟩
      · exact ⟨C, .inl hC, hx⟩
      · exact ⟨_, .inr rfl, List.mem_mergeSort.2 hx⟩
    · rintro ⟨C, hC | rfl, hx⟩
      · exact ⟨h.lt C hC x hx, .inl ⟨C, hC, hx⟩⟩
      · rw [List.mem_mergeSort] at hx
        exact ⟨hd.lt x (.inl hx), .inr hx⟩
  · intro C hC x hx
    rcases List.mem_append.1 hC with hC | hC
    · exact h.lt C hC x hx
    · rw [List.mem_singleton] at hC
      subst hC
      exact hd.lt x (.inl (List.mem_mergeSort.1 hx))
  · rw [List.pairwise_append]
    refine ⟨h.pairwise, List.pairwise_singleton _ _, ?_⟩
    intro C hC D hD x hx hxD
    rw [List.mem_singleton] at hD
    subst hD
    exact hd.notOld x (.inl (List.mem_mergeSort.1 hxD)) ⟨C, hC, hx⟩
  · intro C hC i hi j hj
    rcases List.mem_append.1 hC with hC | hC
    · exact h.closed C hC i hi j hj
    · rw [List.mem_singleton] at hC
      subst hC
      rw [List.mem_mergeSort] at hi ⊢
      obtain ⟨-, ho | hj' | hj'⟩ := (hd.seenIff j).1 (hd.closed i hi j hj)
      · obtain ⟨D, hD, hjD⟩ := ho
        exact absurd ⟨D, hD, h.closed D hD j hjD i (hsym i j hj)⟩ (hd.notOld i (.inl hi))
      · exact hj'
      · simp at hj'

/-- **`components` is correct**: on a symmetric graph whose neighbours are in range, it lists
disjoint sets of vertices covering `[0, n)`, each closed under neighbours. -/
theorem components_spec {n : ℕ} {nbrs : Array (List ℕ)} (hlt : ∀ i : ℕ, ∀ j ∈ nbrs[i]!, j < n)
    (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) :
    (∀ i < n, ∃ C ∈ components n nbrs, i ∈ C) ∧
      (components n nbrs).Pairwise (fun C D ↦ ∀ x ∈ C, x ∉ D) ∧
      (∀ C ∈ components n nbrs, ∀ i ∈ C, i < n) ∧
      ∀ C ∈ components n nbrs, ∀ i ∈ C, ∀ j ∈ nbrs[i]!, j ∈ C := by
  have key : ∀ (l : List ℕ) (st : Array Bool × List (List ℕ)), (∀ s ∈ l, s < n) →
      CompInv n nbrs st.1 st.2 →
      CompInv n nbrs (l.foldl (componentsStep n nbrs) st).1
          (l.foldl (componentsStep n nbrs) st).2 ∧
        ∀ s ∈ l, (l.foldl (componentsStep n nbrs) st).1[s]! = true := by
    intro l
    induction l with
    | nil => exact fun st _ h ↦ ⟨h, by simp⟩
    | cons s l ih =>
      intro st hl h
      obtain ⟨seen, comps⟩ := st
      obtain ⟨h1, h2, h3⟩ := componentsStep_inv hlt hsym (hl s List.mem_cons_self) h
      rw [List.foldl_cons]
      obtain ⟨i1, i2⟩ := ih _ (fun s hs ↦ hl s (List.mem_cons_of_mem _ hs)) h1
      refine ⟨i1, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · -- seen stays seen through the later steps
        have hmono : ∀ (l : List ℕ) (st : Array Bool × List (List ℕ)), (∀ s ∈ l, s < n) →
            CompInv n nbrs st.1 st.2 → ∀ y : ℕ, st.1[y]! = true →
              (l.foldl (componentsStep n nbrs) st).1[y]! = true := by
          intro l
          induction l with
          | nil => exact fun _ _ _ _ h ↦ h
          | cons s' l ih' =>
            intro st hl' hst y hy
            obtain ⟨seen, comps⟩ := st
            obtain ⟨g1, -, g3⟩ := componentsStep_inv hlt hsym (hl' s' List.mem_cons_self) hst
            rw [List.foldl_cons]
            exact ih' _ (fun s hs ↦ hl' s (List.mem_cons_of_mem _ hs)) g1 y (g3 y hy)
        exact hmono l _ (fun s hs ↦ hl s (List.mem_cons_of_mem _ hs)) h1 x h2
      · exact i2 x hx
  have hinit : CompInv n nbrs (Array.replicate n false) [] := by
    refine ⟨by simp, ?_, by simp, .nil, by simp⟩
    intro x
    constructor
    · intro hx'
      by_cases hx : x < n
      · rw [getElem!_pos _ x (by simpa using hx)] at hx'; simp at hx'
      · rw [getElem!_neg _ x (by simpa using hx)] at hx'; cases hx'
    · rintro ⟨C, hC, -⟩
      simp at hC
  obtain ⟨hi, hs⟩ := key (List.range n) (Array.replicate n false, [])
    (fun s hs ↦ List.mem_range.1 hs) hinit
  unfold components
  refine ⟨fun i hi' ↦ (hi.seenIff i).1 (hs i (List.mem_range.2 hi')), hi.pairwise, hi.lt,
    hi.closed⟩

/-! ### Fused ring systems -/

namespace Work

/-- The rings sharing a bond with each ring (`Kekulize.cpp:727-746`), as `kekulize` builds them. -/
def kekFusedNbrs (m : Work) (rings : Array (List ℕ)) : Array (List ℕ) :=
  let rbonds := rings.map m.ringBonds
  (List.range rings.size).toArray.map fun i ↦
    (List.range rings.size).filter fun j ↦ j != i && rbonds[i]!.any rbonds[j]!.contains

/-- The atoms of a fused system (indices into `rings`), as `kekulizeSystem` collects them. -/
def systemAtoms (rings : Array (List ℕ)) (system : List ℕ) : List ℕ :=
  (system.flatMap (rings[·]!)).eraseDups

lemma mem_kekFusedNbrs {m : Work} {rings : Array (List ℕ)} {i j : ℕ} :
    j ∈ (m.kekFusedNbrs rings)[i]! ↔ i < rings.size ∧ j < rings.size ∧ j ≠ i ∧
      ∃ k ∈ m.ringBonds rings[i]!, k ∈ m.ringBonds rings[j]! := by
  have hm : ∀ t : ℕ, (rings.map m.ringBonds)[t]! = m.ringBonds rings[t]! := by
    intro t
    by_cases ht : t < rings.size
    · rw [getElem!_pos _ t (by simpa using ht), getElem!_pos rings t ht]; simp
    · rw [getElem!_neg _ t (by simpa using ht), getElem!_neg rings t ht]
      rfl
  unfold kekFusedNbrs
  dsimp only
  by_cases hi : i < rings.size
  · rw [getElem!_pos _ i (by simpa using hi)]
    rw [Array.getElem_map, List.getElem_toArray, List.getElem_range, List.mem_filter,
      List.mem_range, hm, hm]
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.contains_iff_mem]
    tauto
  · rw [getElem!_neg _ i (by simpa using hi)]
    constructor
    · intro h; exact absurd h List.not_mem_nil
    · exact fun h ↦ absurd h.1 hi

lemma mem_systemAtoms {rings : Array (List ℕ)} {system : List ℕ} {x : ℕ} :
    x ∈ systemAtoms rings system ↔ ∃ i ∈ system, x ∈ rings[i]! := by
  unfold systemAtoms
  rw [List.mem_eraseDups, List.mem_flatMap]

/-- **The fused systems**: every atom of a ring is in the atoms of a system, and an atom with at
most three bonds is in the atoms of at most one. -/
theorem fusedSystems_spec (m : Work) {rings : Array (List ℕ)}
    (hr : ∀ ring ∈ rings, m.IsRing ring) :
    (∀ i < rings.size, ∀ x ∈ rings[i]!, ∃ C ∈ components rings.size (m.kekFusedNbrs rings),
        x ∈ systemAtoms rings C) ∧
      (components rings.size (m.kekFusedNbrs rings)).Pairwise fun C D ↦
        ∀ x, x ∈ systemAtoms rings C → x ∈ systemAtoms rings D → 3 < (m.bondsOf x).length := by
  obtain ⟨hcov, hdis, -, hcl⟩ := components_spec (n := rings.size) (nbrs := m.kekFusedNbrs rings)
    (fun i j h ↦ (mem_kekFusedNbrs.1 h).2.1)
    (fun i j h ↦ by
      obtain ⟨h1, h2, h3, k, hk1, hk2⟩ := mem_kekFusedNbrs.1 h
      exact mem_kekFusedNbrs.2 ⟨h2, h1, Ne.symm h3, k, hk2, hk1⟩)
  refine ⟨fun i hi x hx ↦ ?_, ?_⟩
  · obtain ⟨C, hC, hiC⟩ := hcov i hi
    exact ⟨C, hC, mem_systemAtoms.2 ⟨i, hiC, hx⟩⟩
  · refine hdis.imp_of_mem fun {C D} hC hD hCD x hxC hxD ↦ ?_
    obtain ⟨i, hiC, hxi⟩ := mem_systemAtoms.1 hxC
    obtain ⟨j, hjD, hxj⟩ := mem_systemAtoms.1 hxD
    by_contra hle
    have hij : i ≠ j := fun e ↦ hCD i hiC (e ▸ hjD)
    have hi : i < rings.size := by
      by_contra h'; rw [getElem!_neg rings i h'] at hxi; exact absurd hxi List.not_mem_nil
    have hj : j < rings.size := by
      by_contra h'; rw [getElem!_neg rings j h'] at hxj; exact absurd hxj List.not_mem_nil
    have hRi : m.IsRing rings[i]! :=
      hr _ (by rw [getElem!_pos rings i hi]; exact Array.getElem_mem hi)
    have hRj : m.IsRing rings[j]! :=
      hr _ (by rw [getElem!_pos rings j hj]; exact Array.getElem_mem hj)
    obtain ⟨k, hk1, hk2⟩ := hRi.shared_bond hRj hxi hxj (by omega)
    have := hcl C hC i hiC j (mem_kekFusedNbrs.2 ⟨hi, hj, Ne.symm hij, k, hk1, hk2⟩)
    exact hCD j this hjD

end Work

end LeanSMILES.Aromaticity
