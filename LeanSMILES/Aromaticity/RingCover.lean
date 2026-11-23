/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeWalk
public import LeanSMILES.Aromaticity.Resonance
public import LeanSMILES.Aromaticity.ResonanceProofs
public import LeanSMILES.Aromaticity.RingSetIso

/-!
# LeanSMILES.Aromaticity.RingCover

**Ring perception misses no ring bond**: every bond on a cycle is a bond of one of the rings
`Work.relevantCycles` returns (`Molecule.ringsCoverCycles`).

Let bond `k` join `u` and `v`, still joined without it (`Work.onCycle`). Take a shortest walk
`x 0 = u, …, x n = v` that does not step between `u` and `v` (`Work.ShortOff`), and let `r` be its
middle atom. Both halves of the walk are shortest paths from `r` in the whole graph, so with the
bond they form a candidate cycle from `r`: closed by the bond when `n` is even, through `v` when
`n` is odd (`Work.ShortOff.exists_cand`). Its mask is not a sum of masks of strictly smaller
candidates, since one of those would be a shorter ring through bond `k`, and a ring through bond
`k` is a walk from `u` to `v` off the bond (`Work.relevant_of_min`). So ring perception keeps a
cycle with that mask, and bond `k` is one of its bonds.

## Main definitions

* `RWalk`: a walk of a given number of steps of a relation.
* `Work.Off`: two atoms are bonded and are not the two given atoms; adjacency without one bond.
* `Work.ShortOff`: a shortest walk between two bonded atoms off their bond.

## Main statements

* `Work.exists_rwalk_of_onCycle`: the ends of a bond on a cycle are joined by a walk off the bond.
* `Work.IsRing.rwalk_off_of_mem_ringBonds`: a ring through a bond is a walk between its ends off
  the bond.
* `Work.ShortOff.exists_cand`: a shortest such walk and the bond form a candidate cycle.
* `Work.mem_ringBonds_of_onCycle`: on a simple graph, a bond on a cycle is on a relevant cycle.
* `Molecule.ringsCoverCycles`: every molecule has `Molecule.RingsCoverCycles`.
* `aromaticBondsKekuleInvariant`: property 1 of `LeanSMILES.Aromaticity.Resonance`.

## Implementation notes

The statement needs the graph to be simple (`Work.NbrsDistinct`, true of the working copy of a
`Molecule`). Of two bonds between the same two atoms each is on a cycle, and neither is on a ring.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-! ### Walks of a relation -/

/-- A walk of `d` steps of the relation `R` from `a`. -/
inductive RWalk (R : ℕ → ℕ → Prop) (a : ℕ) : ℕ → ℕ → Prop
  /-- The empty walk. -/
  | refl : RWalk R a a 0
  /-- A walk to `b` extended by a step from `b` to `c`. -/
  | step {b c d : ℕ} : RWalk R a b d → R b c → RWalk R a c (d + 1)

namespace RWalk

variable {R : ℕ → ℕ → Prop}

/-- One step is a walk of length one. -/
lemma single {a b : ℕ} (h : R a b) : RWalk R a b 1 := .step .refl h

/-- Walks join end to end. -/
lemma trans {a b c d e : ℕ} (h : RWalk R a b d) (h' : RWalk R b c e) : RWalk R a c (d + e) := by
  induction h' with
  | refl => exact h
  | step _ hr ih => exact .step ih hr

/-- A walk of a symmetric relation runs backwards too. -/
lemma symm (hR : ∀ a b, R a b → R b a) {a b d : ℕ} (h : RWalk R a b d) : RWalk R b a d := by
  induction h with
  | refl => exact .refl
  | step _ hr ih =>
    have := (single (hR _ _ hr)).trans ih
    rwa [Nat.add_comm] at this

/-- A walk of `R` is a walk of any relation containing `R`. -/
lemma mono {S : ℕ → ℕ → Prop} (hRS : ∀ a b, R a b → S a b) {a b d : ℕ} (h : RWalk R a b d) :
    RWalk S a b d := by
  induction h with
  | refl => exact .refl
  | step _ hr ih => exact .step ih (hRS _ _ hr)

/-- The atoms of a walk, numbered from its start. -/
lemma exists_fun {a b d : ℕ} (h : RWalk R a b d) :
    ∃ x : ℕ → ℕ, x 0 = a ∧ x d = b ∧ ∀ j < d, R (x j) (x (j + 1)) := by
  induction h with
  | refl => exact ⟨fun _ ↦ a, rfl, rfl, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  | @step b c d _ hr ih =>
    obtain ⟨x, h0, hd, hx⟩ := ih
    refine ⟨fun j ↦ if j ≤ d then x j else c, by simp [h0], by simp, fun j hj ↦ ?_⟩
    by_cases hjd : j < d
    · simp only [if_pos hjd.le, if_pos (Nat.succ_le_of_lt hjd)]
      exact hx j hjd
    · obtain rfl : j = d := by omega
      simpa [hd] using hr

/-- Consecutive steps along numbered atoms make a walk between any two of them. -/
lemma of_fun {x : ℕ → ℕ} {n : ℕ} (hx : ∀ j < n, R (x j) (x (j + 1))) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ n) : RWalk R (x i) (x j) (j - i) := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    exact .refl
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | h
    · rw [Nat.sub_self]
      exact .refl
    · have := (ih (by omega) (by omega)).step (hx j (by omega))
      rwa [show j - i + 1 = j + 1 - i by omega] at this

end RWalk

namespace Work

/-- A walk of the copy is a walk of its adjacency. -/
lemma Walk.rwalk {m : Work} {r v d : ℕ} (h : m.Walk r v d) : RWalk m.Adj r v d := by
  induction h with
  | refl => exact .refl
  | step _ hadj ih => exact .step ih hadj

/-- A walk of the adjacency is a walk of the copy. -/
lemma walk_of_rwalk {m : Work} {r v d : ℕ} (h : RWalk m.Adj r v d) : m.Walk r v d := by
  induction h with
  | refl => exact .refl
  | step _ hadj ih => exact .step ih hadj

/-! ### Adjacency without one bond -/

/-- Atoms `a` and `b` are bonded and are not `u` and `v`: adjacency without the bond between `u`
and `v`. -/
def Off (m : Work) (u v a b : ℕ) : Prop := m.Adj a b ∧ ¬(a = u ∧ b = v) ∧ ¬(a = v ∧ b = u)

/-- Adjacency without a bond is symmetric. -/
lemma Off.symm {m : Work} {u v a b : ℕ} (h : m.Off u v a b) : m.Off u v b a :=
  ⟨h.1.symm, fun e ↦ h.2.2 ⟨e.2, e.1⟩, fun e ↦ h.2.1 ⟨e.2, e.1⟩⟩

/-- A walk off a bond runs backwards too. -/
lemma rwalk_off_symm {m : Work} {u v a b d : ℕ} (h : RWalk (m.Off u v) a b d) :
    RWalk (m.Off u v) b a d :=
  h.symm fun _ _ ↦ Off.symm

/-- A walk off a bond is a walk. -/
lemma rwalk_adj_of_off {m : Work} {u v a b d : ℕ} (h : RWalk (m.Off u v) a b d) :
    RWalk m.Adj a b d :=
  h.mono fun _ _ h ↦ h.1

/-- The two ends of a bond are adjacent. -/
lemma adj_src_dst (m : Work) {k : ℕ} (hk : k < m.numBonds) :
    m.Adj (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst := by
  refine ⟨k, List.mem_map.2 ⟨k, ?_, ?_⟩⟩
  · simp [bondsOf, hk, WBond.touches]
  · simp [WBond.other]

/-- On a simple graph, two bonds joining the same two atoms are one bond. -/
lemma eq_of_same_ends {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k k' : ℕ}
    (hk : k < m.numBonds) (hk' : k' < m.numBonds)
    (h : ((m.bonds[k']! : WBond).src = (m.bonds[k]! : WBond).src ∧
        (m.bonds[k']! : WBond).dst = (m.bonds[k]! : WBond).dst) ∨
      ((m.bonds[k']! : WBond).src = (m.bonds[k]! : WBond).dst ∧
        (m.bonds[k']! : WBond).dst = (m.bonds[k]! : WBond).src)) : k' = k := by
  have hne := (hwf k hk).2.2
  apply hnd (m.bonds[k]! : WBond).src
  · simp only [bondsOf, List.mem_filter, List.mem_range, WBond.touches, Bool.or_eq_true,
      beq_iff_eq]
    exact ⟨hk', by omega⟩
  · simp [bondsOf, hk, WBond.touches]
  · simp only [WBond.other, beq_iff_eq, if_true]
    split <;> omega

/-- On a simple graph, the ends of another bond are adjacent off bond `k`. -/
lemma off_src_dst {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k k' : ℕ}
    (hk : k < m.numBonds) (hk' : k' < m.numBonds) (hne : k' ≠ k) :
    m.Off (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst
      (m.bonds[k']! : WBond).src (m.bonds[k']! : WBond).dst :=
  ⟨adj_src_dst m hk', fun e ↦ hne (eq_of_same_ends hwf hnd hk hk' (.inl e)),
    fun e ↦ hne (eq_of_same_ends hwf hnd hk hk' (.inr e))⟩

/-- On a simple graph, `bondBetween?` finds bond `k` between the ends of bond `k`. -/
lemma bondBetween?_src_dst {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k : ℕ}
    (hk : k < m.numBonds) :
    m.bondBetween? (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst = some k := by
  obtain ⟨k', hk'⟩ := bondBetween?_of_adj (adj_src_dst m hk)
  rw [hk', eq_of_same_ends hwf hnd hk (bondBetween?_lt hk') (bondBetween?_ends hk')]

/-! ### From `onCycle` to a walk off the bond -/

/-- Every marked atom is joined to the first end of bond `k` by a walk off the bond. -/
def SweepInv (m : Work) (k : ℕ) (s : Array Bool) : Prop :=
  ∀ i : ℕ, s[i]! = true → ∃ d, RWalk (m.Off (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst)
    (m.bonds[k]! : WBond).src i d

/-- The start of the sweeps marks the first end of the bond alone. -/
lemma sweepInv_init (m : Work) (k : ℕ) :
    m.SweepInv k ((Array.replicate m.numAtoms false).set! (m.bonds[k]! : WBond).src true) := by
  intro i hi
  rw [getElem!_set!_any] at hi
  split at hi
  · rename_i hc
    exact ⟨0, hc.1 ▸ .refl⟩
  · by_cases hin : i < m.numAtoms
    · rw [getElem!_pos _ i (by simpa using hin)] at hi
      simp at hi
    · rw [getElem!_neg _ i (by simpa using hin)] at hi
      cases hi

/-- One bond of a sweep marks only atoms joined to the first end off the bond. -/
lemma SweepInv.sweepStep {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k : ℕ}
    (hk : k < m.numBonds) {s : Array Bool} (hs : m.SweepInv k s) {k' : ℕ}
    (hk' : k' < m.numBonds) : m.SweepInv k (m.sweepStep k s k') := by
  unfold Work.sweepStep
  split
  · exact hs
  rename_i hne
  have hoff := off_src_dst hwf hnd hk hk' (by simpa using hne)
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    intro i hi
    rw [getElem!_set!_any] at hi
    split at hi
    · rename_i hc
      obtain ⟨d, hd⟩ := hs _ h.1
      exact ⟨d + 1, hc.1 ▸ hd.step hoff⟩
    · exact hs i hi
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      intro i hi
      rw [getElem!_set!_any] at hi
      split at hi
      · rename_i hc
        obtain ⟨d, hd⟩ := hs _ h.1
        exact ⟨d + 1, hc.1 ▸ hd.step hoff.symm⟩
      · exact hs i hi
    · exact hs

/-- A sweep marks only atoms joined to the first end off the bond. -/
lemma SweepInv.reachSweep {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k : ℕ}
    (hk : k < m.numBonds) {s : Array Bool} (hs : m.SweepInv k s) :
    m.SweepInv k (m.reachSweep k s) := by
  rw [reachSweep_eq]
  suffices ∀ (l : List ℕ) (s : Array Bool), (∀ k' ∈ l, k' < m.numBonds) → m.SweepInv k s →
      m.SweepInv k (l.foldl (m.sweepStep k) s) from
    this _ s (fun k' hk' ↦ List.mem_range.1 hk') hs
  intro l
  induction l with
  | nil => exact fun _ _ h ↦ h
  | cons k' l ih =>
    intro s hl hs
    rw [List.foldl_cons]
    exact ih _ (fun j hj ↦ hl j (List.mem_cons_of_mem _ hj))
      (hs.sweepStep hwf hnd hk (hl k' List.mem_cons_self))

/-- **The ends of a bond on a cycle are joined by a walk off the bond**, on a simple graph. -/
theorem exists_rwalk_of_onCycle {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k : ℕ}
    (hk : k < m.numBonds) (hon : m.onCycle k = true) :
    ∃ d, RWalk (m.Off (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst)
      (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst d := by
  have hinv : ∀ t s, m.SweepInv k s → m.SweepInv k ((m.reachSweep k)^[t] s) := by
    intro t
    induction t with
    | zero => exact fun _ h ↦ h
    | succ t ih =>
      intro s hs
      rw [Function.iterate_succ_apply']
      exact (ih s hs).reachSweep hwf hnd hk
  exact hinv _ _ (sweepInv_init m k) _ hon

/-! ### A ring through a bond -/

/-- Around a ring, every step but the one from `u` to `v` (or back) is off their bond. -/
lemma IsRing.off_get {m : Work} {c : List ℕ} (hc : m.IsRing c) {t s u v : ℕ}
    (ht : t < c.length) (hs : s < c.length) (hst : s ≠ t)
    (huv : (c[t]! = u ∧ c[(t + 1) % c.length]! = v) ∨
      (c[t]! = v ∧ c[(t + 1) % c.length]! = u)) :
    m.Off u v c[s]! c[(s + 1) % c.length]! := by
  have h3 := hc.three
  have hmt : (t + 1) % c.length < c.length := Nat.mod_lt _ (by omega)
  have hms : (s + 1) % c.length < c.length := Nat.mod_lt _ (by omega)
  have h1 : c[s]! ≠ c[t]! := fun e ↦ hst (getElem!_inj hc.nodup hs ht e)
  have h2 : ¬(c[s]! = c[(t + 1) % c.length]! ∧ c[(s + 1) % c.length]! = c[t]!) := by
    rintro ⟨e1, e2⟩
    have a1 := getElem!_inj hc.nodup hs hmt e1
    have a2 := getElem!_inj hc.nodup hms ht e2
    rw [succ_mod ht] at a1
    rw [succ_mod hs] at a2
    split_ifs at a1 a2 <;> omega
  rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hc.adj_get hs, fun e ↦ h1 e.1, h2⟩
  · exact ⟨hc.adj_get hs, h2, fun e ↦ h1 e.1⟩

/-- A ring with `u` and `v` consecutive is a walk from `u` to `v` off their bond, the long way
round. -/
lemma IsRing.rwalk_off {m : Work} {c : List ℕ} (hc : m.IsRing c) {t u v : ℕ}
    (ht : t < c.length)
    (huv : (c[t]! = u ∧ c[(t + 1) % c.length]! = v) ∨
      (c[t]! = v ∧ c[(t + 1) % c.length]! = u)) :
    RWalk (m.Off u v) u v (c.length - 1) := by
  have hy : ∀ i < c.length - 1, m.Off u v ((fun i ↦ c[(t + 1 + i) % c.length]!) i)
      ((fun i ↦ c[(t + 1 + i) % c.length]!) (i + 1)) := by
    intro i hi
    have hs : (t + 1 + i) % c.length < c.length := Nat.mod_lt _ (by omega)
    have hne : (t + 1 + i) % c.length ≠ t := by
      by_cases h : t + 1 + i < c.length
      · rw [Nat.mod_eq_of_lt h]
        omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        omega
    have := hc.off_get ht hs hne huv
    rwa [Nat.mod_add_mod] at this
  have hw := RWalk.of_fun (R := m.Off u v) (x := fun i ↦ c[(t + 1 + i) % c.length]!) hy
    (Nat.zero_le (c.length - 1)) le_rfl
  have h1 : c[(t + 1 + (c.length - 1)) % c.length]! = c[t]! := by
    rw [show t + 1 + (c.length - 1) = t + c.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt ht]
  simp only [Nat.add_zero, Nat.sub_zero, h1] at hw
  rcases huv with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2] at hw
    exact rwalk_off_symm hw
  · rw [e1, e2] at hw
    exact hw

/-- **A ring through a bond is a walk between the bond's ends off the bond**, one step shorter
than the ring. -/
theorem IsRing.rwalk_off_of_mem_ringBonds {m : Work} {c : List ℕ} (hc : m.IsRing c) {k : ℕ}
    (hk : k ∈ m.ringBonds c) :
    RWalk (m.Off (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst)
      (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst (c.length - 1) := by
  rw [ringBonds_eq_filterMap, List.mem_filterMap] at hk
  obtain ⟨t, ht, hbb⟩ := hk
  refine hc.rwalk_off (List.mem_range.1 ht) ?_
  rcases bondBetween?_ends hbb with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact .inl ⟨e1.symm, e2.symm⟩
  · exact .inr ⟨e2.symm, e1.symm⟩

/-! ### Lists and paths -/

/-- A list of at least two atoms, reversed and without its last atom, starts with the list's last
atom. -/
lemma reverse_dropLast_eq_cons {q : List ℕ} {v : ℕ} (hl : q.getLast? = some v)
    (h2 : 2 ≤ q.length) : ∃ rest, q.reverse.dropLast = v :: rest := by
  obtain ⟨l, rfl⟩ : ∃ l, q = l ++ [v] := ⟨_, (List.dropLast_append_getLast? v hl).symm⟩
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  cases hr : l.reverse with
  | nil =>
    rw [List.reverse_eq_nil_iff] at hr
    subst hr
    simp at h2
  | cons b l' => exact ⟨_, rfl⟩

/-- The bond between the last atom of `p` and the atom after it is a ring bond. -/
lemma mem_ringBonds_append {m : Work} {p rest : List ℕ} {u v k : ℕ} (hp : p.getLast? = some u)
    (hbb : m.bondBetween? u v = some k) : k ∈ m.ringBonds (p ++ v :: rest) := by
  have hp0 : 0 < p.length := by
    rcases p with _ | ⟨a, p⟩
    · simp at hp
    · simp
  have hlen : (p ++ v :: rest).length = p.length + rest.length + 1 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hu : p[p.length - 1] = u := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hp
    exact Option.some.inj hp
  apply mem_ringBonds_of (t := p.length - 1) (by omega)
  rw [show p.length - 1 + 1 = p.length by omega, Nat.mod_eq_of_lt (by omega),
    getElem!_pos _ (p.length - 1) (by omega), getElem!_pos _ p.length (by omega),
    List.getElem_append_left (by omega), List.getElem_append_right (by omega), hu]
  simpa using hbb

/-- Atoms `y 0 = r, …, y d`, bonded in turn, the `i`-th at distance `i`, are a shortest path. -/
lemma pathOK_of_fun {m : Work} {dist : Array (Option ℕ)} {r d : ℕ} {y : ℕ → ℕ} (h0 : y 0 = r)
    (hadj : ∀ i < d, m.Adj (y i) (y (i + 1))) (hd : ∀ i ≤ d, dist[y i]! = some i) :
    m.PathOK dist r (y d) d ((List.range (d + 1)).map y) := by
  refine ⟨by simp, by simp [List.head?_range, h0], by simp [List.getLast?_range], ?_,
    fun i hi ↦ ?_⟩
  · rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_map, List.length_range] at hi
    simpa using hadj i (by omega)
  · simp only [List.length_map, List.length_range] at hi
    simpa using hd i (by omega)

/-- Two shortest paths from `r` that meet only at `r` have disjoint tails. -/
lemma disjointTails_of_inter {m : Work} {dist : Array (Option ℕ)} {r w w' d d' : ℕ}
    {p q : List ℕ} (hp : m.PathOK dist r w d p) (hq : m.PathOK dist r w' d' q)
    (h : ∀ z ∈ p, z ∈ q → z = r) : disjointTails p q = true := by
  obtain ⟨pt, rfl, -⟩ := hp.cons
  obtain ⟨qt, rfl, -⟩ := hq.cons
  have hn := hp.nodup
  simp only [disjointTails, List.tail_cons, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not]
  intro z hz hzq
  obtain rfl := h z (List.mem_cons_of_mem _ hz) (List.mem_cons_of_mem _ hzq)
  exact (List.nodup_cons.1 hn).1 hz

/-- A walk stays off the bond between `u` and `v`, or reaches `u` or `v` off the bond in fewer
steps. -/
lemma rwalk_off_cases {m : Work} {u v r w e : ℕ} (h : RWalk m.Adj r w e) :
    RWalk (m.Off u v) r w e ∨ (∃ e' < e, RWalk (m.Off u v) r u e') ∨
      ∃ e' < e, RWalk (m.Off u v) r v e' := by
  induction h with
  | refl => exact .inl .refl
  | @step b c d _ hadj ih =>
    rcases ih with ih | ⟨e', he', ih⟩ | ⟨e', he', ih⟩
    · by_cases h1 : b = u ∧ c = v
      · exact .inr (.inl ⟨d, Nat.lt_succ_self d, h1.1 ▸ ih⟩)
      · by_cases h2 : b = v ∧ c = u
        · exact .inr (.inr ⟨d, Nat.lt_succ_self d, h2.1 ▸ ih⟩)
        · exact .inl (ih.step ⟨hadj, h1, h2⟩)
    · exact .inr (.inl ⟨e', by omega, ih⟩)
    · exact .inr (.inr ⟨e', by omega, ih⟩)

/-! ### A shortest walk off the bond -/

/-- `x 0 = u, …, x n = v` is a shortest walk from `u` to `v` off their bond. -/
structure ShortOff (m : Work) (u v n : ℕ) (x : ℕ → ℕ) : Prop where
  /-- `u` and `v` are bonded. -/
  adj : m.Adj u v
  /-- `u` and `v` are different atoms. -/
  ne : u ≠ v
  /-- The walk starts at `u`. -/
  zero : x 0 = u
  /-- The walk ends at `v`. -/
  last : x n = v
  /-- Each step is off the bond. -/
  step : ∀ j < n, m.Off u v (x j) (x (j + 1))
  /-- No walk off the bond is shorter. -/
  min : ∀ e, RWalk (m.Off u v) u v e → n ≤ e

namespace ShortOff

variable {m : Work} {u v n : ℕ} {x : ℕ → ℕ}

/-- The part of the walk between two of its atoms. -/
lemma walk (h : m.ShortOff u v n x) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    RWalk (m.Off u v) (x i) (x j) (j - i) :=
  RWalk.of_fun h.step hij hj

/-- The walk has at least two steps. -/
lemma two_le (h : m.ShortOff u v n x) : 2 ≤ n := by
  by_contra hn
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · exact h.ne (h.zero.symm.trans h.last)
  · have := h.step 0 (by omega)
    have h1 : x (0 + 1) = v := h.last
    rw [h.zero, h1] at this
    exact this.2.1 ⟨rfl, rfl⟩

/-- The walk repeats no atom. -/
lemma inj (h : m.ShortOff u v n x) {i j : ℕ} (hij : i < j) (hj : j ≤ n) : x i ≠ x j := by
  intro e
  have w1 := h.walk (Nat.zero_le i) (by omega)
  have w2 := h.walk hj le_rfl
  rw [e, h.zero] at w1
  rw [h.last] at w2
  have := h.min _ (w1.trans w2)
  omega

/-- A walk off the bond from `x a` to `u` has at least `a` steps. -/
lemma le_of_rwalk_left (h : m.ShortOff u v n x) {a e : ℕ} (ha : a ≤ n)
    (hw : RWalk (m.Off u v) (x a) u e) : a ≤ e := by
  have w2 := h.walk ha le_rfl
  rw [h.last] at w2
  have := h.min _ ((rwalk_off_symm hw).trans w2)
  omega

/-- A walk off the bond from `x a` to `v` has at least `n - a` steps. -/
lemma le_of_rwalk_right (h : m.ShortOff u v n x) {a e : ℕ} (ha : a ≤ n)
    (hw : RWalk (m.Off u v) (x a) v e) : n - a ≤ e := by
  have w1 := h.walk (Nat.zero_le a) ha
  rw [h.zero] at w1
  have := h.min _ (w1.trans hw)
  omega

/-- From an atom `x a` no nearer `v` than `u`, every walk to `u` has at least `a` steps. -/
lemma le_of_adj_left (h : m.ShortOff u v n x) {a e : ℕ} (ha : a ≤ n) (hab : a ≤ n - a)
    (hw : RWalk m.Adj (x a) u e) : a ≤ e := by
  rcases rwalk_off_cases (u := u) (v := v) hw with hw | ⟨e', he', hw⟩ | ⟨e', he', hw⟩
  · exact h.le_of_rwalk_left ha hw
  · have := h.le_of_rwalk_left ha hw
    omega
  · have := h.le_of_rwalk_right ha hw
    omega

/-- From an atom `x a` at most one step nearer `u` than `v`, every walk to `v` has at least
`n - a` steps. -/
lemma le_of_adj_right (h : m.ShortOff u v n x) {a e : ℕ} (ha : a ≤ n) (hab : n - a ≤ a + 1)
    (hw : RWalk m.Adj (x a) v e) : n - a ≤ e := by
  rcases rwalk_off_cases (u := u) (v := v) hw with hw | ⟨e', he', hw⟩ | ⟨e', he', hw⟩
  · exact h.le_of_rwalk_right ha hw
  · have := h.le_of_rwalk_left ha hw
    omega
  · have := h.le_of_rwalk_right ha hw
    omega

/-- Back along the walk from `x a`, the `i`-th atom is at distance `i` in the whole graph. -/
lemma isDist_left (h : m.ShortOff u v n x) {a i : ℕ} (ha : a ≤ n) (hab : a ≤ n - a)
    (hi : i ≤ a) : m.IsDist (x a) (x (a - i)) i := by
  have w := rwalk_off_symm (h.walk (Nat.sub_le a i) ha)
  rw [show a - (a - i) = i by omega] at w
  refine ⟨walk_of_rwalk (rwalk_adj_of_off w), fun e he ↦ ?_⟩
  have w' := rwalk_off_symm (h.walk (Nat.zero_le (a - i)) (by omega))
  rw [h.zero] at w'
  have := h.le_of_adj_left ha hab (he.rwalk.trans (rwalk_adj_of_off w'))
  omega

/-- Forward along the walk from `x a`, the `i`-th atom is at distance `i` in the whole graph. -/
lemma isDist_right (h : m.ShortOff u v n x) {a i : ℕ} (hab : n - a ≤ a + 1)
    (hi : a + i ≤ n) : m.IsDist (x a) (x (a + i)) i := by
  have w := h.walk (Nat.le_add_right a i) hi
  rw [Nat.add_sub_cancel_left] at w
  refine ⟨walk_of_rwalk (rwalk_adj_of_off w), fun e he ↦ ?_⟩
  have w' := h.walk hi le_rfl
  rw [h.last] at w'
  have := h.le_of_adj_right (by omega) hab (he.rwalk.trans (rwalk_adj_of_off w'))
  omega

/-- The first half of the walk, read back from `x a` to `u`, is a shortest path from `x a`. -/
lemma pathOK_left (h : m.ShortOff u v n x) (hwf : m.WF) {a : ℕ} (ha : a ≤ n)
    (hab : a ≤ n - a) (hr : x a < m.numAtoms) :
    m.PathOK (m.bfs (x a)).1 (x a) u a ((List.range (a + 1)).map fun i ↦ x (a - i)) := by
  have e : x (a - a) = u := by rw [Nat.sub_self, h.zero]
  rw [← e]
  refine pathOK_of_fun (y := fun i ↦ x (a - i)) rfl (fun i hi ↦ ?_)
    fun i hi ↦ (bfs_dist hwf hr _ _).2 (h.isDist_left ha hab hi)
  have := (h.step (a - (i + 1)) (by omega)).1.symm
  rwa [show a - (i + 1) + 1 = a - i by omega] at this

/-- The walk from `x a` on to `x (a + b)` is a shortest path from `x a`. -/
lemma pathOK_right (h : m.ShortOff u v n x) (hwf : m.WF) {a b : ℕ} (hab : n - a ≤ a + 1)
    (hb : a + b ≤ n) (hr : x a < m.numAtoms) :
    m.PathOK (m.bfs (x a)).1 (x a) (x (a + b)) b ((List.range (b + 1)).map fun i ↦ x (a + i)) :=
  pathOK_of_fun (y := fun i ↦ x (a + i)) rfl (fun i hi ↦ (h.step (a + i) (by omega)).1)
    fun i hi ↦ (bfs_dist hwf hr _ _).2 (h.isDist_right hab (by omega))

/-- The walk back from `x a` and the walk on from `x a` meet only at `x a`. -/
lemma inter (h : m.ShortOff u v n x) {a b : ℕ} (hb : a + b ≤ n) :
    ∀ z ∈ (List.range (a + 1)).map fun i ↦ x (a - i),
      z ∈ (List.range (b + 1)).map (fun i ↦ x (a + i)) → z = x a := by
  intro z hz hz'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
  obtain ⟨j, hj, e⟩ := List.mem_map.1 hz'
  rw [List.mem_range] at hi hj
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · rfl
  · exact absurd e.symm (h.inj (by omega) (by omega))

/-- **A shortest walk of an even number of steps and the bond form an odd candidate** from the
walk's middle atom. -/
lemma exists_oddCand (h : m.ShortOff u v n x) (hwf : m.WF) {k a : ℕ}
    (hbb : m.bondBetween? u v = some k) (hn : n = 2 * a) :
    ∃ c, m.OddCand (x a) c ∧ x a < m.numAtoms ∧ c.length = n + 1 ∧ k ∈ m.ringBonds c := by
  have h2 := h.two_le
  have hr : x a < m.numAtoms := (Adj.lt hwf (h.step a (by omega)).1).1
  have hp := h.pathOK_left hwf (a := a) (by omega) (by omega) hr
  have hq := h.pathOK_right hwf (a := a) (b := a) (by omega) (by omega) hr
  have hdis := disjointTails_of_inter hp hq (h.inter (by omega))
  have hxa : x (a + a) = v := by rw [← h.last, hn, Nat.two_mul]
  rw [hxa] at hq
  obtain ⟨rest, hrest⟩ := reverse_dropLast_eq_cons hq.last (by rw [hq.length]; omega)
  have hdu := (bfs_dist hwf hr _ _).2 (h.isDist_left (a := a) (i := a) (by omega) (by omega)
    le_rfl)
  have hdv := (bfs_dist hwf hr _ _).2 (h.isDist_right (a := a) (i := a) (by omega) (by omega))
  rw [Nat.sub_self, h.zero] at hdu
  rw [hxa] at hdv
  refine ⟨_, ⟨u, v, a, _, _, hdu, by omega, hdv, h.adj, hp, hq, hdis, rfl⟩, hr, ?_, ?_⟩
  · simp only [List.length_append, List.length_dropLast, List.length_reverse, List.length_map,
      List.length_range]
    omega
  · rw [hrest]
    exact mem_ringBonds_append hp.last hbb

/-- **A shortest walk of an odd number of steps and the bond form an even candidate** from the
atom before the walk's middle bond, closed through `v`. -/
lemma exists_evenCand (h : m.ShortOff u v n x) (hwf : m.WF) {k a : ℕ}
    (hbb : m.bondBetween? u v = some k) (hn : n = 2 * a + 1) :
    ∃ c, m.EvenCand (x a) c ∧ x a < m.numAtoms ∧ c.length = n + 1 ∧ k ∈ m.ringBonds c := by
  have h2 := h.two_le
  have hr : x a < m.numAtoms := (Adj.lt hwf (h.step a (by omega)).1).1
  have hp := h.pathOK_left hwf (a := a) (by omega) (by omega) hr
  have hq := h.pathOK_right hwf (a := a) (b := a) (by omega) (by omega) hr
  have hdis := disjointTails_of_inter hp hq (h.inter (by omega))
  have hv : x (a + a + 1) = v := by rw [← h.last, hn, Nat.two_mul]
  have hstep := h.step (a + a) (by omega)
  rw [hv] at hstep
  have hdu := (bfs_dist hwf hr _ _).2 (h.isDist_left (a := a) (i := a) (by omega) (by omega)
    le_rfl)
  have hdw := (bfs_dist hwf hr _ _).2 (h.isDist_right (a := a) (i := a) (by omega) (by omega))
  have hdv := (bfs_dist hwf hr _ _).2 (h.isDist_right (a := a) (i := a + 1) (by omega)
    (by omega))
  rw [Nat.sub_self, h.zero] at hdu
  rw [← Nat.add_assoc, hv] at hdv
  have hne : u ≠ x (a + a) := by
    rw [← h.zero]
    exact h.inj (by omega) (by omega)
  refine ⟨_, ⟨v, u, x (a + a), a + 1, _, _, hdv, by omega, h.adj.symm, hstep.1.symm, hne, hdu,
    hdw, hp, hq, hdis, rfl⟩, hr, ?_, ?_⟩
  · simp only [List.length_append, List.length_dropLast, List.length_reverse, List.length_map,
      List.length_range, List.length_cons, List.length_nil]
    omega
  · rw [List.append_assoc, List.singleton_append]
    exact mem_ringBonds_append hp.last hbb

/-- **A shortest walk off a bond and the bond form a candidate cycle**: one more atom than the
walk has steps, with the bond among its ring bonds. -/
theorem exists_cand (h : m.ShortOff u v n x) (hwf : m.WF) {k : ℕ}
    (hbb : m.bondBetween? u v = some k) :
    ∃ r < m.numAtoms, ∃ c, m.Cand r c ∧ c.length = n + 1 ∧ k ∈ m.ringBonds c := by
  rcases Nat.even_or_odd' n with ⟨a, hn | hn⟩
  · obtain ⟨c, hc, hr, hl, hk⟩ := h.exists_oddCand hwf hbb hn
    exact ⟨_, hr, c, .inl hc, hl, hk⟩
  · obtain ⟨c, hc, hr, hl, hk⟩ := h.exists_evenCand hwf hbb hn
    exact ⟨_, hr, c, .inr hc, hl, hk⟩

end ShortOff

/-! ### The candidate is relevant -/

/-- A sum of masks with bit `k` set has a summand with bit `k` set. -/
lemma exists_testBit_of_xspan {S : List ℕ} {v k : ℕ} (hv : XSpan S v)
    (hk : v.testBit k = true) : ∃ s ∈ S, s.testBit k = true := by
  induction hv with
  | zero => simp at hk
  | @add s v hs _ ih =>
    rw [Nat.testBit_xor] at hk
    by_cases hsk : s.testBit k = true
    · exact ⟨s, hs, hsk⟩
    · exact ih (by simpa [hsk] using hk)

/-- **A candidate through bond `k` no longer than every ring through `k` is relevant**: if no
walk between the ends of bond `k` off the bond has fewer than `n` steps, a candidate of `n + 1`
bonds with bond `k` is not a sum of strictly smaller candidates. -/
theorem relevant_of_min {m : Work} {k n : ℕ}
    (hmin : ∀ e, RWalk (m.Off (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst)
      (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst e → n ≤ e)
    {c : ℕ × List ℕ} (hpop : popcount c.1 = n + 1) (hbit : c.1.testBit k = true) :
    Relevant (m.candidateCycles.toList.mergeSort relevantCmp) c := by
  intro hspan
  obtain ⟨s, hs, hsk⟩ := exists_testBit_of_xspan hspan hbit
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hs
  obtain ⟨hd, hlt⟩ := List.mem_filter.1 hd
  rw [List.mem_mergeSort] at hd
  rw [decide_eq_true_eq, hpop, popcount_of_mem_candidateCycles m hd] at hlt
  have hring := isRing_of_mem_candidateCycles m (Array.mem_def.2 hd)
  rw [((candidateCycles_spec m).2.1 d hd).1, ← mem_ringBonds_iff_testBit] at hsk
  have h3 := hring.three
  have := hmin _ (hring.rwalk_off_of_mem_ringBonds hsk)
  omega

/-- **On a simple graph, a bond on a cycle is a bond of a relevant cycle.** -/
theorem mem_ringBonds_of_onCycle {m : Work} (hwf : m.WF) (hnd : m.NbrsDistinct) {k : ℕ}
    (hk : k < m.numBonds) (hon : m.onCycle k = true) :
    ∃ c ∈ m.relevantCycles.toList, k ∈ m.ringBonds c := by
  classical
  have hex := exists_rwalk_of_onCycle hwf hnd hk hon
  obtain ⟨x, h0, hn, hx⟩ := (Nat.find_spec hex).exists_fun
  have hshort : m.ShortOff (m.bonds[k]! : WBond).src (m.bonds[k]! : WBond).dst (Nat.find hex) x :=
    ⟨adj_src_dst m hk, (hwf k hk).2.2, h0, hn, hx, fun e he ↦ Nat.find_min' hex he⟩
  obtain ⟨r, hr, c, hc, hlen, hkc⟩ := hshort.exists_cand hwf (bondBetween?_src_dst hwf hnd hk)
  obtain ⟨c', hc', hcc'⟩ := exists_mem_cyclesFrom_of_cand hwf hr hc
  obtain ⟨e, he, hmask⟩ := (candidateCycles_spec m).2.2 r hr c' hc'
  have hpop : popcount e.1 = Nat.find hex + 1 := by
    rw [hmask, (isRing_of_mem_cyclesFrom m hr hc').popcount_cycleMask, hcc'.length, hlen]
  have hbit : e.1.testBit k = true := by
    rw [hmask, ← mem_ringBonds_iff_testBit]
    exact (hcc'.ringBonds m).mem_iff.2 hkc
  refine ⟨e.2, ?_, ?_⟩
  · rw [relevantCycles_toList]
    exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨List.mem_mergeSort.2 he,
      decide_eq_true (relevant_of_min (fun e he ↦ Nat.find_min' hex he) hpop hbit)⟩, rfl⟩
  · rw [mem_ringBonds_iff_testBit, ← ((candidateCycles_spec m).2.1 e he).1]
    exact hbit

end Work

end LeanSMILES.Aromaticity

namespace LeanSMILES.Molecule

open Aromaticity

/-- **Ring perception misses no ring bond**: every bond of a molecule that lies on a cycle is a
bond of one of the rings `Work.relevantCycles` returns. -/
theorem ringsCoverCycles {n : ℕ} (m : Molecule n) : m.RingsCoverCycles := by
  intro k hk hon
  obtain ⟨c, hc, hkc⟩ := Work.mem_ringBonds_of_onCycle (ofMolecule_wf m)
    (Work.nbrsDistinct_ofMolecule m) (by rwa [ofMolecule_numBonds]) hon
  exact List.mem_flatMap.2 ⟨c, hc, hkc⟩

end LeanSMILES.Molecule

namespace LeanSMILES.Aromaticity

/-- **Property 1.** Kekulé partners whose moved bonds avoid the atoms `cleanUp` rewrites get the
same aromatic bonds. From `aromaticBonds_aromatize_eq_of_ringsCoverCycles`, since ring perception
misses no ring bond (`Molecule.ringsCoverCycles`). -/
theorem aromaticBondsKekuleInvariant : AromaticBondsKekuleInvariant :=
  fun _ m₁ _ hk hp hc ↦
    aromaticBonds_aromatize_eq_of_ringsCoverCycles hk hp hc (Molecule.ringsCoverCycles m₁)

end LeanSMILES.Aromaticity
