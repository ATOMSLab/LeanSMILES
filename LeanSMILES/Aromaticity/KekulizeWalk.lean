/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeFacts
public import LeanSMILES.Aromaticity.KekuleSim
public import LeanSMILES.Aromaticity.ResonanceProofs

/-!
# LeanSMILES.Aromaticity.KekulizeWalk

RDKit's kekulization walk (`Work.kekulizeWorker`) is correct: when it succeeds on a fused system,
every atom that needed a double bond has exactly one, on a bond written aromatic, and no other
atom of the system has one.

The walk visits the system's atoms through a queue, gives each atom that still needs a double
bond one to its first neighbour that also needs one, and on getting stuck backtracks to the
latest atom that had other neighbours to try (`Work.KekState.backTrack`).  On revisiting that
atom it takes the next of the neighbours it stored, without checking again that they still need
a double bond (RDKit does the same).  That is safe because of the order in which atoms are done:
a neighbour stored for atom `a` is either still without a double bond, or got one across a bond
both of whose ends were done after `a`; backtracking to `a` undoes exactly those bonds.

This file proves it in steps: first the structural facts (the neighbour scan in closed form,
`nextAtom`), then an invariant of the walk's state, then the conclusion.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-! ### The neighbour scan -/

/-- Whether the scan takes neighbour `j` of `curr` as an option for its double bond: both need
one and their bond was written aromatic. -/
def scanTakes (m : Work) (wa : ℕ → Bool) (cands : Array Bool) (curr : ℕ) (ccand : Bool)
    (j : ℕ) : Bool :=
  match m.bondBetween? curr j with
  | some k => ccand && cands[j]! && wa k
  | none => false

/-- **The neighbour scan in closed form**: it queues the neighbours not already queued, and
takes as options those `scanTakes` accepts, in order. -/
lemma foldl_scanStep (m : Work) (wa : ℕ → Bool) (cands : Array Bool) (curr : ℕ) (ccand : Bool)
    (queue : List ℕ) :
    ∀ (l : List ℕ) (a b : List ℕ), l.foldl (scanStep m wa cands curr ccand queue) (a, b) =
      (a ++ l.filter (fun j ↦ !queue.contains j), b ++ l.filter (scanTakes m wa cands curr ccand))
  | [], a, b => by simp
  | j :: l, a, b => by
    rw [List.foldl_cons]
    have e : scanStep m wa cands curr ccand queue (a, b) j =
        (if !queue.contains j then a ++ [j] else a,
          if scanTakes m wa cands curr ccand j then b ++ [j] else b) := by
      unfold scanStep scanTakes
      dsimp only
      cases m.bondBetween? curr j <;> simp
    rw [e, foldl_scanStep m wa cands curr ccand queue l]
    simp only [List.filter_cons]
    split <;> split <;> simp

/-- An option the scan takes is a neighbour across a bond written aromatic, and needs a double
bond, as does `curr`. -/
lemma scanTakes_spec {m : Work} {wa : ℕ → Bool} {cands : Array Bool} {curr : ℕ} {ccand : Bool}
    {j : ℕ} (h : scanTakes m wa cands curr ccand j = true) :
    ccand = true ∧ cands[j]! = true ∧ ∃ k, m.bondBetween? curr j = some k ∧ wa k = true := by
  unfold scanTakes at h
  split at h
  · rename_i k hk
    simp only [Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2, k, hk, h.2⟩
  · cases h

/-! ### The next atom -/

/-- The next atom is the queue's head, or with an empty queue the lowest atom not done. -/
lemma nextAtom_eq_some {s : KekState} {sorted : List ℕ} {curr : ℕ} {q : List ℕ}
    (h : s.nextAtom sorted = some (curr, q)) :
    s.queue = curr :: q ∨ (s.queue = [] ∧ q = [] ∧ curr ∈ sorted ∧ curr ∉ s.done) := by
  unfold KekState.nextAtom at h
  split at h
  · rename_i c rest hq
    cases h
    exact .inl hq
  · rename_i hq
    obtain ⟨c, hc, he⟩ := Option.map_eq_some_iff.mp h
    cases he
    have hmem := List.mem_of_find?_eq_some hc
    have hnd := List.find?_some hc
    exact .inr ⟨hq, rfl, hmem, by simpa using hnd⟩

/-- With no next atom, the queue is empty and every atom is done. -/
lemma nextAtom_eq_none {s : KekState} {sorted : List ℕ} (h : s.nextAtom sorted = none) :
    s.queue = [] ∧ ∀ x ∈ sorted, x ∈ s.done := by
  unfold KekState.nextAtom at h
  split at h
  · cases h
  · rename_i hq
    refine ⟨hq, fun x hx ↦ ?_⟩
    rw [Option.map_eq_none_iff, List.find?_eq_none] at h
    have := h x hx
    simpa using this

/-! ### Distinct neighbours -/

/-- No two bonds join an atom to the same neighbour. -/
def NbrsDistinct (w : Work) : Prop :=
  ∀ c k₁ k₂, k₁ ∈ w.bondsOf c → k₂ ∈ w.bondsOf c →
    (w.bonds[k₁]! : WBond).other c = (w.bonds[k₂]! : WBond).other c → k₁ = k₂

/-- With distinct neighbours, an atom's neighbour list has no repeats. -/
lemma nodup_neighbors {w : Work} (h : w.NbrsDistinct) (c : ℕ) :
    ((w.neighbors c).map (·.2)).Nodup := by
  have hb : (w.bondsOf c).Nodup := (List.nodup_range).filter _
  simp only [neighbors, List.map_map]
  refine hb.map_on fun k₁ hk₁ k₂ hk₂ he ↦ h c k₁ k₂ hk₁ hk₂ ?_
  simpa using he

/-! ### Lists -/

/-- The part of a list before `a`. -/
def before (l : List ℕ) (a : ℕ) : List ℕ := l.takeWhile (· != a)

lemma before_sub {l : List ℕ} {a x : ℕ} (h : x ∈ before l a) : x ∈ l :=
  (List.takeWhile_sublist _).subset h

/-- Before an element not in the list: the whole list. -/
lemma before_of_not_mem : ∀ {l : List ℕ} {a : ℕ}, a ∉ l → before l a = l
  | [], _, _ => rfl
  | x :: l, a, h => by
    rw [List.mem_cons, not_or] at h
    have hx : (x != a) = true := by simpa using Ne.symm h.1
    simp only [before, List.takeWhile_cons, hx, ↓reduceIte, List.cons.injEq, true_and]
    exact before_of_not_mem h.2

/-- Appending after `a` does not change what comes before it. -/
lemma before_append_of_mem : ∀ {l r : List ℕ} {a : ℕ}, a ∈ l → before (l ++ r) a = before l a
  | [], _, _, h => by simp at h
  | x :: l, r, a, h => by
    by_cases hx : x = a
    · subst hx
      simp [before, List.takeWhile_cons]
    · have hx' : (x != a) = true := by simpa using hx
      rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hx
      · simp only [before, List.cons_append, List.takeWhile_cons, hx', ↓reduceIte,
          List.cons.injEq, true_and]
        exact before_append_of_mem h

/-- A key of an association list is found by `lookup`. -/
lemma lookup_isSome_of_mem {β : Type*} {l : List (ℕ × β)} {a : ℕ} (h : a ∈ l.map (·.1)) :
    (l.lookup a).isSome := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨x, y⟩ := p
    simp only [List.lookup]
    split
    · rfl
    · rename_i hx
      rw [List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · subst h
        simp at hx
      · exact ih h

/-! ### The invariant -/

section Walk

variable (wa : ℕ → Bool) (atoms : List ℕ) (m0 : Work) (cands0 : Array Bool)

/-- Bond `k` of the starting copy touches atom `x`. -/
def Tch (k x : ℕ) : Prop := (m0.bonds[k]! : WBond).touches x = true

/-- Atom `x` has a double bond the walk placed. -/
def Matched (s : KekState) (x : ℕ) : Prop := ∃ k, s.adds[k]! = true ∧ Tch m0 k x

/-- **The walk's invariant** over a fused system with atoms `atoms`, starting from the copy `m0`
(its aromatic bonds made single) and the candidates `cands0`. -/
structure WalkInv (s : KekState) : Prop where
  /-- The bonds join the same atoms as in `m0`. -/
  skel : SameSkel m0 s.m
  /-- A bond is double where the walk placed one, else as in `m0`. -/
  kinds : ∀ k : ℕ, (s.m.bonds[k]! : WBond).kind =
    if s.adds[k]! then .double else (m0.bonds[k]! : WBond).kind
  /-- One flag per bond. -/
  addsSize : s.adds.size = m0.bonds.size
  /-- One flag per atom. -/
  candsSize : s.cands.size = m0.atoms.size
  /-- A placed double bond was a single bond written aromatic between two candidates. -/
  addsOk : ∀ k : ℕ, s.adds[k]! = true → k < m0.bonds.size ∧ wa k = true ∧
    (m0.bonds[k]! : WBond).kind = .single ∧ cands0[(m0.bonds[k]! : WBond).src]! = true ∧
    cands0[(m0.bonds[k]! : WBond).dst]! = true
  /-- No atom has two placed double bonds. -/
  matching : ∀ k₁ k₂ x : ℕ, s.adds[k₁]! = true → s.adds[k₂]! = true → Tch m0 k₁ x →
    Tch m0 k₂ x → k₁ = k₂
  /-- An atom still needs a double bond iff it needed one and has none. -/
  cands : ∀ x : ℕ, s.cands[x]! = true ↔ cands0[x]! = true ∧ ¬ Matched m0 s x
  /-- No done atom still needs a double bond. -/
  doneNC : ∀ x ∈ s.done, s.cands[x]! = false
  /-- Every placed double bond has an end done. -/
  addsDone : ∀ k : ℕ, s.adds[k]! = true →
    (m0.bonds[k]! : WBond).src ∈ s.done ∨ (m0.bonds[k]! : WBond).dst ∈ s.done
  /-- The done list has no repeats. -/
  doneNodup : s.done.Nodup
  /-- The queue has no repeats. -/
  queueNodup : s.queue.Nodup
  /-- No queued atom is done. -/
  disjoint : ∀ x ∈ s.queue, x ∉ s.done
  /-- Done atoms are the system's. -/
  doneSub : ∀ x ∈ s.done, x ∈ atoms
  /-- Queued atoms are the system's. -/
  queueSub : ∀ x ∈ s.queue, x ∈ atoms
  /-- **The order fact**: an option kept for `a` needed a double bond, lies across a bond
  written aromatic, and any double bond it has now joins two atoms done after `a` (or not done). -/
  opt : ∀ a o, (a, o) ∈ s.options → o ≠ [] ∧ o.Nodup ∧ ∀ j ∈ o, j ≠ a ∧ cands0[j]! = true ∧
    j ∈ atoms ∧ (∃ k, m0.bondBetween? a j = some k ∧ wa k = true) ∧
    ∀ k : ℕ, s.adds[k]! = true → Tch m0 k j →
      (m0.bonds[k]! : WBond).src ∉ before s.done a ∧ (m0.bonds[k]! : WBond).dst ∉ before s.done a
  /-- The atoms with kept options are the backtrack points, in order. -/
  keys : s.options.map (·.1) = s.btMoves
  /-- The atom to backtrack to is the latest. -/
  lastOpt : s.lastOpt = s.btMoves.getLast?
  /-- The backtrack points were done in order; right after a backtrack the latest is the head
  of the queue, not done. -/
  order : s.btMoves.Sublist s.done ∨ ∃ lo bt, s.btMoves = bt ++ [lo] ∧ bt.Sublist s.done ∧
    s.queue.head? = some lo ∧ lo ∉ s.done

/-- With no self-bond, a bond's other end is not the atom itself. -/
lemma other_ne_of_mem_bondsOf {w : Work} (hwf : WF w) {c k : ℕ} (hk : k ∈ w.bondsOf c) :
    (w.bonds[k]! : WBond).other c ≠ c := by
  obtain ⟨-, -, hne⟩ := hwf k (lt_of_mem_bondsOf hk)
  have ht := touches_of_mem_bondsOf hk
  simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
  simp only [WBond.other]
  split
  · rename_i h
    simp only [beq_iff_eq] at h
    rw [← h]
    exact Ne.symm hne
  · rename_i h
    simp only [beq_iff_eq] at h
    rcases ht with ht | ht
    · exact absurd ht h
    · rw [← ht]
      exact hne

/-- What is known once the next atom `curr` is taken, with queue `q2` after the scan and options
`opts`; `stored` says whether they were kept from an earlier visit. -/
structure Popped (s : KekState) (curr : ℕ) (q2 opts : List ℕ) (stored : Bool) : Prop where
  currNotDone : curr ∉ s.done
  currAtom : curr ∈ atoms
  qNodup : q2.Nodup
  qDisj : ∀ x ∈ q2, x ∉ s.done ∧ x ≠ curr
  qSub : ∀ x ∈ q2, x ∈ atoms
  optsNodup : opts.Nodup
  optsOk : ∀ j ∈ opts, j ≠ curr ∧ j ∈ atoms ∧ s.cands[j]! = true ∧
    ∃ k, m0.bondBetween? curr j = some k ∧ wa k = true
  storedBt : stored = true → (curr, opts) ∈ s.options ∧ ∃ bt, s.btMoves = bt ++ [curr] ∧
    bt.Sublist s.done
  freshBt : stored = false → curr ∉ s.btMoves ∧ s.btMoves.Sublist s.done

variable {wa atoms m0 cands0}

/-- The queue after taking the next atom. -/
lemma popped_queue {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {sorted : List ℕ}
    (hsorted : ∀ x ∈ sorted, x ∈ atoms) {curr : ℕ} {q1 : List ℕ}
    (h : s.nextAtom sorted = some (curr, q1)) :
    curr ∉ s.done ∧ curr ∈ atoms ∧ q1.Nodup ∧ (∀ x ∈ q1, x ∉ s.done ∧ x ≠ curr) ∧
      (∀ x ∈ q1, x ∈ atoms) ∧ (s.queue ≠ [] → s.queue = curr :: q1) := by
  rcases nextAtom_eq_some h with hq | ⟨hq, rfl, hmem, hnd⟩
  · have hn := hi.queueNodup
    rw [hq, List.nodup_cons] at hn
    refine ⟨hi.disjoint _ (by rw [hq]; exact List.mem_cons_self),
      hi.queueSub _ (by rw [hq]; exact List.mem_cons_self), hn.2, fun x hx ↦
      ⟨hi.disjoint _ (by rw [hq]; exact List.mem_cons_of_mem _ hx), fun e ↦ hn.1 (e ▸ hx)⟩,
      fun x hx ↦ hi.queueSub _ (by rw [hq]; exact List.mem_cons_of_mem _ hx), fun _ ↦ hq⟩
  · exact ⟨hnd, hsorted _ hmem, List.nodup_nil, by simp, by simp, fun h' ↦ absurd hq h'⟩

/-- **Options kept from an earlier visit**: the atom is the latest backtrack point, and each
kept option still needs a double bond, by the order fact. -/
lemma popped_stored {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {sorted : List ℕ}
    (hsorted : ∀ x ∈ sorted, x ∈ atoms) {curr : ℕ} {q1 o : List ℕ}
    (h : s.nextAtom sorted = some (curr, q1)) (ho : s.options.lookup curr = some o) :
    Popped wa atoms m0 s curr q1 o true := by
  obtain ⟨hcd, hca, hq1, hqd, hqs, -⟩ := popped_queue hi hsorted h
  have hmem := mem_of_lookup ho
  obtain ⟨-, hond, hoj⟩ := hi.opt curr o hmem
  have hkey : curr ∈ s.btMoves := by
    rw [← hi.keys]
    exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  refine ⟨hcd, hca, hq1, hqd, hqs, hond, fun j hj ↦ ?_, fun _ ↦ ⟨hmem, ?_⟩, fun h ↦ by cases h⟩
  · obtain ⟨hjc, hj0, hja, hjk, hjadds⟩ := hoj j hj
    refine ⟨hjc, hja, (hi.cands j).mpr ⟨hj0, ?_⟩, hjk⟩
    rintro ⟨k, hk, ht⟩
    obtain ⟨hs, hd⟩ := hjadds k hk ht
    rw [before_of_not_mem hcd] at hs hd
    rcases hi.addsDone k hk with h' | h'
    · exact hs h'
    · exact hd h'
  · rcases hi.order with hs | ⟨lo, bt, hbt, hbts, -, hlo⟩
    · exact absurd (hs.subset hkey) hcd
    · rw [hbt, List.mem_append, List.mem_singleton] at hkey
      rcases hkey with hk | rfl
      · exact absurd (hbts.subset hk) hcd
      · exact ⟨bt, hbt, hbts⟩

/-- **Options from a fresh scan**: the queued neighbours are new, and each option is a distinct
neighbour that still needs a double bond across a bond written aromatic. -/
lemma popped_fresh {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {sorted : List ℕ}
    (hsorted : ∀ x ∈ sorted, x ∈ atoms) (hnd : m0.NbrsDistinct) (hwf : WF m0) {curr : ℕ}
    {q1 : List ℕ} (h : s.nextAtom sorted = some (curr, q1))
    (ho : s.options.lookup curr = none) :
    let L := (((s.m.neighbors curr).map (·.2)).filter
      (fun j ↦ atoms.contains j && !(s.done ++ [curr]).contains j)).mergeSort (· ≤ ·)
    Popped wa atoms m0 s curr (q1 ++ L.filter (fun j ↦ !q1.contains j))
      (L.filter (scanTakes s.m wa s.cands curr s.cands[curr]!)) false := by
  intro L
  obtain ⟨hcd, hca, hq1, hqd, hqs, hqh⟩ := popped_queue hi hsorted h
  have hnb : s.m.neighbors = m0.neighbors := hi.skel.neighbors.symm
  have hbb : s.m.bondBetween? = m0.bondBetween? := hi.skel.bondBetween?.symm
  have hL : L.Nodup := by
    have := (nodup_neighbors hnd curr).filter
      (fun j ↦ atoms.contains j && !(s.done ++ [curr]).contains j)
    rw [← hnb] at this
    exact (List.mergeSort_perm _ _).nodup_iff.mpr this
  have hmemL : ∀ j ∈ L, j ∈ atoms ∧ j ∉ s.done ∧ j ≠ curr := by
    intro j hj
    rw [List.mem_mergeSort, List.mem_filter, hnb] at hj
    obtain ⟨hjn, hjc⟩ := hj
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hjc
    have h1 : j ∈ atoms := List.contains_iff_mem.mp hjc.1
    have h2 : j ∉ s.done := fun hm ↦ by
      rw [List.contains_iff_mem.mpr (List.mem_append_left _ hm)] at hjc
      cases hjc.2
    obtain ⟨⟨k, j'⟩, hk, he⟩ := List.mem_map.mp hjn
    simp only at he
    subst he
    obtain ⟨hkb, hjo⟩ := mem_neighbors hk
    refine ⟨h1, h2, ?_⟩
    rw [hjo]
    exact other_ne_of_mem_bondsOf hwf hkb
  have hfresh : s.btMoves.Sublist s.done ∧ curr ∉ s.btMoves := by
    have hnk : curr ∉ s.btMoves := by
      intro hk
      rw [← hi.keys] at hk
      have := lookup_isSome_of_mem hk
      rw [ho] at this
      cases this
    refine ⟨?_, hnk⟩
    rcases hi.order with hs | ⟨lo, bt, hbt, -, hhead, -⟩
    · exact hs
    · have hne : s.queue ≠ [] := by
        intro e
        rw [e] at hhead
        cases hhead
      rw [hqh hne] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      exact absurd (by rw [hbt]; simp) hnk
  refine ⟨hcd, hca, ?_, fun x hx ↦ ?_, fun x hx ↦ ?_, hL.filter _, fun j hj ↦ ?_,
    (fun h ↦ by cases h), fun _ ↦ ⟨hfresh.2, hfresh.1⟩⟩
  · refine List.nodup_append.mpr ⟨hq1, hL.filter _, fun a ha b hb ↦ ?_⟩
    rintro rfl
    rw [List.mem_filter, Bool.not_eq_true'] at hb
    rw [List.contains_iff_mem.mpr ha] at hb
    cases hb.2
  · rcases List.mem_append.mp hx with hx | hx
    · exact hqd x hx
    · obtain ⟨-, hd, hc⟩ := hmemL x (List.mem_of_mem_filter hx)
      exact ⟨hd, hc⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hqs x hx
    · exact (hmemL x (List.mem_of_mem_filter hx)).1
  · rw [List.mem_filter] at hj
    obtain ⟨ha, hd, hc⟩ := hmemL j hj.1
    obtain ⟨-, hcj, k, hk, hwk⟩ := scanTakes_spec hj.2
    exact ⟨hc, ha, hcj, k, by rw [← hbb]; exact hk, hwk⟩

/-- Before the last element, if it is new: the rest. -/
lemma before_append_self : ∀ {l : List ℕ} {x : ℕ}, x ∉ l → before (l ++ [x]) x = l
  | [], x, _ => by simp [before]
  | y :: l, x, h => by
    rw [List.mem_cons, not_or] at h
    have hy : (y != x) = true := by simpa using Ne.symm h.1
    simp only [before, List.cons_append, List.takeWhile_cons, hy, ↓reduceIte, List.cons.injEq,
      true_and]
    exact before_append_self h.2

/-- Doing `curr` does not change what was done before any backtrack point. -/
lemma Popped.before_keys {s : KekState} {curr : ℕ} {q2 opts : List ℕ} {stored : Bool}
    (hp : Popped wa atoms m0 s curr q2 opts stored) {a : ℕ} (ha : a ∈ s.btMoves) :
    before (s.done ++ [curr]) a = before s.done a := by
  cases stored
  · exact before_append_of_mem ((hp.freshBt rfl).2.subset ha)
  · obtain ⟨-, bt, hbt, hbts⟩ := hp.storedBt rfl
    rw [hbt, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact before_append_of_mem (hbts.subset ha)
    · rw [before_append_self hp.currNotDone, before_of_not_mem hp.currNotDone]

/-- The backtrack points are done in order once `curr` is. -/
lemma Popped.btMoves_sublist {s : KekState} {curr : ℕ} {q2 opts : List ℕ} {stored : Bool}
    (hp : Popped wa atoms m0 s curr q2 opts stored) :
    s.btMoves.Sublist (s.done ++ [curr]) := by
  cases stored
  · exact (hp.freshBt rfl).2.trans (List.sublist_append_left _ _)
  · obtain ⟨-, bt, hbt, hbts⟩ := hp.storedBt rfl
    rw [hbt]
    exact hbts.append (List.Sublist.refl _)

/-- **A step that only does `curr`** (it needs no double bond) keeps the invariant. -/
lemma walkInv_continue {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {curr : ℕ}
    {q2 opts : List ℕ} {stored : Bool} (hp : Popped wa atoms m0 s curr q2 opts stored)
    (hc : s.cands[curr]! = false) :
    WalkInv wa atoms m0 cands0 { s with done := s.done ++ [curr], queue := q2 } where
  skel := hi.skel
  kinds := hi.kinds
  addsSize := hi.addsSize
  candsSize := hi.candsSize
  addsOk := hi.addsOk
  matching := hi.matching
  cands := hi.cands
  doneNC x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hi.doneNC x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hc
  addsDone k hk := by
    rcases hi.addsDone k hk with h | h
    · exact .inl (List.mem_append_left _ h)
    · exact .inr (List.mem_append_left _ h)
  doneNodup := List.nodup_append.mpr ⟨hi.doneNodup, List.nodup_singleton _,
    fun a ha b hb ↦ by
      rw [List.mem_singleton] at hb; subst hb; exact fun e ↦ hp.currNotDone (e ▸ ha)⟩
  queueNodup := hp.qNodup
  disjoint x hx := by
    obtain ⟨hd, hc'⟩ := hp.qDisj x hx
    rw [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hd, hc'⟩
  doneSub x hx := by
    rcases List.mem_append.mp hx with hx | hx
    · exact hi.doneSub x hx
    · rw [List.mem_singleton] at hx
      exact hx ▸ hp.currAtom
  queueSub := hp.qSub
  opt a o hao := by
    have ha : a ∈ s.btMoves := by
      rw [← hi.keys]
      exact List.mem_map.mpr ⟨_, hao, rfl⟩
    obtain ⟨hne, hnd, hj⟩ := hi.opt a o hao
    refine ⟨hne, hnd, fun j hjo ↦ ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hj j hjo
    refine ⟨h1, h2, h3, h4, fun k hk ht ↦ ?_⟩
    simp only
    rw [hp.before_keys ha]
    exact h5 k hk ht
  keys := hi.keys
  lastOpt := hi.lastOpt
  order := .inl hp.btMoves_sublist

/-- The bond `bondBetween?` finds joins exactly the two atoms. -/
lemma touches_of_bondBetween {w : Work} {i j k : ℕ} (h : w.bondBetween? i j = some k) :
    k < w.bonds.size ∧ ∀ x, (w.bonds[k]! : WBond).touches x = true ↔ x = i ∨ x = j := by
  obtain ⟨hk, he⟩ := bondBetween?_eq_some h
  refine ⟨hk, fun x ↦ ?_⟩
  rw [getElem!_pos w.bonds k hk]
  simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq]
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> constructor <;> intro hx <;> omega

/-- A `true` read with `!` is in range. -/
lemma lt_size_of_getElem!_bool {a : Array Bool} {i : ℕ} (h : a[i]! = true) : i < a.size := by
  by_contra hi
  rw [getElem!_neg a i hi] at h
  cases h

/-- **Placing a double bond** from `curr` to its first option `n`, with any update of the kept
options that keeps or drops old entries and may add `(curr, rest)`, keeps the invariant. -/
lemma walkInv_place_core
    (hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
      (m0.bonds[k]! : WBond).kind = .single)
    {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {curr : ℕ} {q2 opts : List ℕ}
    {stored : Bool} (hp : Popped wa atoms m0 s curr q2 opts stored) (hcc : s.cands[curr]! = true)
    {n : ℕ} {rest : List ℕ} (hopts : opts = n :: rest) {k : ℕ}
    (hk : m0.bondBetween? curr n = some k)
    (options' : List (ℕ × List ℕ)) (btMoves' : List ℕ) (lastOpt' : Option ℕ)
    (hopt' : ∀ a o, (a, o) ∈ options' → (a, o) ∈ s.options ∨ (a = curr ∧ o = rest ∧ rest ≠ []))
    (hkeys' : options'.map (·.1) = btMoves') (hlast' : lastOpt' = btMoves'.getLast?)
    (hbt' : btMoves'.Sublist (s.done ++ [curr])) :
    WalkInv wa atoms m0 cands0
      { s with m := s.m.setKind k .double, cands := (s.cands.set! curr false).set! n false,
               adds := s.adds.set! k true, done := s.done ++ [curr], queue := q2,
               options := options', btMoves := btMoves', lastOpt := lastOpt' } := by
  obtain ⟨hkl, hkt⟩ := touches_of_bondBetween hk
  have hn := hp.optsOk n (by rw [hopts]; exact List.mem_cons_self)
  obtain ⟨hnc, hna, hncand, k', hk', hwk⟩ := hn
  rw [hk] at hk'
  cases hk'
  obtain ⟨hc0, hcm⟩ := (hi.cands curr).mp hcc
  obtain ⟨hn0, hnm⟩ := (hi.cands n).mp hncand
  have hnd : n ∉ s.done := fun h ↦ by rw [hi.doneNC n h] at hncand; cases hncand
  have hsz : s.m.bonds.size = m0.bonds.size := hi.skel.numBonds.symm
  -- the new double bond and the placed ones
  have hA : ∀ k₁, (s.adds.set! k true)[k₁]! = true ↔ k₁ = k ∨ s.adds[k₁]! = true := by
    intro k₁
    rw [getElem!_set!_bool]
    split
    · rename_i h
      exact ⟨fun _ ↦ .inl h.1.symm, fun _ ↦ rfl⟩
    · rename_i h
      refine ⟨fun h' ↦ .inr h', fun h' ↦ ?_⟩
      rcases h' with rfl | h'
      · exact absurd ⟨rfl, by rw [hi.addsSize]; exact hkl⟩ h
      · exact h'
  have hM : ∀ x, (∃ k₁, (s.adds.set! k true)[k₁]! = true ∧ Tch m0 k₁ x) ↔
      x = curr ∨ x = n ∨ Matched m0 s x := by
    intro x
    constructor
    · rintro ⟨k₁, hk₁, ht⟩
      rcases (hA k₁).mp hk₁ with rfl | hk₁
      · rcases (hkt x).mp ht with h | h
        · exact .inl h
        · exact .inr (.inl h)
      · exact .inr (.inr ⟨k₁, hk₁, ht⟩)
    · rintro (rfl | rfl | ⟨k₁, hk₁, ht⟩)
      · exact ⟨k, (hA k).mpr (.inl rfl), (hkt _).mpr (.inl rfl)⟩
      · exact ⟨k, (hA k).mpr (.inl rfl), (hkt _).mpr (.inr rfl)⟩
      · exact ⟨k₁, (hA k₁).mpr (.inr hk₁), ht⟩
  have hC : ∀ x, ((s.cands.set! curr false).set! n false)[x]! =
      if x = curr ∨ x = n then false else s.cands[x]! := by
    intro x
    rw [getElem!_set!_bool, getElem!_set!_bool]
    have hcs := lt_size_of_getElem!_bool hcc
    have hns := lt_size_of_getElem!_bool hncand
    by_cases h1 : x = curr
    · simp [h1, hcs, hnc]
    · by_cases h2 : x = n
      · simp [h2, hns]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have hsrc : ∀ x, (m0.bonds[k]! : WBond).src = x → x = curr ∨ x = n := fun x hx ↦
    (hkt x).mp (by simp [WBond.touches, hx])
  have hdst : ∀ x, (m0.bonds[k]! : WBond).dst = x → x = curr ∨ x = n := fun x hx ↦
    (hkt x).mp (by simp [WBond.touches, hx])
  refine ⟨hi.skel.trans (skel_setKind _ _ _), fun k₁ ↦ ?_, by simp [hi.addsSize],
    by simp [hi.candsSize], fun k₁ hk₁ ↦ ?_,
    fun k₁ k₂ x h₁ h₂ t₁ t₂ ↦ ?_, fun x ↦ ?_, fun x hx ↦ ?_, fun k₁ hk₁ ↦ ?_, ?_, hp.qNodup,
    fun x hx ↦ ?_, fun x hx ↦ ?_, hp.qSub, fun a o hao ↦ ?_, hkeys', hlast', .inl hbt'⟩
  · -- kinds
    simp only
    rw [kind_setKind, hi.kinds, getElem!_set!_bool, hsz, hi.addsSize]
    by_cases h : k = k₁ ∧ k₁ < m0.bonds.size
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h]
  · -- placed double bonds are fine
    rcases (hA k₁).mp hk₁ with e | hk₁
    · rw [e]
      have hsingle' := hsingle k hwk curr hc0 ((hkt curr).mpr (.inl rfl))
      refine ⟨hkl, hwk, hsingle', ?_, ?_⟩
      · rcases hsrc _ rfl with h | h <;> rw [h] <;> assumption
      · rcases hdst _ rfl with h | h <;> rw [h] <;> assumption
    · exact hi.addsOk k₁ hk₁
  · -- matching
    simp only at h₁ h₂
    rcases (hA k₁).mp h₁ with e₁ | a₁ <;> rcases (hA k₂).mp h₂ with e₂ | a₂
    · rw [e₁, e₂]
    · exfalso
      rw [e₁] at t₁
      rcases (hkt x).mp t₁ with e | e
      · exact hcm ⟨k₂, a₂, e ▸ t₂⟩
      · exact hnm ⟨k₂, a₂, e ▸ t₂⟩
    · exfalso
      rw [e₂] at t₂
      rcases (hkt x).mp t₂ with e | e
      · exact hcm ⟨k₁, a₁, e ▸ t₁⟩
      · exact hnm ⟨k₁, a₁, e ▸ t₁⟩
    · exact hi.matching k₁ k₂ x a₁ a₂ t₁ t₂
  · -- cands
    simp only [hC]
    show _ ↔ cands0[x]! = true ∧ ¬ ∃ k₁, (s.adds.set! k true)[k₁]! = true ∧ Tch m0 k₁ x
    rw [hM]
    by_cases h : x = curr ∨ x = n
    · simp only [if_pos h]
      constructor
      · intro h'
        cases h'
      · rintro ⟨-, h'⟩
        exact absurd (h.elim (fun h ↦ .inl h) (fun h ↦ .inr (.inl h))) h'
    · rw [if_neg h, hi.cands x]
      simp only [not_or] at h
      simp [h.1, h.2]
  · -- done atoms
    simp only [hC]
    rcases List.mem_append.mp hx with hx | hx
    · have hxn : x ≠ n := fun e ↦ hnd (e ▸ hx)
      have hxc : x ≠ curr := fun e ↦ hp.currNotDone (e ▸ hx)
      rw [if_neg (by omega)]
      exact hi.doneNC x hx
    · rw [List.mem_singleton] at hx
      rw [if_pos (.inl hx)]
  · -- placed double bonds have an end done
    simp only at hk₁ ⊢
    rcases (hA k₁).mp hk₁ with e | hk₁
    · rw [e]
      have hct : Tch m0 k curr := (hkt curr).mpr (.inl rfl)
      simp only [Tch, WBond.touches, Bool.or_eq_true, beq_iff_eq] at hct
      rcases hct with h | h
      · exact .inl (by rw [h]; simp)
      · exact .inr (by rw [h]; simp)
    · rcases hi.addsDone k₁ hk₁ with h | h
      · exact .inl (List.mem_append_left _ h)
      · exact .inr (List.mem_append_left _ h)
  · exact List.nodup_append.mpr ⟨hi.doneNodup, List.nodup_singleton _,
      fun a ha b hb ↦ by
        rw [List.mem_singleton] at hb
        subst hb
        exact fun e ↦ hp.currNotDone (e ▸ ha)⟩
  · obtain ⟨hd, hc'⟩ := hp.qDisj x hx
    simp only [List.mem_append, List.mem_singleton, not_or]
    exact ⟨hd, hc'⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hi.doneSub x hx
    · rw [List.mem_singleton] at hx
      exact hx ▸ hp.currAtom
  · -- the order fact
    simp only
    rcases hopt' a o hao with hold | ⟨ha, ho, hne⟩
    · have ha : a ∈ s.btMoves := by
        rw [← hi.keys]
        exact List.mem_map.mpr ⟨_, hold, rfl⟩
      obtain ⟨hne, hnd', hj⟩ := hi.opt a o hold
      refine ⟨hne, hnd', fun j hjo ↦ ?_⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hj j hjo
      refine ⟨h1, h2, h3, h4, fun k₁ hk₁ ht ↦ ?_⟩
      rw [hp.before_keys ha]
      rcases (hA k₁).mp hk₁ with e | hk₁
      · rw [e]
        have hb : ∀ y, y ∈ before s.done a → y ≠ curr ∧ y ≠ n := fun y hy ↦
          ⟨fun e ↦ hp.currNotDone (e ▸ before_sub hy), fun e ↦ hnd (e ▸ before_sub hy)⟩
        exact ⟨fun hy ↦ (hsrc _ rfl).elim (hb _ hy).1 (hb _ hy).2,
          fun hy ↦ (hdst _ rfl).elim (hb _ hy).1 (hb _ hy).2⟩
      · exact h5 k₁ hk₁ ht
    · rw [ha, ho]
      have hrest : ∀ j ∈ rest, j ∈ opts := fun j hj ↦ by
        rw [hopts]
        exact List.mem_cons_of_mem _ hj
      have hond := hp.optsNodup
      rw [hopts, List.nodup_cons] at hond
      refine ⟨hne, hond.2, fun j hj ↦ ?_⟩
      obtain ⟨hjc, hja, hjcand, hjk⟩ := hp.optsOk j (hrest j hj)
      obtain ⟨hj0, hjm⟩ := (hi.cands j).mp hjcand
      have hjn : j ≠ n := fun e ↦ hond.1 (e ▸ hj)
      refine ⟨hjc, hj0, hja, hjk, fun k₁ hk₁ ht ↦ ?_⟩
      exfalso
      rcases (hA k₁).mp hk₁ with e | hk₁
      · rw [e] at ht
        rcases (hkt j).mp ht with h | h
        · exact hjc h
        · exact hjn h
      · exact hjm ⟨k₁, hk₁, ht⟩

/-- The keys left after dropping one. -/
lemma map_fst_filter {β : Type*} (c : ℕ) :
    ∀ l : List (ℕ × β), (l.filter (·.1 != c)).map (·.1) = (l.map (·.1)).filter (· != c)
  | [] => rfl
  | p :: l => by
    simp only [List.filter_cons, List.map_cons]
    split <;> simp_all [map_fst_filter c l]

/-- **Placing a double bond keeps the invariant**, whichever way `placeDouble` updates the kept
options: dropping the atom's entry when it has no options left, replacing it with the rest,
adding one for a new branch point, or leaving them. -/
lemma walkInv_placeDouble
    (hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
      (m0.bonds[k]! : WBond).kind = .single)
    {s : KekState} (hi : WalkInv wa atoms m0 cands0 s) {curr : ℕ} {q2 opts : List ℕ}
    {stored : Bool} (hp : Popped wa atoms m0 s curr q2 opts stored)
    (hlook : (s.options.lookup curr).isSome = stored) (hcc : s.cands[curr]! = true)
    {n : ℕ} {rest : List ℕ} (hopts : opts = n :: rest) {k : ℕ}
    (hk : m0.bondBetween? curr n = some k) :
    WalkInv wa atoms m0 cands0
      ({ s with done := s.done ++ [curr], queue := q2 }.placeDouble curr n k rest) := by
  unfold KekState.placeDouble
  dsimp only
  split
  · rename_i hsome
    rw [hlook] at hsome
    subst hsome
    obtain ⟨-, bt, hbt, hbts⟩ := hp.storedBt rfl
    have hcbt : curr ∉ bt := fun h ↦ hp.currNotDone (hbts.subset h)
    split
    · -- no options left: drop the entry
      refine walkInv_place_core hsingle hi hp hcc hopts hk _ _ _
        (fun a o h ↦ .inl (List.mem_of_mem_filter h)) ?_ rfl ?_
      · rw [map_fst_filter, hi.keys, hbt, List.dropLast_concat, List.filter_append]
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.filter_nil, List.append_nil]
        rw [List.filter_eq_self]
        intro a ha
        simp only [bne_iff_ne, ne_eq]
        rintro rfl
        exact hcbt ha
      · rw [hbt, List.dropLast_concat]
        exact hbts.trans (List.sublist_append_left _ _)
    · -- options left: keep the rest
      rename_i hne
      refine walkInv_place_core hsingle hi hp hcc hopts hk _ _ _ (fun a o h ↦ ?_) ?_ hi.lastOpt
        hp.btMoves_sublist
      · obtain ⟨q, hm, he⟩ := List.mem_map.mp h
        obtain ⟨a', o'⟩ := q
        simp only at he
        split at he
        · rename_i ha'
          cases he
          rw [beq_iff_eq] at ha'
          exact .inr ⟨ha', rfl, by simpa using hne⟩
        · cases he
          exact .inl hm
      · rw [List.map_map, ← hi.keys]
        congr 1
        funext q
        obtain ⟨a', o'⟩ := q
        simp only [Function.comp_apply]
        split <;> rfl
  · rename_i hsome
    have hstored : stored = false := by
      cases stored
      · rfl
      · exact absurd hlook hsome
    subst hstored
    obtain ⟨hcbt, hbts⟩ := hp.freshBt rfl
    split
    · -- a new branch point
      rename_i hne
      refine walkInv_place_core hsingle hi hp hcc hopts hk _ _ _ (fun a o h ↦ ?_) ?_ ?_ ?_
      · rcases List.mem_append.mp h with h | h
        · exact .inl h
        · rw [List.mem_singleton, Prod.mk.injEq] at h
          exact .inr ⟨h.1, h.2, by simpa using hne⟩
      · rw [List.map_append, hi.keys]
        rfl
      · simp
      · exact hbts.append (List.Sublist.refl _)
    · exact walkInv_place_core hsingle hi hp hcc hopts hk _ _ _ (fun a o h ↦ .inl h) hi.keys
        hi.lastOpt hp.btMoves_sublist

/-! ### Backtracking -/

/-- What comes before `a` is the list up to `a`'s index. -/
lemma before_eq_take : ∀ (l : List ℕ) (a : ℕ), before l a = l.take (l.idxOf a)
  | [], _ => rfl
  | x :: l, a => by
    by_cases hx : x = a
    · subst hx
      simp [before, List.takeWhile_cons]
    · have hx' : (x != a) = true := by simpa using hx
      have hx'' : (x == a) = false := by simpa using hx
      simp only [before, List.takeWhile_cons, hx', ↓reduceIte, List.idxOf_cons, hx'',
        cond_false, List.take_succ_cons]
      rw [← before, before_eq_take l a]

lemma not_mem_before : ∀ (l : List ℕ) (a : ℕ), a ∉ before l a
  | [], _ => by simp [before]
  | x :: l, a => by
    by_cases hx : x = a
    · subst hx
      simp [before]
    · have hx' : (x != a) = true := by simpa using hx
      simp only [before, List.takeWhile_cons, hx', ↓reduceIte, List.mem_cons, not_or]
      exact ⟨Ne.symm hx, not_mem_before l a⟩

/-- The rest of a list from `a` on starts with `a`. -/
lemma head?_drop_idxOf : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → (l.drop (l.idxOf a)).head? = some a
  | [], _, h => by simp at h
  | x :: l, a, h => by
    by_cases hx : x = a
    · subst hx
      simp
    · have hx'' : (x == a) = false := by simpa using hx
      rcases List.mem_cons.mp h with h | h
      · exact absurd h.symm hx
      · simp only [List.idxOf_cons, hx'', cond_false, List.drop_succ_cons]
        exact head?_drop_idxOf h

/-- Before an element that is itself before `lo`: the same as in the whole list. -/
lemma before_before : ∀ {l : List ℕ} {lo a : ℕ}, a ∈ before l lo →
    before (before l lo) a = before l a
  | [], _, _, h => by simp [before] at h
  | x :: l, lo, a, h => by
    by_cases hxl : x = lo
    · subst hxl
      simp [before, List.takeWhile_cons] at h
    · have hxl' : (x != lo) = true := by simpa using hxl
      have e : before (x :: l) lo = x :: before l lo := by
        simp [before, List.takeWhile_cons, hxl']
      rw [e] at h ⊢
      by_cases hxa : x = a
      · subst hxa
        simp [before, List.takeWhile_cons]
      · have hxa' : (x != a) = true := by simpa using hxa
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hxa
        · simp only [before, List.takeWhile_cons, hxa', ↓reduceIte, List.cons.injEq, true_and]
          exact before_before h

/-- In a list without repeats, the backtrack points before the latest are done before it. -/
lemma sublist_before : ∀ {bt l : List ℕ} {lo : ℕ}, (bt ++ [lo]).Sublist l → l.Nodup →
    bt.Sublist (before l lo)
  | _, [], _, h, _ => by simp at h
  | bt, x :: l, lo, h, hnd => by
    have hbn : (bt ++ [lo]).Nodup := h.nodup hnd
    have hlo : lo ∉ bt := by
      intro hm
      rw [List.nodup_append] at hbn
      exact hbn.2.2 lo hm lo (List.mem_singleton_self lo) rfl
    rw [List.nodup_cons] at hnd
    rcases List.sublist_cons_iff.mp h with h | ⟨r, hr, hrl⟩
    · by_cases hxl : x = lo
      · subst hxl
        exact absurd (h.subset (by simp)) hnd.1
      · have hxl' : (x != lo) = true := by simpa using hxl
        simp only [before, List.takeWhile_cons, hxl', ↓reduceIte]
        exact (sublist_before h hnd.2).cons x
    · cases bt with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hr
        obtain ⟨rfl, -⟩ := hr
        exact List.nil_sublist _
      | cons b bt =>
        simp only [List.cons_append, List.cons.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        have hxl : b ≠ lo := fun e ↦ hlo (by rw [e]; exact List.mem_cons_self)
        have hxl' : (b != lo) = true := by simpa using hxl
        simp only [before, List.takeWhile_cons, hxl', ↓reduceIte]
        exact (sublist_before hrl hnd.2).cons₂ b

/-- Bond `j` is undone by backtracking to `keep`: the walk placed it, and neither end is kept. -/
@[reducible] def Undone (w : Work) (A : Array Bool) (keep : List ℕ) (j : ℕ) : Prop :=
  A[j]! = true ∧ (w.bonds[j]! : WBond).src ∉ keep ∧ (w.bonds[j]! : WBond).dst ∉ keep

lemma undoAdds_eq (keep : List ℕ) (w : Work) (A C : Array Bool) (j : ℕ) :
    undoAdds keep (w, A, C) j = if Undone w A keep j then
      (w.setKind j .single, A.set! j false,
        (C.set! (w.bonds[j]! : WBond).src true).set! (w.bonds[j]! : WBond).dst true)
    else (w, A, C) := by
  unfold undoAdds
  dsimp only
  by_cases hA : A[j]! = true
  · rw [if_pos hA]
    by_cases hs : (w.bonds[j]! : WBond).src ∈ keep
    · rw [if_neg (by simp [List.contains_iff_mem, hs]), if_neg (by simp [hs])]
    · by_cases hd : (w.bonds[j]! : WBond).dst ∈ keep
      · rw [if_neg (by simp [List.contains_iff_mem, hd]), if_neg (by simp [hd])]
      · rw [if_pos (by simp [List.contains_iff_mem, hs, hd]), if_pos ⟨hA, hs, hd⟩]
  · rw [if_neg hA, if_neg (fun h ↦ hA h.1)]

/-- The undo loop keeps which atoms each bond joins and the sizes of the flag arrays. -/
lemma foldl_undoAdds_skel (keep : List ℕ) : ∀ (l : List ℕ) (w : Work) (A C : Array Bool),
    let r := l.foldl (undoAdds keep) (w, A, C)
    SameSkel w r.1 ∧ r.2.1.size = A.size ∧ r.2.2.size = C.size
  | [], w, A, C => ⟨⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, rfl, rfl⟩
  | j :: l, w, A, C => by
    simp only [List.foldl_cons, undoAdds_eq]
    split
    · obtain ⟨h1, h2, h3⟩ := foldl_undoAdds_skel keep l _ _ _
      exact ⟨(skel_setKind _ _ _).trans h1, by rw [h2]; simp, by rw [h3]; simp⟩
    · exact foldl_undoAdds_skel keep l _ _ _

/-- What the undo loop leaves of the placed flags: those not undone. -/
lemma foldl_undoAdds_adds (keep : List ℕ) : ∀ (l : List ℕ) (w : Work) (A C : Array Bool),
    l.Nodup → ∀ j, ((l.foldl (undoAdds keep) (w, A, C)).2.1[j]! = true ↔
      A[j]! = true ∧ ¬ (j ∈ l ∧ Undone w A keep j))
  | [], w, A, C, _, j => by simp
  | i :: l, w, A, C, hnd, j => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons, undoAdds_eq]
    by_cases hU : Undone w A keep i
    · rw [if_pos hU, foldl_undoAdds_adds keep l _ _ _ hnd.2 j]
      have hsk := skel_setKind w i .single
      have hlt := lt_size_of_getElem!_bool hU.1
      by_cases hji : j = i
      · subst hji
        simp [getElem!_set!_bool, hlt, hnd.1, hU]
      · simp only [Undone, getElem!_set!_bool, Ne.symm hji, false_and, ↓reduceIte,
          ← hsk.src, ← hsk.dst, List.mem_cons, hji, false_or]
    · rw [if_neg hU, foldl_undoAdds_adds keep l _ _ _ hnd.2 j]
      by_cases hji : j = i
      · subst hji
        simp [hU, hnd.1]
      · simp [hji]

/-- What the undo loop does to the kinds: an undone bond is single, any other is as it was. -/
lemma foldl_undoAdds_kind (keep : List ℕ) : ∀ (l : List ℕ) (w : Work) (A C : Array Bool),
    l.Nodup → ∀ j,
      (j ∈ l → Undone w A keep j → j < w.bonds.size →
        ((l.foldl (undoAdds keep) (w, A, C)).1.bonds[j]! : WBond).kind = .single) ∧
      (¬ (j ∈ l ∧ Undone w A keep j) →
        ((l.foldl (undoAdds keep) (w, A, C)).1.bonds[j]! : WBond).kind =
          (w.bonds[j]! : WBond).kind)
  | [], w, A, C, _, j => ⟨by simp, fun _ ↦ rfl⟩
  | i :: l, w, A, C, hnd, j => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons, undoAdds_eq]
    by_cases hU : Undone w A keep i
    · rw [if_pos hU]
      have hsk := skel_setKind w i .single
      obtain ⟨ih1, ih2⟩ := foldl_undoAdds_kind keep l (w.setKind i .single) (A.set! i false)
        ((C.set! (w.bonds[i]! : WBond).src true).set! (w.bonds[i]! : WBond).dst true) hnd.2 j
      have hU' : j ≠ i → (Undone (w.setKind i .single) (A.set! i false) keep j ↔
          Undone w A keep j) := fun hji ↦ by
        simp only [Undone, getElem!_set!_bool, Ne.symm hji, false_and, ↓reduceIte,
          ← hsk.src, ← hsk.dst]
      by_cases hji : j = i
      · subst hji
        have hnu : ¬ (j ∈ l ∧ Undone (w.setKind j .single) (A.set! j false) keep j) :=
          fun h ↦ hnd.1 h.1
        refine ⟨fun _ _ hlt ↦ ?_, fun h ↦ absurd ⟨List.mem_cons_self, hU⟩ h⟩
        rw [ih2 hnu, kind_setKind, if_pos ⟨rfl, hlt⟩]
      · refine ⟨fun hj hu hlt ↦ ?_, fun h ↦ ?_⟩
        · have hj' : j ∈ l := (List.mem_cons.mp hj).resolve_left hji
          exact ih1 hj' ((hU' hji).mpr hu) (by simpa [setKind] using hlt)
        · rw [ih2 (fun h' ↦ h ⟨List.mem_cons_of_mem _ h'.1, (hU' hji).mp h'.2⟩), kind_setKind,
            if_neg (fun h' ↦ hji h'.1.symm)]
    · rw [if_neg hU]
      obtain ⟨ih1, ih2⟩ := foldl_undoAdds_kind keep l w A C hnd.2 j
      refine ⟨fun hj hu hlt ↦ ?_, fun h ↦ ih2 (fun h' ↦ h ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩)⟩
      rcases List.mem_cons.mp hj with rfl | hj'
      · exact absurd hu hU
      · exact ih1 hj' hu hlt

/-- What the undo loop does to the candidates: the ends of undone bonds need one again. -/
lemma foldl_undoAdds_cands (keep : List ℕ) : ∀ (l : List ℕ) (w : Work) (A C : Array Bool),
    l.Nodup → ∀ x, ((l.foldl (undoAdds keep) (w, A, C)).2.2[x]! = true ↔
      C[x]! = true ∨ (x < C.size ∧ ∃ j ∈ l, Undone w A keep j ∧
        (w.bonds[j]! : WBond).touches x = true))
  | [], w, A, C, _, x => by simp
  | i :: l, w, A, C, hnd, x => by
    rw [List.nodup_cons] at hnd
    simp only [List.foldl_cons, undoAdds_eq]
    by_cases hU : Undone w A keep i
    · rw [if_pos hU, foldl_undoAdds_cands keep l _ _ _ hnd.2 x]
      have hsk := skel_setKind w i .single
      have hU' : ∀ j ∈ l, (Undone (w.setKind i .single) (A.set! i false) keep j ↔
          Undone w A keep j) := fun j hj ↦ by
        have hji : j ≠ i := fun e ↦ hnd.1 (e ▸ hj)
        simp only [Undone, getElem!_set!_bool, Ne.symm hji, false_and, ↓reduceIte,
          ← hsk.src, ← hsk.dst]
      have htc : ∀ j, ((w.setKind i .single).bonds[j]! : WBond).touches x =
          (w.bonds[j]! : WBond).touches x := fun j ↦ by
        simp only [WBond.touches]
        rw [← hsk.src j, ← hsk.dst j]
      have hs' : (C.set! (w.bonds[i]! : WBond).src true).size = C.size := by simp
      rw [getElem!_set!_bool, getElem!_set!_bool, hs']
      simp only [Array.size_setIfInBounds, Array.set!]
      constructor
      · rintro (h | ⟨hx, j, hj, hu, ht⟩)
        · split at h
          · rename_i h'
            exact .inr ⟨h'.2, i, List.mem_cons_self, hU, by simp [WBond.touches, h'.1]⟩
          · split at h
            · rename_i h'
              exact .inr ⟨h'.2, i, List.mem_cons_self, hU, by simp [WBond.touches, h'.1]⟩
            · exact .inl h
        · exact .inr ⟨by simpa using hx, j, List.mem_cons_of_mem _ hj, (hU' j hj).mp hu,
            by rw [← htc]; exact ht⟩
      · rintro (h | ⟨hx, j, hj, hu, ht⟩)
        · left
          split_ifs <;> simp_all
        · rcases List.mem_cons.mp hj with rfl | hj'
          · left
            simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
            rcases ht with ht | ht
            · by_cases hd : (w.bonds[j]! : WBond).dst = x
              · simp [hd, hx]
              · simp [hd, ht, hx]
            · simp [ht, hx]
          · right
            exact ⟨by simpa using hx, j, hj', (hU' j hj').mpr hu, by rw [htc]; exact ht⟩
    · rw [if_neg hU, foldl_undoAdds_cands keep l _ _ _ hnd.2 x]
      constructor
      · rintro (h | ⟨hx, j, hj, hu, ht⟩)
        · exact .inl h
        · exact .inr ⟨hx, j, List.mem_cons_of_mem _ hj, hu, ht⟩
      · rintro (h | ⟨hx, j, hj, hu, ht⟩)
        · exact .inl h
        · rcases List.mem_cons.mp hj with rfl | hj'
          · exact absurd hu hU
          · exact .inr ⟨hx, j, hj', hu, ht⟩

/-- **Backtracking keeps the invariant.** After a fresh scan found no option for `curr`, the
walk goes back to the latest backtrack point `lo`: the atoms done before it are kept, the double
bonds with neither end kept are undone, and `lo` with the atoms after it goes back to the head of
the queue.  The order fact survives because the kept prefix is exactly what was done before `lo`,
and the earlier backtrack points are all in it. -/
lemma walkInv_backTrack (hwf : WF m0) {s : KekState} (hi : WalkInv wa atoms m0 cands0 s)
    {curr : ℕ} {q2 opts : List ℕ} (hp : Popped wa atoms m0 s curr q2 opts false) {lo : ℕ}
    (hlo : s.lastOpt = some lo) :
    WalkInv wa atoms m0 cands0
      ({ s with done := s.done ++ [curr], queue := q2 }.backTrack lo) := by
  obtain ⟨hcbt, hbts⟩ := hp.freshBt rfl
  rw [hi.lastOpt, List.getLast?_eq_some_iff] at hlo
  obtain ⟨bt, hbt⟩ := hlo
  have hlod : lo ∈ s.done := hbts.subset (by rw [hbt]; simp)
  have hd1 : (s.done ++ [curr]).Nodup := List.nodup_append.mpr ⟨hi.doneNodup,
    List.nodup_singleton _, fun a ha b hb ↦ by
      rw [List.mem_singleton] at hb
      subst hb
      exact fun e ↦ hp.currNotDone (e ▸ ha)⟩
  set done1 := s.done ++ [curr] with hdone1
  set keep := done1.take (done1.idxOf lo) with hkeep
  have hkb : keep = before s.done lo := by
    rw [hkeep, ← before_eq_take, hdone1, before_append_of_mem hlod]
  have hbtk : bt.Sublist keep := by
    rw [hkb]
    exact sublist_before (hbt ▸ hbts) hi.doneNodup
  have hlok : lo ∉ keep := by
    rw [hkb]
    exact not_mem_before _ _
  have hkd : ∀ x ∈ keep, x ∈ s.done := fun x hx ↦ by
    rw [hkb] at hx
    exact before_sub hx
  -- the undo loop
  have hnb : (List.range s.m.numBonds).Nodup := List.nodup_range
  obtain ⟨hsk, hAs, hCs⟩ := foldl_undoAdds_skel keep (List.range s.m.numBonds) s.m s.adds s.cands
  have hA := foldl_undoAdds_adds keep _ s.m s.adds s.cands hnb
  have hK := foldl_undoAdds_kind keep _ s.m s.adds s.cands hnb
  have hC := foldl_undoAdds_cands keep _ s.m s.adds s.cands hnb
  have hsz : s.m.bonds.size = m0.bonds.size := hi.skel.numBonds.symm
  have hrange : ∀ k, s.adds[k]! = true → k ∈ List.range s.m.numBonds := fun k hk ↦ by
    rw [List.mem_range, numBonds, hsz]
    exact (hi.addsOk k hk).1
  have hsrc : ∀ k, (s.m.bonds[k]! : WBond).src = (m0.bonds[k]! : WBond).src :=
    fun k ↦ (hi.skel.src k).symm
  have hdst : ∀ k, (s.m.bonds[k]! : WBond).dst = (m0.bonds[k]! : WBond).dst :=
    fun k ↦ (hi.skel.dst k).symm
  have htch : ∀ k x, (s.m.bonds[k]! : WBond).touches x = (m0.bonds[k]! : WBond).touches x :=
    fun k x ↦ by unfold WBond.touches; rw [hsrc, hdst]
  set r := (List.range s.m.numBonds).foldl (undoAdds keep) (s.m, s.adds, s.cands) with hr
  have e : ({ s with done := done1, queue := q2 } : KekState).backTrack lo =
      { s with m := r.1, adds := r.2.1, cands := r.2.2, queue := done1.drop (done1.idxOf lo) ++ q2,
               done := keep, numBt := s.numBt + 1 } := rfl
  rw [e]
  have hA' : ∀ k, r.2.1[k]! = true → s.adds[k]! = true := fun k hk ↦ ((hA k).mp hk).1
  have hkeepsub : ∀ x ∈ keep, x ∈ s.done := hkd
  have hdk : ∀ x ∈ done1.drop (done1.idxOf lo), x ∉ keep := fun x hx hxk ↦
    List.disjoint_take_drop hd1 (le_refl _) hxk hx
  -- an atom some undone bond touches is not kept, and needed a double bond
  have hund : ∀ j x, j ∈ List.range s.m.numBonds → Undone s.m s.adds keep j →
      (s.m.bonds[j]! : WBond).touches x = true → x ∉ keep ∧ cands0[x]! = true := by
    intro j x _ hu ht
    obtain ⟨-, -, -, h1, h2⟩ := hi.addsOk j hu.1
    simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with ht | ht
    · exact ⟨ht ▸ hu.2.1, by rw [← ht, hsrc]; exact h1⟩
    · exact ⟨ht ▸ hu.2.2, by rw [← ht, hdst]; exact h2⟩
  refine ⟨hi.skel.trans hsk, fun k ↦ ?_, by rw [hAs, hi.addsSize], by rw [hCs, hi.candsSize],
    fun k hk ↦ hi.addsOk k (hA' k hk),
    fun k₁ k₂ x h₁ h₂ ↦ hi.matching k₁ k₂ x (hA' _ h₁) (hA' _ h₂),
    fun x ↦ ?_, fun x hx ↦ ?_, fun k hk ↦ ?_, (List.take_sublist _ _).nodup hd1, ?_,
    fun x hx ↦ ?_, fun x hx ↦ hi.doneSub x (hkd x hx), fun x hx ↦ ?_, fun a o hao ↦ ?_, hi.keys,
    hi.lastOpt, .inr ⟨lo, bt, hbt, hbtk, ?_, hlok⟩⟩
  · -- kinds
    simp only
    by_cases hk : r.2.1[k]! = true
    · obtain ⟨ha, hnu⟩ := (hA k).mp hk
      rw [if_pos hk, (hK k).2 hnu, hi.kinds k, if_pos ha]
    · rw [if_neg hk]
      by_cases ha : s.adds[k]! = true
      · have hu : k ∈ List.range s.m.numBonds ∧ Undone s.m s.adds keep k := by
          by_contra h
          exact hk ((hA k).mpr ⟨ha, h⟩)
        rw [(hK k).1 hu.1 hu.2 (List.mem_range.mp hu.1), (hi.addsOk k ha).2.2.1]
      · rw [(hK k).2 (fun h ↦ ha h.2.1), hi.kinds k, if_neg ha]
  · -- candidates
    simp only
    rw [hC x]
    constructor
    · rintro (h | ⟨hx, j, hj, hu, ht⟩)
      · obtain ⟨h0, hm⟩ := (hi.cands x).mp h
        exact ⟨h0, fun ⟨k, hk, ht⟩ ↦ hm ⟨k, hA' k hk, ht⟩⟩
      · refine ⟨(hund j x hj hu ht).2, fun ⟨k, hk, ht'⟩ ↦ ?_⟩
        have hkj : k = j := hi.matching k j x (hA' k hk) hu.1 ht' (by rw [Tch, ← htch]; exact ht)
        subst hkj
        exact ((hA k).mp hk).2 ⟨hj, hu⟩
    · rintro ⟨h0, hm⟩
      by_cases hmx : Matched m0 s x
      · obtain ⟨k, hk, ht⟩ := hmx
        have hu : k ∈ List.range s.m.numBonds ∧ Undone s.m s.adds keep k := by
          by_contra h
          exact hm ⟨k, (hA k).mpr ⟨hk, h⟩, ht⟩
        have hxs : x < s.cands.size := by
          rw [hi.candsSize]
          have hw := hwf k (by rw [numBonds]; exact (hi.addsOk k hk).1)
          simp only [Tch, WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
          rcases ht with ht | ht
          · rw [← ht]; exact hw.1
          · rw [← ht]; exact hw.2.1
        exact .inr ⟨hxs, k, hu.1, hu.2, by rw [htch]; exact ht⟩
      · exact .inl ((hi.cands x).mpr ⟨h0, hmx⟩)
  · -- kept atoms are done with
    simp only
    rw [Bool.eq_false_iff]
    intro h
    rw [hC x] at h
    rcases h with h | ⟨-, j, hj, hu, ht⟩
    · rw [hi.doneNC x (hkd x hx)] at h
      cases h
    · exact (hund j x hj hu ht).1 hx
  · -- placed bonds kept have an end kept
    obtain ⟨ha, hnu⟩ := (hA k).mp hk
    simp only
    by_contra h
    simp only [not_or] at h
    exact hnu ⟨hrange k ha, ha, by rw [hsrc]; exact h.1, by rw [hdst]; exact h.2⟩
  · -- the queue has no repeats
    refine List.nodup_append.mpr ⟨(List.drop_sublist _ _).nodup hd1, hp.qNodup, ?_⟩
    intro a ha b hb e
    subst e
    obtain ⟨hbd, hbc⟩ := hp.qDisj a hb
    have := (List.drop_sublist _ _).subset ha
    rcases List.mem_append.mp this with h | h
    · exact hbd h
    · exact hbc (List.mem_singleton.mp h)
  · -- the queue is not kept
    rcases List.mem_append.mp hx with hx | hx
    · exact hdk x hx
    · exact fun hk ↦ (hp.qDisj x hx).1 (hkd x hk)
  · -- the queue is in the system
    rcases List.mem_append.mp hx with hx | hx
    · have := (List.drop_sublist _ _).subset hx
      rcases List.mem_append.mp this with h | h
      · exact hi.doneSub x h
      · rw [List.mem_singleton] at h
        exact h ▸ hp.currAtom
    · exact hp.qSub x hx
  · -- the order fact
    have ha : a ∈ s.btMoves := by
      rw [← hi.keys]
      exact List.mem_map.mpr ⟨_, hao, rfl⟩
    have hbef : before keep a = before s.done a := by
      rw [hbt, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · rw [hkb]
        exact before_before (hbtk.subset ha |> fun h ↦ by rw [hkb] at h; exact h)
      · rw [before_of_not_mem hlok, hkb]
    obtain ⟨hne, hnd, hj⟩ := hi.opt a o hao
    refine ⟨hne, hnd, fun j hjo ↦ ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hj j hjo
    refine ⟨h1, h2, h3, h4, fun k hk ht ↦ ?_⟩
    simp only
    rw [hbef]
    exact h5 k (hA' k hk) ht
  · -- the backtrack point heads the queue
    simp only
    rw [List.head?_append, head?_drop_idxOf (List.mem_append_left _ hlod)]
    rfl

/-- What a step's result says: it ends with the molecule only once every atom is done; it goes
on from a state that keeps the invariant. -/
def StepW (wa : ℕ → Bool) (atoms sorted : List ℕ) (m0 : Work) (cands0 : Array Bool)
    (s : KekState) : Option Work ⊕ KekState → Prop
  | .inl (some w) => w = s.m ∧ ∀ x ∈ sorted, x ∈ s.done
  | .inl none => True
  | .inr s' => WalkInv wa atoms m0 cands0 s'

/-- **One step of the walk keeps the invariant.** -/
theorem kekulizeStep_walkInv (hwf : WF m0) (hnd : m0.NbrsDistinct)
    (hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
      (m0.bonds[k]! : WBond).kind = .single)
    {sorted : List ℕ} (hsorted : ∀ x ∈ sorted, x ∈ atoms) {s : KekState}
    (hi : WalkInv wa atoms m0 cands0 s) :
    StepW wa atoms sorted m0 cands0 s (kekulizeStep wa atoms sorted s) := by
  have hbb : s.m.bondBetween? = m0.bondBetween? := hi.skel.bondBetween?.symm
  unfold kekulizeStep
  split
  · rename_i hnone
    exact ⟨rfl, (nextAtom_eq_none hnone).2⟩
  · rename_i curr q1 hnext
    split
    · -- options kept from an earlier visit
      rename_i o ho
      have hp := popped_stored hi hsorted hnext ho
      have hlook : (s.options.lookup curr).isSome = true := by rw [ho]; rfl
      dsimp only
      split
      · rename_i hc
        exact walkInv_continue hi hp (by simpa using hc)
      · rename_i hc
        have hcc : s.cands[curr]! = true := by simpa using hc
        split
        · rename_i n rest
          split
          · rename_i k hk
            exact walkInv_placeDouble hsingle hi hp hlook hcc rfl (by rw [← hbb]; exact hk)
          · trivial
        · exact absurd rfl (hi.opt curr _ (mem_of_lookup ho)).1
    · -- a fresh scan
      rename_i ho
      have hp := popped_fresh hi hsorted hnd hwf hnext ho
      have hlook : (s.options.lookup curr).isSome = false := by rw [ho]; rfl
      dsimp only
      rw [foldl_scanStep]
      simp only [List.nil_append]
      split
      · rename_i hc
        exact walkInv_continue hi hp (by simpa using hc)
      · rename_i hc
        have hcc : s.cands[curr]! = true := by simpa using hc
        split
        · rename_i n rest hnr
          split
          · rename_i k hk
            exact walkInv_placeDouble hsingle hi hp hlook hcc hnr (by rw [← hbb]; exact hk)
          · trivial
        · split
          · rename_i lo hlo
            split
            · trivial
            · exact walkInv_backTrack hwf hi hp hlo
          · trivial

/-- **The walk ends with every atom done**, in a state that keeps the invariant. -/
theorem kekulizeLoop_walkInv (hwf : WF m0) (hnd : m0.NbrsDistinct)
    (hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
      (m0.bonds[k]! : WBond).kind = .single)
    {sorted : List ℕ} (hperm : sorted.Perm atoms) (hatoms : atoms.Nodup) :
    ∀ (fuel : ℕ) (s : KekState), WalkInv wa atoms m0 cands0 s → ∀ w,
      kekulizeLoop wa atoms sorted fuel s = some w →
        ∃ sf, WalkInv wa atoms m0 cands0 sf ∧ w = sf.m ∧ ∀ x ∈ atoms, x ∈ sf.done
  | 0, _, _, _, hw => by simp [kekulizeLoop] at hw
  | fuel + 1, s, hi, w, hw => by
    have hsorted : ∀ x ∈ sorted, x ∈ atoms := fun x hx ↦ hperm.subset hx
    unfold kekulizeLoop at hw
    split at hw
    · have hst := kekulizeStep_walkInv hwf hnd hsingle hsorted hi
      split at hw
      · rename_i r hr
        rw [hr] at hst
        subst hw
        obtain ⟨rfl, hall⟩ := hst
        exact ⟨s, hi, rfl, fun x hx ↦ hall x (hperm.symm.subset hx)⟩
      · rename_i s' hs'
        rw [hs'] at hst
        exact kekulizeLoop_walkInv hwf hnd hsingle hperm hatoms fuel s' hst w hw
    · rename_i hc
      cases hw
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, not_lt] at hc
      -- the done list has no repeats, is in the system and is at least as long: it is all of it
      have hsub : s.done ⊆ atoms := fun x hx ↦ hi.doneSub x hx
      have hp := (List.subperm_of_subset hi.doneNodup hsub).perm_of_length_le
        (by rw [← hperm.length_eq]; exact hc.1)
      exact ⟨s, hi, rfl, fun x hx ↦ hp.symm.subset hx⟩

/-- The walk's starting state keeps the invariant. -/
lemma walkInv_start {done : List ℕ} (hcs : cands0.size = m0.atoms.size) (hd : done.Nodup)
    (hds : ∀ x ∈ done, x ∈ atoms) (hdc : ∀ x ∈ done, cands0[x]! = false) :
    WalkInv wa atoms m0 cands0
      { m := m0, cands := cands0, done, adds := Array.replicate m0.numBonds false, queue := [],
        options := [], lastOpt := none, btMoves := [], numBt := 0 } where
  skel := ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  kinds k := by simp [getElem!_replicate_false]
  addsSize := by simp [numBonds]
  candsSize := hcs
  addsOk k h := by simp [getElem!_replicate_false] at h
  matching k₁ _ _ h := by simp [getElem!_replicate_false] at h
  cands x := by simp [Matched, getElem!_replicate_false]
  doneNC := hdc
  addsDone k h := by simp [getElem!_replicate_false] at h
  doneNodup := hd
  queueNodup := List.nodup_nil
  disjoint := by simp
  doneSub := hds
  queueSub := by simp
  opt := by simp
  keys := rfl
  lastOpt := rfl
  order := .inl (List.nil_sublist _)

/-- **The kekulization walk is correct.**  When it succeeds on a fused system, its result is the
starting copy with a set `D` of bonds made double: each a single bond written aromatic between
two atoms that needed a double bond, no atom with two, and every atom of the system that needed a
double bond with one. -/
theorem kekulizeWorker_correct (hwf : WF m0) (hnd : m0.NbrsDistinct)
    (hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
      (m0.bonds[k]! : WBond).kind = .single)
    (hatoms : atoms.Nodup) (hcs : cands0.size = m0.atoms.size) {done : List ℕ}
    (hd : done.Nodup) (hds : ∀ x ∈ done, x ∈ atoms) (hdc : ∀ x ∈ done, cands0[x]! = false)
    {w : Work} (hw : m0.kekulizeWorker wa atoms cands0 done = some w) :
    SameSkel m0 w ∧ ∃ D : Array Bool,
      (∀ k : ℕ, (w.bonds[k]! : WBond).kind =
        if D[k]! = true then .double else (m0.bonds[k]! : WBond).kind) ∧
      (∀ k : ℕ, D[k]! = true → k < m0.bonds.size ∧ wa k = true ∧
        (m0.bonds[k]! : WBond).kind = .single ∧ cands0[(m0.bonds[k]! : WBond).src]! = true ∧
        cands0[(m0.bonds[k]! : WBond).dst]! = true) ∧
      (∀ k₁ k₂ x : ℕ, D[k₁]! = true → D[k₂]! = true → Tch m0 k₁ x → Tch m0 k₂ x → k₁ = k₂) ∧
      ∀ x ∈ atoms, cands0[x]! = true → ∃ k : ℕ, D[k]! = true ∧ Tch m0 k x := by
  obtain ⟨sf, hi, rfl, hall⟩ := kekulizeLoop_walkInv hwf hnd hsingle (List.mergeSort_perm _ _)
    hatoms _ _ (walkInv_start hcs hd hds hdc) w hw
  refine ⟨hi.skel, sf.adds, hi.kinds, hi.addsOk, hi.matching, fun x hx hc ↦ ?_⟩
  by_contra h
  have := (hi.cands x).mpr ⟨hc, fun ⟨k, hk, ht⟩ ↦ h ⟨k, hk, ht⟩⟩
  rw [hi.doneNC x (hall x hx)] at this
  cases this











end Walk

/-! ### The graph of the working copy -/

/-- `cleanUp` keeps which atoms each bond joins. -/
lemma CleanRel.skel {o w : Work} (h : CleanRel o w) : SameSkel o w where
  numAtoms := h.atoms_size.symm
  numBonds := h.bonds_size.symm
  src k := (ends_getElem! h.bonds_size (fun k ↦ ends_of_single (h.bonds k)) k).1.symm
  dst k := (ends_getElem! h.bonds_size (fun k ↦ ends_of_single (h.bonds k)) k).2.symm

/-- Distinct neighbours depend only on which atoms the bonds join. -/
lemma SameSkel.nbrsDistinct {w w' : Work} (h : SameSkel w w') (hw : w.NbrsDistinct) :
    w'.NbrsDistinct := by
  intro c k₁ k₂ h₁ h₂ he
  rw [← h.bondsOf] at h₁ h₂
  rw [← h.other, ← h.other] at he
  exact hw c k₁ k₂ h₁ h₂ he

/-- A molecule's working copy has distinct neighbours: its graph is simple. -/
lemma nbrsDistinct_ofMolecule {n : ℕ} (m : Molecule n) : (Work.ofMolecule m).NbrsDistinct := by
  intro c k₁ k₂ h₁ h₂ he
  have hl₁ : k₁ < m.bonds.length := by
    simpa [Work.ofMolecule, numBonds] using lt_of_mem_bondsOf h₁
  have hl₂ : k₂ < m.bonds.length := by
    simpa [Work.ofMolecule, numBonds] using lt_of_mem_bondsOf h₂
  have t₁ := touches_of_mem_bondsOf h₁
  have t₂ := touches_of_mem_bondsOf h₂
  rw [ofMolecule_bond m hl₁] at t₁ he
  rw [ofMolecule_bond m hl₂] at t₂ he
  -- both bonds join `c` to the same neighbour, so they are the same edge
  have hedge : (m.bonds[k₁]).edge = (m.bonds[k₂]).edge := by
    simp only [toWBond, WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq] at t₁ t₂ he
    simp only [Bond.edge, Sym2.eq_iff, Fin.ext_iff]
    split at he <;> split at he <;> simp_all <;> omega
  have hnd := m.nodup
  have e : (m.bonds.map Bond.edge)[k₁]'(by simpa using hl₁) =
      (m.bonds.map Bond.edge)[k₂]'(by simpa using hl₂) := by simpa using hedge
  exact (List.Nodup.getElem_inj_iff hnd).mp e

/-- The copy `aromatize` kekulizes is well formed with distinct neighbours. -/
lemma wf_nbrsDistinct_prepare {n : ℕ} (m : Molecule n) :
    WF (Work.prepare m) ∧ (Work.prepare m).NbrsDistinct := by
  have hs : SameSkel (Work.ofMolecule m) (Work.prepare m) :=
    (skel_freezeHs _).trans ((cleanRel_cleanUp _).skel.trans (skel_cacheValences _))
  exact ⟨hs.wf (ofMolecule_wf m), hs.nbrsDistinct (nbrsDistinct_ofMolecule m)⟩

/-! ### One fused system -/

/-- `eraseDups` leaves no repeats. -/
theorem nodup_eraseDups' : ∀ (l : List ℕ), l.eraseDups.Nodup
  | [] => List.nodup_nil
  | a :: as => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun h ↦ ?_, ?_⟩
    · rw [List.mem_eraseDups, List.mem_filter] at h
      simp at h
    · exact nodup_eraseDups' _
  termination_by l => l.length
  decreasing_by
    simp only [List.length_cons]
    exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The candidate array `kekulizeSystem` builds: an atom of `l` that `p` accepts, in range. -/
lemma foldl_cands (p : ℕ → Bool) : ∀ (l : List ℕ) (c : Array Bool),
    (l.foldl (fun c i ↦ if p i then c.set! i true else c) c).size = c.size ∧
    ∀ x, (l.foldl (fun c i ↦ if p i then c.set! i true else c) c)[x]! = true ↔
      c[x]! = true ∨ (x ∈ l ∧ p x = true ∧ x < c.size)
  | [], c => ⟨rfl, by simp⟩
  | i :: l, c => by
    obtain ⟨ih1, ih2⟩ := foldl_cands p l (if p i then c.set! i true else c)
    simp only [List.foldl_cons]
    refine ⟨by rw [ih1]; split <;> simp, fun x ↦ ?_⟩
    rw [ih2 x]
    by_cases hp : p i = true
    · simp only [hp, ↓reduceIte]
      have hs : (c.set! i true).size = c.size := by simp
      rw [hs, getElem!_set!_bool]
      by_cases hx : i = x
      · subst hx
        by_cases hlt : i < c.size <;> simp [hlt, hp]
      · simp [hx, Ne.symm hx]
    · simp only [Bool.not_eq_true] at hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (h | ⟨hm, hpx, hlt⟩)
        · exact .inl h
        · exact .inr ⟨.inr hm, hpx, hlt⟩
      · rintro (h | ⟨hm | hm, hpx, hlt⟩)
        · exact .inl h
        · subst hm
          rw [hp] at hpx
          cases hpx
        · exact .inr ⟨hm, hpx, hlt⟩

/-- Making single the bonds written aromatic at one atom, if it is flagged aromatic. -/
lemma singleAromaticBonds_kind (wa : ℕ → Bool) (out : Work) (i k : ℕ) :
    SameSkel out (singleAromaticBonds wa out i) ∧
    ((singleAromaticBonds wa out i).bonds[k]! : WBond).kind =
      if (out.atoms[i]! : WAtom).aromatic = true ∧ k ∈ out.bondsOf i ∧ wa k = true then .single
      else (out.bonds[k]! : WBond).kind := by
  unfold singleAromaticBonds
  split
  · rename_i ha
    have key : ∀ (l : List ℕ) (o : Work), SameSkel out o →
        SameSkel out (l.foldl (fun o k ↦ if wa k then o.setKind k .single else o) o) ∧
        ((l.foldl (fun o k ↦ if wa k then o.setKind k .single else o) o).bonds[k]! : WBond).kind =
          if k ∈ l ∧ wa k = true ∧ k < out.bonds.size then .single
          else (o.bonds[k]! : WBond).kind := by
      intro l
      induction l with
      | nil => intro o h; exact ⟨h, by simp⟩
      | cons j l ih =>
        intro o h
        rw [List.foldl_cons]
        by_cases hj : wa j = true
        · rw [if_pos hj]
          obtain ⟨h1, h2⟩ := ih _ (h.trans (skel_setKind _ _ _))
          refine ⟨h1, ?_⟩
          rw [h2, kind_setKind]
          have hsz : o.bonds.size = out.bonds.size := h.numBonds.symm
          by_cases hk : k ∈ l ∧ wa k = true ∧ k < out.bonds.size
          · rw [if_pos hk, if_pos ⟨List.mem_cons_of_mem _ hk.1, hk.2⟩]
          · rw [if_neg hk]
            by_cases hjk : j = k ∧ k < o.bonds.size
            · rw [if_pos hjk, if_pos ⟨by rw [hjk.1]; exact List.mem_cons_self, hjk.1 ▸ hj,
                hsz ▸ hjk.2⟩]
            · rw [if_neg hjk, if_neg]
              rintro ⟨hm, hw, hlt⟩
              rcases List.mem_cons.mp hm with e | e
              · exact hjk ⟨e.symm, hsz ▸ hlt⟩
              · exact hk ⟨e, hw, hlt⟩
        · rw [if_neg hj]
          obtain ⟨h1, h2⟩ := ih _ h
          refine ⟨h1, ?_⟩
          rw [h2]
          congr 1
          apply propext
          constructor
          · rintro ⟨hm, hw, hlt⟩
            exact ⟨List.mem_cons_of_mem _ hm, hw, hlt⟩
          · rintro ⟨hm, hw, hlt⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · exact absurd hw hj
            · exact ⟨hm, hw, hlt⟩
    obtain ⟨h1, h2⟩ := key (out.bondsOf i) out ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
    refine ⟨h1, ?_⟩
    rw [h2]
    by_cases hk : k ∈ out.bondsOf i ∧ wa k = true
    · rw [if_pos ⟨hk.1, hk.2, lt_of_mem_bondsOf hk.1⟩, if_pos ⟨ha, hk⟩]
    · rw [if_neg (fun h ↦ hk ⟨h.1, h.2.1⟩), if_neg (fun h ↦ hk h.2)]
  · rename_i ha
    exact ⟨⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, by rw [if_neg (fun h ↦ ha h.1)]⟩

/-- Making bonds single does not touch the atoms. -/
lemma singleAromaticBonds_atoms (wa : ℕ → Bool) (out : Work) (i : ℕ) :
    (singleAromaticBonds wa out i).atoms = out.atoms := by
  unfold singleAromaticBonds
  split
  · have key : ∀ (l : List ℕ) (o : Work),
        (l.foldl (fun o k ↦ if wa k then o.setKind k .single else o) o).atoms = o.atoms := by
      intro l
      induction l with
      | nil => intro o; rfl
      | cons k l ih =>
        intro o
        rw [List.foldl_cons, ih]
        split <;> rfl
    exact key _ _
  · rfl

/-- Making single the aromatic bonds of the system's aromatic atoms: a bond written aromatic at
one of them becomes single; nothing else changes. -/
lemma foldl_singleAromaticBonds_kind (wa : ℕ → Bool) : ∀ (l : List ℕ) (out : Work),
    SameSkel out (l.foldl (singleAromaticBonds wa) out) ∧
    (l.foldl (singleAromaticBonds wa) out).atoms = out.atoms ∧
    ∀ k, ((l.foldl (singleAromaticBonds wa) out).bonds[k]! : WBond).kind =
      if ∃ x ∈ l, (out.atoms[x]! : WAtom).aromatic = true ∧ k ∈ out.bondsOf x ∧ wa k = true
      then .single else (out.bonds[k]! : WBond).kind
  | [], out => ⟨⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, rfl, by simp⟩
  | i :: l, out => by
    rw [List.foldl_cons]
    have hs := fun k ↦ singleAromaticBonds_kind wa out i k
    have hsk : SameSkel out (singleAromaticBonds wa out i) := (hs 0).1
    have hat := singleAromaticBonds_atoms wa out i
    obtain ⟨h1, h2, h3⟩ := foldl_singleAromaticBonds_kind wa l (singleAromaticBonds wa out i)
    refine ⟨hsk.trans h1, h2.trans hat, fun k ↦ ?_⟩
    rw [h3 k, (hs k).2, hat, ← hsk.bondsOf]
    by_cases hl : ∃ x ∈ l, (out.atoms[x]! : WAtom).aromatic = true ∧ k ∈ out.bondsOf x ∧
        wa k = true
    · rw [if_pos hl, if_pos (by obtain ⟨x, hx, h⟩ := hl; exact ⟨x, List.mem_cons_of_mem _ hx, h⟩)]
    · rw [if_neg hl]
      congr 1
      apply propext
      constructor
      · intro h
        exact ⟨i, List.mem_cons_self, h⟩
      · rintro ⟨x, hx, h⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact h
        · exact absurd ⟨x, hx, h⟩ hl

/-- **One fused system is kekulized correctly.**  With `atoms` its atoms and `cand x` "aromatic
and needing a double bond": the result has the input's atoms and bond ends; a bond is double
where a set `D` says, else single if it is written aromatic at an aromatic atom of the system,
else as it was; `D` is a matching of candidates of the system across bonds written aromatic; and
every candidate of the system is matched. -/
theorem kekulizeSystem_correct {wa : ℕ → Bool} {ev0 : List ℕ} {rings : Array (List ℕ)}
    {out w : Work} {system : List ℕ} (hwf : WF out) (hnd : out.NbrsDistinct)
    (hw : kekulizeSystem wa ev0 rings out system = .ok w) :
    let atoms := (system.flatMap (rings[·]!)).eraseDups
    let cand := fun x ↦ (out.atoms[x]! : WAtom).aromatic && out.needsDoubleBond wa ev0[x]! x
    w.atoms = out.atoms ∧ SameSkel out w ∧ ∃ D : Array Bool,
      (∀ k : ℕ, (w.bonds[k]! : WBond).kind = if D[k]! = true then .double else
        if ∃ x ∈ atoms, (out.atoms[x]! : WAtom).aromatic = true ∧ k ∈ out.bondsOf x ∧ wa k = true
        then .single else (out.bonds[k]! : WBond).kind) ∧
      (∀ k : ℕ, D[k]! = true → k < out.bonds.size ∧ wa k = true ∧
        ∀ x, (out.bonds[k]! : WBond).touches x = true → x ∈ atoms ∧ cand x = true) ∧
      (∀ k₁ k₂ x : ℕ, D[k₁]! = true → D[k₂]! = true → (out.bonds[k₁]! : WBond).touches x = true →
        (out.bonds[k₂]! : WBond).touches x = true → k₁ = k₂) ∧
      ∀ x ∈ atoms, cand x = true → x < out.atoms.size →
        ∃ k : ℕ, D[k]! = true ∧ (out.bonds[k]! : WBond).touches x = true := by
  intro atoms cand
  unfold kekulizeSystem at hw
  dsimp only at hw
  split at hw
  · -- nothing aromatic in the system: unchanged
    rename_i hna
    cases hw
    have hnone : ∀ x ∈ atoms, (out.atoms[x]! : WAtom).aromatic = false := by
      intro x hx
      simp only [Bool.not_eq_true', List.any_eq_false] at hna
      simpa using hna x hx
    refine ⟨rfl, ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, #[], fun k ↦ ?_, fun k h ↦ ?_,
      fun k₁ _ _ h ↦ ?_, fun x hx hc _ ↦ ?_⟩
    · rw [if_neg (by simp), if_neg]
      rintro ⟨x, hx, h, -⟩
      rw [hnone x hx] at h
      cases h
    · simp at h
    · simp at h
    · simp only [cand, hnone x hx, Bool.false_and] at hc
      cases hc
  · split at hw
    · rename_i m' hm'
      have hw' : m' = w := by cases hw; rfl
      subst hw'
      set m0 := atoms.foldl (singleAromaticBonds wa) out with hm0
      obtain ⟨hsk0, hat0, hkind0⟩ := foldl_singleAromaticBonds_kind wa atoms out
      have hcf := foldl_cands cand atoms (Array.replicate out.numAtoms false)
      set cands0 := atoms.foldl (fun c i ↦ if cand i then c.set! i true else c)
        (Array.replicate out.numAtoms false) with hc0
      have hcand : ∀ x, cands0[x]! = true ↔ x ∈ atoms ∧ cand x = true ∧ x < out.atoms.size := by
        intro x
        rw [hcf.2 x]
        simp [getElem!_replicate_false, numAtoms, Array.size_replicate]
      have htch : ∀ k x, Tch m0 k x ↔ (out.bonds[k]! : WBond).touches x = true := by
        intro k x
        simp only [Tch, WBond.touches]
        rw [← hsk0.src k, ← hsk0.dst k]
      have hsingle : ∀ k, wa k = true → ∀ x, cands0[x]! = true → Tch m0 k x →
          (m0.bonds[k]! : WBond).kind = .single := by
        intro k hk x hx ht
        obtain ⟨hxa, hxc, -⟩ := (hcand x).mp hx
        have harom : (out.atoms[x]! : WAtom).aromatic = true := by
          simp only [cand, Bool.and_eq_true] at hxc
          exact hxc.1
        by_cases hlt : k < out.bonds.size
        · have hmem : k ∈ out.bondsOf x :=
            List.mem_filter.mpr ⟨List.mem_range.mpr hlt, (htch k x).mp ht⟩
          rw [hkind0 k, if_pos ⟨x, hxa, harom, hmem, hk⟩]
        · have hsz0 : m0.bonds.size = out.bonds.size := hsk0.numBonds.symm
          rw [getElem!_neg _ k (by rw [hsz0]; exact hlt)]
          rfl
      have hdone : ∀ x ∈ atoms.filter (fun x ↦ !(out.atoms[x]! : WAtom).aromatic),
          cands0[x]! = false := by
        intro x hx
        rw [Bool.eq_false_iff]
        intro h
        obtain ⟨-, hxc, -⟩ := (hcand x).mp h
        simp only [List.mem_filter, Bool.not_eq_true'] at hx
        simp [cand, hx.2] at hxc
      obtain ⟨hskw, D, hDk, hDok, hDm, hDcov⟩ := kekulizeWorker_correct
        (hsk0.wf hwf) (hsk0.nbrsDistinct hnd) hsingle (nodup_eraseDups' _)
        (by rw [hcf.1, hat0]; simp [numAtoms]) ((nodup_eraseDups' _).filter _)
        (fun x hx ↦ List.mem_of_mem_filter hx) hdone hm'
      have hatw : m'.atoms = out.atoms := by
        have := kekulizeWorker_m (Q := fun w ↦ w.atoms = m0.atoms) (fun _ _ _ h ↦ h) rfl hm'
        rw [this, hat0]
      refine ⟨hatw, hsk0.trans hskw, D, fun k ↦ ?_, fun k hk ↦ ?_, fun k₁ k₂ x h₁ h₂ t₁ t₂ ↦ ?_,
        fun x hx hc hlt ↦ ?_⟩
      · rw [hDk k, hkind0 k]
      · obtain ⟨hlt, hwk, -, hs, hd⟩ := hDok k hk
        have hsz0 : m0.bonds.size = out.bonds.size := hsk0.numBonds.symm
        refine ⟨hsz0 ▸ hlt, hwk, fun x ht ↦ ?_⟩
        simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
        rcases ht with ht | ht
        · obtain ⟨h1, h2, -⟩ := (hcand x).mp (by rw [← ht, hsk0.src]; exact hs)
          exact ⟨h1, h2⟩
        · obtain ⟨h1, h2, -⟩ := (hcand x).mp (by rw [← ht, hsk0.dst]; exact hd)
          exact ⟨h1, h2⟩
      · exact hDm k₁ k₂ x h₁ h₂ ((htch _ _).mpr t₁) ((htch _ _).mpr t₂)
      · obtain ⟨k, hk, ht⟩ := hDcov x hx ((hcand x).mpr ⟨hx, hc, hlt⟩)
        exact ⟨k, hk, (htch k x).mp ht⟩
    · cases hw

end LeanSMILES.Aromaticity.Work
