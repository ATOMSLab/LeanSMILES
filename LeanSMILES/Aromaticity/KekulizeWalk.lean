/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeFacts
public import LeanSMILES.Aromaticity.KekuleSim

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
    fun a ha b hb ↦ by rw [List.mem_singleton] at hb; subst hb; exact fun e ↦ hp.currNotDone (e ▸ ha)⟩
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
  refine ⟨hi.skel.trans (skel_setKind _ _ _), fun k₁ ↦ ?_, by simp [hi.addsSize], fun k₁ hk₁ ↦ ?_,
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

end Walk





end LeanSMILES.Aromaticity.Work
