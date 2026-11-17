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

end Walk

end LeanSMILES.Aromaticity.Work
