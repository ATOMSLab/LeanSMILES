/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RelistPerceive
public import LeanSMILES.Aromaticity.KekulizeRelabel

/-!
# LeanSMILES.Aromaticity.KekulizeRelist

The kekulization walk on a relisted copy

The walk (`Work.kekulizeWorker`) never reads a bond's kind: it reads which atoms the bonds join
(through `bondBetween?` and the neighbour lists, the latter sorted before use), the flags
"written aromatic" and the candidates.  So on two copies whose bonds join the same atoms, bond `k`
of one listed as `π k` of the other (`Work.WalkRel`), it takes the same steps, places the same
double bonds renumbered, and succeeds or fails alike (`Work.kekulizeWorker_rel`).  The atoms done
at the start may also be listed in another order: the walk reads the done list only up to order,
except for the part it adds itself, which is the same on both sides (`Work.StRel`).

## Main definitions

* `Work.WalkRel Q π ρ m m'`: `m'` has `m`'s atoms, bond `π k` of `m'` joins the atoms bond `k` of
  `m` joins, and the kinds agree where `Q` says.
* `Work.StRel`: two states of the walk in step.
* `Work.kekSys`: `kekulizeSystem` once the system's atoms are listed.
* `Work.ExRel R`: two results that fail alike or succeed related by `R`.

## Main statements

* `Work.kekulizeStep_rel`, `Work.kekulizeLoop_rel`: one step of the walk, and the whole walk, in
  step.
* `Work.kekulizeWorker_rel`: the worker on related copies ends alike, on related copies.
* `Work.kekSys_rel`: one fused system on related copies fails alike or succeeds on related copies.
* `Work.kekulize_walkRel`: kekulization of a relisted copy, over the same rings, fails alike or
  succeeds on relisted copies.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- `m'` has `m`'s atoms, and bond `π k` of `m'` joins the atoms bond `k` of `m` joins; the kinds
agree where `Q` says. -/
structure WalkRel (Q : ℕ → Prop) (π ρ : ℕ → ℕ) (m m' : Work) : Prop where
  /-- The atoms are the same. -/
  atoms : m'.atoms = m.atoms
  /-- There are as many bonds. -/
  size : m'.bonds.size = m.bonds.size
  /-- `π` and `ρ` are inverse renumberings of the bonds. -/
  bij : IdxBij m.bonds.size π ρ
  /-- Bond `π k` of `m'` has the endpoints of bond `k` of `m`, in the same or the other order. -/
  ends : ∀ k < m.bonds.size,
    ((m'.bonds[π k]! : WBond).src = (m.bonds[k]! : WBond).src ∧
      (m'.bonds[π k]! : WBond).dst = (m.bonds[k]! : WBond).dst) ∨
    ((m'.bonds[π k]! : WBond).src = (m.bonds[k]! : WBond).dst ∧
      (m'.bonds[π k]! : WBond).dst = (m.bonds[k]! : WBond).src)
  /-- The bond between two atoms is renumbered by `π`. -/
  bb : ∀ u v, m'.bondBetween? u v = (m.bondBetween? u v).map π
  /-- Every atom has the same neighbour atoms, in some order. -/
  nbrs : ∀ u, ((m'.neighbors u).map (·.2)).Perm ((m.neighbors u).map (·.2))
  /-- Bond `π k` of `m'` has the kind of bond `k` of `m` where `Q k` holds. -/
  kind : ∀ k < m.bonds.size, Q k → (m'.bonds[π k]! : WBond).kind = (m.bonds[k]! : WBond).kind

namespace WalkRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work}

/-- Bond `π k` of `m'` touches the same atoms as bond `k` of `m`. -/
lemma touches (h : WalkRel Q π ρ m m') {k : ℕ} (hk : k < m.bonds.size) (x : ℕ) :
    (m'.bonds[π k]! : WBond).touches x = (m.bonds[k]! : WBond).touches x := by
  simp only [WBond.touches]
  rcases h.ends k hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, Bool.or_comm]

/-- Changing the kinds alike keeps the relation. -/
lemma of_skel (h : WalkRel Q π ρ m m') {r r' : Work} (hs : SameSkel m r) (hs' : SameSkel m' r')
    (ha : r'.atoms = r.atoms) {Q' : ℕ → Prop}
    (hk : ∀ k < m.bonds.size, Q' k → (r'.bonds[π k]! : WBond).kind = (r.bonds[k]! : WBond).kind) :
    WalkRel Q' π ρ r r' := by
  have e : r.bonds.size = m.bonds.size := hs.numBonds.symm
  have e' : r'.bonds.size = m'.bonds.size := hs'.numBonds.symm
  refine ⟨ha, by rw [e, e', h.size], e ▸ h.bij, fun k hk' ↦ ?_,
    fun u v ↦ ?_, fun u ↦ ?_, fun k hk' hq ↦ hk k (e ▸ hk') hq⟩
  · rw [e] at hk'
    rw [← hs.src, ← hs.dst, ← hs'.src, ← hs'.dst]
    exact h.ends k hk'
  · rw [← hs.bondBetween?, ← hs'.bondBetween?]
    exact h.bb u v
  · rw [← hs.neighbors, ← hs'.neighbors]
    exact h.nbrs u

/-- Setting the kind of a bond, alike on both sides. -/
lemma setKind (h : WalkRel Q π ρ m m') {k : ℕ} (hk : k < m.bonds.size) (o : BondKind) :
    WalkRel Q π ρ (m.setKind k o) (m'.setKind (π k) o) := by
  refine h.of_skel (skel_setKind _ _ _) (skel_setKind _ _ _) h.atoms fun j hj hq ↦ ?_
  rw [kind_setKind, kind_setKind, h.size]
  by_cases hjk : k = j
  · subst hjk
    rw [if_pos ⟨rfl, h.bij.lt k hk⟩, if_pos ⟨rfl, hk⟩]
  · rw [if_neg (fun e ↦ hjk (h.bij.inj hk hj e.1)), if_neg (fun e ↦ hjk e.1)]
    exact h.kind j hj hq

end WalkRel

/-! ### Helpers on lists -/

/-- Two orderings of the same list of numbers sort to the same list. -/
lemma mergeSort_eq_of_perm {l l' : List ℕ} (h : l'.Perm l) :
    l'.mergeSort (fun a b ↦ decide (a ≤ b)) = l.mergeSort (fun a b ↦ decide (a ≤ b)) := by
  have htr : ∀ a b c : ℕ, decide (a ≤ b) = true → decide (b ≤ c) = true → decide (a ≤ c) = true :=
    fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; omega
  have htot : ∀ a b : ℕ, (decide (a ≤ b) || decide (b ≤ a)) = true :=
    fun a b ↦ by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
  apply List.Perm.eq_of_pairwise (le := fun a b : ℕ ↦ decide (a ≤ b) = true)
  · intro a b _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    omega
  · exact List.pairwise_mergeSort htr htot _
  · exact List.pairwise_mergeSort htr htot _
  · exact ((List.mergeSort_perm _ _).trans h).trans (List.mergeSort_perm _ _).symm

/-- The index of `a` in `p ++ t`, with `a` not in `p`, is the length of `p` plus its index in
`t`. -/
lemma idxOf_append_of_not_mem : ∀ {p t : List ℕ} {a : ℕ}, a ∉ p →
    (p ++ t).idxOf a = p.length + t.idxOf a
  | [], _, _, _ => by simp
  | x :: p, t, a, h => by
    rw [List.mem_cons, not_or] at h
    rw [List.cons_append, List.idxOf_cons_ne _ (fun e ↦ h.1 e.symm),
      idxOf_append_of_not_mem h.2, List.length_cons]
    omega

/-- Reordering the prefix does not change what `p ++ t` contains. -/
lemma contains_append_perm {p p' t : List ℕ} (h : p'.Perm p) (x : ℕ) :
    (p' ++ t).contains x = (p ++ t).contains x := by
  rw [List.contains_append, List.contains_append, h.contains_eq]

/-! ### Two walks in step -/

/-- Two states of the walk in step: on related copies, with the same candidates, queue, options
and backtracking data, the placed double bonds renumbered, and done lists that differ only in
the order of a prefix the walk started with; atoms the walk handles avoid that prefix. -/
structure StRel (Q : ℕ → Prop) (π ρ : ℕ → ℕ) (N : ℕ) (p p' : List ℕ) (s s' : KekState) :
    Prop where
  /-- The molecules are related. -/
  m : WalkRel Q π ρ s.m s'.m
  /-- The molecule has `N` bonds. -/
  sz : s.m.bonds.size = N
  /-- The same candidates. -/
  cands : s'.cands = s.cands
  /-- Bond `π k` is made double on one side exactly when bond `k` is on the other. -/
  adds : ∀ k < N, s'.adds[π k]! = s.adds[k]!
  /-- One flag per bond. -/
  asz : s.adds.size = N
  /-- One flag per bond, on the other side. -/
  asz' : s'.adds.size = N
  /-- The same queue. -/
  queue : s'.queue = s.queue
  /-- The same options. -/
  options : s'.options = s.options
  /-- The same atom to back-track to. -/
  lastOpt : s'.lastOpt = s.lastOpt
  /-- The same atoms with untried options. -/
  btMoves : s'.btMoves = s.btMoves
  /-- As many back-tracks. -/
  numBt : s'.numBt = s.numBt
  /-- The starting prefixes are reorderings of each other. -/
  perm : p'.Perm p
  /-- The done lists are the prefixes followed by a common tail that avoids `p`. -/
  tail : ∃ t, s.done = p ++ t ∧ s'.done = p' ++ t ∧ ∀ x ∈ t, x ∉ p
  /-- The queue avoids `p`. -/
  avoidQ : ∀ x ∈ s.queue, x ∉ p
  /-- The atoms with untried options avoid `p`. -/
  avoidB : ∀ x ∈ s.btMoves, x ∉ p
  /-- The atom to back-track to is not in `p`. -/
  avoidL : ∀ x ∈ s.lastOpt, x ∉ p

namespace StRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ} {s s' : KekState}

/-- The done lists contain the same atoms. -/
lemma done_contains (h : StRel Q π ρ N p p' s s') (x : ℕ) :
    s'.done.contains x = s.done.contains x := by
  obtain ⟨t, h1, h2, -⟩ := h.tail
  rw [h1, h2, contains_append_perm h.perm]

/-- The done lists have the same length. -/
lemma done_length (h : StRel Q π ρ N p p' s s') : s'.done.length = s.done.length := by
  obtain ⟨t, h1, h2, -⟩ := h.tail
  rw [h1, h2, List.length_append, List.length_append, h.perm.length_eq]

/-- States in step visit the same atom next, with the same queue after it. -/
lemma nextAtom (h : StRel Q π ρ N p p' s s') (sorted : List ℕ) :
    s'.nextAtom sorted = s.nextAtom sorted := by
  unfold KekState.nextAtom
  rw [h.queue]
  have : (fun x ↦ !s'.done.contains x) = (fun x ↦ !s.done.contains x) := by
    funext x; rw [h.done_contains]
  rw [this]

/-- The atom the walk visits next is not in the starting prefix. -/
lemma nextAtom_not_mem (h : StRel Q π ρ N p p' s s') {sorted : List ℕ} {c : ℕ} {q : List ℕ}
    (hn : s.nextAtom sorted = some (c, q)) : c ∉ p ∧ ∀ x ∈ q, x ∉ p := by
  unfold KekState.nextAtom at hn
  split at hn
  · rename_i c' rest hq
    cases hn
    exact ⟨h.avoidQ _ (by rw [hq]; exact List.mem_cons_self),
      fun x hx ↦ h.avoidQ x (by rw [hq]; exact List.mem_cons_of_mem _ hx)⟩
  · obtain ⟨c', hc', e⟩ := Option.map_eq_some_iff.1 hn
    cases e
    refine ⟨fun hcp ↦ ?_, by simp⟩
    have := List.find?_some hc'
    obtain ⟨t, h1, -, -⟩ := h.tail
    rw [h1] at this
    have hn : c ∉ p ++ t := by simpa [List.contains_iff_mem] using this
    exact hn (List.mem_append_left _ hcp)

end StRel

/-- What two steps of the walk in step give: the same end, related, or states in step. -/
def StepRel (Q : ℕ → Prop) (π ρ : ℕ → ℕ) (N : ℕ) (p p' : List ℕ) :
    Option Work ⊕ KekState → Option Work ⊕ KekState → Prop
  | .inl r, .inl r' => Option.Rel (WalkRel Q π ρ) r r'
  | .inr s, .inr s' => StRel Q π ρ N p p' s s'
  | _, _ => False

/-! ### Placing a double bond, backtracking -/

/-- The bookkeeping of `KekState.placeDouble`: options, backtrack points, latest one. -/
def pdBook (options : List (ℕ × List ℕ)) (btMoves : List ℕ) (lastOpt : Option ℕ) (curr : ℕ)
    (rest : List ℕ) : List (ℕ × List ℕ) × List ℕ × Option ℕ :=
  if (options.lookup curr).isSome then
    if rest.isEmpty then
      (options.filter (·.1 != curr), btMoves.dropLast, btMoves.dropLast.getLast?)
    else
      (options.map fun (a, o) ↦ if a == curr then (a, rest) else (a, o), btMoves, lastOpt)
  else if !rest.isEmpty then (options ++ [(curr, rest)], btMoves ++ [curr], some curr)
  else (options, btMoves, lastOpt)

/-- `KekState.placeDouble` with its bookkeeping written through `pdBook`. -/
lemma placeDouble_eq (s : KekState) (curr n k : ℕ) (rest : List ℕ) :
    s.placeDouble curr n k rest =
      { s with m := s.m.setKind k .double, cands := (s.cands.set! curr false).set! n false,
               adds := s.adds.set! k true,
               options := (pdBook s.options s.btMoves s.lastOpt curr rest).1,
               btMoves := (pdBook s.options s.btMoves s.lastOpt curr rest).2.1,
               lastOpt := (pdBook s.options s.btMoves s.lastOpt curr rest).2.2 } := by
  unfold KekState.placeDouble pdBook
  split_ifs <;> rfl

/-- If the backtrack points, the latest one and `curr` avoid `p`, so do the new backtrack points
and latest one `pdBook` gives. -/
lemma pdBook_avoid {options : List (ℕ × List ℕ)} {btMoves : List ℕ} {lastOpt : Option ℕ}
    {curr : ℕ} {rest p : List ℕ} (hb : ∀ x ∈ btMoves, x ∉ p) (hl : ∀ x ∈ lastOpt, x ∉ p)
    (hc : curr ∉ p) :
    (∀ x ∈ (pdBook options btMoves lastOpt curr rest).2.1, x ∉ p) ∧
      ∀ x ∈ (pdBook options btMoves lastOpt curr rest).2.2, x ∉ p := by
  unfold pdBook
  split_ifs
  · refine ⟨fun x hx ↦ hb x (List.dropLast_subset _ hx), fun x hx ↦ ?_⟩
    exact hb x (List.dropLast_subset _ (List.mem_of_getLast? hx))
  · exact ⟨hb, hl⟩
  · refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact hb x hx
      · rw [List.mem_singleton.1 hx]; exact hc
    · rw [Option.mem_def, Option.some.injEq] at hx
      rw [← hx]; exact hc
  · exact ⟨hb, hl⟩

namespace StRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ} {s s' : KekState}

/-- Placing the double bond `k`, renumbered on the other side, keeps the walks in step. -/
lemma placeDouble (h : StRel Q π ρ N p p' s s') {curr n k : ℕ} (hk : k < N) (hc : curr ∉ p)
    (rest : List ℕ) :
    StRel Q π ρ N p p' (s.placeDouble curr n k rest) (s'.placeDouble curr n (π k) rest) := by
  rw [placeDouble_eq, placeDouble_eq, h.options, h.btMoves, h.lastOpt, h.cands]
  obtain ⟨hb, hl⟩ := pdBook_avoid (options := s.options) (rest := rest) h.avoidB h.avoidL hc
  have hk' : k < s.m.bonds.size := h.sz ▸ hk
  refine ⟨h.m.setKind hk' .double, by simp [setKind, h.sz], rfl, fun j hj ↦ ?_,
    by simp [h.asz], by simp [h.asz'], h.queue, rfl, rfl, rfl, h.numBt, h.perm, h.tail, h.avoidQ,
    hb, hl⟩
  dsimp only
  rw [getElem!_set!_bool, getElem!_set!_bool, h.adds j hj]
  have hj' : j < s.m.bonds.size := h.sz ▸ hj
  by_cases hjk : k = j
  · subst hjk
    have : π k < N := h.sz ▸ h.m.bij.lt k hk'
    simp [h.asz, h.asz', this, hk]
  · have : π k ≠ π j := fun e ↦ hjk (h.m.bij.inj hk' hj' e)
    simp [this, hjk]

end StRel

/-- `KekState.backTrack` unfolded, field by field. -/
lemma backTrack_eq (s : KekState) (lo : ℕ) :
    s.backTrack lo =
      { s with m := ((List.range s.m.numBonds).foldl (undoAdds (s.done.take (s.done.idxOf lo)))
                      (s.m, s.adds, s.cands)).1,
               adds := ((List.range s.m.numBonds).foldl (undoAdds (s.done.take (s.done.idxOf lo)))
                      (s.m, s.adds, s.cands)).2.1,
               cands := ((List.range s.m.numBonds).foldl
                      (undoAdds (s.done.take (s.done.idxOf lo))) (s.m, s.adds, s.cands)).2.2,
               queue := s.done.drop (s.done.idxOf lo) ++ s.queue,
               done := s.done.take (s.done.idxOf lo), numBt := s.numBt + 1 } := rfl

/-- A fold of `undoAdds` keeps the atoms. -/
lemma foldl_undoAdds_atoms (keep : List ℕ) : ∀ (l : List ℕ) (w : Work) (A C : Array Bool),
    (l.foldl (undoAdds keep) (w, A, C)).1.atoms = w.atoms
  | [], _, _, _ => rfl
  | j :: l, w, A, C => by
    simp only [List.foldl_cons, undoAdds_eq]
    split
    · rw [foldl_undoAdds_atoms keep l]; rfl
    · exact foldl_undoAdds_atoms keep l _ _ _

/-- `undoAdds` reads the atoms kept only through membership. -/
lemma undoAdds_congr {keep keep' : List ℕ} (h : ∀ x, keep'.contains x = keep.contains x) :
    undoAdds keep' = undoAdds keep := by
  funext q k
  unfold undoAdds
  simp only [h]

namespace StRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ} {s s' : KekState}

/-- Backtracking to the same atom keeps the walks in step. -/
lemma backTrack (h : StRel Q π ρ N p p' s s') {lo : ℕ} (hlo : lo ∈ s.lastOpt) :
    StRel Q π ρ N p p' (s.backTrack lo) (s'.backTrack lo) := by
  obtain ⟨t, h1, h2, ht⟩ := h.tail
  have hlp : lo ∉ p := h.avoidL lo hlo
  have hlp' : lo ∉ p' := fun e ↦ hlp (h.perm.subset e)
  have hpos : s.done.idxOf lo = p.length + t.idxOf lo := by
    rw [h1, idxOf_append_of_not_mem hlp]
  have hpos' : s'.done.idxOf lo = p.length + t.idxOf lo := by
    rw [h2, idxOf_append_of_not_mem hlp', h.perm.length_eq]
  have hkeep : s.done.take (s.done.idxOf lo) = p ++ t.take (t.idxOf lo) := by
    rw [hpos, h1, List.take_append]; simp
  have hkeep' : s'.done.take (s'.done.idxOf lo) = p' ++ t.take (t.idxOf lo) := by
    rw [hpos', h2, List.take_append, ← h.perm.length_eq]; simp
  have hdrop : s.done.drop (s.done.idxOf lo) = t.drop (t.idxOf lo) := by
    rw [hpos, h1, List.drop_append]; simp
  have hdrop' : s'.done.drop (s'.done.idxOf lo) = t.drop (t.idxOf lo) := by
    rw [hpos', h2, List.drop_append, ← h.perm.length_eq]; simp
  have hcont : ∀ x, (p' ++ t.take (t.idxOf lo)).contains x =
      (p ++ t.take (t.idxOf lo)).contains x := contains_append_perm h.perm
  rw [backTrack_eq, backTrack_eq]
  simp only [hkeep, hkeep', hdrop, hdrop', undoAdds_congr hcont]
  have hnb : s'.m.numBonds = N := by rw [numBonds, h.m.size, h.sz]
  have hnb0 : s.m.numBonds = N := h.sz
  rw [hnb, hnb0]
  generalize hkp : p ++ t.take (t.idxOf lo) = keep
  have hU : ∀ j < N, Undone s'.m s'.adds keep (π j) ↔ Undone s.m s.adds keep j := by
    intro j hj
    have hj' : j < s.m.bonds.size := h.sz ▸ hj
    simp only [Undone, h.adds j hj]
    rcases h.m.ends j hj' with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    tauto
  obtain ⟨sk, as, cs⟩ := foldl_undoAdds_skel keep (List.range N) s.m s.adds s.cands
  obtain ⟨sk', as', cs'⟩ := foldl_undoAdds_skel keep (List.range N) s'.m s'.adds s'.cands
  have hlt : ∀ j < N, j < s.m.bonds.size := fun j hj ↦ h.sz ▸ hj
  have hπ : ∀ j < N, π j < N := fun j hj ↦ h.sz ▸ h.m.bij.lt j (hlt j hj)
  refine ⟨h.m.of_skel sk sk' (by rw [foldl_undoAdds_atoms, foldl_undoAdds_atoms, h.m.atoms])
    fun j hj hq ↦ ?_, ?_, ?_, fun j hj ↦ ?_, as.trans h.asz, as'.trans h.asz',
    by rw [h.queue], h.options, h.lastOpt, h.btMoves, by rw [h.numBt], h.perm,
    ⟨t.take (t.idxOf lo), hkp.symm, rfl, fun x hx ↦ ht x (List.mem_of_mem_take hx)⟩,
    fun x hx ↦ ?_, h.avoidB, h.avoidL⟩
  · have hj0 : j < N := h.sz ▸ hj
    obtain ⟨a1, a2⟩ := foldl_undoAdds_kind keep (List.range N) s.m s.adds s.cands
      List.nodup_range j
    obtain ⟨b1, b2⟩ := foldl_undoAdds_kind keep (List.range N) s'.m s'.adds s'.cands
      List.nodup_range (π j)
    by_cases hu : Undone s.m s.adds keep j
    · rw [a1 (List.mem_range.2 hj0) hu hj, b1 (List.mem_range.2 (hπ j hj0)) ((hU j hj0).2 hu)
        (by rw [h.m.size]; exact h.m.bij.lt j hj)]
    · rw [a2 (fun e ↦ hu e.2), b2 (fun e ↦ hu ((hU j hj0).1 e.2))]
      exact h.m.kind j hj hq
  · exact sk.numBonds.symm.trans h.sz
  · refine array_ext_of_getElem! (by rw [cs', h.cands]) cs fun x _ ↦ ?_
    rw [Bool.eq_iff_iff, foldl_undoAdds_cands keep _ _ _ _ List.nodup_range,
      foldl_undoAdds_cands keep _ _ _ _ List.nodup_range, h.cands]
    apply or_congr_right
    apply and_congr_right
    intro _
    constructor
    · rintro ⟨j', hj', hu, htc⟩
      have hj'N := List.mem_range.1 hj'
      have hj's : j' < s.m.bonds.size := hlt j' hj'N
      have hρ : ρ j' < N := h.sz ▸ h.m.bij.lt' j' hj's
      rw [← h.m.bij.right j' hj's] at hu htc
      exact ⟨ρ j', List.mem_range.2 hρ, (hU _ hρ).1 hu, by rwa [h.m.touches (hlt _ hρ)] at htc⟩
    · rintro ⟨j, hj, hu, htc⟩
      have hjN := List.mem_range.1 hj
      exact ⟨π j, List.mem_range.2 (hπ j hjN), (hU j hjN).2 hu,
        by rw [h.m.touches (hlt j hjN)]; exact htc⟩
  · rw [Bool.eq_iff_iff, foldl_undoAdds_adds keep _ _ _ _ List.nodup_range,
      foldl_undoAdds_adds keep _ _ _ _ List.nodup_range, h.adds j hj, List.mem_range,
      List.mem_range, hU j hj]
    simp [hj, hπ j hj]
  · rcases List.mem_append.1 hx with hx | hx
    · exact ht x (List.mem_of_mem_drop hx)
    · exact h.avoidQ x hx

end StRel

/-! ### One step, the loop, the worker -/

/-- The options and the queue a step computes for the atom `curr` it visits. -/
def stepScan (wa : ℕ → Bool) (atoms : List ℕ) (s : KekState) (curr : ℕ) (queue : List ℕ) :
    List ℕ × List ℕ :=
  match s.options.lookup curr with
  | some o => (o, queue)
  | none =>
    let done := s.done ++ [curr]
    let nbrs := ((s.m.neighbors curr).map (·.2)).filter fun j ↦
      atoms.contains j && !done.contains j
    let p := (nbrs.mergeSort (· ≤ ·)).foldl
      (scanStep s.m wa s.cands curr s.cands[curr]! queue) ([], [])
    (p.2, queue ++ p.1)

/-- What a step does once it has the options for `curr`. -/
def kekCont (curr : ℕ) (s : KekState) (opts : List ℕ) : Option Work ⊕ KekState :=
  if !s.cands[curr]! then .inr s else
  match opts with
  | n :: rest =>
    match s.m.bondBetween? curr n with
    | some k => .inr (s.placeDouble curr n k rest)
    | none => .inl none
  | [] =>
    match s.lastOpt with
    | some lo => if 100 ≤ s.numBt then .inl none else .inr (s.backTrack lo)
    | none => .inl none

/-- `kekulizeStep` written through `stepScan` and `kekCont`. -/
lemma kekulizeStep_eq (wa : ℕ → Bool) (atoms sorted : List ℕ) (s : KekState) :
    kekulizeStep wa atoms sorted s =
      match s.nextAtom sorted with
      | none => .inl (some s.m)
      | some (curr, queue) =>
        kekCont curr
          { s with done := s.done ++ [curr], queue := (stepScan wa atoms s curr queue).2 }
          (stepScan wa atoms s curr queue).1 := by
  unfold kekulizeStep
  rcases s.nextAtom sorted with _ | ⟨c, q⟩
  · rfl
  · dsimp only
    unfold stepScan
    rcases s.options.lookup c with _ | o <;> rfl

/-- An atom of the queue `stepScan` returns was in the queue before or is not done. -/
lemma mem_stepScan {wa : ℕ → Bool} {atoms : List ℕ} {s : KekState} {curr : ℕ} {queue : List ℕ}
    {x : ℕ} (hx : x ∈ (stepScan wa atoms s curr queue).2) : x ∈ queue ∨ x ∉ s.done := by
  unfold stepScan at hx
  split at hx
  · exact .inl hx
  · dsimp only at hx
    rw [foldl_scanStep] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl hx
    · right
      simp only [List.nil_append, List.mem_filter] at hx
      have := ((List.mergeSort_perm _ _).subset hx.1)
      simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.contains_append,
        Bool.or_eq_false_iff] at this
      intro hd
      have h2 := this.2.2.1
      rw [List.contains_iff_mem.2 hd] at h2
      cases h2

namespace StRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ} {s s' : KekState}

/-- States in step get the same options and queue from `stepScan`, with the flags "written
aromatic" renumbered and the system's atoms the same. -/
lemma stepScan (h : StRel Q π ρ N p p' s s') {wa wa' : ℕ → Bool}
    (hwa : ∀ k < N, wa' (π k) = wa k) {atoms atoms' : List ℕ}
    (hat : ∀ x, atoms'.contains x = atoms.contains x) (curr : ℕ) (queue : List ℕ) :
    Work.stepScan wa' atoms' s' curr queue = Work.stepScan wa atoms s curr queue := by
  unfold Work.stepScan
  rw [h.options]
  split
  · rfl
  · dsimp only
    rw [h.cands, foldl_scanStep, foldl_scanStep]
    have hf : (fun j ↦ atoms'.contains j && !(s'.done ++ [curr]).contains j) =
        (fun j ↦ atoms.contains j && !(s.done ++ [curr]).contains j) := by
      funext j
      rw [hat, List.contains_append, List.contains_append, h.done_contains]
    have ht : scanTakes s'.m wa' s.cands curr s.cands[curr]! =
        scanTakes s.m wa s.cands curr s.cands[curr]! := by
      funext j
      unfold scanTakes
      rw [h.m.bb]
      rcases hb : s.m.bondBetween? curr j with _ | k
      · rfl
      · have hk : k < N := h.sz ▸ bondBetween?_lt hb
        simp only [Option.map_some, hwa k hk]
    rw [hf, ht, mergeSort_eq_of_perm ((h.m.nbrs curr).filter _)]

/-- The states a step goes on from, after visiting `curr`, are in step. -/
lemma visit (h : StRel Q π ρ N p p' s s') {curr : ℕ} (hc : curr ∉ p) {q : List ℕ}
    (hq : ∀ x ∈ q, x ∉ p) :
    StRel Q π ρ N p p' { s with done := s.done ++ [curr], queue := q }
      { s' with done := s'.done ++ [curr], queue := q } := by
  obtain ⟨t, h1, h2, ht⟩ := h.tail
  refine ⟨h.m, h.sz, h.cands, h.adds, h.asz, h.asz', rfl, h.options, h.lastOpt, h.btMoves,
    h.numBt, h.perm, ⟨t ++ [curr], by simp [h1], by simp [h2], fun x hx ↦ ?_⟩, hq, h.avoidB,
    h.avoidL⟩
  rcases List.mem_append.1 hx with hx | hx
  · exact ht x hx
  · rw [List.mem_singleton.1 hx]; exact hc

/-- `kekCont` on states in step, at an atom not in `p`, gives results in step. -/
lemma kekCont (h : StRel Q π ρ N p p' s s') {curr : ℕ} (hc : curr ∉ p) (opts : List ℕ) :
    StepRel Q π ρ N p p' (Work.kekCont curr s opts) (Work.kekCont curr s' opts) := by
  unfold Work.kekCont
  rw [h.cands]
  cases hcc : s.cands[curr]!
  · exact h
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases opts with _ | ⟨n, rest⟩
    · rw [h.lastOpt, h.numBt]
      rcases hlo : s.lastOpt with _ | lo
      · exact Option.Rel.none
      · dsimp only
        split_ifs
        · exact Option.Rel.none
        · exact h.backTrack (by rw [hlo]; rfl)
    · dsimp only
      rw [h.m.bb]
      rcases hb : s.m.bondBetween? curr n with _ | k
      · exact Option.Rel.none
      · exact h.placeDouble (h.sz ▸ bondBetween?_lt hb) hc rest

end StRel

/-- **One step of the walk, in step.** -/
theorem kekulizeStep_rel {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ} {s s' : KekState}
    (h : StRel Q π ρ N p p' s s') {wa wa' : ℕ → Bool} (hwa : ∀ k < N, wa' (π k) = wa k)
    {atoms atoms' : List ℕ} (hat : ∀ x, atoms'.contains x = atoms.contains x) (sorted : List ℕ) :
    StepRel Q π ρ N p p' (kekulizeStep wa atoms sorted s) (kekulizeStep wa' atoms' sorted s') := by
  rw [kekulizeStep_eq, kekulizeStep_eq, h.nextAtom sorted]
  rcases hn : s.nextAtom sorted with _ | ⟨curr, q⟩
  · exact Option.Rel.some h.m
  · obtain ⟨hcp, hqp⟩ := h.nextAtom_not_mem hn
    dsimp only
    rw [h.stepScan hwa hat]
    obtain ⟨t, h1, -, -⟩ := h.tail
    refine (h.visit hcp fun x hx ↦ ?_).kekCont hcp _
    rcases mem_stepScan hx with hx | hx
    · exact hqp x hx
    · exact fun hp ↦ hx (by rw [h1]; exact List.mem_append_left _ hp)

/-- **The walk, in step**: from states in step, both walks end alike, on related copies. -/
theorem kekulizeLoop_rel {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {N : ℕ} {p p' : List ℕ}
    {wa wa' : ℕ → Bool} (hwa : ∀ k < N, wa' (π k) = wa k)
    {atoms atoms' : List ℕ} (hat : ∀ x, atoms'.contains x = atoms.contains x) (sorted : List ℕ) :
    ∀ (fuel : ℕ) (s s' : KekState), StRel Q π ρ N p p' s s' →
      Option.Rel (WalkRel Q π ρ) (kekulizeLoop wa atoms sorted fuel s)
        (kekulizeLoop wa' atoms' sorted fuel s')
  | 0, _, _, _ => Option.Rel.none
  | fuel + 1, s, s', h => by
    unfold kekulizeLoop
    rw [h.done_length, h.queue]
    split
    · have hst := kekulizeStep_rel h hwa hat sorted
      revert hst
      rcases kekulizeStep wa atoms sorted s with r | t <;>
        rcases kekulizeStep wa' atoms' sorted s' with r' | t' <;> intro hst
      · exact hst
      · exact hst.elim
      · exact hst.elim
      · exact kekulizeLoop_rel hwa hat sorted fuel t t' hst
    · exact Option.Rel.some h.m


/-- **The worker, in step**: on related copies, with the same candidates, the system's atoms and
its starting done atoms listed in any order. -/
theorem kekulizeWorker_rel {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work} (hm : WalkRel Q π ρ m m')
    {wa wa' : ℕ → Bool} (hwa : ∀ k < m.bonds.size, wa' (π k) = wa k) {atoms atoms' : List ℕ}
    (hat : atoms'.Perm atoms) (cands : Array Bool) {done done' : List ℕ} (hd : done'.Perm done) :
    Option.Rel (WalkRel Q π ρ) (m.kekulizeWorker wa atoms cands done)
      (m'.kekulizeWorker wa' atoms' cands done') := by
  unfold kekulizeWorker
  have hf : kekulizeFuel atoms' = kekulizeFuel atoms := by simp [kekulizeFuel, hat.length_eq]
  rw [mergeSort_eq_of_perm hat, hf]
  have hnb : m'.numBonds = m.numBonds := hm.size
  refine kekulizeLoop_rel (N := m.bonds.size) (p := done) (p' := done') hwa
    (fun x ↦ hat.contains_eq) _ _ _ _ ⟨hm, rfl, rfl, fun k _ ↦ ?_, by simp [numBonds],
      by simp [numBonds, hm.size], rfl, rfl, rfl, rfl, rfl, hd, ⟨[], by simp, by simp, by simp⟩,
      by simp, by simp, by simp⟩
  simp only [hnb, getElem!_replicate_false]

namespace WalkRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work}

/-- The relation for `Q` gives it for any `Q'` that implies `Q`. -/
lemma mono (h : WalkRel Q π ρ m m') {Q' : ℕ → Prop} (hQ : ∀ k, Q' k → Q k) :
    WalkRel Q' π ρ m m' :=
  ⟨h.atoms, h.size, h.bij, h.ends, h.bb, h.nbrs, fun k hk hq ↦ h.kind k hk (hQ k hq)⟩

/-- With all kinds agreeing, the relation is a relisting. -/
lemma relisted (h : WalkRel (fun _ ↦ True) π ρ m m') : Relisted m m' π ρ :=
  ⟨h.atoms, h.size, h.bij, fun k hk ↦ h.kind k hk trivial, h.ends⟩

/-- Bond `π k` is at atom `i` in `m'` exactly when bond `k` is at `i` in `m`. -/
lemma mem_bondsOf (h : WalkRel Q π ρ m m') {k : ℕ} (hk : k < m.bonds.size) (i : ℕ) :
    π k ∈ m'.bondsOf i ↔ k ∈ m.bondsOf i := by
  simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, h.size, h.touches hk,
    h.bij.lt k hk, hk, true_and]

/-- A bond at an atom is a bond of the working copy. -/
lemma lt_of_mem_bondsOf' {x : Work} {k i : ℕ} (hk : k ∈ x.bondsOf i) : k < x.bonds.size := by
  simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1

/-- The bonds at an atom are the same bonds, renumbered. -/
lemma bondsOf_perm (h : WalkRel Q π ρ m m') (i : ℕ) :
    (m'.bondsOf i).Perm ((m.bondsOf i).map π) := by
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
    ((List.nodup_range.filter _).map_on fun a ha b hb e ↦
      h.bij.inj (lt_of_mem_bondsOf' ha) (lt_of_mem_bondsOf' hb) e)).2 fun k' ↦ ?_
  rw [List.mem_map]
  constructor
  · intro hk'
    have hk's : k' < m.bonds.size := h.size ▸ lt_of_mem_bondsOf' hk'
    refine ⟨ρ k', ?_, h.bij.right k' hk's⟩
    rw [← h.mem_bondsOf (h.bij.lt' k' hk's), h.bij.right k' hk's]
    exact hk'
  · rintro ⟨k, hk, rfl⟩
    exact (h.mem_bondsOf (lt_of_mem_bondsOf' hk) i).2 hk

/-- Related copies give every atom the same `degree`. -/
lemma degree (h : WalkRel Q π ρ m m') (i : ℕ) : m'.degree i = m.degree i := by
  unfold Work.degree
  rw [(h.bondsOf_perm i).length_eq, List.length_map]

end WalkRel

/-- Folding the addition of `g k` over `l` into an integer adds the natural-number sum of `g`
over `l`. -/
lemma foldl_int_add (g : ℕ → ℕ) : ∀ (l : List ℕ) (init : Int),
    l.foldl (fun r k ↦ r + (g k : Int)) init = init + ((l.map g).sum : ℕ)
  | [], init => by simp
  | k :: l, init => by
    rw [List.foldl_cons, foldl_int_add g l, List.map_cons, List.sum_cons, Nat.cast_add, add_assoc]

/-- `needsDoubleBond` reads the bonds at the atom only through a sum. -/
lemma needsDoubleBond_of_sum {m m' : Work} {wa wa' : ℕ → Bool} {e i : ℕ}
    (ha : m'.atoms = m.atoms) (hd : m'.degree i = m.degree i)
    (hs : ((m'.bondsOf i).map fun k ↦
        (if wa' k = true then 1 else (halfOrder (m'.bonds[k]! : WBond).kind + 1) / 2 : ℕ)).Perm
      ((m.bondsOf i).map fun k ↦
        (if wa k = true then 1 else (halfOrder (m.bonds[k]! : WBond).kind + 1) / 2 : ℕ))) :
    m'.needsDoubleBond wa' e i = m.needsDoubleBond wa e i := by
  unfold needsDoubleBond
  simp only [Id.run, pure_bind, List.forIn_pure_yield_eq_foldl, foldl_int_add]
  rw [hs.sum_eq, ha, hd]

/-- On related copies whose kinds agree on the bonds not written aromatic. -/
lemma WalkRel.needsDoubleBond {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work}
    (h : WalkRel Q π ρ m m') {wa wa' : ℕ → Bool} (hwa : ∀ k < m.bonds.size, wa' (π k) = wa k)
    (hQ : ∀ k < m.bonds.size, wa k = false → Q k) (e i : ℕ) :
    m'.needsDoubleBond wa' e i = m.needsDoubleBond wa e i := by
  refine needsDoubleBond_of_sum h.atoms (h.degree i) (((h.bondsOf_perm i).map _).trans ?_)
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun k hk ↦ ?_)
  have hk' := WalkRel.lt_of_mem_bondsOf' hk
  simp only [Function.comp_apply, hwa k hk']
  split
  · rfl
  · rename_i hw
    rw [h.kind k hk' (hQ k hk' (by simpa using hw))]

/-! ### One fused system -/

/-- `kekulizeSystem` once the system's atoms are listed. -/
def kekSys (wa : ℕ → Bool) (ev0 : List ℕ) (out : Work) (atoms : List ℕ) : Except String Work :=
  if !atoms.any (out.atoms[·]!.aromatic) then pure out else
  let cands := atoms.foldl (init := Array.replicate out.numAtoms false) fun c i ↦
    if out.atoms[i]!.aromatic && out.needsDoubleBond wa ev0[i]! i then c.set! i true
    else c
  let done := atoms.filter (!out.atoms[·]!.aromatic)
  match (atoms.foldl (singleAromaticBonds wa) out).kekulizeWorker wa atoms cands done with
  | some m' => pure m'
  | none => throw "Can't kekulize mol"

/-- `kekulizeSystem` is `kekSys` on the system's atoms without repeats. -/
lemma kekulizeSystem_eq (wa : ℕ → Bool) (ev0 : List ℕ) (rings : Array (List ℕ)) (out : Work)
    (system : List ℕ) :
    kekulizeSystem wa ev0 rings out system =
      kekSys wa ev0 out ((system.flatMap (rings[·]!)).eraseDups) := rfl

/-- Two results alike: both fail with the same message, or both succeed, related. -/
def ExRel {α β : Type} (R : α → β → Prop) : Except String α → Except String β → Prop
  | .ok a, .ok b => R a b
  | .error e, .error e' => e = e'
  | _, _ => False

/-- The bonds `kekSys` makes single before the walk: written aromatic, at an aromatic atom of
the system. -/
abbrev SabSet (wa : ℕ → Bool) (out : Work) (atoms : List ℕ) (k : ℕ) : Prop :=
  ∃ x ∈ atoms, (out.atoms[x]! : WAtom).aromatic = true ∧ k ∈ out.bondsOf x ∧ wa k = true

/-- **One fused system, in step**: on related copies, the system's atoms in any order, with the
same candidates, both fail alike or both succeed on copies related where the kinds agreed or the
system rewrote them. -/
theorem kekSys_rel {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {out out' : Work}
    (h : WalkRel Q π ρ out out') {wa wa' : ℕ → Bool} (hwa : ∀ k < out.bonds.size, wa' (π k) = wa k)
    {ev0 ev0' : List ℕ} {atoms atoms' : List ℕ} (hat : atoms'.Perm atoms)
    (hc : ∀ x ∈ atoms, (out.atoms[x]! : WAtom).aromatic = true →
      out'.needsDoubleBond wa' ev0'[x]! x = out.needsDoubleBond wa ev0[x]! x) :
    ExRel (WalkRel (fun k ↦ Q k ∨ SabSet wa out atoms k) π ρ)
      (kekSys wa ev0 out atoms) (kekSys wa' ev0' out' atoms') := by
  unfold kekSys
  have hany : (atoms'.any fun x ↦ (out'.atoms[x]! : WAtom).aromatic) =
      atoms.any fun x ↦ (out.atoms[x]! : WAtom).aromatic := by
    rw [h.atoms]; exact hat.any_eq
  rw [hany]
  split
  · rename_i hna
    refine h.mono fun k hk ↦ hk.resolve_right ?_
    rintro ⟨x, hx, hxa, -⟩
    simp only [Bool.not_eq_true', List.any_eq_false] at hna
    exact absurd hxa (by simpa using hna x hx)
  · -- the candidates
    have hcands : (atoms'.foldl (init := Array.replicate out'.numAtoms false) fun c i ↦
        if (out'.atoms[i]! : WAtom).aromatic && out'.needsDoubleBond wa' ev0'[i]! i then
          c.set! i true else c) =
        (atoms.foldl (init := Array.replicate out.numAtoms false) fun c i ↦
          if (out.atoms[i]! : WAtom).aromatic && out.needsDoubleBond wa ev0[i]! i then
            c.set! i true else c) := by
      have hn : out'.numAtoms = out.numAtoms := by simp [numAtoms, h.atoms]
      have f1 := foldl_cands (fun i ↦ (out'.atoms[i]! : WAtom).aromatic &&
        out'.needsDoubleBond wa' ev0'[i]! i) atoms' (Array.replicate out'.numAtoms false)
      have f2 := foldl_cands (fun i ↦ (out.atoms[i]! : WAtom).aromatic &&
        out.needsDoubleBond wa ev0[i]! i) atoms (Array.replicate out.numAtoms false)
      refine array_ext_of_getElem! (n := out.numAtoms) (by rw [f1.1]; simp [hn])
        (by rw [f2.1]; simp) fun x _ ↦ ?_
      rw [Bool.eq_iff_iff, f1.2, f2.2, hat.mem_iff, hn]
      simp only [getElem!_replicate_false, Bool.false_eq_true, false_or, Array.size_replicate]
      apply and_congr_right
      intro hx
      apply and_congr_left
      intro _
      rw [h.atoms]
      cases hxa : (out.atoms[x]! : WAtom).aromatic
      · simp
      · simp only [Bool.true_and]
        rw [← h.atoms] at hxa
        rw [hc x hx (by rw [← hxa, h.atoms])]
    have hdone : (atoms'.filter fun x ↦ !(out'.atoms[x]! : WAtom).aromatic).Perm
        (atoms.filter fun x ↦ !(out.atoms[x]! : WAtom).aromatic) := by
      rw [h.atoms]; exact hat.filter _
    -- making the aromatic bonds single
    obtain ⟨sk, sa, skind⟩ := foldl_singleAromaticBonds_kind wa atoms out
    obtain ⟨sk', sa', skind'⟩ := foldl_singleAromaticBonds_kind wa' atoms' out'
    have hS : ∀ k < out.bonds.size, ((∃ x ∈ atoms', (out'.atoms[x]! : WAtom).aromatic = true ∧
        π k ∈ out'.bondsOf x ∧ wa' (π k) = true) ↔ SabSet wa out atoms k) := by
      intro k hk
      simp only [SabSet, hat.mem_iff, h.atoms, h.mem_bondsOf hk, hwa k hk]
    have hm0 : WalkRel (fun k ↦ Q k ∨ SabSet wa out atoms k) π ρ
        (atoms.foldl (singleAromaticBonds wa) out) (atoms'.foldl (singleAromaticBonds wa') out') :=
      h.of_skel sk sk' (by rw [sa', sa, h.atoms]) fun k hk hq ↦ by
        rw [skind, skind']
        by_cases hs : SabSet wa out atoms k
        · rw [if_pos hs, if_pos ((hS k hk).2 hs)]
        · rw [if_neg hs, if_neg (fun e ↦ hs ((hS k hk).1 e))]
          exact h.kind k hk (hq.resolve_right hs)
    have hwa0 : ∀ k < (atoms.foldl (singleAromaticBonds wa) out).bonds.size, wa' (π k) = wa k :=
      fun k hk ↦ hwa k (by have e := sk.numBonds; simp only [numBonds] at e; omega)
    have hw := kekulizeWorker_rel hm0 hwa0 hat
      (atoms.foldl (init := Array.replicate out.numAtoms false) fun c i ↦
        if (out.atoms[i]! : WAtom).aromatic && out.needsDoubleBond wa ev0[i]! i then
          c.set! i true else c) hdone
    dsimp only
    rw [hcands]
    revert hw
    rcases (atoms.foldl (singleAromaticBonds wa) out).kekulizeWorker wa atoms _ _ with _ | r <;>
      rcases (atoms'.foldl (singleAromaticBonds wa') out').kekulizeWorker wa' atoms' _ _ with
        _ | r' <;> intro hw
    · rfl
    · cases hw
    · cases hw
    · cases hw; assumption


/-! ### Results alike -/

/-- Binding results alike by functions that take related values to results alike gives results
alike. -/
lemma ExRel.bind {α β γ δ : Type} {R : α → β → Prop} {S : γ → δ → Prop} {x : Except String α}
    {x' : Except String β} (h : ExRel R x x') {f : α → Except String γ}
    {f' : β → Except String δ} (hf : ∀ a a', R a a' → ExRel S (f a) (f' a')) :
    ExRel S (x.bind f) (x'.bind f') := by
  rcases x with e | a <;> rcases x' with e' | a'
  · exact h
  · exact h.elim
  · exact h.elim
  · exact hf a a' h

/-- `ExRel R` gives `ExRel S` if `R` implies `S` on the values the two results succeed with. -/
lemma ExRel.imp {α β : Type} {R S : α → β → Prop} {x : Except String α} {x' : Except String β}
    (h : ExRel R x x') (hRS : ∀ a a', x = .ok a → x' = .ok a' → R a a' → S a a') :
    ExRel S x x' := by
  rcases x with e | a <;> rcases x' with e' | a'
  · exact h
  · exact h.elim
  · exact h.elim
  · exact hRS a a' rfl rfl h

/-- Two `foldlM`s over the same list, from related starts, with steps taking related values to
results alike, give results alike. -/
lemma ExRel.foldlM {α β γ : Type} {R : α → β → Prop} {f : α → γ → Except String α}
    {f' : β → γ → Except String β} (hf : ∀ a a' c, R a a' → ExRel R (f a c) (f' a' c)) :
    ∀ (l : List γ) (a : α) (a' : β), R a a' → ExRel R (l.foldlM f a) (l.foldlM f' a')
  | [], _, _, h => h
  | c :: l, a, a', h => by
    rw [List.foldlM_cons, List.foldlM_cons]
    exact ExRel.bind (hf a a' c h) fun b b' hb ↦ ExRel.foldlM hf l b b' hb

/-! ### Kekulization of a relisted copy, the same rings -/

/-- `kekulize` unfolded, with `kekWa`, `kekEv0` and `kekFusedNbrs` named. -/
lemma kekulize_eq (m : Work) (rings : Array (List ℕ)) :
    m.kekulize rings =
      if ((List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)).isEmpty &&
          !m.atoms.any (·.aromatic) then .ok m
      else ((components rings.size (m.kekFusedNbrs rings)).foldlM
          (kekulizeSystem m.kekWa m.kekEv0 rings) m).bind fun out ↦
        ((List.range out.numAtoms).foldlM (clearAromatic rings.toList.flatten.eraseDups)
          out).bind fun out ↦ if out.bonds.any (·.kind == .aromatic) then
            .error "aromatic bond left after kekulization" else .ok out := rfl

namespace WalkRel

variable {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work}

/-- Editing the same atom alike on both sides keeps the relation. -/
lemma modifyAtom (h : WalkRel Q π ρ m m') (i : ℕ) (f : WAtom → WAtom) :
    WalkRel Q π ρ (m.modifyAtom i f) (m'.modifyAtom i f) :=
  h.of_skel (skel_modifyAtom _ _ _) (skel_modifyAtom _ _ _)
    (by simp only [Work.modifyAtom, h.atoms]) fun k hk hq ↦ h.kind k hk hq

/-- With all kinds agreeing, `m'` has a bond of kind aromatic exactly when `m` has. -/
lemma exists_arom (h : WalkRel (fun _ ↦ True) π ρ m m') :
    (∃ k < m'.bonds.size, (m'.bonds[k]! : WBond).kind = .aromatic) ↔
      ∃ k < m.bonds.size, (m.bonds[k]! : WBond).kind = .aromatic := by
  constructor
  · rintro ⟨k', hk', e⟩
    have hk's : k' < m.bonds.size := h.size ▸ hk'
    refine ⟨ρ k', h.bij.lt' k' hk's, ?_⟩
    have := h.kind (ρ k') (h.bij.lt' k' hk's) trivial
    rw [h.bij.right k' hk's] at this
    rw [← this, e]
  · rintro ⟨k, hk, e⟩
    exact ⟨π k, h.size ▸ h.bij.lt k hk, by rw [h.kind k hk trivial, e]⟩

end WalkRel

/-- Some bond is of kind aromatic, as `Array.any` or as an index below the number of bonds. -/
lemma bonds_any_arom (m : Work) :
    m.bonds.any (·.kind == .aromatic) = true ↔
      ∃ k < m.bonds.size, (m.bonds[k]! : WBond).kind = .aromatic := by
  rw [Array.any_eq_true]
  constructor
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, by rw [getElem!_pos m.bonds k hk]; simpa using e⟩
  · rintro ⟨k, hk, e⟩
    exact ⟨k, hk, by rw [getElem!_pos m.bonds k hk] at e; simp [e]⟩

/-- The list of aromatic bond numbers is empty exactly when no bond is of kind aromatic. -/
lemma filter_arom_isEmpty (m : Work) :
    ((List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)).isEmpty =
      !(m.bonds.any (·.kind == .aromatic)) := by
  rw [Bool.eq_iff_iff, Bool.not_eq_true', ← Bool.not_eq_true, bonds_any_arom, List.isEmpty_iff,
    List.filter_eq_nil_iff]
  simp [numBonds]

/-- Mapping both lists by `π`, injective below `N`, keeps whether they share an element. -/
lemma any_contains_map {π : ℕ → ℕ} {N : ℕ} (hinj : ∀ i < N, ∀ j < N, π i = π j → i = j)
    {A B : List ℕ} (hA : ∀ x ∈ A, x < N) (hB : ∀ x ∈ B, x < N) :
    (A.map π).any (B.map π).contains = A.any B.contains := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_map, List.contains_iff_mem]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, e⟩
    exact ⟨a, ha, by rwa [← hinj b (hB b hb) a (hA a ha) e]⟩
  · rintro ⟨a, ha, hb⟩
    exact ⟨π a, ⟨a, ha, rfl⟩, a, hb, rfl⟩

/-- The bonds of a ring of `m'` are its bonds in `m`, renumbered by `π`. -/
lemma WalkRel.ringBonds {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work} (h : WalkRel Q π ρ m m') :
    m'.ringBonds = fun r ↦ (m.ringBonds r).map π := by
  funext r
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.map_filterMap]
  simp only [h.bb]

/-- Related copies give the same `kekFusedNbrs`. -/
lemma WalkRel.kekFusedNbrs {Q : ℕ → Prop} {π ρ : ℕ → ℕ} {m m' : Work} (h : WalkRel Q π ρ m m')
    (rings : Array (List ℕ)) : m'.kekFusedNbrs rings = m.kekFusedNbrs rings := by
  have hget : ∀ t : ℕ, ((rings.map m'.ringBonds)[t]! : List ℕ) =
      ((rings.map m.ringBonds)[t]! : List ℕ).map π := by
    intro t
    by_cases ht : t < rings.size
    · rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ t (by simpa using ht)]
      simp [h.ringBonds]
    · rw [getElem!_neg _ t (by simpa using ht), getElem!_neg _ t (by simpa using ht)]
      rfl
  have hlt : ∀ t : ℕ, ∀ x ∈ ((rings.map m.ringBonds)[t]! : List ℕ), x < m.bonds.size := by
    intro t x hx
    by_cases ht : t < rings.size
    · rw [getElem!_pos _ t (by simpa using ht)] at hx
      simp only [Array.getElem_map] at hx
      exact lt_of_mem_ringBonds hx
    · rw [getElem!_neg _ t (by simpa using ht)] at hx
      cases hx
  unfold Work.kekFusedNbrs
  dsimp only
  congr 1
  funext i
  congr 1
  funext j
  rw [hget i, hget j, any_contains_map (fun a ha b hb e ↦ h.bij.inj ha hb e) (hlt i) (hlt j)]

/-- Caching each side's own implicit H count at atom `i` keeps the relation. -/
lemma modify2 {π ρ : ℕ → ℕ} {X X' : Work} (hX : WalkRel (fun _ ↦ True) π ρ X X') (i : ℕ) :
    WalkRel (fun _ ↦ True) π ρ (X.modifyAtom i ({ · with cachedImplicit := X.implicitHs i }))
      (X'.modifyAtom i ({ · with cachedImplicit := X'.implicitHs i })) := by
  rw [hX.relisted.implicitHs]
  exact hX.modifyAtom _ _

/-- `clearAromatic` at the same atom on related copies fails alike or succeeds on related
copies. -/
lemma WalkRel.clearAromatic {π ρ : ℕ → ℕ} {out out' : Work}
    (h : WalkRel (fun _ ↦ True) π ρ out out') (ra : List ℕ) (i : ℕ) :
    ExRel (WalkRel (fun _ ↦ True) π ρ) (clearAromatic ra out i) (clearAromatic ra out' i) := by
  have hR := h.relisted
  unfold Work.clearAromatic
  have ha : (out'.atoms[i]! : WAtom) = out.atoms[i]! := by rw [h.atoms]
  have hev : (out'.bondsOf i).foldl (fun s k ↦ s + halfOrder (out'.bonds[k]! : WBond).kind) 0 =
      (out.bondsOf i).foldl (fun s k ↦ s + halfOrder (out.bonds[k]! : WBond).kind) 0 := by
    rw [foldl_halfOrder, foldl_halfOrder]
    congr 1
    refine (((h.bondsOf_perm i).map _).trans ?_).sum_eq
    rw [List.map_map]
    exact List.Perm.of_eq (List.map_congr_left fun k hk ↦ by
      simp only [Function.comp_apply, h.kind k (WalkRel.lt_of_mem_bondsOf' hk) trivial])
  simp only [ha, hev]
  split_ifs
  · exact h
  · rfl
  · exact modify2 (h.modifyAtom i _) i
  · exact h.modifyAtom _ _

/-- **Kekulization of a relisted copy, over the same rings**: both fail alike, or both succeed
on relisted copies. -/
theorem kekulize_walkRel {m m' : Work} {π ρ : ℕ → ℕ} (h : WalkRel (fun _ ↦ True) π ρ m m')
    (hwf : WF m) (hnd : m.NbrsDistinct) (rings : Array (List ℕ)) :
    ExRel (WalkRel (fun _ ↦ True) π ρ) (m.kekulize rings) (m'.kekulize rings) := by
  have hR := h.relisted
  have hwa : ∀ k < m.bonds.size, m'.kekWa (π k) = m.kekWa k := fun k hk ↦ by
    rw [Bool.eq_iff_iff, kekWa_iff, kekWa_iff, h.kind k hk trivial, h.size]
    simp [hk, h.bij.lt k hk]
  have hev : m'.kekEv0 = m.kekEv0 := by
    simp only [kekEv0, numAtoms, h.atoms]
    congr 1
    funext i
    exact hR.explicitValence i
  rw [kekulize_eq, kekulize_eq, h.kekFusedNbrs, filter_arom_isEmpty, filter_arom_isEmpty]
  have hc : m'.bonds.any (·.kind == .aromatic) = m.bonds.any (·.kind == .aromatic) := by
    rw [Bool.eq_iff_iff, bonds_any_arom, bonds_any_arom, h.exists_arom]
  rw [hc, h.atoms]
  split
  · exact h
  · refine ExRel.bind (R := fun out out' ↦ WalkRel (fun _ ↦ True) π ρ out out' ∧ SameSkel m out)
      (ExRel.foldlM (fun out out' C hr ↦ ?_) _ m m' ⟨h, SameSkel.refl m⟩) fun out out' hr ↦ ?_
    · rw [kekulizeSystem_eq, kekulizeSystem_eq]
      have hsz : out.bonds.size = m.bonds.size := hr.2.numBonds.symm
      have hk := kekSys_rel hr.1 (wa := m.kekWa) (wa' := m'.kekWa) (fun k hk ↦ hwa k (hsz ▸ hk))
        (ev0 := m.kekEv0) (ev0' := m'.kekEv0) (List.Perm.refl
          ((C.flatMap (rings[·]!)).eraseDups)) fun x _ _ ↦ by
          rw [hev]
          exact hr.1.needsDoubleBond (fun k hk ↦ hwa k (hsz ▸ hk)) (fun _ _ _ ↦ trivial) _ x
      refine hk.imp fun a a' ha _ hrel ↦ ⟨hrel.mono fun _ _ ↦ .inl trivial, ?_⟩
      have := kekulizeSystem_correct (hr.2.wf hwf) (hr.2.nbrsDistinct hnd)
        (by rw [kekulizeSystem_eq]; exact ha)
      exact hr.2.trans this.2.1
    · have hna : out'.numAtoms = out.numAtoms := by simp [numAtoms, hr.1.atoms]
      rw [hna]
      refine ExRel.bind (ExRel.foldlM (fun o o' i ho ↦ ho.clearAromatic _ i) _ _ _ hr.1)
        fun o o' ho ↦ ?_
      have hc' : o'.bonds.any (·.kind == .aromatic) = o.bonds.any (·.kind == .aromatic) := by
        rw [Bool.eq_iff_iff, bonds_any_arom, bonds_any_arom, ho.exists_arom]
      rw [hc']
      split
      · rfl
      · exact ho

end LeanSMILES.Aromaticity.Work
