/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.HsLocal

/-!
# LeanSMILES.Aromaticity.HsDecide

**`adjustHs` gives back the cached hydrogens at every atom of a kekulized copy**, checked atom by
atom: over every element and charge an atom without brackets can have after `cleanUp`, every list
of at most three bond kinds before kekulization, every way kekulization can make them single and
double, and every set of them perception can make aromatic again (`Loc.bare_ok`, `Loc.branch_ok`,
by `decide`).  An atom that perception makes aromatic passes its candidate test; an atom written
lowercase has at least two aromatic bonds.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Loc

/-- The five bond kinds. -/
def kinds5 : List BondKind := [.single, .double, .triple, .quadruple, .aromatic]

/-- Every list of at most `n` bond kinds. -/
def lists : ℕ → List (List BondKind)
  | 0 => [[]]
  | n + 1 => [] :: (lists n).flatMap fun l ↦ kinds5.map (· :: l)

/-- Every kekulized form of the kinds `pk`: each aromatic kind single or double, with exactly one
double among them if `need`, none otherwise; the other kinds kept. -/
def kekAll : Bool → List BondKind → List (List BondKind)
  | need, [] => if need then [] else [[]]
  | need, p :: ps =>
    if p == .aromatic then
      (kekAll need ps).map (.single :: ·) ++
        (if need then (kekAll false ps).map (.double :: ·) else [])
    else (kekAll need ps).map (p :: ·)

/-- Every way perception can make some single or double bonds of kinds `kk` aromatic. -/
def marks : List BondKind → List (List BondKind)
  | [] => [[]]
  | k :: ks =>
    let r := marks ks
    (r.map (k :: ·)) ++ (if k == .single || k == .double then r.map (.aromatic :: ·) else [])

/-- The elements and charges an atom written without brackets, of an element perception may make
aromatic, can have after `cleanUp`. -/
def bareZC : List (ℕ × ℤ) :=
  (([5, 6, 7, 8, 15, 16] : List ℕ).flatMap fun z ↦ [(z, 0), (z, 1)]) ++ [(7, -1), (8, -1)]

/-- The record of a bare atom of element `z`, charge `ch`, lowercase or not, with bonds of kinds
`pk`, as `prepare` caches it. -/
def bareP (z : ℕ) (ch : ℤ) (flag : Bool) (pk : List BondKind) : WAtom :=
  let a0 : WAtom :=
    { z := z, aromatic := flag, charge := ch, explicitHs := 0, noImplicit := false }
  { a0 with cachedImplicit := impl a0 (bhs pk) flag, cachedValence := some (ev a0 (bhs pk) flag),
            adjustHs := flag }

/-- The check at a bare atom of element `z`, charge `ch`, written lowercase or not (`flag`), with
bonds of kinds `pk` before kekulization. -/
def bareCheck (z : ℕ) (ch : ℤ) (flag : Bool) (pk : List BondKind) : Bool :=
  let narom := (pk.filter (· == .aromatic)).length
  if flag && (narom < 2 || 3 < pk.length || !([5, 6, 7, 8, 15, 16] : List ℕ).contains z) then
    true
  else if !flag && 0 < narom then true
  else
    let aP := bareP z ch flag pk
    let need := flag && ndb aP pk (aP.cachedValence.getD 0)
    let aK : WAtom := { aP with aromatic := false }
    (kekAll need pk).all fun kk ↦ (marks kk).all fun sk ↦
      let aromS := sk.any (· == .aromatic)
      if aromS && (sk.length < 2 || elec aK kk < 0 || !cand aK kk) then true
      else restore aK sk aromS

/-- The record of an `[nH]`/`[pH]` with bonds of kinds `pk`, as `prepare` caches it. -/
def branchP (z : ℕ) (pk : List BondKind) : WAtom :=
  let a0 : WAtom :=
    { z := z, aromatic := true, charge := 0, explicitHs := 1, noImplicit := true }
  { a0 with cachedImplicit := 0, cachedValence := some (ev a0 (bhs pk) true), adjustHs := true }

/-- The record kekulization rewrites an `[nH]`/`[pH]` into, its bonds of kinds `kk`. -/
def branchK (z : ℕ) (pk kk : List BondKind) : WAtom :=
  let aK0 : WAtom :=
    { branchP z pk with aromatic := false, noImplicit := false, explicitHs := 0 }
  { aK0 with cachedValence := some (bhs kk / 2), cachedImplicit := impl aK0 (bhs kk) false }

/-- The check at the `[nH]`/`[pH]` atom that kekulization rewrites into a bare one. -/
def branchCheck (z : ℕ) (pk : List BondKind) : Bool :=
  let narom := (pk.filter (· == .aromatic)).length
  if narom < 2 || 3 < pk.length then true else
  let aP := branchP z pk
  let need := ndb aP pk (aP.cachedValence.getD 0)
  (kekAll need pk).all fun kk ↦
    let aK := branchK z pk kk
    (marks kk).all fun sk ↦
      let aromS := sk.any (· == .aromatic)
      if aromS && (sk.length < 2 || elec aK kk < 0 || !cand aK kk) then true
      else restore aK sk aromS

theorem bare_ok :
    (bareZC.all fun (z, ch) ↦
      (lists 3).all (bareCheck z ch true) && (lists 3).all (bareCheck z ch false)) = true := by
  decide +kernel

theorem branch_ok : (([7, 15] : List ℕ).all fun z ↦ (lists 3).all (branchCheck z)) = true := by
  decide +kernel

/-! ### The enumerations contain the real cases -/

lemma mem_kinds5 (k : BondKind) : k ∈ kinds5 := by cases k <;> simp [kinds5]

lemma mem_lists : ∀ (n : ℕ) (l : List BondKind), l.length ≤ n → l ∈ lists n
  | 0, [], _ => by simp [lists]
  | 0, _ :: _, h => by simp at h
  | n + 1, [], _ => by simp [lists]
  | n + 1, k :: l, h => by
    simp only [lists, List.mem_cons, List.mem_flatMap, List.mem_map]
    exact .inr ⟨l, mem_lists n l (by simpa using h), k, mem_kinds5 k, rfl⟩

/-- How kekulization relates a kind before to a kind after. -/
def KekRel (p k : BondKind) : Prop := if p = .aromatic then k = .single ∨ k = .double else k = p

lemma mem_kekAll : ∀ (pk kk : List BondKind), List.Forall₂ KekRel pk kk → ∀ need : Bool,
    ((pk.zip kk).filter (fun pq ↦ pq.1 == .aromatic && pq.2 == .double)).length =
      (if need then 1 else 0) → kk ∈ kekAll need pk
  | [], [], .nil, need, h => by cases need <;> simp_all [kekAll]
  | p :: ps, k :: ks, .cons hpk hr, need, h => by
    unfold kekAll
    unfold KekRel at hpk
    by_cases hp : p = .aromatic
    · subst hp
      rw [if_pos rfl] at hpk
      simp only [beq_self_eq_true, if_true, List.mem_append, List.mem_map]
      rcases hpk with rfl | rfl
      · left
        refine ⟨ks, mem_kekAll ps ks hr need ?_, rfl⟩
        simpa [List.zip_cons_cons, List.filter_cons] using h
      · cases need
        · simp [List.zip_cons_cons] at h
        · right
          simp only [if_true, List.mem_map]
          refine ⟨ks, mem_kekAll ps ks hr false ?_, rfl⟩
          simpa [List.zip_cons_cons, List.filter_cons] using h
    · rw [if_neg hp] at hpk
      subst hpk
      have hp' : (k == BondKind.aromatic) = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, if_false, List.mem_map]
      refine ⟨ks, mem_kekAll ps ks hr need ?_, rfl⟩
      simpa [List.zip_cons_cons, List.filter_cons, hp'] using h

/-- How perception relates a kind before marking to the kind after. -/
def MarkRel (k s : BondKind) : Prop := s = k ∨ (s = .aromatic ∧ (k = .single ∨ k = .double))

lemma mem_marks : ∀ (kk sk : List BondKind), List.Forall₂ MarkRel kk sk → sk ∈ marks kk
  | [], [], .nil => by simp [marks]
  | k :: ks, s :: ss, .cons hks hr => by
    unfold marks
    simp only [List.mem_append, List.mem_map]
    rcases hks with rfl | ⟨rfl, hk⟩
    · exact .inl ⟨ss, mem_marks ks ss hr, rfl⟩
    · right
      have := mem_marks ks ss hr
      rcases hk with rfl | rfl <;> simpa using this

/-! ### The checks, as statements -/

/-- **`adjustHs` restores the hydrogens of a bare atom.** -/
theorem bare_restore {z : ℕ} {ch : ℤ} {flag : Bool} {pk kk sk : List BondKind}
    (hzc : (z, ch) ∈ bareZC) (hpk : pk ∈ lists 3)
    (hflag : flag = true → 2 ≤ (pk.filter (· == .aromatic)).length ∧ pk.length ≤ 3 ∧
      z ∈ ([5, 6, 7, 8, 15, 16] : List ℕ))
    (hnf : flag = false → (pk.filter (· == .aromatic)).length = 0)
    (hkk : kk ∈ kekAll (flag && ndb (bareP z ch flag pk) pk
      ((bareP z ch flag pk).cachedValence.getD 0)) pk)
    (hsk : sk ∈ marks kk)
    (hperc : sk.any (· == .aromatic) = true → 2 ≤ sk.length ∧
      0 ≤ elec { bareP z ch flag pk with aromatic := false } kk ∧
      cand { bareP z ch flag pk with aromatic := false } kk = true) :
    restore { bareP z ch flag pk with aromatic := false } sk (sk.any (· == .aromatic)) = true := by
  have h := bare_ok
  rw [List.all_eq_true] at h
  have h2 := h _ hzc
  simp only [Bool.and_eq_true, List.all_eq_true] at h2
  have hc : bareCheck z ch flag pk = true := by
    cases flag
    · exact h2.2 pk hpk
    · exact h2.1 pk hpk
  unfold bareCheck at hc
  have hs1 : (flag && (decide ((pk.filter (· == .aromatic)).length < 2) ||
      decide (3 < pk.length) || !([5, 6, 7, 8, 15, 16] : List ℕ).contains z)) = false := by
    cases flag
    · rfl
    · obtain ⟨a, b, c⟩ := hflag rfl
      simp [c]
      omega
  have hs2 : (!flag && decide (0 < (pk.filter (· == .aromatic)).length)) = false := by
    cases flag
    · simp [hnf rfl]
    · rfl
  simp only [hs1, hs2, Bool.false_eq_true, if_false, List.all_eq_true] at hc
  have := hc kk hkk sk hsk
  have hfalse : (sk.any (· == .aromatic) && (decide (sk.length < 2) ||
      decide (elec { bareP z ch flag pk with aromatic := false } kk < 0) ||
      !cand { bareP z ch flag pk with aromatic := false } kk)) = false := by
    cases hs : sk.any (· == .aromatic)
    · rfl
    · obtain ⟨h1, h2, h3⟩ := hperc hs
      simp only [h3, Bool.not_true, Bool.or_false, Bool.true_and, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      dsimp only at h2 ⊢
      omega
  simp only [hfalse, Bool.false_eq_true, if_false] at this
  exact this

/-- **`adjustHs` restores the hydrogens of the `[nH]`/`[pH]` kekulization rewrites.** -/
theorem branch_restore {z : ℕ} {pk kk sk : List BondKind} (hz : z = 7 ∨ z = 15)
    (hpk : pk ∈ lists 3) (h2 : 2 ≤ (pk.filter (· == .aromatic)).length) (h3 : pk.length ≤ 3)
    (hkk : kk ∈ kekAll (ndb (branchP z pk) pk ((branchP z pk).cachedValence.getD 0)) pk)
    (hsk : sk ∈ marks kk)
    (hperc : sk.any (· == .aromatic) = true → 2 ≤ sk.length ∧ 0 ≤ elec (branchK z pk kk) kk ∧
      cand (branchK z pk kk) kk = true) :
    restore (branchK z pk kk) sk (sk.any (· == .aromatic)) = true := by
  have h := branch_ok
  rw [List.all_eq_true] at h
  have hc : branchCheck z pk = true := by
    have := h z (by rcases hz with rfl | rfl <;> simp)
    rw [List.all_eq_true] at this
    exact this pk hpk
  unfold branchCheck at hc
  have hs : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length)) =
      false := by
    simp; omega
  simp only [hs, Bool.false_eq_true, if_false, List.all_eq_true] at hc
  have := hc kk hkk sk hsk
  have hfalse : (sk.any (· == .aromatic) && (decide (sk.length < 2) ||
      decide (elec (branchK z pk kk) kk < 0) || !cand (branchK z pk kk) kk)) = false := by
    cases hs : sk.any (· == .aromatic)
    · rfl
    · obtain ⟨h1, h2, h3⟩ := hperc hs
      simp only [h3, Bool.not_true, Bool.or_false, Bool.true_and, Bool.or_eq_false_iff,
        decide_eq_false_iff_not]
      omega
  simp only [hfalse, Bool.false_eq_true, if_false] at this
  exact this

end LeanSMILES.Aromaticity.Loc
