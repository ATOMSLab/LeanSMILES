/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.HsLocal
public import Mathlib.Tactic.Linarith

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

/-! ### Hydrogen totals of the witness -/

namespace LeanSMILES.Aromaticity.Loc

/-- `Work.radicalCount`, at an atom of element `z`, charge `ch` and Kekulé valence `kv`. -/
def radC (z : ℕ) (ch : ℤ) (kv : ℕ) : ℕ := Id.run do
  let no : ℤ := outerElectrons z
  let tv : ℤ := kv
  let base : ℤ := if z == 1 || z == 2 then 2 else 8
  let mut nr : ℤ := base - no - tv + ch
  if nr < 0 then
    nr := 0
    if 1 < (valences z).length then
      if let some v := ((valences z).map Int.ofNat).find? (fun v ↦ 0 ≤ v - tv + ch) then
        nr := v - tv + ch
  let nr2 := no - tv - ch
  if 0 ≤ nr2 then nr := min nr nr2
  return nr.toNat

/-- A donor type other than `none` is possible: what `Work.donorType` needs before it gives
anything but `none`. -/
def donorOk (a : WAtom) (kk : List BondKind) : Bool :=
  let ne := elec a kk
  0 ≤ ne && (2 ≤ ne || kk.any isMultiple ||
    (ne == 1 && (cv a kk != kk.length + a.explicitHs || a.charge == 1)))

/-- A bare atom kekulization leaves alone: its implicit hydrogens counted on the Kekulé bonds are
those counted before. -/
def bareKekCheck (z : ℕ) (ch : ℤ) (pk : List BondKind) : Bool :=
  let narom := (pk.filter (· == .aromatic)).length
  if narom < 2 || 3 < pk.length || !([5, 6, 7, 8, 15, 16] : List ℕ).contains z then true else
  let aP := bareP z ch true pk
  (kekAll (ndb aP pk (aP.cachedValence.getD 0)) pk).all fun kk ↦
    impl { aP with aromatic := false } (bhs kk) false == aP.cachedImplicit

theorem bareKek_ok :
    (bareZC.all fun (z, ch) ↦ (lists 3).all (bareKekCheck z ch)) = true := by
  decide +kernel

/-- The non-aromatic bonds of up to `n` kinds. -/
def nonArom : ℕ → List (List BondKind)
  | 0 => [[]]
  | n + 1 => [] :: (nonArom n).flatMap fun l ↦
      [BondKind.single, .double, .triple, .quadruple].map (· :: l)

/-- The organic-subset elements. -/
def organic : List Element := [.B, .C, .N, .O, .P, .S, .F, .Cl, .Br, .I]

/-- A bracketed atom written bare in the output, not aromatic: OpenSMILES's count at bond-order sum
`h / 2` is RDKit's on the Kekulé bonds. -/
def bareNonAromCheck (e : Element) (h : ℕ) : Bool :=
  let b : Atom := { element := some e, aromatic := false }
  let q : ℚ := (h : ℚ) / 2
  let w : WAtom :=
    { z := e.atomicNumber, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false }
  Molecule.readsDifferentlyInRDKit b q || impl w h false == Molecule.implicitHydrogens b q

theorem bareNonArom_ok :
    (organic.all fun e ↦ (List.range 9).all fun t ↦ bareNonAromCheck e (2 * t)) = true := by
  decide +kernel

/-- A bracketed atom written bare in the output, aromatic: OpenSMILES's count at the aromatic bonds
is RDKit's on the Kekulé bonds, when perception could make it aromatic. -/
def bareAromCheck (e : Element) (kk : List BondKind) : Bool :=
  let z := e.atomicNumber
  let h := bhs kk
  (marks kk).all fun sk ↦
    let b : Atom := { element := some e, aromatic := true }
    let q : ℚ := ((sk.map BondKind.order).sum)
    let T := Molecule.implicitHydrogens b q
    let aK : WAtom :=
      { z := z, aromatic := false, charge := 0, explicitHs := T, noImplicit := true,
        radicals := radC z 0 (h / 2 + T), cachedImplicit := 0, cachedValence := some (h / 2 + T) }
    let w0 : WAtom :=
      { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false }
    !sk.any (· == .aromatic) || sk.length < 2 ||
      (sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) ||
      Molecule.readsDifferentlyInRDKit b q || elec aK kk < 0 || !cand aK kk || !donorOk aK kk ||
      impl w0 h false == T

theorem bareArom_ok : (organic.all fun e ↦ (nonArom 3).all (bareAromCheck e)) = true := by
  decide +kernel

/-- The `[nH]`/`[pH]` kekulization rewrites has at most one implicit hydrogen. -/
def branchHCheck (z : ℕ) (pk : List BondKind) : Bool :=
  let narom := (pk.filter (· == .aromatic)).length
  if narom < 2 || 3 < pk.length then true else
  let aP := branchP z pk
  (kekAll (ndb aP pk (aP.cachedValence.getD 0)) pk).all fun kk ↦
    (branchK z pk kk).cachedImplicit ≤ 1

theorem branchH_ok : (([7, 15] : List ℕ).all fun z ↦ (lists 3).all (branchHCheck z)) = true := by
  decide +kernel

end LeanSMILES.Aromaticity.Loc

namespace LeanSMILES.Aromaticity.Loc

lemma defaultValences_le_six : ∀ e : Element, ∀ v ∈ e.defaultValences, v ≤ 6 := by decide

lemma elementTable_le_six : ∀ x ∈ elementTable, ∀ v ∈ x.2.1, v ≤ 6 := by decide

lemma valences_le_six (z : ℕ) : ∀ v ∈ valences z, v ≤ 6 := by
  intro v hv
  unfold valences at hv
  cases h : elementTable.find? (·.1 == z) with
  | none => simp [h] at hv
  | some x =>
    simp only [h, Option.map_some, Option.getD_some] at hv
    exact elementTable_le_six x (List.mem_of_find?_eq_some h) v hv

/-- At a bond-order sum above every valence, OpenSMILES gives a bare atom no hydrogen. -/
lemma implicitHydrogens_large (e : Element) {q : ℚ} (hq : 6 < q) :
    Molecule.implicitHydrogens { element := some e, aromatic := false } q = 0 := by
  unfold Molecule.implicitHydrogens
  simp only [Bool.false_and, Bool.false_eq_true, if_false]
  split
  · rename_i v hv
    exfalso
    have hp := List.find?_some hv
    have hmem := List.mem_of_find?_eq_some hv
    simp only [List.pure_def, List.bind_eq_flatMap, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hmem
    obtain ⟨a, ha, rfl⟩ := hmem
    have h6 : (a : ℚ) ≤ 6 := by exact_mod_cast defaultValences_le_six e a ha
    simp only [decide_eq_true_eq] at hp
    split at hp <;> linarith
  · rfl

/-- At a bond half-sum above every valence, RDKit gives a neutral atom no implicit hydrogen,
when it is not hypervalent. -/
lemma impl_large {a : WAtom} {h : ℕ} (hc : a.charge = 0)
    (hz : a.z ≤ 16 ∨ a.z = 17 ∨ a.z = 35 ∨ a.z = 53) (he : a.explicitHs = 0) (hh : 13 < h) :
    impl a h false = 0 := by
  have hev : ev a h false = (h + 1) / 2 := by
    simp [ev, he]
    split <;> rfl
  have hhv : Work.canBeHypervalent a (Work.effectiveZ a) = false := by
    simp only [Work.canBeHypervalent, Work.effectiveZ, hc, sub_zero, Int.toNat_natCast]
    rcases hz with hz | hz | hz | hz
    · simp [hz]; omega
    all_goals simp [hz]
  have hfind : ((valences (Work.effectiveZ a)).map Int.ofNat).find?
      (fun v ↦ decide ((((h + 1) / 2 : ℕ) : ℤ) ≤ v)) = none := by
    rw [List.find?_eq_none]
    intro v hv
    obtain ⟨v', hv', rfl⟩ := List.mem_map.1 hv
    have := valences_le_six _ v' hv'
    simp only [decide_eq_true_eq, not_le, Int.ofNat_eq_natCast]
    omega
  have hfind2 : List.find? ((fun x : ℤ ↦ decide (((h : ℤ) + 1) / 2 ≤ x)) ∘ Int.ofNat)
      (valences (Work.effectiveZ a)) = none := by
    rw [List.find?_eq_none]
    intro v hv
    have := valences_le_six _ v hv
    simp only [Function.comp_apply, decide_eq_true_eq, not_le, Int.ofNat_eq_natCast]
    omega
  unfold impl
  simp [Id.run, hhv, hev, hfind2]
  split
  · rfl
  · split <;> rfl

end LeanSMILES.Aromaticity.Loc
