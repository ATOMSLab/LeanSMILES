/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekuleSim
public import LeanSMILES.Aromaticity.PerceiveAgree
public import LeanSMILES.Aromaticity.Kekulize

/-!
# LeanSMILES.Aromaticity.HsLocal

RDKit's valence and hydrogen arithmetic at one atom, read off the atom's record and the kinds of
its bonds (`Work.kindsAt`): explicit valence (`Loc.ev`), implicit hydrogens (`Loc.impl`), the
`adjustHs` step (`Loc.restore`), kekulization's "needs a double bond" (`Loc.ndb`), and
perception's electron count and candidate test (`Loc.elec`, `Loc.cand`).  Each `Work` function is
its local version at the atom (`Work.implicitHs_eq_loc` and the like), so a claim about one atom
can be checked over finitely many records and bond lists, by `decide`.

## Main definitions

* `Loc.ev`, `Loc.impl`: RDKit's explicit valence and implicit hydrogen count at one atom.
* `Loc.restore`: whether the `adjustHs` step gives back the cached hydrogen total.
* `Loc.ndb`: kekulization's "needs a double bond" at one atom.
* `Loc.elec`, `Loc.cand`: perception's π-electron count and candidate test at one atom.
* `Work.kindsAt`: the kinds of the bonds at an atom, in bond order.

## Main statements

* `Work.implicitHs_eq_loc`, `Work.explicitValence_eq_loc`: the `Work` valence functions are their
  local versions.
* `Work.hsRestored_iff_loc`: `Work.HsRestored` is `Loc.restore` at the atom.
* `Work.needsDoubleBond_eq_loc`, `Work.countAtomElec_eq_loc`,
  `Work.isAromaticCandidate_eq_loc`: kekulization's and perception's tests, locally.
* `Loc.impl_eq_of_ev_eq`: a neutral atom gets as many implied hydrogens read aromatic as plain,
  within its default valence.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Loc

/-- RDKit's explicit valence of an atom with record `a`, bond half-order sum `bhs`, aromatic or
not (`Work.explicitValence`). -/
def ev (a : WAtom) (bhs : ℕ) (arom : Bool) : ℕ := Id.run do
  let mut accum := 2 * a.explicitHs + bhs
  let valens := valences (Work.effectiveZ a)
  if let some dv := valens.head? then
    if 2 * dv < accum && arom then
      let pval := (valens.filter (2 * · ≤ accum)).getLast?.getD dv
      if accum ≤ 2 * pval + 3 then accum := 2 * pval
  return (accum + 1) / 2

/-- RDKit's implicit hydrogen count (`Work.implicitHs`). -/
def impl (a : WAtom) (bhs : ℕ) (arom : Bool) : ℕ := Id.run do
  if a.noImplicit then return 0
  let mut eff := Work.effectiveZ a
  let mut e : ℤ := ev a bhs arom
  if Work.canBeHypervalent a eff then
    eff := a.z
    e := e - a.charge
  let valens := valences eff
  let some dv := valens.head? | return 0
  if arom then
    return if e ≤ dv then (dv - e).toNat else 0
  match (valens.map Int.ofNat).find? (e ≤ ·) with
  | some v => return (v - e).toNat
  | none => return 0

/-- Twice the bond-order sum of bonds of kinds `ks`. -/
def bhs (ks : List BondKind) : ℕ := (ks.map halfOrder).sum

/-- The `adjustHs` step gives back the cached hydrogen total (`Work.HsRestored`), at an atom with
record `a`, bonds of kinds `ks`, aromatic or not. -/
def restore (a : WAtom) (ks : List BondKind) (arom : Bool) : Bool :=
  let new := impl a (bhs ks) arom
  if (a.adjustHs || arom) && new < a.cachedImplicit then
    (a.explicitHs + (a.cachedImplicit - new)) +
      impl { a with explicitHs := a.explicitHs + (a.cachedImplicit - new) } (bhs ks) arom ==
      a.explicitHs + a.cachedImplicit
  else a.explicitHs + new == a.explicitHs + a.cachedImplicit

/-- The cached valence (`Work.cachedValence`). -/
def cv (a : WAtom) (ks : List BondKind) : ℕ := a.cachedValence.getD (bhs ks / 2 + a.explicitHs)

/-- Kekulization's "needs a double bond" (`Work.needsDoubleBond`), at an atom whose bonds have
kinds `ks`, aromatic ones being those written aromatic. -/
def ndb (a : WAtom) (ks : List BondKind) (ev0 : ℕ) : Bool := Id.run do
  let z := a.z
  let totH := a.explicitHs + a.cachedImplicit
  let impl : Int := a.cachedImplicit
  let mut sbo : Int := totH
  for o in ks do
    sbo := sbo + (if o == .aromatic then 1 else ((halfOrder o + 1) / 2 : Nat))
  let mut chrg : Int := a.charge
  if isEarly z then chrg := -chrg
  if z == 6 && 0 < chrg then chrg := -chrg
  let mut dv : Int := defaultValence z + chrg
  let tbo : Int := ev0 + impl
  let nrad : Int := a.radicals
  let tdeg : Int := ks.length + impl
  for v in (valences z).drop 1 do
    if dv < tbo && 0 < v then dv := v + chrg
  if tbo == 5 && sbo == 4 && dv == 3 && tdeg == 3 && nrad == 0 && chrg == 0 &&
      totH == 0 && [7, 15, 33].contains z then
    dv := 5
  if dv ≤ tdeg + nrad then return false
  return dv == sbo + 1 + nrad || (nrad == 0 && a.noImplicit && dv == sbo + 2)

/-- Perception's π-electron count (`Work.countAtomElec`). -/
def elec (a : WAtom) (ks : List BondKind) : Int := Id.run do
  let dv : Int := defaultValence a.z
  if dv ≤ 1 then return -1
  let deg : Int := ks.length + ((a.explicitHs + a.cachedImplicit : ℕ) : Int)
  if 3 < deg then return -1
  let nlp := max ((outerElectrons a.z : Int) - dv - a.charge) 0
  let res := dv - deg + nlp - a.radicals
  if 1 < res && 1 < (cv a ks : Int) - ks.length then return 1
  return res

/-- Perception's candidate test (`Work.isAromaticCandidate`), for a donor type other than
`none`. -/
def cand (a : WAtom) (ks : List BondKind) : Bool := Id.run do
  let z := a.z
  if 18 < z && z != 34 && z != 52 then return false
  let impl := a.cachedImplicit
  let ev := cv a ks
  if 0 < defaultValence z &&
      defaultValence (((z : Int) - a.charge).toNat) < ev + impl then return false
  if 0 < a.radicals && (z != 6 || a.charge != 0) then return false
  if ks.length + 1 < ev then
    let nMult := (ks.filter isMultiple).length
    if 1 < nMult then return false
  return true

/-! ### What each local function reads -/

/-- `Loc.ev` reads only the element, the charge and the written hydrogens of the record. -/
lemma ev_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (h : ℕ) (ar : Bool) : ev a h ar = ev b h ar := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

/-- `Loc.impl` reads only the element, the charge, the written hydrogens and the bracket flag of
the record. -/
lemma impl_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hn : a.noImplicit = b.noImplicit) (h : ℕ) (ar : Bool) :
    impl a h ar = impl b h ar := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

/-- **A neutral atom that takes implied hydrogens gets as many read aromatic as read plain**,
when its explicit valence is the same both ways and, where it is read aromatic, within its default
valence.  RDKit fills an aromatic atom up to its default valence only and a plain one up to the
next allowed valence; within the default valence the two are the same. -/
lemma impl_eq_of_ev_eq {a : WAtom} (hn : a.noImplicit = false) (hc : a.charge = 0) {h h' : ℕ}
    {ar : Bool} (he : ev a h ar = ev a h' false)
    (hle : ar = true → ev a h' false ≤ defaultValence a.z) :
    impl a h ar = impl a h' false := by
  have heff : Work.effectiveZ a = a.z := by simp [Work.effectiveZ, hc]
  have hhv : Work.canBeHypervalent a a.z = false := by
    simp only [Work.canBeHypervalent, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    omega
  unfold impl
  simp only [Id.run, hn, heff, hhv, he, Bool.false_eq_true, if_false]
  cases ar
  · rfl
  · have hle' := hle rfl
    unfold defaultValence at hle'
    cases hv : (valences a.z).head? with
    | none => rfl
    | some dv =>
      rw [hv] at hle'
      simp only [Option.getD_some] at hle'
      obtain ⟨tl, htl⟩ : ∃ tl, valences a.z = dv :: tl := by
        cases hl : valences a.z with
        | nil => simp [hl] at hv
        | cons x tl =>
          rw [hl, List.head?_cons, Option.some.injEq] at hv
          exact ⟨tl, by rw [hv]⟩
      simp [htl, hle']

/-- `Loc.restore` reads only the element, the charge, the written hydrogens, the bracket flag, the
cached implicit count and the `adjustHs` flag of the record. -/
lemma restore_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hn : a.noImplicit = b.noImplicit)
    (hi : a.cachedImplicit = b.cachedImplicit) (hadj : a.adjustHs = b.adjustHs)
    (ks : List BondKind) (ar : Bool) : restore a ks ar = restore b ks ar := by
  have key : ∀ e : ℕ, impl { a with explicitHs := e } (bhs ks) ar =
      impl { b with explicitHs := e } (bhs ks) ar := fun e ↦
    impl_congr (a := { a with explicitHs := e }) (b := { b with explicitHs := e }) hz hc rfl hn _ _
  have h1 : impl a (bhs ks) ar = impl b (bhs ks) ar := impl_congr hz hc he hn _ _
  unfold restore
  simp only [h1]
  rw [key]
  simp only [he, hi, hadj]

/-- `Loc.ndb` reads only the element, the charge, the written hydrogens, the bracket flag, the
cached implicit count and the radicals of the record. -/
lemma ndb_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hn : a.noImplicit = b.noImplicit)
    (hi : a.cachedImplicit = b.cachedImplicit) (hr : a.radicals = b.radicals)
    (ks : List BondKind) (e : ℕ) : ndb a ks e = ndb b ks e := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

/-- `Loc.cv` reads only the written hydrogens and the cached valence of the record. -/
lemma cv_congr {a b : WAtom} (he : a.explicitHs = b.explicitHs)
    (hv : a.cachedValence = b.cachedValence) (ks : List BondKind) : cv a ks = cv b ks := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

/-- `Loc.elec` reads only the element, the charge, the hydrogens (written and cached implicit), the
radicals and the cached valence of the record. -/
lemma elec_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (hv : a.cachedValence = b.cachedValence)
    (ks : List BondKind) : elec a ks = elec b ks := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

/-- `Loc.cand` reads only the element, the charge, the hydrogens (written and cached implicit), the
radicals and the cached valence of the record. -/
lemma cand_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (hv : a.cachedValence = b.cachedValence)
    (ks : List BondKind) : cand a ks = cand b ks := by
  cases a; cases b
  simp only at *
  subst_vars
  rfl

end Loc

namespace Work

/-- The kinds of the bonds at atom `i`, in bond order. -/
def kindsAt (w : Work) (i : ℕ) : List BondKind :=
  (w.bondsOf i).map fun k ↦ (w.bonds[k]! : WBond).kind

/-- An atom's bond half-order sum is `Loc.bhs` of the kinds of its bonds. -/
lemma bondHalfSum_eq_loc (w : Work) (i : ℕ) : w.bondHalfSum i = Loc.bhs (w.kindsAt i) := by
  simp only [bondHalfSum, Loc.bhs, kindsAt, List.map_map, Function.comp_def]

/-- An atom is aromatic for RDKit when its flag is set or one of its bonds is of kind
`aromatic`. -/
lemma isAromaticAtom_eq_loc (w : Work) (i : ℕ) :
    w.isAromaticAtom i =
      ((w.atoms[i]! : WAtom).aromatic || (w.kindsAt i).any (· == .aromatic)) := by
  simp only [isAromaticAtom, kindsAt, List.any_map, Function.comp_def]

/-- An atom's degree is the number of its bond kinds. -/
lemma degree_eq_loc (w : Work) (i : ℕ) : w.degree i = (w.kindsAt i).length := by
  simp [degree, kindsAt]

/-- `Work.explicitValence` is `Loc.ev` at the atom's record. -/
lemma explicitValence_eq_loc (w : Work) (i : ℕ) :
    w.explicitValence i = Loc.ev w.atoms[i]! (w.bondHalfSum i) (w.isAromaticAtom i) := rfl

/-- `Work.implicitHs` is `Loc.impl` at the atom's record. -/
lemma implicitHs_eq_loc (w : Work) (i : ℕ) :
    w.implicitHs i = Loc.impl w.atoms[i]! (w.bondHalfSum i) (w.isAromaticAtom i) := rfl

/-- `Work.cachedValence` is `Loc.cv` at the atom's record and bond kinds. -/
lemma cachedValence_eq_loc (w : Work) (i : ℕ) :
    w.cachedValence i = Loc.cv w.atoms[i]! (w.kindsAt i) := by
  simp only [cachedValence, Loc.cv, kekuleValence, bondHalfSum_eq_loc]

/-- **The `adjustHs` step, locally.** -/
lemma hsRestored_iff_loc (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    HsRestored w i ↔
      Loc.restore w.atoms[i]! (w.kindsAt i) (w.isAromaticAtom i) = true := by
  have hk : ∀ f : WAtom → WAtom, (w.modifyAtom i f).kindsAt i = w.kindsAt i := fun _ ↦ rfl
  have hb : ∀ f : WAtom → WAtom, (w.modifyAtom i f).bondHalfSum i = w.bondHalfSum i := fun _ ↦ rfl
  have ha : ∀ f : WAtom → WAtom, (w.modifyAtom i f).atoms[i]! = f w.atoms[i]! := fun f ↦ by
    rw [atom_modifyAtom, if_pos ⟨rfl, hi⟩]
  have har : ∀ e : ℕ,
      (w.modifyAtom i fun x ↦ { x with explicitHs := e }).isAromaticAtom i =
        w.isAromaticAtom i := fun e ↦ by
    rw [isAromaticAtom_eq_loc, isAromaticAtom_eq_loc, hk, ha]
  unfold HsRestored adjustHsStep Loc.restore
  rw [implicitHs_eq_loc, bondHalfSum_eq_loc]
  simp only [cachedTotalHs]
  by_cases hc : ((w.atoms[i]! : WAtom).adjustHs || w.isAromaticAtom i) = true
  · by_cases hn : Loc.impl w.atoms[i]! (Loc.bhs (w.kindsAt i)) (w.isAromaticAtom i) <
        (w.atoms[i]! : WAtom).cachedImplicit
    · simp only [hc, hn, if_true, Bool.true_and, decide_true]
      rw [implicitHs_eq_loc, ha, har, hb, bondHalfSum_eq_loc, beq_iff_eq]
    · simp only [hc, hn, if_true, if_false, Bool.true_and, decide_false]
      rw [implicitHs_eq_loc, bondHalfSum_eq_loc]
      simp
  · simp only [Bool.not_eq_true] at hc
    rw [Bool.or_eq_false_iff] at hc
    simp only [hc, Bool.false_or, Bool.false_and, implicitHs_eq_loc, bondHalfSum_eq_loc]
    simp [hc.2]

/-- `Work.needsDoubleBond`, with the aromatic bonds being those written aromatic, is `Loc.ndb` at
the atom's record and bond kinds. -/
lemma needsDoubleBond_eq_loc (w : Work) (ev0 i : ℕ) :
    w.needsDoubleBond (fun k ↦ (w.bonds[k]! : WBond).kind == .aromatic) ev0 i =
      Loc.ndb w.atoms[i]! (w.kindsAt i) ev0 := by
  unfold needsDoubleBond Loc.ndb kindsAt
  simp only [Id.run, List.forIn_map, degree, List.length_map]

/-- `Work.countAtomElec` is `Loc.elec` at the atom's record and bond kinds. -/
lemma countAtomElec_eq_loc (w : Work) (i : ℕ) :
    w.countAtomElec i = Loc.elec w.atoms[i]! (w.kindsAt i) := by
  unfold countAtomElec Loc.elec
  simp only [degree_eq_loc, cachedTotalHs, cachedValence_eq_loc]

/-- For a donor type other than `none`, `Work.isAromaticCandidate` is `Loc.cand` at the atom. -/
lemma isAromaticCandidate_eq_loc (w : Work) (i : ℕ) {d : Donor} (hd : d ≠ .none) :
    w.isAromaticCandidate i d = Loc.cand w.atoms[i]! (w.kindsAt i) := by
  have hd' : (d == Donor.none) = false := by cases d <;> first | rfl | exact absurd rfl hd
  unfold isAromaticCandidate Loc.cand
  simp only [Id.run, hd', degree_eq_loc, cachedValence_eq_loc, kindsAt, List.filter_map,
    List.length_map, Function.comp_def]
  rfl

end Work

end LeanSMILES.Aromaticity
