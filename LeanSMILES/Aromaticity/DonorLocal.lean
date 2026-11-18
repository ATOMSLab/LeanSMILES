/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.HsLocal

/-!
# LeanSMILES.Aromaticity.DonorLocal

Perception's donor type and candidate test at one atom, read off the atom's record, the kinds of
its bonds, and three facts about its surroundings that two copies with the same bonds share:
whether it has an exocyclic multiple bond, whether the atom across that bond pulls electrons, and
whether one of its ring bonds is multiple (`Loc.donorL`, `Loc.ringDonorL`, `Loc.candD`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Loc

/-- `Work.donorType`, at an atom with record `a` and bonds of kinds `ks`. -/
def donorL (a : WAtom) (ks : List BondKind) (whoS pulls rm : Bool) : Donor := Id.run do
  let mut nelec := elec a ks
  if nelec < 0 then return .none
  if nelec == 0 then
    if whoS then return .vacant
    if rm then return .one
    return .none
  if nelec == 1 then
    if whoS then return if pulls then .vacant else .one
    if cv a ks != ks.length + a.explicitHs then return .one
    if a.charge == 1 then return .vacant
    return .none
  if pulls then nelec := nelec - 1
  return if nelec % 2 == 1 then .one else .two

/-- `Work.ringDonor`, in a ring of 9 or more atoms (`big`) or not. -/
def ringDonorL (a : WAtom) (ks : List BondKind) (whoS pulls rm big : Bool) : Donor :=
  let d := donorL a ks whoS pulls rm
  if d == .two && big && [8, 16].contains a.z && ks.length == 2 && a.charge == 0 &&
      !ks.any isMultiple then .none
  else d

/-- `Work.isAromaticCandidate`, for any donor type. -/
def candD (a : WAtom) (ks : List BondKind) (d : Donor) : Bool := d != .none && cand a ks

lemma donorL_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (ks : List BondKind) (hcv : cv a ks = cv b ks)
    (w p r : Bool) : donorL a ks w p r = donorL b ks w p r := by
  have hel : elec a ks = elec b ks := by
    simp only [elec, hz, hc, he, hi, hr, hcv]
  simp only [donorL, hel, hcv, he, hc]

lemma ringDonorL_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (ks : List BondKind) (hcv : cv a ks = cv b ks)
    (w p r g : Bool) : ringDonorL a ks w p r g = ringDonorL b ks w p r g := by
  simp only [ringDonorL, donorL_congr hz hc he hi hr ks hcv, hz, hc]

lemma candD_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (hi : a.cachedImplicit = b.cachedImplicit) (hr : a.radicals = b.radicals)
    (ks : List BondKind) (hcv : cv a ks = cv b ks) (d : Donor) : candD a ks d = candD b ks d := by
  simp only [candD, cand, hz, hc, hi, hr, hcv]

end Loc

namespace Work

/-- Whether atom `i` has an exocyclic multiple bond, and whether the atom across it pulls. -/
def whoS (w : Work) (rbs : List ℕ) (i : ℕ) : Bool := (w.exocyclicMultiple? rbs i).isSome

def pullsB (w : Work) (rbs : List ℕ) (i : ℕ) : Bool :=
  match w.exocyclicMultiple? rbs i with
  | some j => moreElectronegative (w.atoms[j]! : WAtom).z (w.atoms[i]! : WAtom).z
  | none => false

def ringMultB (w : Work) (rbs : List ℕ) (i : ℕ) : Bool :=
  (w.bondsOf i).any fun k ↦ rbs.contains k && isMultiple (w.bonds[k]! : WBond).kind

lemma donorType_eq_loc (w : Work) (rbs : List ℕ) (i : ℕ) :
    w.donorType rbs i = Loc.donorL w.atoms[i]! (w.kindsAt i) (w.whoS rbs i) (w.pullsB rbs i)
      (w.ringMultB rbs i) := by
  unfold donorType Loc.donorL whoS pullsB ringMultB
  rw [countAtomElec_eq_loc, cachedValence_eq_loc, degree_eq_loc]
  rfl

lemma ringDonor_eq_loc (w : Work) (rbs : List ℕ) (len i : ℕ) :
    w.ringDonor rbs len i = Loc.ringDonorL w.atoms[i]! (w.kindsAt i) (w.whoS rbs i)
      (w.pullsB rbs i) (w.ringMultB rbs i) (decide (9 ≤ len)) := by
  unfold ringDonor Loc.ringDonorL
  rw [donorType_eq_loc, degree_eq_loc]
  simp only [hasMultipleBond, kindsAt, List.any_map, Function.comp_def, List.length_map]

lemma isAromaticCandidate_eq_candD (w : Work) (i : ℕ) (d : Donor) :
    w.isAromaticCandidate i d = Loc.candD w.atoms[i]! (w.kindsAt i) d := by
  by_cases hd : d = .none
  · subst hd
    unfold isAromaticCandidate Loc.candD
    have e : (Donor.none == Donor.none) = true := rfl
    simp [Id.run, e]
    rfl
  · rw [isAromaticCandidate_eq_loc w i hd]
    have : (d != Donor.none) = true := by cases d <;> first | rfl | exact absurd rfl hd
    simp [Loc.candD, this]

/-- An exocyclic multiple bond, or a multiple ring bond, is a multiple bond at the atom. -/
lemma any_isMultiple_of_whoS (w : Work) (rbs : List ℕ) (i : ℕ) (h : w.whoS rbs i = true) :
    (w.kindsAt i).any isMultiple = true := by
  unfold whoS exocyclicMultiple? at h
  rw [Option.isSome_map] at h
  obtain ⟨⟨k, j⟩, hkj⟩ := Option.isSome_iff_exists.1 h
  have hp := List.find?_some hkj
  have hm := List.mem_of_find?_eq_some hkj
  simp only [neighbors, List.mem_map] at hm
  obtain ⟨k', hk', e⟩ := hm
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, -⟩ := e
  simp only [Bool.and_eq_true] at hp
  exact List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨_, hk', rfl⟩, hp.2⟩

lemma any_isMultiple_of_ringMultB (w : Work) (rbs : List ℕ) (i : ℕ)
    (h : w.ringMultB rbs i = true) : (w.kindsAt i).any isMultiple = true := by
  unfold ringMultB at h
  obtain ⟨k, hk, hp⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at hp
  exact List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨_, hk, rfl⟩, hp.2⟩

end Work

end LeanSMILES.Aromaticity
