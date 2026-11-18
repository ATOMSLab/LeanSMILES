/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.DonorLocal
public import LeanSMILES.Aromaticity.HsDecide

/-!
# LeanSMILES.Aromaticity.DonorDecide

**Perception reads an atom alike whether its hydrogens are written or implied**, in the cases the
witness argument meets (`Loc.swap_ok`, by `decide`): the record with `T` hydrogens written in
brackets and the one with `T` implied pass or fail the candidate test together and, as
candidates, have the same donor type, when `T` is RDKit's count on the Kekulé bonds or
OpenSMILES's count on the bonds perception leaves (with the written record a candidate in some
environment, when perception made the atom aromatic).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Loc

/-- The record of an atom of element `z`, charge `c`, with hydrogen total `T`, bond half-sum `h`,
`eH` hydrogens written and in brackets or not (`nI`): what both working copies cache. -/
def canon (z : ℕ) (c : ℤ) (T h eH : ℕ) (nI : Bool) : WAtom :=
  { z := z, aromatic := false, charge := c, explicitHs := eH, noImplicit := nI,
    radicals := if nI && z != 0 then radC z c (h / 2 + eH) else 0, cachedImplicit := T - eH,
    cachedValence := some (h / 2 + eH) }

/-- Perception reads the written and the implied record alike: the same candidate verdict and, at a
candidate, the same donor type. -/
def readAlike (a b : WAtom) (kk : List BondKind) (w p r g : Bool) : Bool :=
  candD a kk (ringDonorL a kk w p r g) == candD b kk (ringDonorL b kk w p r g) &&
    (!candD a kk (ringDonorL a kk w p r g) || ringDonorL a kk w p r g == ringDonorL b kk w p r g)

/-- The environments an atom can have: an exocyclic multiple bond (whose far atom pulls or not), a
multiple ring bond, a ring of 9 or more; the first two only with a multiple bond. -/
def envs (kk : List BondKind) : List (Bool × Bool × Bool × Bool) :=
  ([false, true].flatMap fun w ↦ [false, true].flatMap fun p ↦ [false, true].flatMap fun r ↦
    [false, true].map fun g ↦ (w, p, r, g)).filter fun (w, p, r, _) ↦
      (!(w || r) || kk.any isMultiple) && (!p || w)

/-- The check at element `e` and Kekulé bonds `kk`. -/
def swapCheck (e : Element) (kk : List BondKind) : Bool :=
  let z := e.atomicNumber
  let h := bhs kk
  if kk.length < 2 then true else
  -- hydrogens implied in the kekulized copy: RDKit's count, at the charges `cleanUp` leaves on a
  -- bare atom
  (([-1, 0, 1] : List ℤ).all fun c ↦
    let Tr := impl { z := z, aromatic := false, charge := c, explicitHs := 0, noImplicit := false }
      h false
    (envs kk).all fun (w, p, r, g) ↦
      readAlike (canon z c Tr h 0 false) (canon z c Tr h Tr true) kk w p r g) &&
  -- hydrogens written in the kekulized copy: OpenSMILES's count on the bonds perception leaves
  ((marks kk).all fun sk ↦
    let ar := sk.any (· == .aromatic)
    let b : Atom := { element := some e, aromatic := ar }
    let q : ℚ := (sk.map BondKind.order).sum
    let T := Molecule.implicitHydrogens b q
    Molecule.readsDifferentlyInRDKit b q ||
      (ar && sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) ||
      (ar && !(envs kk).any fun (w', p', r', g') ↦
          candD (canon z 0 T h T true) kk (ringDonorL (canon z 0 T h T true) kk w' p' r' g')) ||
      (envs kk).all fun (w, p, r, g) ↦
        readAlike (canon z 0 T h T true) (canon z 0 T h 0 false) kk w p r g)

theorem swap_ok : (organic.all fun e ↦ (nonArom 3).all (swapCheck e)) = true := by
  decide +kernel

end LeanSMILES.Aromaticity.Loc

namespace LeanSMILES.Aromaticity.Loc

lemma elec_eq_neg_one {a : WAtom} {ks : List BondKind}
    (h : 3 < ks.length + (a.explicitHs + a.cachedImplicit)) : elec a ks = -1 := by
  unfold elec
  have h3 : (3 : ℤ) < ks.length + ((a.explicitHs : ℤ) + a.cachedImplicit) := by
    exact_mod_cast h
  by_cases hd : (defaultValence a.z : ℤ) ≤ 1
  · simp [Id.run, hd]; rfl
  · simp [Id.run, hd, h3]; rfl

/-- No electrons to count, no donor. -/
lemma ringDonorL_none_of_elec {a : WAtom} {ks : List BondKind} (he : elec a ks = -1)
    (w p r g : Bool) : ringDonorL a ks w p r g = .none := by
  have hd : donorL a ks w p r = .none := by
    simp only [donorL, Id.run, he]
    rfl
  simp only [ringDonorL, hd]
  split <;> rfl

lemma ringDonorL_none_of_deg {a : WAtom} {ks : List BondKind}
    (h : 3 < ks.length + (a.explicitHs + a.cachedImplicit)) (w p r g : Bool) :
    ringDonorL a ks w p r g = .none :=
  ringDonorL_none_of_elec (elec_eq_neg_one h) w p r g

end LeanSMILES.Aromaticity.Loc
