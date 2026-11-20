/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.HsDecide
public import LeanSMILES.Aromaticity.HsRestoreK
public import LeanSMILES.Aromaticity.KekulizeRelabel

/-!
# LeanSMILES.Aromaticity.RoundDecide

**An aromatic `[nH]`/`[pH]` keeps its hydrogen through kekulization when RDKit's rounded valence
is the one kekulization gives it**, checked over both elements and every list of at most three
bond kinds (`Loc.branchTot_ok`, by `decide`).  Kekulization rewrites such an atom into a bare one
whose hydrogens RDKit counts on the Kekulé bonds (`Work.branchRec`); the count is the one written
hydrogen exactly when the Kekulé bond-order sum is the rounded valence less that hydrogen.  Where
the two differ the count is wrong: the nitrogen of `c1cc[nH](C)c1`, rounded to five, gets three
single bonds and no hydrogen.

## Main definitions

* `Loc.kekBaseL`: twice the bond-order sum with the aromatic bonds made single.
* `Loc.branchTotCheck`: the check at an `[nH]`/`[pH]` with given bond kinds.

## Main statements

* `Loc.branchTot_ok`: the check holds for N and P and every list of at most three bond kinds.
* `Loc.branchTot`: an `[nH]`/`[pH]` whose rounded valence is the one kekulization gives it keeps
  its hydrogen.
* `Work.kekBase_eq_loc`: `Work.kekBase` is `Loc.kekBaseL` of the atom's bond kinds.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Loc

/-- Twice the bond-order sum of bonds of kinds `ks` with the aromatic ones made single
(`Work.kekBase`). -/
def kekBaseL (ks : List BondKind) : ℕ :=
  (ks.map fun o ↦ if o == .aromatic then 2 else halfOrder o).sum

/-- The check at an `[nH]`/`[pH]` with bonds of kinds `pk`: if twice its rounded valence less the
written hydrogen is the bond-order sum kekulization gives it, RDKit counts one hydrogen on the
bare atom kekulization leaves. -/
def branchTotCheck (z : ℕ) (pk : List BondKind) : Bool :=
  let e := (branchP z pk).cachedValence.getD 0
  let h := kekBaseL pk + if ndb (branchP z pk) pk e then 2 else 0
  decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length) ||
    decide (2 * e ≠ h + 2) ||
    impl { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false } h
      false == 1

/-- `branchTotCheck` holds for N and P and every list of at most three bond kinds. -/
theorem branchTot_ok :
    (([7, 15] : List ℕ).all fun z ↦ (lists 3).all (branchTotCheck z)) = true := by
  decide +kernel

/-- **An `[nH]`/`[pH]` whose rounded valence is the one kekulization gives it keeps its
hydrogen**: RDKit counts one hydrogen on the bare atom at the Kekulé bond-order sum. -/
theorem branchTot {z : ℕ} (hz : z = 7 ∨ z = 15) {pk : List BondKind} (h3 : pk.length ≤ 3)
    (h2 : 2 ≤ (pk.filter (· == .aromatic)).length) {h : ℕ}
    (hh : h = kekBaseL pk +
      if ndb (branchP z pk) pk ((branchP z pk).cachedValence.getD 0) then 2 else 0)
    (hr : 2 * (branchP z pk).cachedValence.getD 0 = h + 2) :
    impl { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false } h
      false = 1 := by
  have hb := branchTot_ok
  rw [List.all_eq_true] at hb
  have hzl : z ∈ ([7, 15] : List ℕ) := by rcases hz with h | h <;> rw [h] <;> decide
  have := hb z hzl
  rw [List.all_eq_true] at this
  have hc := this pk (mem_lists 3 pk h3)
  simp only [branchTotCheck, ← hh, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · omega
  · omega
  · exact absurd hr hc
  · exact hc

end Loc

namespace Work

/-- An atom's bond-order sum with the bonds written aromatic made single, from the kinds of its
bonds. -/
lemma kekBase_eq_loc (w : Work) (i : ℕ) : w.kekBase i = Loc.kekBaseL (w.kindsAt i) := by
  simp only [kekBase, kekWa_eq, Loc.kekBaseL, kindsAt, List.map_map, Function.comp_def]

end Work

end LeanSMILES.Aromaticity
