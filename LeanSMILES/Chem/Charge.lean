/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.Chem.Charge

Formal-charge sanity checks: chemistry-level, decidable predicates a caller
opts into *after* parsing.

The parser checks syntax.  `[C+123]` is a well-formed bracket atom — the
tokenizer accepts any run of signs and any number of digits, by design — so it
parses, round-trips and canonicalizes like any other atom.  (RDKit accepts it
too, and "balances" it with 127 radical electrons.)  Whether the charge is one
the element can carry is a separate question, answered here by two bounds:

* an atom cannot lose more electrons than it has: `charge ≤ atomicNumber`;
* an atom cannot gain more electrons than complete its valence shell:
  `-shellVacancy ≤ charge`, where `Element.shellVacancy` is the distance to
  the next noble gas — `C` 4, `N` 3, `O` 2, `Fe` 10.

Both are bounds on what is physically possible, not on what is chemically
common: `[C-4]` (carbide) and `[Fe-2]` (a carbonylferrate) pass; `[C+7]`,
`[O-3]`, `[Ne-]` and `[C-123]` fail.  The wildcard `*` names no element, so it
gets the range OpenSMILES requires every implementation to accept, −15 to +15.

None of this is an invariant of `Molecule`, whose invariants are graph facts;
the canonicalization theorems carry no chemistry.  Instead
`Molecule.chargesConsistent` is a property of the atom vector, preserved by
relabeling (`chargesConsistent_relabel`) and, in `LeanSMILES.SMILES.Canon`, by
canonicalization.  `Molecule.checkCharges` is the same predicate as an
`Except` whose message names the offending atom (`checkCharges_eq_ok_iff`).
-/

@[expose] public section

namespace LeanSMILES

namespace Element

/-- Atomic numbers of the noble gases: the closed-shell configurations. -/
def nobleGasNumbers : List ℕ := [2, 10, 18, 36, 54, 86, 118]

/-- Electrons needed to complete the valence shell: the distance to the next
noble gas, `0` for a noble gas itself.  For a main-group element this is the
octet gap (`C` 4, `O` 2, `Cl` 1); for a transition metal the 18-electron gap
(`Fe` 10); for a lanthanide the 32-electron gap.  It bounds how negative the
formal charge can be: `Atom.minCharge`. -/
def shellVacancy (e : Element) : ℕ :=
  ((nobleGasNumbers.find? fun z ↦ decide (e.atomicNumber ≤ z)).getD e.atomicNumber)
    - e.atomicNumber

example : Element.H.shellVacancy = 1 := by decide
example : Element.C.shellVacancy = 4 := by decide
example : Element.O.shellVacancy = 2 := by decide
example : Element.Ne.shellVacancy = 0 := by decide
example : Element.Fe.shellVacancy = 10 := by decide
example : Element.Og.shellVacancy = 0 := by decide

end Element

namespace Atom

/-- The charge range OpenSMILES requires every implementation to accept,
`-15` to `+15`.  Used to bound the wildcard `*`, which names no element. -/
def wildcardChargeBound : ℤ := 15

/-- The lowest formal charge the atom can carry: it cannot gain more electrons
than complete its valence shell, `-shellVacancy`.  `-15` for the wildcard. -/
def minCharge (a : Atom) : ℤ :=
  match a.element with
  | none => -wildcardChargeBound
  | some e => -(e.shellVacancy : ℤ)

/-- The highest formal charge the atom can carry: it cannot lose more electrons
than it has, `atomicNumber`.  `+15` for the wildcard. -/
def maxCharge (a : Atom) : ℤ :=
  match a.element with
  | none => wildcardChargeBound
  | some e => e.atomicNumber

/-- The formal charge is one the element can physically carry:
`minCharge ≤ charge ≤ maxCharge`.  `[Na+]`, `[O-2]`, `[Fe+3]`, `[C-4]` and
every neutral atom satisfy it; `[C+7]`, `[O-3]`, `[C+123]` do not. -/
def chargeConsistent (a : Atom) : Prop := a.minCharge ≤ a.charge ∧ a.charge ≤ a.maxCharge

instance (a : Atom) : Decidable a.chargeConsistent :=
  inferInstanceAs (Decidable (a.minCharge ≤ a.charge ∧ a.charge ≤ a.maxCharge))

/-- A neutral atom is always consistent — in particular every bare atom. -/
theorem chargeConsistent_of_charge_eq_zero {a : Atom} (h : a.charge = 0) :
    a.chargeConsistent := by
  unfold chargeConsistent minCharge maxCharge wildcardChargeBound
  rw [h]
  cases a.element <;> simp

end Atom

namespace Molecule

/-- Every atom's formal charge is one its element can carry. -/
def chargesConsistent {n : ℕ} (m : Molecule n) : Prop := ∀ i : Fin n, (m.atom i).chargeConsistent

instance {n : ℕ} (m : Molecule n) : Decidable m.chargesConsistent :=
  inferInstanceAs (Decidable (∀ i : Fin n, (m.atom i).chargeConsistent))

variable {n : ℕ} (m : Molecule n)

/-- The first atom, in index order, whose charge is out of range. -/
def firstBadCharge : Option (Fin n) :=
  (List.finRange n).find? fun i ↦ !decide (m.atom i).chargeConsistent

theorem firstBadCharge_eq_none_iff : m.firstBadCharge = none ↔ m.chargesConsistent := by
  simp [firstBadCharge, chargesConsistent, List.find?_eq_none]

/-- `+3`, `-2`, `0`: a signed charge for messages. -/
def signedString (c : ℤ) : String := if 0 < c then s!"+{c}" else toString c

/-- The charge check as an `Except`, to run on the result of `SMILES.parse`:
`ok` exactly when `chargesConsistent` holds (`checkCharges_eq_ok_iff`),
otherwise a message naming the first offending atom's index, element symbol,
charge and allowed range, such as
`atom 1 (C) has formal charge +123; C can carry -4 to +6`. -/
def checkCharges : Except String Unit :=
  match m.firstBadCharge with
  | none => .ok ()
  | some i =>
    let a := m.atom i
    let sym := (a.element.map Element.symbol).getD "*"
    .error s!"atom {i.val} ({sym}) has formal charge {signedString a.charge}; \
      {sym} can carry {signedString a.minCharge} to {signedString a.maxCharge}"

/-- The checker is the predicate. -/
theorem checkCharges_eq_ok_iff : m.checkCharges = .ok () ↔ m.chargesConsistent := by
  rw [← firstBadCharge_eq_none_iff]
  unfold checkCharges
  split <;> simp_all

/-- Relabeling the atoms neither creates nor removes an inconsistent charge. -/
theorem chargesConsistent_relabel (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).chargesConsistent ↔ m.chargesConsistent := by
  constructor
  · intro h i
    simpa using h (σ i)
  · intro h j
    have := h (σ.symm j)
    rwa [← atom_relabel m σ (σ.symm j), Equiv.apply_symm_apply] at this

end Molecule

/-- `Molecule.chargesConsistent` for a bundled molecule. -/
def Mol.chargesConsistent (M : Mol) : Prop := M.mol.chargesConsistent

instance (M : Mol) : Decidable M.chargesConsistent :=
  inferInstanceAs (Decidable M.mol.chargesConsistent)

/-- `Molecule.checkCharges` for a bundled molecule: run it on the result of
`SMILES.parse`, which checks syntax only. -/
def Mol.checkCharges (M : Mol) : Except String Unit := M.mol.checkCharges

theorem Mol.checkCharges_eq_ok_iff (M : Mol) : M.checkCharges = .ok () ↔ M.chargesConsistent :=
  M.mol.checkCharges_eq_ok_iff

end LeanSMILES
