/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Element

/-!
# LeanSMILES.Chem.Atom

An atom as SMILES describes one: an element (or the wildcard `*`), the aromatic
flag, and the bracket-atom decorations — isotope, charge, written hydrogen
count, chirality mark and atom class.  Two hydrogen counts are kept apart, as
RDKit does: `explicitH` is what the string said inside brackets (`[CH3]`), and
`implicitH` is what the default-valence rule later infers for a bare
organic-subset atom.  Their sum is `totalH`.

Chirality is *recorded*, not *interpreted*: `@`/`@@` are relative to the order
in which the atom's neighbors appear in the SMILES string, which is a property
of the string and of the bond order in `Molecule.bonds`, not of the atom alone.
The named classes `@TH1` … `@OH30` are recorded the same way, as written; the
shorthand equivalence (`@` for `@TH1`) is not applied.
-/

@[expose] public section

namespace LeanSMILES

/-- The chirality mark of a bracket atom, as written.  `@` (anticlockwise) and
`@@` (clockwise) are the tetrahedral shorthands: viewed from the first
neighbor towards the atom, the remaining neighbors are taken in the order
the SMILES string lists them.  The named classes of OpenSMILES §3.7 carry
their index, one-based in the string and zero-based here: tetrahedral
`@TH1`–`@TH2`, allenal `@AL1`–`@AL2`, square-planar `@SP1`–`@SP3`,
trigonal-bipyramidal `@TB1`–`@TB20` and octahedral `@OH1`–`@OH30`.  The
shorthand equivalence (`@` for `@TH1`, and so on) is not applied. -/
inductive Chirality
  | anticlockwise
  | clockwise
  /-- `@TH1`, `@TH2`. -/
  | th (k : Fin 2)
  /-- `@AL1`, `@AL2`. -/
  | al (k : Fin 2)
  /-- `@SP1`–`@SP3`. -/
  | sp (k : Fin 3)
  /-- `@TB1`–`@TB20`. -/
  | tb (k : Fin 20)
  /-- `@OH1`–`@OH30`. -/
  | oh (k : Fin 30)
  deriving DecidableEq, Repr, Inhabited, Ord

namespace Chirality

/-- The SMILES mark: `@`, `@@`, or a named class with its one-based index. -/
def toSmiles : Chirality → String
  | anticlockwise => "@"
  | clockwise => "@@"
  | th k => s!"@TH{k.val + 1}"
  | al k => s!"@AL{k.val + 1}"
  | sp k => s!"@SP{k.val + 1}"
  | tb k => s!"@TB{k.val + 1}"
  | oh k => s!"@OH{k.val + 1}"

/-- An injective numeric code, for invariant vectors: `@` is 1, `@@` is 2 and
the named classes follow in order, `@OH30` last at 59. -/
def code : Chirality → ℕ
  | anticlockwise => 1
  | clockwise => 2
  | th k => 3 + k.val
  | al k => 5 + k.val
  | sp k => 7 + k.val
  | tb k => 10 + k.val
  | oh k => 30 + k.val

end Chirality

/-- An atom. All fields default to the bare carbon-like reading so that
`{ element := some .O }` is a plain oxygen. -/
structure Atom where
  /-- The element, or `none` for the SMILES wildcard `*`. -/
  element : Option Element := none
  /-- Written with a lowercase symbol in SMILES. -/
  aromatic : Bool := false
  /-- Mass number, when written: `[13C]`. -/
  isotope : Option ℕ := none
  /-- Formal charge: `[NH4+]`, `[O-]`, `[Fe+2]`. -/
  charge : ℤ := 0
  /-- The hydrogen count written inside brackets (`[CH3]` is `some 3`, `[C]` is
  `some 0`); `none` for an atom written without brackets. -/
  explicitH : Option ℕ := none
  /-- Hydrogens implied by the default-valence rule; `0` until
  `Molecule.assignImplicitH` runs, and always `0` for bracket atoms. -/
  implicitH : ℕ := 0
  /-- Chirality mark, when written. -/
  chirality : Option Chirality := none
  /-- Atom class `[C:1]`, when written. -/
  atomClass : Option ℕ := none
  deriving DecidableEq, Repr, Inhabited

namespace Atom

/-- A bare atom of element `e`. -/
def ofElement (e : Element) : Atom := { element := some e }

/-- The wildcard atom `*`. -/
def wildcard : Atom := {}

/-- Atomic number, with `0` for the wildcard. -/
def atomicNumber (a : Atom) : ℕ := (a.element.map Element.atomicNumber).getD 0

/-- Written plus inferred hydrogens. -/
def totalH (a : Atom) : ℕ := a.explicitH.getD 0 + a.implicitH

/-- The element symbol as SMILES writes it: lowercase when aromatic, `*` for
the wildcard. -/
def symbol (a : Atom) : String :=
  match a.element with
  | none => "*"
  | some e => if a.aromatic then e.symbol.toLower else e.symbol

/-- Whether the atom can be written without brackets: an organic-subset
element (or `*`) carrying no bracket-only information. -/
def canBeBare (a : Atom) : Bool :=
  a.explicitH.isNone && a.isotope.isNone && a.charge == 0 &&
    a.chirality.isNone && a.atomClass.isNone &&
    (match a.element with
      | none => true
      | some e => e.inOrganicSubset)

/-- `+`, `-`, `+2`, `-3`, …; empty for a neutral atom. -/
def chargeString (c : ℤ) : String :=
  if c == 0 then ""
  else if c == 1 then "+"
  else if c == -1 then "-"
  else if c > 0 then s!"+{c}"
  else s!"{c}"

/-- `H`, `H2`, …; empty for no hydrogens. -/
def hString (h : ℕ) : String :=
  if h == 0 then "" else if h == 1 then "H" else s!"H{h}"

/-- The bracket form `[isotope symbol chirality H charge :class]`, always
valid, carrying the *total* hydrogen count. -/
def toBracket (a : Atom) : String :=
  "[" ++ (a.isotope.map toString).getD ""
    ++ a.symbol
    ++ (a.chirality.map Chirality.toSmiles).getD ""
    ++ hString a.totalH
    ++ chargeString a.charge
    ++ (a.atomClass.map fun c ↦ s!":{c}").getD ""
    ++ "]"

/-- The atom as SMILES writes it: bare when it can be, bracketed otherwise. -/
def toSmiles (a : Atom) : String :=
  if a.canBeBare then a.symbol else a.toBracket

instance : ToString Atom := ⟨toSmiles⟩

end Atom

end LeanSMILES
