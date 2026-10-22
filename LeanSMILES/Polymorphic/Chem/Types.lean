module

/-!
# Molecules — Types

Data types for molecules and their string and fingerprint representations. The functions
that build and consume them live in the other files of `Polymorphic/Chem/`.

Atoms are referred to by their index (`Nat`) in `Molecule.atoms`. `Molecule.WellFormed`
(in `Graph.lean`) states that every bond refers to existing, distinct atoms.
-/

@[expose] public section

namespace Chem

inductive BondOrder where
  | single
  | double
  | triple
  | aromatic
  deriving DecidableEq, Repr, Inhabited

structure Atom where
  /-- Atomic number; `0` is the SMILES wildcard `*`. -/
  element : Nat
  aromatic : Bool := false
  charge : Int := 0
  isotope : Option Nat := none
  /-- Hydrogens written in a bracket atom (`[CH3]` ↦ `some 3`, `[C]` ↦ `some 0`).
  `none` for organic-subset atoms (`C`, `n`, …), whose hydrogens are implicit and
  follow from the normal valence. -/
  explicitH : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- An undirected bond between the atoms with indices `src` and `dst`. -/
structure Bond where
  src : Nat
  dst : Nat
  order : BondOrder
  deriving DecidableEq, Repr, Inhabited

/-- A molecular graph. Hydrogens are normally implicit (see `Atom.explicitH`). -/
structure Molecule where
  atoms : Array Atom
  bonds : Array Bond
  deriving DecidableEq, Repr, Inhabited

/-- A SMILES string. Any string can be wrapped; `SMILES.parse` decides whether it is one
the parser accepts. -/
structure SMILES where
  str : String
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- A canonical SMILES string: the same string for every SMILES of the same molecule.
Build it with `Molecule.canonicalSMILES` or `SMILES.canonicalize`, not with the
constructor; `SMILES.isCanonical` checks the fixed-point property. -/
structure CanonicalSMILES where
  smiles : SMILES
  deriving DecidableEq, Repr, Hashable, Inhabited

/-- An `nBits`-bit Morgan (ECFP-style) fingerprint. Bit `j` is set iff some atom
environment of radius `≤ r` hashes to `j` modulo `nBits`. -/
structure MorganFingerprint (nBits : Nat) where
  bits : Vector Bool nBits
  deriving DecidableEq, Repr

end Chem

end
