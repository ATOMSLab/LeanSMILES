
/-!
# LeanSMILES.Canonical.Molecule

Elements, atoms, bonds and the molecule graph.
-/

/-!
# Elements

Atomic numbers, symbols, RDKit's allowed-valence lists and outer-electron counts
(RDKit 2026.09.1, `atomic_data.cpp`). Only the elements that can appear in SMILES
we support are listed; implicit hydrogens and aromaticity use these values.
-/

namespace Chem

/-- Atomic number, symbol, allowed valences (smallest first; the first is the
default valence), outer (valence-shell) electrons. Values copied from RDKit. -/
private def table : List (Nat × String × List Nat × Nat) :=
  [(1, "H", [1], 1), (2, "He", [0], 2), (4, "Be", [2], 2), (5, "B", [3], 3),
   (6, "C", [4], 4), (7, "N", [3], 5), (8, "O", [2], 6), (9, "F", [1], 7),
   (10, "Ne", [0], 8), (13, "Al", [3], 3), (14, "Si", [4], 4), (15, "P", [3, 5], 5),
   (16, "S", [2, 4, 6], 6), (17, "Cl", [1], 7), (18, "Ar", [0], 8), (31, "Ga", [3], 3),
   (32, "Ge", [4], 4), (33, "As", [3, 5], 5), (34, "Se", [2, 4, 6], 6), (35, "Br", [1], 7),
   (36, "Kr", [0], 8), (49, "In", [3], 3), (50, "Sn", [2, 4], 4), (51, "Sb", [3, 5], 5),
   (52, "Te", [2, 4, 6], 6), (53, "I", [1, 3, 5], 7), (54, "Xe", [0, 2, 4, 6], 8)]

private def entry? (z : Nat) := table.find? (·.1 == z)

def symbol (z : Nat) : String :=
  (entry? z).map (·.2.1) |>.getD s!"#{z}"

def ofSymbol? (s : String) : Option Nat :=
  (table.find? (·.2.1 == s)).map (·.1)

/-- Allowed valences of element `z`; empty if unknown (no implicit H is added). -/
def valences (z : Nat) : List Nat :=
  (entry? z).map (·.2.2.1) |>.getD []

/-- RDKit's default valence (first allowed valence), 0 if unknown. -/
def defaultValence (z : Nat) : Nat := (valences z).head?.getD 0

/-- Electrons in the outer shell (5 for N, 6 for O). -/
def outerElectrons (z : Nat) : Nat :=
  (entry? z).map (·.2.2.2) |>.getD 0

/-- RDKit's `isEarlyAtom` (`Atom.cpp:58`), restricted to our table: elements left
of carbon in their row, whose charges count the other way in kekulization. -/
def isEarly (z : Nat) : Bool := [4, 5, 13, 31, 32, 49, 50, 51].contains z

/-- RDKit's `PeriodicTable::moreElectroNegative` (`PeriodicTable.h:304`):
more outer electrons, or the same number and a smaller atomic number. -/
def moreElectronegative (z1 z2 : Nat) : Bool :=
  outerElectrons z1 > outerElectrons z2 ||
  (outerElectrons z1 == outerElectrons z2 && z1 < z2)

/-- Elements that may be written without brackets (SMILES organic subset). -/
def organicSubset : List String := ["B", "C", "N", "O", "P", "S", "F", "Cl", "Br", "I"]

/-- Elements that may be written as lowercase aromatic atoms. -/
def aromaticSymbols : List String := ["b", "c", "n", "o", "p", "s", "se", "as", "te"]

end Chem

/-!
# Molecular graph

Plain array-based structures, easy to compute with and `#eval`. Atoms are kept in
the order they appear in the SMILES string (as RDKit does), so atom `i` here is
atom `i` in RDKit and in `datasets/delaney-oracle.csv`.
-/

namespace Chem

inductive BondOrder where
  | single | double | triple | aromatic
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Bond order counted in half-units (aromatic = 1.5 → 3), as in RDKit's
`getBondTypeAsDouble`. -/
def BondOrder.halfValence : BondOrder → Nat
  | .single => 2 | .double => 4 | .triple => 6 | .aromatic => 3

/-- RDKit's bond-type number (`Chem.BondType`), used by Morgan fingerprints and
the oracle files. -/
def BondOrder.rdkitType : BondOrder → Nat
  | .single => 1 | .double => 2 | .triple => 3 | .aromatic => 12

structure Atom where
  atomicNum : Nat
  /-- Written in lowercase in the SMILES. -/
  aromatic : Bool := false
  charge : Int := 0
  isotope : Option Nat := none
  /-- Hydrogens written explicitly, e.g. the `H` in `[nH]`. -/
  explicitHs : Nat := 0
  /-- Bracket atoms get no implicit hydrogens. -/
  noImplicit : Bool := false
  /-- Total H count fixed before kekulization (RDKit keeps it unchanged from
  then on); `none` means "compute from the graph". -/
  frozenHs : Option Nat := none
  /-- Unpaired electrons (only bracket atoms can have them). -/
  radicals : Nat := 0
  /-- Explicit valence as RDKit caches it before kekulization; aromaticity
  perception reads this cached value, not one recomputed on the Kekulé graph. -/
  cachedValence : Option Nat := none
  /-- Implicit H count cached at the same time (RDKit's `getValence(IMPLICIT)`). -/
  cachedImplicit : Nat := 0
  /-- Was aromatic (or touched an aromatic bond) before kekulization: RDKit's
  `adjustHs` may give such atoms back hydrogens at the end. -/
  adjustHs : Bool := false
  deriving BEq, Repr, Inhabited

structure Bond where
  /-- Atom that came first in the SMILES. -/
  src : Nat
  dst : Nat
  order : BondOrder
  deriving BEq, Repr, Inhabited

def Bond.other (b : Bond) (i : Nat) : Nat := if b.src == i then b.dst else b.src

def Bond.touches (b : Bond) (i : Nat) : Bool := b.src == i || b.dst == i

structure Mol where
  atoms : Array Atom := #[]
  bonds : Array Bond := #[]
  deriving Repr, Inhabited

namespace Mol

def numAtoms (m : Mol) : Nat := m.atoms.size
def numBonds (m : Mol) : Nat := m.bonds.size

/-- Indices of the bonds touching atom `i`, in bond order. -/
def bondsOf (m : Mol) (i : Nat) : List Nat :=
  (List.range m.numBonds).filter fun k => m.bonds[k]!.touches i

/-- Neighbours of atom `i` with the connecting bond, `(bond, atom)`, in bond
order (RDKit's adjacency order). -/
def neighbors (m : Mol) (i : Nat) : List (Nat × Nat) :=
  (m.bondsOf i).map fun k => (k, m.bonds[k]!.other i)

/-- Number of heavy-atom neighbours of atom `i`. -/
def degree (m : Mol) (i : Nat) : Nat := (m.bondsOf i).length

/-- Index of the bond joining atoms `i` and `j`, if any. -/
def bondBetween? (m : Mol) (i j : Nat) : Option Nat :=
  (List.range m.numBonds).find? fun k =>
    let b := m.bonds[k]!
    (b.src == i && b.dst == j) || (b.src == j && b.dst == i)

/-- Set the order of bond `k`. -/
def setOrder (m : Mol) (k : Nat) (o : BondOrder) : Mol :=
  { m with bonds := m.bonds.modify k fun b => { b with order := o } }

/-- Update atom `i`. -/
def modifyAtom (m : Mol) (i : Nat) (f : Atom → Atom) : Mol :=
  { m with atoms := m.atoms.modify i f }

end Mol

end Chem
