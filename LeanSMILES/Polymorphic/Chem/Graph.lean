module

public import LeanSMILES.Polymorphic.Chem.Types

/-!
# Molecules — Graph basics

Elements, valence, and the molecular graph: neighbours, degrees, implicit hydrogens and
ring bonds. Atoms are referred to by their index in `Molecule.atoms`.
-/

@[expose] public section

namespace Chem

/-! ## Elements and valence -/

/-- Element symbols indexed by atomic number (`0` is the wildcard `*`). -/
def elementSymbols : Array String := #["*",
  "H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne", "Na", "Mg", "Al", "Si", "P", "S",
  "Cl", "Ar", "K", "Ca", "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn", "Ga",
  "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr", "Nb", "Mo", "Tc", "Ru", "Rh", "Pd",
  "Ag", "Cd", "In", "Sn", "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd", "Pm",
  "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb", "Lu", "Hf", "Ta", "W", "Re", "Os",
  "Ir", "Pt", "Au", "Hg", "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th", "Pa",
  "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm", "Md", "No", "Lr", "Rf", "Db", "Sg",
  "Bh", "Hs", "Mt", "Ds", "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og"]

def symbolOf (z : Nat) : String := elementSymbols.getD z "*"

def elementOf? (sym : String) : Option Nat := elementSymbols.findIdx? (· == sym)

/-- Elements that may be written without brackets. -/
def organicSubset : List Nat := [0, 5, 6, 7, 8, 9, 15, 16, 17, 35, 53]

/-- Normal valences of the organic-subset elements, in increasing order. -/
def normalValences : Nat → List Nat
  | 5 => [3]
  | 6 => [4]
  | 7 => [3, 5]
  | 8 => [2]
  | 15 => [3, 5]
  | 16 => [2, 4, 6]
  | 9 | 17 | 35 | 53 => [1]
  | _ => []

/-- Valence used by a bond. Aromatic bonds count `1`; the extra aromatic electron is
counted once per atom in `Molecule.bondValence`. -/
def BondOrder.valence : BondOrder → Nat
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 1

/-- Distinct numeric code per bond order, used in ranking and hashing. -/
def BondOrder.code : BondOrder → Nat
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 4

/-! ## Molecular graph -/

namespace Molecule

/-- Every bond joins two distinct existing atoms. -/
def WellFormed (m : Molecule) : Prop :=
  ∀ b ∈ m.bonds.toList, b.src < m.atoms.size ∧ b.dst < m.atoms.size ∧ b.src ≠ b.dst

instance (m : Molecule) : Decidable m.WellFormed := by
  unfold WellFormed; infer_instance

def atom (m : Molecule) (i : Nat) : Atom := m.atoms.getD i default

/-- The atoms bonded to atom `i`, with the bond orders. -/
def neighbors (m : Molecule) (i : Nat) : List (Nat × BondOrder) :=
  m.bonds.toList.filterMap fun b =>
    if b.src = i then some (b.dst, b.order)
    else if b.dst = i then some (b.src, b.order)
    else none

/-- `neighbors` for every atom. -/
def adjacency (m : Molecule) : Array (List (Nat × BondOrder)) :=
  (Array.range m.atoms.size).map m.neighbors

/-- Number of explicit (graph) neighbours. -/
def degree (m : Molecule) (i : Nat) : Nat := (m.neighbors i).length

/-- Valence used by the bonds of atom `i`, plus `1` if the atom is aromatic. -/
def bondValence (m : Molecule) (i : Nat) : Nat :=
  ((m.neighbors i).map (·.2.valence)).sum + (if (m.atom i).aromatic then 1 else 0)

/-- Hydrogens that atom `i` would carry if written without brackets: the smallest normal
valence that is at least `bondValence`, minus `bondValence`. Aromatic atoms use only
the lowest normal valence (so `c` ↦ 1 H, `n`, `o`, `s` ↦ 0 H). -/
def implicitH (m : Molecule) (i : Nat) : Nat :=
  let a := m.atom i
  let used := m.bondValence i
  let vs := normalValences a.element
  if a.aromatic then (vs.head?.map (· - used)).getD 0
  else ((vs.find? (used ≤ ·)).map (· - used)).getD 0

/-- Total hydrogens on atom `i`: the bracket count if given, otherwise `implicitH`. -/
def totalH (m : Molecule) (i : Nat) : Nat := (m.atom i).explicitH.getD (m.implicitH i)

end Molecule

/-! ## Ring perception -/

/-- Is `target` reachable from the atoms in `frontier` without using bond number `skip`?
Breadth-first search with at most `fuel` layers. -/
def reachableWithout (adjB : Array (List (Nat × Nat))) (skip target : Nat) :
    Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | fuel + 1, frontier, visited =>
    if target ∈ frontier then true
    else
      let next := (frontier.flatMap fun v => (adjB.getD v []).filterMap fun (u, k) =>
        if k = skip ∨ u ∈ visited then none else some u).eraseDups
      if next.isEmpty then false else reachableWithout adjB skip target fuel next (visited ++ next)

/-- A bond is in a ring iff its endpoints stay connected without it. -/
def Molecule.bondInRing (m : Molecule) (k : Nat) : Bool :=
  let n := m.atoms.size
  let adjB : Array (List (Nat × Nat)) := (Array.range n).map fun v =>
    (m.bonds.toList.zipIdx).filterMap fun (b, k) =>
      if b.src = v then some (b.dst, k) else if b.dst = v then some (b.src, k) else none
  match m.bonds[k]? with
  | some b => reachableWithout adjB k b.dst (n + 1) [b.src] [b.src]
  | none => false

/-- Is the bond between atoms `i` and `j` (if any) in a ring? -/
def Molecule.bondInRingBetween (m : Molecule) (i j : Nat) : Bool :=
  (m.bonds.toList.zipIdx).any fun (b, k) =>
    ((b.src = i && b.dst = j) || (b.src = j && b.dst = i)) && m.bondInRing k

def Molecule.atomInRing (m : Molecule) (i : Nat) : Bool :=
  (m.bonds.toList.zipIdx).any fun (b, k) => (b.src = i || b.dst = i) && m.bondInRing k

/-! ## Utilities -/

/-- Lexicographic `≤` on lists of naturals. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

/-- Insert `x` into a list sorted by `le`, before the first element it is `le` to. -/
def orderedInsert {β : Type} (le : β → β → Bool) (x : β) : List β → List β
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: orderedInsert le x ys

/-- Insertion sort. Unlike `List.mergeSort` it is structurally recursive, so the kernel
can evaluate it: fingerprints use it on neighbour lists (a few entries each), which lets
`decide` compute them in proofs. -/
def insertionSort {β : Type} (le : β → β → Bool) : List β → List β
  | [] => []
  | x :: xs => orderedInsert le x (insertionSort le xs)

end Chem

end
