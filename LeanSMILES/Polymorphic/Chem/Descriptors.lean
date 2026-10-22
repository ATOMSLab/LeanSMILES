module

public import LeanSMILES.Polymorphic.Chem.Graph
public import LeanSMILES.Polymorphic.Decimal

/-!
# Molecules — Descriptors

RDKit-style descriptors: molecular weight (exact, from decimal atomic masses), formula,
H-bond donors, ring count, rotatable bonds and minimum degree.
-/

@[expose] public section

namespace Chem

/-! ## Descriptors (RDKit-style) -/

open Primitives (Decimal)

/-- Standard atomic weights (the values RDKit uses), as exact decimals. `0` for elements
not in the table. -/
def atomicMass : Nat → Decimal
  | 1 => ⟨1008, -3⟩
  | 3 => ⟨6941, -3⟩
  | 5 => ⟨10812, -3⟩
  | 6 => ⟨12011, -3⟩
  | 7 => ⟨14007, -3⟩
  | 8 => ⟨15999, -3⟩
  | 9 => ⟨18998, -3⟩
  | 11 => ⟨22990, -3⟩
  | 12 => ⟨24305, -3⟩
  | 13 => ⟨26982, -3⟩
  | 14 => ⟨28086, -3⟩
  | 15 => ⟨30974, -3⟩
  | 16 => ⟨32067, -3⟩
  | 17 => ⟨35453, -3⟩
  | 19 => ⟨39098, -3⟩
  | 20 => ⟨40078, -3⟩
  | 26 => ⟨55845, -3⟩
  | 29 => ⟨63546, -3⟩
  | 30 => ⟨65390, -3⟩
  | 34 => ⟨78960, -3⟩
  | 35 => ⟨79904, -3⟩
  | 50 => ⟨118710, -3⟩
  | 53 => ⟨126904, -3⟩
  | 80 => ⟨200590, -3⟩
  | _ => 0

namespace Molecule

/-- Mass of atom `i` with its hydrogens. An isotope label replaces the average mass by
the mass number. -/
def atomMass (m : Molecule) (i : Nat) : Decimal :=
  let a := m.atom i
  let heavy := match a.isotope with
    | some k => ⟨k, 0⟩
    | none => atomicMass a.element
  heavy + Decimal.nsmul (m.totalH i) (atomicMass 1)

/-- Average molecular weight, exactly (RDKit's `Descriptors.MolWt`). -/
def molecularWeightExact (m : Molecule) : Decimal :=
  (List.range m.atoms.size).foldl (fun acc i => acc + m.atomMass i) 0

/-- Average molecular weight in any `Scalar` (exact over `ℝ`). -/
def molecularWeight {α : Type} [Primitives.Scalar α] (m : Molecule) : α :=
  m.molecularWeightExact.toScalar

def heavyAtomCount (m : Molecule) : Nat := (m.atoms.toList.filter (·.element != 1)).length

def hydrogenCount (m : Molecule) : Nat :=
  (List.range m.atoms.size).foldl (fun acc i => acc + m.totalH i) 0 +
    (m.atoms.toList.filter (·.element == 1)).length

/-- Hill formula: `C`, then `H`, then the other elements alphabetically (alphabetically
throughout if there is no carbon). -/
def formula (m : Molecule) : String :=
  let counts : List (String × Nat) :=
    (m.atoms.toList.map (symbolOf ·.element)).eraseDups.map fun sym =>
      (sym, (m.atoms.toList.filter (symbolOf ·.element == sym)).length)
  let counts := (counts.filter (·.1 != "H")) ++
    (let h := m.hydrogenCount; if h = 0 then [] else [("H", h)])
  let hasC := counts.any (·.1 == "C")
  let rank := fun (sym : String) =>
    if hasC && sym == "C" then "0" else if hasC && sym == "H" then "1" else "2" ++ sym
  let sorted := counts.mergeSort fun a b => decide (rank a.1 ≤ rank b.1)
  String.join (sorted.map fun (sym, k) => if k = 1 then sym else s!"{sym}{k}")

/-- Connected components (`.`-separated fragments), by repeated breadth-first search. -/
def componentLabels (m : Molecule) : Array Nat :=
  let n := m.atoms.size
  let adj := m.adjacency.map (·.map Prod.fst)
  let rec spread : Nat → List Nat → Nat → Array Nat → Array Nat
    | 0, _, _, labels => labels
    | _, [], _, labels => labels
    | fuel + 1, v :: rest, c, labels =>
      let new := (adj.getD v []).filter fun u => labels.getD u 0 == 0
      spread fuel (rest ++ new) c (new.foldl (fun l u => l.setIfInBounds u c) labels)
  ((List.range n).foldl (fun (labels, c) v =>
      if labels.getD v 0 != 0 then (labels, c)
      else (spread (n * n + 1) [v] (c + 1) (labels.setIfInBounds v (c + 1)), c + 1))
    (Array.replicate n 0, 0)).1

def componentCount (m : Molecule) : Nat := (m.componentLabels.toList.eraseDups).length

/-- Number of independent rings, `bonds − atoms + components` (equals RDKit's SSSR
`RingCount`). -/
def ringCount (m : Molecule) : Nat := m.bonds.size + m.componentCount - m.atoms.size

/-- Lipinski H-bond donors (RDKit's `NumHDonors`): N with hydrogens (neutral or +1), O
or S with exactly one hydrogen and no charge, aromatic `[nH]`. -/
def isHDonor (m : Molecule) (i : Nat) : Bool :=
  let a := m.atom i
  let h := m.totalH i
  (a.element == 7 && !a.aromatic && h > 0 && (a.charge == 0 || a.charge == 1)) ||
  ((a.element == 8 || a.element == 16) && h == 1 && a.charge == 0) ||
  (a.element == 7 && a.aromatic && h == 1 && a.charge == 0)

def hDonorCount (m : Molecule) : Nat := ((List.range m.atoms.size).filter m.isHDonor).length

def hasTripleBond (m : Molecule) (i : Nat) : Bool :=
  (m.neighbors i).any (·.2 == .triple)

/-- `C` with three neighbours of element `z` (CF₃, CCl₃, CBr₃). -/
def isTrihalomethyl (m : Molecule) (i : Nat) (z : Nat) : Bool :=
  (m.atom i).element == 6 && ((m.neighbors i).filter fun (u, _) => (m.atom u).element == z).length == 3

/-- `C` bonded to three methyl groups (the centre of a t-butyl group). -/
def isTertButylCenter (m : Molecule) (i : Nat) : Bool :=
  (m.atom i).element == 6 &&
    ((m.neighbors i).filter fun (u, _) =>
      (m.atom u).element == 6 && m.degree u == 1 && m.totalH u == 3).length == 3

/-- The carbon of an amide, ester, thioester or amidine group: degree 3, a double bond to
N, O or S (or to N⁺), and a single non-ring bond to a heteroatom. -/
def isAcylCarbon (m : Molecule) (i : Nat) : Bool :=
  let nbrs := (m.neighbors i)
  (m.atom i).element == 6 && m.degree i == 3 &&
    nbrs.any (fun (u, b) => b == .double && [7, 8, 16].contains (m.atom u).element) &&
    nbrs.any (fun (u, b) => b == .single && !m.bondInRingBetween i u &&
      ((m.atom u).element == 7 || (m.atom u).element == 8 ||
        ((m.atom u).element == 16 && m.degree u != 1)))

/-- A heteroatom single-bonded (outside rings) to an acyl carbon. -/
def isAcylHeteroatom (m : Molecule) (i : Nat) : Bool :=
  let a := m.atom i
  (a.element == 7 || a.element == 8 || (a.element == 16 && m.degree i != 1)) &&
    (m.neighbors i).any fun (u, b) => b == .single && !m.bondInRingBetween i u && m.isAcylCarbon u

/-- Right-hand atom of RDKit's strict rotatable-bond pattern. -/
def rotorEnd (m : Molecule) (i : Nat) : Bool :=
  !m.hasTripleBond i && m.degree i > 1 &&
    !m.isTrihalomethyl i 9 && !m.isTrihalomethyl i 17 && !m.isTrihalomethyl i 35 &&
    !m.isTertButylCenter i

/-- Left-hand atom: additionally not part of an amide/ester-like linkage. -/
def rotorStart (m : Molecule) (i : Nat) : Bool :=
  m.rotorEnd i && !m.isAcylCarbon i && !m.isAcylHeteroatom i

/-- RDKit's `NumRotatableBonds` with the default *strict* pattern: single (or aromatic),
non-ring bonds between non-terminal atoms that are not in triple bonds, excluding CF₃,
CCl₃, CBr₃ and t-butyl rotors and amide, ester, thioester and amidine C–X bonds. -/
def rotatableBondCount (m : Molecule) : Nat :=
  (m.bonds.toList.zipIdx.filter fun (b, k) =>
    (b.order == .single || b.order == .aromatic) && !m.bondInRing k &&
    ((m.rotorStart b.src && m.rotorEnd b.dst) || (m.rotorStart b.dst && m.rotorEnd b.src))).length

/-- Smallest number of heavy-atom neighbours (DeepChem's "Minimum Degree"). -/
def minDegree (m : Molecule) : Nat :=
  (List.range m.atoms.size).foldl (fun acc i => min acc (m.degree i)) m.atoms.size

end Molecule

/-- A summary of the computed descriptors. -/
structure Descriptors where
  formula : String
  molecularWeight : Decimal
  heavyAtoms : Nat
  hDonors : Nat
  rings : Nat
  rotatableBonds : Nat
  minDegree : Nat
  deriving Repr

def Molecule.descriptors (m : Molecule) : Descriptors :=
  { formula := m.formula, molecularWeight := m.molecularWeightExact
    heavyAtoms := m.heavyAtomCount, hDonors := m.hDonorCount, rings := m.ringCount
    rotatableBonds := m.rotatableBondCount, minDegree := m.minDegree }

end Chem

end
