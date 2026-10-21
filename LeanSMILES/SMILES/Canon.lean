import LeanSMILES.SMILES.Parse
import LeanSMILES.SMILES.Write
import Mathlib.Data.Fintype.Inv

/-!
# LeanSMILES.SMILES.Canon

A canonical atom order, and from it a canonical SMILES and a canonical
relabelling of the molecule.

**Refinement.** Each atom starts with an invariant that depends only on the
atom and its degree; atoms are ranked by it; then each atom's rank is refined
by the sorted multiset of (neighbour rank, bond kind) until the partition
stops splitting.  This is Morgan's iteration, Weisfeiler–Lehman colour
refinement, and the first stage of every canonical-SMILES algorithm
(Weininger 1989; Schneider, Sayle & Landrum 2015).  It is label-independent:
relabelling the atoms permutes the ranks.

**Tie-breaking.** Refinement can leave atoms tied — symmetric ones, but also
some that merely look alike.  RDKit individualizes one tied atom and never
looks back, which is fast but only canonical when the tie was a true
symmetry.  Here every tied atom of the lowest tied class is tried in turn,
each choice refined and recursively broken, and of all the discrete rankings
reached the one whose SMILES string is lexicographically smallest wins.  The
set of leaves is label-independent, so the minimum is too — the
nauty / InChI approach, at exponential worst-case cost, bounded by `budget`
leaves (beyond it the result is still a valid SMILES but no longer guaranteed
canonical).

**Relabelling.** `canonicalPerm` turns the winning ranks into an
`Equiv.Perm (Fin n)` (checked bijective by decision, inverted computably), and
`canonicalize` relabels the molecule by it — an isomorphism of molecular
graphs, `Molecule.canonicalize_iso` in `LeanSMILES.Chem.Graph`, by
`Molecule.relabelIso`.

Ranks are `Vector ℕ n` *data*, never functions: Lean eta-expands a definition
that returns a closure, so a rank-as-function would recompute every rank on
every lookup, and nested refinement rounds would compound that exponentially.
-/

namespace LeanSMILES.Molecule

variable {n : ℕ}

/-- A rank for each atom; equal ranks mean "not yet distinguished". -/
abbrev Ranks (n : ℕ) := Vector ℕ n

/-! ### Invariants and ranks -/

/-- Lexicographic order on invariant vectors. -/
def lexLt : List ℤ → List ℤ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

def kindIdx : BondKind → ℤ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .quadruple => 4
  | .aromatic => 5

/-- What an atom is, independent of its label: degree, element, hydrogens,
aromaticity, charge, isotope, whether it was bracketed, class, chirality mark. -/
def atomInvariant (m : Molecule n) (i : Fin n) : List ℤ :=
  let a := m.atom i
  [(m.degree i : ℤ), (a.atomicNumber : ℤ), (a.totalH : ℤ), (if a.aromatic then 1 else 0),
    a.charge, ((a.isotope.getD 0 : ℕ) : ℤ), (if a.explicitH.isSome then 1 else 0),
    ((a.atomClass.getD 0 : ℕ) : ℤ),
    (match a.chirality with
      | none => 0
      | some .anticlockwise => 1
      | some .clockwise => 2)]

/-- Rank each atom by how many atoms have a strictly smaller invariant, so
tied atoms share a rank and the ranks are label-independent. -/
def ranksOf (inv : Vector (List ℤ) n) : Ranks n :=
  Vector.ofFn fun i => ((List.finRange n).filter fun j => lexLt inv[j] inv[i]).length

def numClasses (rank : Ranks n) : ℕ := rank.toList.eraseDups.length

def isDiscrete (rank : Ranks n) : Bool := numClasses rank == n

/-- One refinement step: an atom's new invariant is its rank followed by the
sorted (neighbour rank, bond kind) pairs. Classes only ever split. -/
def refineOnce (m : Molecule n) (rank : Ranks n) : Ranks n :=
  ranksOf <| Vector.ofFn fun i =>
    let nbrs := (m.bondsAt i).map fun b => (((rank[b.other i] : ℕ) : ℤ), kindIdx b.kind)
    let sorted := nbrs.mergeSort fun p q => decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2))
    ((rank[i] : ℕ) : ℤ) :: sorted.flatMap fun p => [p.1, p.2]

/-- Refine until the partition stops splitting (`n` steps always suffice). -/
def refine (m : Molecule n) : ℕ → Ranks n → Ranks n
  | 0, r => r
  | fuel + 1, r =>
    let r' := refineOnce m r
    if numClasses r' ≤ numClasses r then r else refine m fuel r'

/-! ### Tie-breaking -/

/-- Put `a` strictly below the other atoms of its class, keeping every other
relation. -/
def individualize (rank : Ranks n) (a : Fin n) : Ranks n :=
  Vector.ofFn fun i => if i = a then 2 * rank[i] else 2 * rank[i] + 1

/-- The smallest rank shared by two or more atoms. -/
def firstTie (rank : Ranks n) : Option ℕ :=
  go (rank.toList.mergeSort fun a b => decide (a ≤ b))
where
  go : List ℕ → Option ℕ
    | a :: b :: rest => if a == b then some a else go (b :: rest)
    | _ => none

/-- Every discrete ranking reachable by individualizing, in turn, each atom of
the lowest tied class and refining — at most `budget` of them. Returns the
leaves and the budget left. -/
def leaves (m : Molecule n) : ℕ → ℕ → Ranks n → List (Ranks n) × ℕ
  | _, 0, _ => ([], 0)
  | 0, budget, r => ([r], budget - 1)
  | fuel + 1, budget, r =>
    if isDiscrete r then ([r], budget - 1) else
    match firstTie r with
    | none => ([r], budget - 1)
    | some c =>
      let tied := (List.finRange n).filter fun a => r[a] == c
      tied.foldl (init := (([] : List (Ranks n)), budget)) fun ⟨acc, b⟩ a =>
        if b = 0 then (acc, 0) else
        let ⟨ls, b'⟩ := leaves m fuel b (refine m n (individualize r a))
        (acc ++ ls, b')

/-! ### The canonical order -/

/-- Write with a rank vector. -/
def writeRanked (m : Molecule n) (rank : Ranks n) : String := m.write fun i => rank[i]

/-- The canonical ranks and the canonical SMILES: the lexicographically
smallest string over all tie-breaking leaves. -/
def canonical (m : Molecule n) (budget : ℕ := 1024) : Ranks n × String :=
  let r₀ := refine m n (ranksOf (Vector.ofFn m.atomInvariant))
  match (leaves m n budget r₀).1 with
  | [] => (r₀, m.writeRanked r₀)
  | l :: rest =>
    rest.foldl (init := (l, m.writeRanked l)) fun ⟨best, bs⟩ r =>
      let s := m.writeRanked r
      if s < bs then (r, s) else (best, bs)

def canonicalRanks (m : Molecule n) (budget : ℕ := 1024) : Ranks n := (m.canonical budget).1

def canonicalSmiles (m : Molecule n) (budget : ℕ := 1024) : String := (m.canonical budget).2

/-- The canonical ranks as a permutation of the atoms. The ranks of a discrete
ranking are exactly `0, …, n-1`; that is checked by decision, and the identity
is returned if it fails (it cannot, but the function is total). -/
def canonicalPerm (m : Molecule n) (budget : ℕ := 1024) : Equiv.Perm (Fin n) :=
  let rank := m.canonicalRanks budget
  let f : Fin n → Fin n := fun i => if h : rank[i] < n then ⟨rank[i], h⟩ else i
  if hf : Function.Bijective f then
    { toFun := f
      invFun := Fintype.bijInv hf
      left_inv := Fintype.leftInverse_bijInv hf
      right_inv := Fintype.rightInverse_bijInv hf }
  else Equiv.refl _

/-- The molecule with its atoms in canonical order. That this changes labels
and nothing else is `Molecule.canonicalize_iso` (`LeanSMILES.Chem.Graph`). -/
def canonicalize (m : Molecule n) (budget : ℕ := 1024) : Molecule n :=
  m.relabel (m.canonicalPerm budget)

theorem numBonds_canonicalize (m : Molecule n) (budget : ℕ := 1024) :
    (m.canonicalize budget).numBonds = m.numBonds :=
  m.numBonds_relabel _

end LeanSMILES.Molecule

namespace LeanSMILES

def Mol.canonicalSmiles (M : Mol) (budget : ℕ := 1024) : String := M.mol.canonicalSmiles budget

def Mol.canonicalize (M : Mol) (budget : ℕ := 1024) : Mol := ⟨M.n, M.mol.canonicalize budget⟩

def Mol.relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) : Mol := ⟨M.n, M.mol.relabel σ⟩

end LeanSMILES
