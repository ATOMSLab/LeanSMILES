/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Chem.Charge
public import LeanSMILES.Chem.Graph
public import LeanSMILES.SMILES.Parse
public import LeanSMILES.SMILES.Write
public import Mathlib.Data.Fintype.Inv
public import Mathlib.Data.String.Basic

/-!
# LeanSMILES.SMILES.Canon

A canonical atom order, and from it a canonical SMILES and a canonical
relabeling of the molecule.

The search reads a molecule as `MolData` — its atoms and its bond matrix,
which is the molecule up to the order and orientation of its bond list.  On
that data a relabeling acts literally, so an automorphism is an equality
`d.relabel γ = d` that can be checked, which is what makes pruning sound.

**Refinement.** Each atom starts with an invariant that depends only on the
atom and its degree; atoms are ranked by it; then each atom's rank is refined
by the sorted multiset of (neighbor rank, bond kind) until the partition
stops splitting.  This is Morgan's iteration, Weisfeiler–Lehman color
refinement, and the first stage of every canonical-SMILES algorithm
(Weininger 1989; Schneider, Sayle & Landrum 2015).  It is label-independent:
relabeling the atoms permutes the ranks.

**Tie-breaking.** Refinement can leave atoms tied — symmetric ones, but also
some that merely look alike.  RDKit individualizes one tied atom and never
looks back, which is fast but only canonical when the tie was a true
symmetry.  Here every tied atom of the lowest tied class is tried in turn,
each choice refined and recursively broken (`leavesAll`), and of all the
discrete rankings reached the one whose SMILES string is lexicographically
smallest wins.  The set of leaves is label-independent, so the minimum is
too.

**Pruning.** Visiting every leaf costs one leaf per element of the
automorphism group — 31 104 for tetra-*tert*-butylmethane, astronomical for a
dendrimer.  `search` is `leavesAll` with nauty's pruning: before exploring the
subtree under a tied atom `a`, it walks that subtree to its first leaf and
asks whether some already explored sibling `e` has a first leaf that is an
automorphic image of it.  The candidate automorphism (`automorphismOf`) is
*verified* — it must map the data to itself, fix the current ranking, and
send `e` to `a` (`isSymmetry`) — and then the whole subtree under `a` is the
image of the one under `e` and writes the same strings, so it is skipped.
Soundness rests on the check alone, never on the heuristic that proposed the
candidate; `LeanSMILES.SMILES.Canonicity` proves that `search` and
`leavesAll` have the same minimum, and that the minimum is label-independent.

**Stereochemistry.** The data carries each centre's configuration and each
stereo double bond's arrangement (at both ends), which a relabeling moves
along with their atoms, so automorphisms, pruning and the written marks all
respect them: the string a leaf writes has the `@`/`@@` and `/` `\` for the
order it writes (`LeanSMILES.SMILES.Write`), and the minimum over leaves picks
among them like any other character.  Whether an atom is a centre or the end
of a stereo double bond is part of its invariant.

A mark can be meaningless — `C[C@H](C)C`, whose mirror image is the same
molecule, or `C/C=C(/C)C`, whose flipped double bond is — and must
canonicalize like no mark.  A double bond's two ends are one unit
(`sameUnit`): mirrored and erased together.  `dropFake` erases such marks
first, by asking the canonical search itself: a mark goes when mirroring it
alone gives the same canonical string, and still does once the other such
marks are erased (`keptStereo`).  The second condition keeps the marks of
*cis,trans*-1,3,5-trimethylcyclohexane, where mirroring either of the two
alike centres alone is invisible but mirroring both is not.  Only centres
with two neighbors of the same rank can be affected, which the search is
asked about; the rest cost nothing.  Every step is label-independent, so
`dropFake` commutes with relabeling and canonicity survives
(`LeanSMILES.SMILES.Canonicity`).

**Redundant brackets.** `[CH](C)(C)C` is `CC(C)C`: brackets that only state
the hydrogen count the default-valence rule gives anyway are dropped first
(`normalizeBrackets`, `Atom.unbracket`) — which is also what lets a
meaningless `[C@H]` become the plain `C` it stands for.  `reduce` is both
steps; it is what the search sees.  `reduceAndCanonical` computes it together
with its canonical form, reusing the search the mark check ran first whenever
the check erases nothing — the usual case — and is proved to agree with
`reduce` and `reduce.canonical`.

**Relabeling.** A discrete ranking is a permutation, `permOfRanks`: atom `i`
goes to its position in rank order.  The string a ranking writes is the data
relabeled by it, as a molecule in normal form, written in its new atom order
(`writeRanked`); `canonicalSmiles` is by definition the canonical molecule
`canonicalize` written out.

Ranks are `Vector ℕ n` *data*, never functions: Lean eta-expands a definition
that returns a closure, so a rank-as-function would recompute every rank on
every lookup, and nested refinement rounds would compound that exponentially.
-/

@[expose] public section

namespace LeanSMILES

variable {n : ℕ}

/-- A rank for each atom; equal ranks mean "not yet distinguished". -/
abbrev Ranks (n : ℕ) := Vector ℕ n

/-- The atom without redundant brackets: when nothing but its hydrogen count
needs brackets and that count is what the default-valence rule gives for its
bond-order sum, the bare atom, the hydrogens implicit. The sum is asked for
only for a bracket atom (most atoms are not). -/
def Atom.unbracket (a : Atom) (orderSum : Unit → ℚ) : Atom :=
  let bare := { a with explicitH := none, implicitH := 0 }
  match a.explicitH with
  | some h =>
    if bare.canBeBare && h == Molecule.implicitHydrogens bare (orderSum ()) then
      { bare with implicitH := h }
    else a
  | none => a

/-! ### Ranks -/

/-- Lexicographic order on invariant vectors. -/
def lexLt : List ℤ → List ℤ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

/-- Rank each atom by how many atoms have a strictly smaller invariant, so
tied atoms share a rank and the ranks are label-independent. -/
def ranksOf (inv : Vector (List ℤ) n) : Ranks n :=
  Vector.ofFn fun i ↦ ((List.finRange n).filter fun j ↦ lexLt inv[j] inv[i]).length

/-- The number of distinct ranks. -/
def numClasses (rank : Ranks n) : ℕ := rank.toList.dedup.length

/-- Whether every atom has its own rank. -/
def isDiscrete (rank : Ranks n) : Bool := numClasses rank == n

/-- Put `a` strictly below the other atoms of its class, keeping every other
relation. -/
def individualize (rank : Ranks n) (a : Fin n) : Ranks n :=
  Vector.ofFn fun i ↦ if i = a then 2 * rank[i] else 2 * rank[i] + 1

/-- The smallest rank shared by two or more atoms. -/
def firstTie (rank : Ranks n) : Option ℕ :=
  (((List.finRange n).filter fun a ↦ 2 ≤ rank.toList.count rank[a]).map fun a ↦ rank[a]).min?

/-- The atoms of rank `c`. -/
def tiedAtoms (rank : Ranks n) (c : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun a ↦ rank[a] == c

/-- Atom `i`'s position in rank order: the number of atoms ranked strictly
below it. Ranks are discrete but not contiguous (tie-breaking doubles them),
so this, not the rank, is the permutation. -/
def rankPos (rank : Ranks n) (i : Fin n) : Fin n :=
  ⟨((List.finRange n).filter fun j ↦ decide (rank[j] < rank[i])).length, by
    calc ((List.finRange n).filter fun j ↦ decide (rank[j] < rank[i])).length
        < (List.finRange n).length :=
          List.length_filter_lt_length_iff_exists.mpr ⟨i, List.mem_finRange i, by simp⟩
      _ = n := List.length_finRange⟩

/-- Whether a table of positions takes every value: the tabulated function is
a permutation. -/
def isPermTable (pos : Vector (Fin n) n) : Bool :=
  (List.finRange n).all fun j ↦ (List.finRange n).any fun i ↦ pos[i] == j

lemma surjective_of_isPermTable {pos : Vector (Fin n) n} (h : isPermTable pos = true) :
    Function.Surjective fun i : Fin n ↦ pos[i] := by
  intro j
  simp only [isPermTable, List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and,
    true_implies, beq_iff_eq] at h
  exact h j

/-- The preimage of `j` under a permutation table, found by lookup. -/
def invTable (pos : Vector (Fin n) n) (j : Fin n) : Fin n :=
  ((List.finRange n).find? fun i ↦ pos[i] == j).getD j

lemma getElem_invTable {pos : Vector (Fin n) n} (h : isPermTable pos = true) (j : Fin n) :
    pos[invTable pos j] = j := by
  obtain ⟨i, hi⟩ := surjective_of_isPermTable h j
  have hs : ((List.finRange n).find? fun i ↦ pos[i] == j).isSome :=
    List.find?_isSome.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩
  obtain ⟨i', hi'⟩ := Option.isSome_iff_exists.mp hs
  have e : invTable pos j = i' := by
    unfold invTable
    rw [hi', Option.getD_some]
  have h' := List.find?_some hi'
  rw [← e] at h'
  simpa using h'

/-- A ranking as a permutation of the atoms, `rankPos`, when that is a
bijection (which a discrete ranking guarantees); the identity otherwise. Both
directions are tabulated, so applying it is O(1) and building it is O(n²). -/
def permOfRanks (rank : Ranks n) : Equiv.Perm (Fin n) :=
  let pos : Vector (Fin n) n := Vector.ofFn (rankPos rank)
  if h : isPermTable pos = true then
    let inv : Vector (Fin n) n := Vector.ofFn (invTable pos)
    { toFun := fun i ↦ pos[i]
      invFun := fun j ↦ inv[j]
      left_inv := fun i ↦ (Finite.injective_iff_surjective.mpr (surjective_of_isPermTable h))
        (by simp only [inv, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
            exact getElem_invTable h _)
      right_inv := fun j ↦ by
        simp only [inv, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
        exact getElem_invTable h j }
  else Equiv.refl _

/-- A numeric code for a bond kind, for invariant vectors. -/
def kindIdx : BondKind → ℤ
  | .single => 1
  | .double => 2
  | .triple => 3
  | .quadruple => 4
  | .aromatic => 5

/-- Lexicographic order on (neighbor rank, bond kind) pairs. -/
def pairLE (p q : ℤ × ℤ) : Bool := decide (p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 ≤ q.2))

namespace MolData

variable (d : MolData n)

/-! ### Invariants and refinement -/

/-- Heavy-atom degree: the number of bonds in the atom's row. -/
def degree (i : Fin n) : ℕ := ((List.finRange n).filter fun j ↦ d.bonds i j != 0).length

/-- What an atom is, independent of its label: degree, element, hydrogens,
aromaticity, charge, isotope, whether it was bracketed, class, a
non-tetrahedral chirality mark, whether it is a tetrahedral centre or the end
of a stereo double bond. -/
def atomInvariant (i : Fin n) : List ℤ :=
  let a := d.atoms[i]
  [(d.degree i : ℤ), (a.atomicNumber : ℤ), (a.totalH : ℤ), (if a.aromatic then 1 else 0),
    a.charge, ((a.isotope.getD 0 : ℕ) : ℤ), (if a.explicitH.isSome then 1 else 0),
    ((a.atomClass.getD 0 : ℕ) : ℤ),
    (((a.chirality.map Chirality.code).getD 0 : ℕ) : ℤ),
    (((d.stereo[i].map Stereo.code).getD 0 : ℕ) : ℤ)]

/-- The sorted (neighbor rank, bond kind) pairs of an atom. -/
def neighborInvariant (rank : Ranks n) (i : Fin n) : List (ℤ × ℤ) :=
  ((List.finRange n).filterMap fun j ↦
    (d.bonds.kindAt i j).map fun k ↦ (((rank[j] : ℕ) : ℤ), kindIdx k)).mergeSort pairLE

/-- The invariant vector one refinement step ranks by: an atom's rank followed
by its sorted (neighbor rank, bond kind) pairs. -/
def refineInvariant (rank : Ranks n) : Vector (List ℤ) n :=
  Vector.ofFn fun i ↦
    ((rank[i] : ℕ) : ℤ) :: (d.neighborInvariant rank i).flatMap fun p ↦ [p.1, p.2]

/-- One refinement step. Classes only ever split. -/
def refineOnce (rank : Ranks n) : Ranks n := ranksOf (d.refineInvariant rank)

/-- Refine until the partition stops splitting (`n` steps always suffice). -/
def refine : ℕ → Ranks n → Ranks n
  | 0, r => r
  | fuel + 1, r =>
    let r' := d.refineOnce r
    if numClasses r' ≤ numClasses r then r else refine fuel r'

/-- The ranks every search starts from: the atom invariants, refined. -/
def initialRanks : Ranks n := d.refine n (ranksOf (Vector.ofFn d.atomInvariant))

/-! ### Tie-breaking -/

/-- Every ranking reachable by individualizing, in turn, each atom of the
lowest tied class and refining, through `fuel` levels of tie-breaking. With
`fuel = n` every leaf is discrete (`Canonicity`). This is the specification;
`search` is what runs. -/
def leavesAll : ℕ → Ranks n → List (Ranks n)
  | 0, r => [r]
  | fuel + 1, r =>
    if isDiscrete r then [r] else
    match firstTie r with
    | none => [r]
    | some c => (tiedAtoms r c).flatMap fun a ↦ leavesAll fuel (d.refine n (individualize r a))

/-- The leftmost leaf of `leavesAll`: always the first tied atom. -/
def firstLeaf : ℕ → Ranks n → Ranks n
  | 0, r => r
  | fuel + 1, r =>
    if isDiscrete r then r else
    match firstTie r with
    | none => r
    | some c =>
      match tiedAtoms r c with
      | [] => r
      | a :: _ => firstLeaf fuel (d.refine n (individualize r a))

/-- Whether `γ` maps the data to itself: an automorphism of the molecule,
configurations included. -/
def isAutomorphism (γ : Equiv.Perm (Fin n)) : Bool :=
  let g : Vector (Fin n) n := Vector.ofFn γ
  (List.finRange n).all fun i ↦ d.atoms[g[i]] == d.atoms[i] &&
    decide (d.stereo[g[i]] = d.stereo[i].map (Stereo.map γ)) &&
    (List.finRange n).all fun j ↦ d.bonds g[i] g[j] == d.bonds i j

/-- Whether `γ` certifies that the subtree under tied atom `a` is the image of
the subtree under `e`: an automorphism that fixes the ranking `r` and sends
`e` to `a`. -/
def isSymmetry (r : Ranks n) (e a : Fin n) (γ : Equiv.Perm (Fin n)) : Bool :=
  γ e == a && relabelVec γ r == r && d.isAutomorphism γ

/-- Explore the subtrees under the tied atoms `pending` in turn, with `sub`
searching a subtree and `first` finding its first leaf. `reps` records each
explored atom with the permutation of its first leaf; an atom whose first
leaf is a verified automorphic image of a representative's — the candidate
carries the representative's rank order onto the new leaf's — is skipped. -/
def exploreChildren (r : Ranks n) (sub : Ranks n → List (Ranks n)) (first : Ranks n → Ranks n) :
    List (Fin n) → List (Fin n × Equiv.Perm (Fin n)) → List (Ranks n) → List (Ranks n)
  | [], _, acc => acc
  | a :: pending, reps, acc =>
    let ra := d.refine n (individualize r a)
    let πa := permOfRanks (first ra)
    if reps.any fun p ↦ d.isSymmetry r p.1 a (p.2.trans πa.symm) then
      exploreChildren r sub first pending reps acc
    else
      exploreChildren r sub first pending ((a, πa) :: reps) (acc ++ sub ra)

/-- `leavesAll` with automorphism pruning: the leaves it returns are leaves of
`leavesAll`, and every leaf of `leavesAll` writes the same string as one of
them (`Canonicity`). -/
def search : ℕ → Ranks n → List (Ranks n)
  | 0, r => [r]
  | fuel + 1, r =>
    if isDiscrete r then [r] else
    match firstTie r with
    | none => [r]
    | some c => d.exploreChildren r (search fuel) (d.firstLeaf fuel) (tiedAtoms r c) [] []

/-! ### The canonical order -/

/-- The string a ranking writes: the data relabeled into rank order, as a
molecule in normal form, written in its new atom order. -/
def writeRanked (rank : Ranks n) : String := (d.relabel (permOfRanks rank)).toMolecule.toSmiles

/-- The canonical SMILES — the lexicographically smallest string over the
tie-breaking leaves — and a leaf that writes it. -/
def canonical : Ranks n × String :=
  let r₀ := d.initialRanks
  let ls := d.search n r₀
  match (ls.map d.writeRanked).min? with
  | none => (r₀, d.writeRanked r₀)
  | some s => ((ls.find? fun r ↦ d.writeRanked r == s).getD r₀, s)

/-- The data relabeled into canonical order, as a molecule in normal form. -/
def canonicalMolecule : Molecule n := (d.relabel (permOfRanks d.canonical.1)).toMolecule

/-! ### Meaningless marks -/

/-- The data with the configurations erased where `p` holds. -/
def eraseStereo (p : Fin n → Bool) : MolData n :=
  { d with stereo := Vector.ofFn fun i ↦ if p i then none else d.stereo[i] }

/-- Whether `i` and `j` carry one configuration: the same atom, or the two ends
of a stereo double bond, which carry the same arrangement. Mirroring and
erasing act on such a unit as a whole. -/
def sameUnit (i j : Fin n) : Bool :=
  j == i || (d.stereo[i].any Stereo.isPlanar && decide (d.stereo[j] = d.stereo[i]))

/-- The data with the configuration of `i`'s unit mirrored. -/
def mirrorAt (i : Fin n) : MolData n :=
  { d with
    stereo := Vector.ofFn fun j ↦
      if d.sameUnit i j then d.stereo[j].map Stereo.mirror else d.stereo[j] }

/-- Whether the configuration at `i` is its own mirror image (two alike
ligands, as two hydrogens): a mark that cannot mean anything. -/
def selfMirror (i : Fin n) : Bool := d.stereo[i].any fun t ↦ decide (t.mirror = t)

/-- Whether two neighbors of `i` have the same rank. Only then can mirroring
the unit of `i` give an isomorphic molecule (an automorphism doing it must
permute the ligands at one of its atoms oddly, or a power of it must). -/
def tiedNeighbors (r : Ranks n) (i : Fin n) : Bool :=
  !decide (((List.finRange n).filter fun j ↦ d.bonds i j != 0).map fun j ↦ r[j]).Nodup

/-- An atom whose mark might be meaningless: some atom of its unit has two
neighbors of the same rank. -/
def candidate (r : Ranks n) (i : Fin n) : Bool :=
  d.stereo[i].isSome && (List.finRange n).any fun j ↦ d.sameUnit i j && d.tiedNeighbors r j

/-- Whether mirroring `i` alone leaves the canonical string `s` — the data's
own — unchanged: the mirrored molecule is the same molecule. -/
def mirrorInvisible (s : String) (i : Fin n) : Bool := (d.mirrorAt i).canonical.2 == s

/-- The candidates whose mirroring alone is invisible, given the data's
canonical string `s` and ranks `r`. -/
def invisible (s : String) (r : Ranks n) : Vector Bool n :=
  Vector.ofFn fun i ↦ d.candidate r i && d.mirrorInvisible s i

/-- Whether the invisible unit of `i` stays invisible once the other invisible
units `D` are erased: then its mark carries nothing the rest do not. -/
def droppable (D : Vector Bool n) (i : Fin n) : Bool :=
  D[i] &&
    let dA := d.eraseStereo fun j ↦ D[j] && !d.sameUnit i j
    dA.mirrorInvisible dA.canonical.2 i

/-- The configurations left once the droppable marks are erased. -/
def stripStereo : Vector (Option (Stereo n)) n :=
  if (List.finRange n).all fun i ↦ d.stereo[i].isNone then d.stereo else
  let r := d.initialRanks
  if (List.finRange n).any (d.candidate r) then
    (d.eraseStereo (d.droppable (d.invisible d.canonical.2 r))).stereo
  else d.stereo

/-- The configurations worth writing: neither their own mirror image nor
droppable. -/
def keptStereo : Vector (Option (Stereo n)) n := (d.eraseStereo d.selfMirror).stripStereo

/-- The data with its meaningless marks erased. -/
def dropFake : MolData n := { d with stereo := d.keptStereo }

/-! ### Redundant brackets -/

/-- The bond orders at `i`, summed. -/
def orderSum (i : Fin n) : ℚ := ((List.finRange n).map fun j ↦ d.bonds i j).sum

/-- The data with redundant brackets dropped (`Atom.unbracket`). -/
def normalizeBrackets : MolData n :=
  { d with atoms := Vector.ofFn fun i ↦ d.atoms[i].unbracket fun _ ↦ d.orderSum i }

/-- What is canonicalized: the data without redundant brackets, then without
meaningless marks. -/
def reduce : MolData n := d.normalizeBrackets.dropFake

/-- `reduce` and its canonical form, sharing work: the meaningless-mark check
canonicalizes the data (marks of their own mirror image erased) before it
decides anything, and when it then erases nothing, that data is `reduce` and
its canonical form is reused rather than searched for again
(`reduceAndCanonical_fst`, `reduceAndCanonical_snd`). -/
def reduceAndCanonical : MolData n × (Ranks n × String) :=
  let nb := d.normalizeBrackets
  let d₀ := nb.eraseStereo nb.selfMirror
  if (List.finRange n).all fun i ↦ d₀.stereo[i].isNone then (d₀, d₀.canonical) else
  let r := d₀.initialRanks
  if (List.finRange n).any (d₀.candidate r) then
    let c := d₀.canonical
    let drop : Vector Bool n := Vector.ofFn (d₀.droppable (d₀.invisible c.2 r))
    if (List.finRange n).all fun i ↦ !drop[i] then (d₀, c)
    else
      let d₁ := d₀.eraseStereo fun i ↦ drop[i]
      (d₁, d₁.canonical)
  else (d₀, d₀.canonical)

/-- The canonical molecule writes the canonical string. -/
theorem writeRanked_canonical : d.writeRanked d.canonical.1 = d.canonical.2 := by
  simp only [canonical]
  split
  · rfl
  · rename_i s hmin
    obtain ⟨r, hr, hrs⟩ := List.mem_map.mp (List.min?_mem hmin)
    have hfind : ((d.search n d.initialRanks).find? fun r ↦ d.writeRanked r == s).isSome :=
      List.find?_isSome.mpr ⟨r, hr, by simp [hrs]⟩
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hfind
    have h := List.find?_some hr'
    simp only [beq_iff_eq] at h
    rw [hr']
    exact h

/-- Erasing nowhere changes nothing. -/
lemma eraseStereo_of_forall_false {p : Fin n → Bool} (h : ∀ i, p i = false) :
    d.eraseStereo p = d := by
  cases d
  simp only [eraseStereo, h, Bool.false_eq_true, if_false, MolData.mk.injEq, true_and]
  ext i hi
  simp

/-- The data `reduceAndCanonical` returns is `reduce`. -/
theorem reduceAndCanonical_fst : d.reduceAndCanonical.1 = d.reduce := by
  simp only [reduceAndCanonical, reduce, dropFake, keptStereo, stripStereo]
  set d₀ := d.normalizeBrackets.eraseStereo d.normalizeBrackets.selfMirror
  split_ifs with h₁ h₂ h₃
  · rfl
  · have hf : ∀ i, d₀.droppable (d₀.invisible d₀.canonical.2 d₀.initialRanks) i = false := by
      intro i
      have := List.all_eq_true.mp h₃ i (List.mem_finRange i)
      simpa using this
    rw [eraseStereo_of_forall_false _ hf]
    rfl
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rfl
  · rfl

/-- The canonical form `reduceAndCanonical` returns is that of its data. -/
lemma reduceAndCanonical_snd_eq : d.reduceAndCanonical.2 = d.reduceAndCanonical.1.canonical := by
  simp only [reduceAndCanonical]
  split_ifs <;> rfl

/-- The canonical form `reduceAndCanonical` returns is `reduce`'s. -/
theorem reduceAndCanonical_snd : d.reduceAndCanonical.2 = d.reduce.canonical := by
  rw [reduceAndCanonical_snd_eq, reduceAndCanonical_fst]

end MolData

namespace Molecule

variable (m : Molecule n)

/-- The molecule without redundant brackets and meaningless tetrahedral marks
(`MolData.reduce`): what canonicalization writes. -/
def reduce : Molecule n :=
  { m with atoms := m.toMolData.normalizeBrackets.atoms
           stereo := m.toMolData.normalizeBrackets.keptStereo }

lemma toMolData_reduce : m.reduce.toMolData = m.toMolData.reduce := rfl

/-- The canonical ranks. -/
def canonicalRanks : Ranks n := m.toMolData.reduceAndCanonical.2.1

/-- The canonical SMILES string. -/
def canonicalSmiles : String := m.toMolData.reduceAndCanonical.2.2

/-- The canonical ranks as a permutation of the atoms. -/
def canonicalPerm : Equiv.Perm (Fin n) := permOfRanks m.canonicalRanks

/-- The molecule with its atoms in canonical order, in normal form, without
redundant brackets and meaningless marks. That this changes labels and nothing
else is `canonicalizeIso`; that writing it out gives the canonical SMILES is
`toSmiles_canonicalize`. -/
def canonicalize : Molecule n :=
  let rc := m.toMolData.reduceAndCanonical
  (rc.1.relabel (permOfRanks rc.2.1)).toMolecule

/-- The canonical molecule is the reduced molecule relabeled into canonical
order, normalized. -/
theorem canonicalize_eq_normalize_relabel :
    m.canonicalize = (m.reduce.relabel m.canonicalPerm).normalize := by
  rw [← toMolecule_toMolData, toMolData_relabel, toMolData_reduce]
  simp only [canonicalize, canonicalPerm, canonicalRanks, MolData.reduceAndCanonical_fst]

/-- The canonical molecule, written in its atom order, is the canonical SMILES. -/
theorem toSmiles_canonicalize : m.canonicalize.toSmiles = m.canonicalSmiles := by
  simp only [canonicalize, canonicalSmiles, MolData.reduceAndCanonical_fst,
    MolData.reduceAndCanonical_snd]
  exact m.toMolData.reduce.writeRanked_canonical

lemma numBonds_canonicalize : m.canonicalize.numBonds = m.numBonds := by
  rw [canonicalize_eq_normalize_relabel, numBonds_normalize, numBonds_relabel]
  rfl

lemma graph_canonicalize : m.canonicalize.graph = (m.relabel m.canonicalPerm).graph := by
  rw [canonicalize_eq_normalize_relabel, graph_normalize]
  rfl

/-- Canonicalization changes labels and nothing else: the canonical molecule's
graph is isomorphic to the original's. -/
def canonicalizeIso : SimpleGraph.Iso m.graph m.canonicalize.graph :=
  m.graph_canonicalize ▸ m.relabelIso m.canonicalPerm

/-! ### Chemistry predicates survive the pipeline

`chargesConsistent` (`LeanSMILES.Chem.Charge`) is not an invariant of
`Molecule` and the pipeline carries no chemistry; but it is a property of the
atoms alone, and canonicalization only permutes them. -/

lemma chargesConsistent_normalize : m.normalize.chargesConsistent ↔ m.chargesConsistent :=
  Iff.rfl

/-- Dropping a redundant bracket keeps the charge, which is zero. -/
lemma _root_.LeanSMILES.Atom.chargeConsistent_unbracket (a : Atom) (q : Unit → ℚ) :
    (a.unbracket q).chargeConsistent ↔ a.chargeConsistent := by
  unfold Atom.unbracket
  split
  · dsimp only
    split_ifs with h
    · have h0 : a.charge = 0 := by simp_all [Atom.canBeBare]
      exact iff_of_true (Atom.chargeConsistent_of_charge_eq_zero h0)
        (Atom.chargeConsistent_of_charge_eq_zero h0)
    · exact Iff.rfl
  · exact Iff.rfl

lemma chargesConsistent_reduce : m.reduce.chargesConsistent ↔ m.chargesConsistent := by
  refine forall_congr' fun i ↦ ?_
  simp only [reduce, atom, MolData.normalizeBrackets, Fin.getElem_fin, Vector.getElem_ofFn]
  exact Atom.chargeConsistent_unbracket _ _

/-- Canonicalization neither creates nor removes an inconsistent charge. -/
theorem chargesConsistent_canonicalize :
    m.canonicalize.chargesConsistent ↔ m.chargesConsistent := by
  rw [canonicalize_eq_normalize_relabel, chargesConsistent_normalize, chargesConsistent_relabel,
    chargesConsistent_reduce]

end Molecule

/-- The canonical SMILES of a bundled molecule. -/
def Mol.canonicalSmiles (M : Mol) : String := M.mol.canonicalSmiles

/-- A bundled molecule with its atoms in canonical order, in normal form. -/
def Mol.canonicalize (M : Mol) : Mol := ⟨M.n, M.mol.canonicalize⟩

/-- Relabel the atoms of a bundled molecule. -/
def Mol.relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) : Mol := ⟨M.n, M.mol.relabel σ⟩

theorem Mol.chargesConsistent_relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    (M.relabel σ).chargesConsistent ↔ M.chargesConsistent :=
  M.mol.chargesConsistent_relabel σ

theorem Mol.chargesConsistent_canonicalize (M : Mol) :
    M.canonicalize.chargesConsistent ↔ M.chargesConsistent :=
  M.mol.chargesConsistent_canonicalize

end LeanSMILES
