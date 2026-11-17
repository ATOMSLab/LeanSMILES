/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Kekulize
public import LeanSMILES.SMILES.Parse

/-!
# LeanSMILES.Aromaticity.Perceive

Aromaticity perception, RDKit's default model

Decides which rings are aromatic on a Kekulé structure and marks their bonds
`aromatic` (`Aromaticity.cpp`, `aromaticityHelper`, Release_2026_09_1). Ported
from `tools/rdkit_reference/aromaticity_ref.py` (`assign_radicals`, `set_aromaticity`).

1. **Electrons per atom.** Each ring atom gets a donor type: how many π electrons
   it can put into the ring (benzene C: 1, pyrrole NH / furan O: 2, ring C=O: 0).
2. **Candidate rings.** A ring is a candidate if every atom can be aromatic.
3. **Hückel 4n + 2**, first on single rings, then on fused groups. Rings are
   "fused" here only if they share exactly one bond and both have ≤ 24 bonds;
   groups of up to 6 rings are tried (`applyHuckelToFused`, `Aromaticity.cpp:334`).
   When a group passes, every bond that occurs once in the group becomes aromatic.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- How many π electrons a ring atom can give to an aromatic ring (RDKit's `ElectronDonorType`). -/
inductive Donor where
  /-- An empty p orbital: no electrons, yet it may be aromatic (the C of a ring C=O). -/
  | vacant
  /-- One electron, as a benzene carbon. -/
  | one
  /-- A lone pair, as pyrrole NH or furan O. -/
  | two
  /-- One or two electrons. -/
  | oneOrTwo
  /-- Any count, read as one or two; `huckel` allows at most one such atom in a ring system. -/
  | any
  /-- No electrons to give: the atom cannot be aromatic. -/
  | none
  deriving BEq, Repr, Inhabited

/-- Fewest and most π electrons of each donor type (`getMinMaxAtomElecs`). -/
def Donor.range : Donor → Nat × Nat
  | .any | .oneOrTwo => (1, 2) | .one => (1, 1) | .two => (2, 2) | .none | .vacant => (0, 0)

namespace Work

/-- π electrons atom `i` could donate, or -1 (`countAtomElec`, `Aromaticity.cpp:656`). -/
def countAtomElec (m : Work) (i : Nat) : Int := Id.run do
  let a := m.atoms[i]!
  let dv : Int := defaultValence a.z
  if dv ≤ 1 then return -1
  let deg : Int := m.degree i + m.cachedTotalHs i
  if 3 < deg then return -1
  let nlp := max ((outerElectrons a.z : Int) - dv - a.charge) 0
  let res := dv - deg + nlp - a.radicals
  if 1 < res && 1 < (m.cachedValence i : Int) - m.degree i then return 1
  return res

/-- Atom across the first non-ring double/triple bond of atom `i`
(`incidentNonCyclicMultipleBond`, `Aromaticity.cpp:234`). -/
def exocyclicMultiple? (m : Work) (ringBonds : List Nat) (i : Nat) : Option Nat :=
  ((m.neighbors i).find? fun (k, _) ↦ !ringBonds.contains k && isMultiple m.bonds[k]!.kind).map
    (·.2)

/-- Donor type of atom `i` (`getAtomDonorTypeArom`, `Aromaticity.cpp:581`). -/
def donorType (m : Work) (ringBonds : List Nat) (i : Nat) : Donor := Id.run do
  let a := m.atoms[i]!
  let mut nelec := m.countAtomElec i
  let who := m.exocyclicMultiple? ringBonds i
  let pullsElectrons := match who with
    | some j => moreElectronegative m.atoms[j]!.z a.z
    | none => false
  if nelec < 0 then return .none
  if nelec == 0 then
    if who.isSome then return .vacant
    if (m.bondsOf i).any fun k ↦ ringBonds.contains k && isMultiple m.bonds[k]!.kind then
      return .one
    return .none
  if nelec == 1 then
    if who.isSome then return if pullsElectrons then .vacant else .one
    -- any multiple bond at all
    if m.cachedValence i != m.degree i + a.explicitHs then return .one
    if a.charge == 1 then return .vacant
    return .none
  if pullsElectrons then nelec := nelec - 1
  return if nelec % 2 == 1 then .one else .two

/-- Can atom `i` be in an aromatic ring? (`isAtomCandForArom`, `Aromaticity.cpp:440`) -/
def isAromaticCandidate (m : Work) (i : Nat) (d : Donor) : Bool := Id.run do
  let a := m.atoms[i]!
  let z := a.z
  if 18 < z && z != 34 && z != 52 then return false
  if d == .none then return false
  let impl := a.cachedImplicit
  let ev := m.cachedValence i
  if 0 < defaultValence z &&
      defaultValence (((z : Int) - a.charge).toNat) < ev + impl then return false
  if 0 < a.radicals && (z != 6 || a.charge != 0) then return false
  if m.degree i + 1 < ev then
    let nMult := ((m.bondsOf i).filter fun k ↦ isMultiple m.bonds[k]!.kind).length
    if 1 < nMult then return false
  return true

/-- Hückel's rule over a set of atoms (`applyHuckel`, `Aromaticity.cpp:278`). -/
def huckel (atoms : List Nat) (donor : Array Donor) : Bool := Id.run do
  if 1 < (atoms.filter (donor[·]! == .any)).length then return false
  let lo := atoms.foldl (fun s a ↦ s + (donor[a]!).range.1) 0
  let hi := atoms.foldl (fun s a ↦ s + (donor[a]!).range.2) 0
  if 6 ≤ hi then
    return (List.range (hi + 1 - lo)).any fun t ↦ (lo + t) % 4 == 2
  return hi == 2

/-- All `k`-element subsets of `[0, n)`, in lexicographic order: the order RDKit's
`nextCombination` steps through. -/
def combinations (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (combinations n k).flatMap fun c ↦
      let start := match c.getLast? with | some x => x + 1 | none => 0
      (List.range (n - start)).map fun d ↦ c ++ [start + d]

/-- Are the rings `rids` connected to each other through `nbrs`? (`checkFused`,
`Aromaticity.cpp:97`) -/
def isConnectedSet (rids : List Nat) (nbrs : Array (List Nat)) : Bool := Id.run do
  let some first := rids.head? | return true
  let mut seen := [first]
  for _ in rids do
    for r in seen do
      for v in nbrs[r]! do
        if rids.contains v && !seen.contains v then seen := seen ++ [v]
  return seen.length == rids.length

/-- Make bond `b` aromatic, with its two atoms, if it is single or double; otherwise leave it.
`setAromaticity` folds this over `aromaticBondList`. -/
def markAromatic (out : Work) (b : Nat) : Work :=
  let bd := out.bonds[b]!
  if bd.kind == .single || bd.kind == .double then
    ((out.setKind b .aromatic).modifyAtom bd.src ({ · with aromatic := true }))
      |>.modifyAtom bd.dst ({ · with aromatic := true })
  else out

/-- Does atom `i` have a double or triple bond? -/
def hasMultipleBond (m : Work) (i : Nat) : Bool := (m.bondsOf i).any (isMultiple m.bonds[·]!.kind)

/-- The donor type `setAromaticity` gives atom `i` when it first sees it, in a ring of `len` atoms:
`donorType`, except that an ether-like O or S in a ring of 9 or more gives nothing (the macrocycle
rule, `Aromaticity.cpp:871`). -/
def ringDonor (m : Work) (ringBondSet : List Nat) (len : Nat) (i : Nat) : Donor :=
  let d := m.donorType ringBondSet i
  if d == .two && 9 ≤ len && [8, 16].contains m.atoms[i]!.z && m.degree i == 2 &&
      m.atoms[i]!.charge == 0 && !m.hasMultipleBond i then .none
  else d

/-- The bookkeeping of `setAromaticity`'s first pass: which atoms have been seen, which of them
can be aromatic, their donor types, and the candidate rings so far. -/
structure DonorState where
  /-- Atoms already seen in a ring. -/
  seen : Array Bool
  /-- Seen atoms that can be aromatic. -/
  cand : Array Bool
  /-- Donor types of the seen atoms. -/
  donor : Array Donor
  /-- Rings all of whose atoms can be aromatic, in order. -/
  candRings : Array (List Nat)

/-- One atom of a ring of `len` atoms in the first pass: the first time it is seen it gets its
donor type and candidacy; the flag says whether every atom of the ring so far is a candidate. -/
def donorAtomStep (m : Work) (ringBondSet : List Nat) (len : Nat) (p : DonorState × Bool)
    (i : Nat) : DonorState × Bool :=
  let (s, allCand) := p
  if s.seen[i]! then (s, allCand && s.cand[i]!)
  else
    let d := m.ringDonor ringBondSet len i
    let cand := s.cand.set! i (m.isAromaticCandidate i d)
    ({ s with seen := s.seen.set! i true, donor := s.donor.set! i d, cand }, allCand && cand[i]!)

/-- One ring of the first pass: its atoms, then the ring itself if all of them are candidates. -/
def donorRingStep (m : Work) (ringBondSet : List Nat) (s : DonorState) (ring : List Nat) :
    DonorState :=
  let (s, allCand) := ring.foldl (m.donorAtomStep ringBondSet ring.length) (s, true)
  if allCand then { s with candRings := s.candRings.push ring } else s

/-- `setAromaticity`'s first pass (`aromaticityHelper`, `Aromaticity.cpp:839`): donor types (set
the first time each atom is seen) and candidate rings. -/
def donorData (m : Work) (rings : Array (List Nat)) : DonorState :=
  let ringBondSet := (rings.toList.flatMap m.ringBonds).eraseDups
  rings.toList.foldl (m.donorRingStep ringBondSet)
    ⟨Array.replicate m.numAtoms false, Array.replicate m.numAtoms false,
      Array.replicate m.numAtoms Donor.none, #[]⟩

/-- The bonds a group `cur` of candidate rings makes aromatic, in increasing order: if the group
is connected and its atoms in one or two of its rings (GitHub #2895) pass Hückel's rule, the bonds
that occur in exactly one of its rings. `rbonds` are the candidate rings' bonds. -/
def groupBonds (numAtoms : Nat) (rbonds candRings : Array (List Nat)) (donor : Array Donor)
    (nbrs : Array (List Nat)) (cur : List Nat) : List Nat :=
  if !isConnectedSet cur nbrs then [] else
  let counts := cur.foldl (fun acc r ↦ candRings[r]!.foldl
    (fun acc a ↦ acc.modify a (· + 1)) acc) (Array.replicate numAtoms 0)
  let atoms := (List.range numAtoms).filter fun a ↦ counts[a]! == 1 || counts[a]! == 2
  if huckel atoms donor then
    let all := cur.flatMap (rbonds[·]!)
    (all.eraseDups.mergeSort (· ≤ ·)).filter (all.count · == 1)
  else []

/-- The bonds one fused system `fused` makes aromatic (`applyHuckelToFused`,
`Aromaticity.cpp:334`): groups of 1 to 6 of its rings, smallest first, stopping once every bond of
the system is done (or at three rings, for systems of more than 300). -/
def systemBonds (numAtoms : Nat) (rbonds candRings : Array (List Nat)) (donor : Array Donor)
    (nbrs : Array (List Nat)) (fused : List Nat) : List Nat :=
  let nRings := fused.length
  let allBonds := (fused.flatMap (rbonds[·]!)).eraseDups
  let step (st : List Nat × List Nat × Bool) (size : Nat) : List Nat × List Nat × Bool :=
    let (out, doneBonds, stop) := st
    if stop || (size == 3 && 300 < nRings) || allBonds.length ≤ doneBonds.length then
      (out, doneBonds, true)
    else
      let new := (combinations nRings size).flatMap fun comb ↦
        groupBonds numAtoms rbonds candRings donor nbrs (comb.map (fused[·]!))
      (out ++ new, new.foldl (fun d b ↦ if d.contains b then d else d ++ [b]) doneBonds, false)
  ((List.range' 1 (min nRings 6)).foldl step ([], [], false)).1

/-- Fused systems of candidate rings: rings sharing exactly one bond, each at most 24 bonds. -/
def fusedNbrs (rbonds : Array (List Nat)) : Array (List Nat) := Id.run do
  let nr := rbonds.size
  let mut nbrs : Array (List Nat) := Array.replicate nr []
  for i in [0:nr] do
    for j in [i + 1:nr] do
      if rbonds[i]!.length ≤ 24 && rbonds[j]!.length ≤ 24 &&
          (rbonds[i]!.filter rbonds[j]!.contains).length == 1 then
        nbrs := (nbrs.modify i (· ++ [j])).modify j (· ++ [i])
  return nbrs

/-- `setAromaticity`'s second pass: the bonds Hückel's rule makes aromatic, system by system. -/
def fusedBonds (numAtoms : Nat) (rbonds candRings : Array (List Nat)) (donor : Array Donor) :
    List Nat :=
  let nbrs := fusedNbrs rbonds
  (components candRings.size nbrs).flatMap (systemBonds numAtoms rbonds candRings donor nbrs)

/-- The bonds `setAromaticity` makes aromatic, in the order it visits them, repeats included: every
bond that occurs once in a group of fused candidate rings passing Hückel's rule. -/
def aromaticBondList (m : Work) (rings : Array (List Nat)) : List Nat :=
  let s := m.donorData rings
  fusedBonds m.numAtoms (s.candRings.map m.ringBonds) s.candRings s.donor

/-- Mark the aromatic rings' bonds and atoms (`setAromaticity`, default model): each bond of
`aromaticBondList` that is single or double becomes aromatic, with its two atoms. -/
def setAromaticity (m : Work) (rings : Array (List Nat)) : Work :=
  (m.aromaticBondList rings).foldl markAromatic m

end Work
end LeanSMILES.Aromaticity

/-! ### `Molecule.aromatize` -/

namespace LeanSMILES

namespace Aromaticity

/-- The bonds of `m` with the kinds of the working copy (same endpoints, so the
graph stays simple). -/
def withKinds {n : ℕ} (m : Molecule n) (w : Work) : List (Bond n) :=
  m.bonds.zipIdx.map fun (b, k) ↦ { b with kind := (w.bonds[k]?.map (·.kind)).getD b.kind }

/-- `withKinds` keeps every bond's endpoints, so its edge list is that of `m`. -/
lemma map_edge_withKinds {n : ℕ} (m : Molecule n) (w : Work) :
    (withKinds m w).map Bond.edge = m.bonds.map Bond.edge := by
  rw [← List.zipIdx_map_fst 0 m.bonds, List.map_map, withKinds, List.map_map]
  rfl

/-- The working copy `aromatize` kekulizes: `cleanUp` after the hydrogen counts are frozen, with
valences cached. -/
def Work.prepare {n : ℕ} (m : Molecule n) : Work :=
  (Work.ofMolecule m).freezeHs.cleanUp.cacheValences

/-- What `aromatize` does after kekulization: radicals, aromaticity perception over `rings`, and
the final hydrogen counts. -/
def Work.finish (w : Work) (rings : Array (List Nat)) : Work :=
  (w.assignRadicals.setAromaticity rings).finalizeHs

end Aromaticity

open Aromaticity in
/-- Atom `i` of the output from the final working copy `w`, before bracket normalization: `m`'s
atom with `w`'s aromaticity, charge and hydrogen count. The written hydrogens are kept, but never
more than the pipeline left (RDKit drops the one of `C1=[nH]C=CC=C1`, GitHub #141), so the atom
carries exactly `w`'s count. -/
def Molecule.outAtom {n : ℕ} (m : Molecule n) (w : Work) (i : Fin n) : Atom :=
  let a := m.atom i
  let wa := w.atoms[i.val]!
  let total := wa.frozenHs.getD (wa.explicitHs + w.implicitHs i.val)
  let written := a.explicitH.map (min · total)
  { a with aromatic := w.isAromaticAtom i.val, charge := wa.charge, explicitH := written,
           implicitH := total - written.getD 0 }

open Aromaticity in
/-- The molecule `aromatize` returns from the final working copy `w` of `m`: `m`'s atoms with
`w`'s aromatic flags, charges and hydrogen counts (`Molecule.outAtom`), `m`'s bonds with `w`'s
kinds, in bracket normal form. -/
def Molecule.aromatizeOutput {n : ℕ} (m : Molecule n) (w : Work) : Molecule n :=
  Molecule.normalizeBrackets
    { atoms := Vector.ofFn (m.outAtom w), bonds := withKinds m w,
      nodup := map_edge_withKinds m w ▸ m.nodup, stereo := m.stereo }

open Aromaticity in
/-- RDKit's view of the molecule's bonds, charges and hydrogens: `cleanUp` (nitro `N(=O)=O` →
`[N+](=O)[O-]` and the like), kekulize, then perceive aromaticity with RDKit's default model, then
RDKit's final hydrogen counts (`MolOps::sanitizeMol` from `cleanUp` to `adjustHs`, without valence
rejection or hydrogen removal). Bond kinds, charges, aromatic flags and implicit hydrogens change;
atoms, bonds and everything else stay. The atoms come back in bracket normal form
(`Molecule.normalizeBrackets`), so that `toSmiles` writes each hydrogen count the way it parses
back: pyrrole's nitrogen from `C1=CNC=C1` is `[nH]`, not a hydrogen-less `n`, and a redundant
`[CH4]` is `C`. Fails when RDKit's would ("Can't kekulize mol", e.g. `c1cccc1`). -/
def Molecule.aromatize {n : ℕ} (m : Molecule n) : Except String (Molecule n) := do
  let w := Work.prepare m
  let rings := w.relevantCycles
  let w ← w.kekulize rings
  return m.aromatizeOutput (w.finish rings)

/-- `Molecule.aromatize` on a bundled molecule. -/
def Mol.aromatize (M : Mol) : Except String Mol := do
  return ⟨M.n, ← M.mol.aromatize⟩

/-- Parse a SMILES string and give it RDKit's bonds, aromaticity and hydrogens. -/
def SMILES.parseAromatized (s : String) : Except String Mol := do
  let M ← (SMILES.parse s).mapError toString
  M.aromatize

end LeanSMILES
