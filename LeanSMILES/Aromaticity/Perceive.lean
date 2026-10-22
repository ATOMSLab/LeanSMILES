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

inductive Donor where
  | vacant | one | two | oneOrTwo | any | none
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
  if deg > 3 then return -1
  let nlp := max ((outerElectrons a.z : Int) - dv - a.charge) 0
  let res := dv - deg + nlp - a.radicals
  if res > 1 && (m.cachedValence i : Int) - m.degree i > 1 then return 1
  return res

/-- Atom across the first non-ring double/triple bond of atom `i`. -/
def exocyclicMultiple? (m : Work) (ringBonds : List Nat) (i : Nat) : Option Nat :=
  ((m.neighbors i).find? fun (k, _) => !ringBonds.contains k && isMultiple m.bonds[k]!.kind).map
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
    if (m.bondsOf i).any fun k => ringBonds.contains k && isMultiple m.bonds[k]!.kind then
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
  if z > 18 && z != 34 && z != 52 then return false
  if d == .none then return false
  let impl := a.cachedImplicit
  let ev := m.cachedValence i
  if defaultValence z > 0 &&
      ev + impl > defaultValence (((z : Int) - a.charge).toNat) then return false
  if a.radicals > 0 && (z != 6 || a.charge != 0) then return false
  if ev > m.degree i + 1 then
    let nMult := ((m.bondsOf i).filter fun k => isMultiple m.bonds[k]!.kind).length
    if nMult > 1 then return false
  return true

/-- Hückel's rule over a set of atoms (`applyHuckel`, `Aromaticity.cpp:278`). -/
def huckel (atoms : List Nat) (donor : Array Donor) : Bool := Id.run do
  if (atoms.filter (donor[·]! == .any)).length > 1 then return false
  let lo := atoms.foldl (fun s a => s + (donor[a]!).range.1) 0
  let hi := atoms.foldl (fun s a => s + (donor[a]!).range.2) 0
  if hi ≥ 6 then
    return (List.range (hi + 1 - lo)).any fun t => (lo + t) % 4 == 2
  return hi == 2

/-- All `k`-element subsets of `[0, n)`, in lexicographic order. -/
def combinations (n : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | k + 1 => (combinations n k).flatMap fun c =>
      let start := match c.getLast? with | some x => x + 1 | none => 0
      (List.range (n - start)).map fun d => c ++ [start + d]

/-- Are the rings `rids` connected to each other through `nbrs`? (`checkFused`) -/
def isConnectedSet (rids : List Nat) (nbrs : Array (List Nat)) : Bool := Id.run do
  let some first := rids.head? | return true
  let mut seen := [first]
  for _ in rids do
    for r in seen do
      for v in nbrs[r]! do
        if rids.contains v && !seen.contains v then seen := seen ++ [v]
  return seen.length == rids.length

/-- Mark the aromatic rings (`setAromaticity`, default model). -/
def setAromaticity (m : Work) (rings : Array (List Nat)) : Work := Id.run do
  let ringBondSet := (rings.toList.flatMap m.ringBonds).eraseDups
  -- 1-2. donor types (first time each atom is seen) and candidate rings
  let mut seen := Array.replicate m.numAtoms false
  let mut cand := Array.replicate m.numAtoms false
  let mut donor := Array.replicate m.numAtoms Donor.none
  let mut candRings : Array (List Nat) := #[]
  for ring in rings do
    let mut allCand := true
    for i in ring do
      if seen[i]! then
        if !cand[i]! then allCand := false
        continue
      seen := seen.set! i true
      let mut d := m.donorType ringBondSet i
      -- macrocycle rule (Aromaticity.cpp:871): ether-like O/S in a ring of 9 or more
      if d == .two && ring.length ≥ 9 && [8, 16].contains m.atoms[i]!.z &&
          m.degree i == 2 && m.atoms[i]!.charge == 0 &&
          !(m.bondsOf i).any (isMultiple m.bonds[·]!.kind) then
        d := .none
      donor := donor.set! i d
      cand := cand.set! i (m.isAromaticCandidate i d)
      if !cand[i]! then allCand := false
    if allCand then candRings := candRings.push ring
  -- 3. fused systems: rings sharing exactly one bond, each at most 24 bonds
  let nr := candRings.size
  let rbonds := candRings.map m.ringBonds
  let mut nbrs : Array (List Nat) := Array.replicate nr []
  for i in [0:nr] do
    for j in [i + 1:nr] do
      if rbonds[i]!.length ≤ 24 && rbonds[j]!.length ≤ 24 &&
          (rbonds[i]!.filter rbonds[j]!.contains).length == 1 then
        nbrs := (nbrs.modify i (· ++ [j])).modify j (· ++ [i])
  let mut out := m
  for fused in components nr nbrs do
    let nRings := fused.length
    let systemBonds := (fused.flatMap (rbonds[·]!)).eraseDups
    let mut doneBonds : List Nat := []
    for size in [1:(min nRings 6) + 1] do
      if size == 3 && nRings > 300 then break
      if doneBonds.length ≥ systemBonds.length then break
      for comb in combinations nRings size do
        let cur := comb.map (fused[·]!)
        if !isConnectedSet cur nbrs then continue
        -- atoms in 1 or 2 of the chosen rings (GitHub #2895)
        let counts := cur.foldl (fun acc r => candRings[r]!.foldl
          (fun acc a => acc.modify a (· + 1)) acc) (Array.replicate m.numAtoms 0)
        let atoms := (List.range m.numAtoms).filter fun a => counts[a]! == 1 || counts[a]! == 2
        if huckel atoms donor then
          -- bonds that occur once in the group become aromatic
          let all := cur.flatMap (rbonds[·]!)
          for b in all.eraseDups.mergeSort (· ≤ ·) do
            if all.count b == 1 then
              let bd := out.bonds[b]!
              if bd.kind == .single || bd.kind == .double then
                out := ((out.setKind b .aromatic).modifyAtom bd.src ({ · with aromatic := true }))
                  |>.modifyAtom bd.dst ({ · with aromatic := true })
              if !doneBonds.contains b then doneBonds := doneBonds ++ [b]
  return out

end Work
end LeanSMILES.Aromaticity

/-! ### `Molecule.aromatize` -/

namespace LeanSMILES

namespace Aromaticity

/-- The bonds of `m` with the kinds of the working copy (same endpoints, so the
graph stays simple). -/
def withKinds {n : ℕ} (m : Molecule n) (w : Work) : List (Bond n) :=
  m.bonds.zipIdx.map fun (b, k) ↦ { b with kind := (w.bonds[k]?.map (·.kind)).getD b.kind }

lemma map_edge_withKinds {n : ℕ} (m : Molecule n) (w : Work) :
    (withKinds m w).map Bond.edge = m.bonds.map Bond.edge := by
  rw [withKinds, List.map_map]
  have : (Bond.edge ∘ fun (p : Bond n × ℕ) ↦
      ({ p.1 with kind := (w.bonds[p.2]?.map (·.kind)).getD p.1.kind } : Bond n))
      = Bond.edge ∘ Prod.fst := rfl
  rw [this, ← List.map_map, List.zipIdx_map_fst]

end Aromaticity

open Aromaticity in
/-- RDKit's view of the molecule's bonds and hydrogens: kekulize, then perceive
aromaticity with RDKit's default model, then RDKit's final hydrogen counts
(`MolOps::sanitizeMol` from `updatePropertyCache` to `adjustHs`, without
`cleanUp`, valence rejection or hydrogen removal). Bond kinds, aromatic flags
and implicit hydrogens change; atoms, bonds and everything else stay. Fails when
RDKit's would ("Can't kekulize mol", e.g. `c1cccc1`). -/
def Molecule.aromatize {n : ℕ} (m : Molecule n) : Except String (Molecule n) := do
  let w := (Work.ofMolecule m).freezeHs.cacheValences
  let rings := w.relevantCycles
  let w ← w.kekulize rings
  let w := (w.assignRadicals.setAromaticity rings).finalizeHs
  let atoms := Vector.ofFn fun i : Fin n ↦
    let a := m.atom i
    let wa := w.atoms[i.val]!
    let total := wa.frozenHs.getD (wa.explicitHs + w.implicitHs i.val)
    { a with aromatic := w.isAromaticAtom i.val, implicitH := total - a.explicitH.getD 0 }
  return { atoms, bonds := withKinds m w,
           nodup := by rw [map_edge_withKinds]; exact m.nodup }

/-- `Molecule.aromatize` on a bundled molecule. -/
def Mol.aromatize (M : Mol) : Except String Mol := do
  return ⟨M.n, ← M.mol.aromatize⟩

/-- Parse a SMILES string and give it RDKit's bonds, aromaticity and hydrogens. -/
def SMILES.parseAromatized (s : String) : Except String Mol := do
  let M ← (SMILES.parse s).mapError toString
  M.aromatize

end LeanSMILES
