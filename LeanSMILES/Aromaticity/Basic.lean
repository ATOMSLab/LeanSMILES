/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.Aromaticity.Basic

The bookkeeping RDKit's kekulization and aromaticity perception need, beyond
what a `Molecule n` records: RDKit's allowed-valence lists and outer-electron
counts, its explicit and implicit valence (`Atom.cpp`), cached values, and
radicals.

The perception passes run on `Work`, a working copy of a `Molecule n` indexed by
plain numbers (atom `i` is `Fin` atom `i`, bond `k` is the `k`-th bond of
`Molecule.bonds`), carrying that bookkeeping per atom. `Molecule.aromatize`
(`LeanSMILES.Aromaticity.Perceive`) builds it, runs the passes, and writes the
bond kinds, aromatic flags and hydrogen counts back.

Ported from the `canonical-smiles` branch's `Canonical/Sanitize.lean` (commit
`5b5fe9e`), which matches RDKit 2026.09.1 on the oracle datasets; RDKit file and
line references are to `Release_2026_09_1`.
-/

namespace LeanSMILES.Aromaticity

/-! ### RDKit's element data -/

/-- Atomic number, RDKit's allowed valences (smallest first; the first is the
default) and outer-shell electrons (`atomic_data.cpp`), for the elements whose
valence RDKit constrains. Other elements get no implicit hydrogens and are
never aromatic. -/
def elementTable : List (ℕ × List ℕ × ℕ) :=
  [(1, [1], 1), (2, [0], 2), (4, [2], 2), (5, [3], 3), (6, [4], 4), (7, [3], 5), (8, [2], 6),
   (9, [1], 7), (10, [0], 8), (13, [3], 3), (14, [4], 4), (15, [3, 5], 5), (16, [2, 4, 6], 6),
   (17, [1], 7), (18, [0], 8), (31, [3], 3), (32, [4], 4), (33, [3, 5], 5), (34, [2, 4, 6], 6),
   (35, [1], 7), (36, [0], 8), (49, [3], 3), (50, [2, 4], 4), (51, [3, 5], 5),
   (52, [2, 4, 6], 6), (53, [1, 3, 5], 7), (54, [0, 2, 4, 6], 8)]

/-- RDKit's allowed valences of element `z`; empty if it does not constrain them. -/
def valences (z : ℕ) : List ℕ := ((elementTable.find? (·.1 == z)).map (·.2.1)).getD []

/-- RDKit's default valence (the first allowed one), `0` if none. -/
def defaultValence (z : ℕ) : ℕ := (valences z).head?.getD 0

/-- Outer-shell electrons (5 for N, 6 for O). -/
def outerElectrons (z : ℕ) : ℕ := ((elementTable.find? (·.1 == z)).map (·.2.2)).getD 0

/-- RDKit's `isEarlyAtom` (`Atom.cpp:58`), on the table above: elements left of
carbon in their row, whose charges count the other way in kekulization. -/
def isEarly (z : ℕ) : Bool := [4, 5, 13, 31, 32, 49, 50, 51].contains z

/-- RDKit's `moreElectroNegative` (`PeriodicTable.h:304`): more outer electrons,
or the same number and a smaller atomic number. -/
def moreElectronegative (z₁ z₂ : ℕ) : Bool :=
  outerElectrons z₁ > outerElectrons z₂ ||
    (outerElectrons z₁ == outerElectrons z₂ && z₁ < z₂)

/-- Bond order in half-units, so aromatic (3/2) stays an integer: RDKit's
`getBondTypeAsDouble` times two. -/
def halfOrder : BondKind → ℕ
  | .single => 2
  | .double => 4
  | .triple => 6
  | .quadruple => 8
  | .aromatic => 3

/-- Double or triple. -/
def isMultiple (k : BondKind) : Bool := k == .double || k == .triple

/-! ### The working copy -/

/-- An atom with RDKit's sanitization bookkeeping. -/
structure WAtom where
  /-- Atomic number (`0` for `*`). -/
  z : ℕ
  aromatic : Bool
  charge : ℤ
  /-- Hydrogens written in brackets, plus any `adjustHs` adds back. -/
  explicitHs : ℕ
  /-- Bracket atoms get no implicit hydrogens. -/
  noImplicit : Bool
  /-- Total H count fixed before kekulization (RDKit keeps it from then on). -/
  frozenHs : Option ℕ := none
  /-- Unpaired electrons (bracket atoms only). -/
  radicals : ℕ := 0
  /-- Explicit valence as cached before kekulization; aromaticity reads this. -/
  cachedValence : Option ℕ := none
  /-- Implicit H count cached at the same time. -/
  cachedImplicit : ℕ := 0
  /-- Was aromatic before kekulization: `adjustHs` may give it hydrogens back. -/
  adjustHs : Bool := false
  deriving Inhabited

/-- A bond of the working copy: endpoints as atom numbers, and its kind. -/
structure WBond where
  src : ℕ
  dst : ℕ
  kind : BondKind
  deriving Inhabited

/-- A molecule's working copy. -/
structure Work where
  atoms : Array WAtom
  bonds : Array WBond
  deriving Inhabited

/-- The working copy of a molecule. Bracket atoms (and `*`) take no implicit
hydrogens. -/
def Work.ofMolecule {n : ℕ} (m : Molecule n) : Work where
  atoms := (List.finRange n).toArray.map fun i ↦
    let a := m.atom i
    { z := a.atomicNumber, aromatic := a.aromatic, charge := a.charge,
      explicitHs := a.explicitH.getD 0, noImplicit := a.explicitH.isSome || a.element.isNone }
  bonds := m.bonds.toArray.map fun b ↦ { src := b.src.val, dst := b.dst.val, kind := b.kind }

namespace Work

variable (m : Work)

def numAtoms : ℕ := m.atoms.size
def numBonds : ℕ := m.bonds.size

def WBond.touches (b : WBond) (i : ℕ) : Bool := b.src == i || b.dst == i
def WBond.other (b : WBond) (i : ℕ) : ℕ := if b.src == i then b.dst else b.src

/-- Bond numbers at atom `i`, in bond order. -/
def bondsOf (i : ℕ) : List ℕ := (List.range m.numBonds).filter fun k ↦ WBond.touches m.bonds[k]! i

/-- `(bond, neighbor)` pairs of atom `i`, in bond order (RDKit's adjacency order). -/
def neighbors (i : ℕ) : List (ℕ × ℕ) := (m.bondsOf i).map fun k ↦ (k, WBond.other m.bonds[k]! i)

def degree (i : ℕ) : ℕ := (m.bondsOf i).length

/-- The bond joining `i` and `j`, if any. -/
def bondBetween? (i j : ℕ) : Option ℕ :=
  (List.range m.numBonds).find? fun k ↦
    let b := m.bonds[k]!
    (b.src == i && b.dst == j) || (b.src == j && b.dst == i)

def setKind (k : ℕ) (o : BondKind) : Work :=
  { m with bonds := m.bonds.modify k fun b ↦ { b with kind := o } }

def modifyAtom (i : ℕ) (f : WAtom → WAtom) : Work := { m with atoms := m.atoms.modify i f }

/-! ### Valence and hydrogens (`Atom.cpp:350-613`) -/

/-- RDKit's `isAromaticAtom`: lowercase, or touching an aromatic bond. -/
def isAromaticAtom (i : ℕ) : Bool :=
  m.atoms[i]!.aromatic || (m.bondsOf i).any fun k ↦ m.bonds[k]!.kind == .aromatic

/-- Charged atoms take the valences of the isoelectronic element (N⁺ like C). -/
def effectiveZ (a : WAtom) : ℕ := (a.z - a.charge).toNat

/-- P, S (and As, Se) with a negative charge keep their own valence list. -/
def canBeHypervalent (a : WAtom) (eff : ℕ) : Bool :=
  (eff > 16 && (a.z == 15 || a.z == 16)) || (eff > 34 && (a.z == 33 || a.z == 34))

/-- RDKit's explicit valence: bond orders plus written hydrogens, with the
aromatic snap to an allowed valence and "round x.5 up" (`Atom.cpp:350-415`). -/
def explicitValence (i : ℕ) : ℕ := Id.run do
  let a := m.atoms[i]!
  let mut accum := 2 * a.explicitHs
  for k in m.bondsOf i do
    accum := accum + halfOrder m.bonds[k]!.kind
  let valens := valences (effectiveZ a)
  if let some dv := valens.head? then
    if accum > 2 * dv && m.isAromaticAtom i then
      let pval := (valens.filter (2 * · ≤ accum)).getLast?.getD dv
      if accum ≤ 2 * pval + 3 then accum := 2 * pval
  return (accum + 1) / 2

/-- RDKit's implicit hydrogen count (`Atom.cpp:458-613`). -/
def implicitHs (i : ℕ) : ℕ := Id.run do
  let a := m.atoms[i]!
  if a.noImplicit then return 0
  let mut eff := effectiveZ a
  let mut ev : ℤ := m.explicitValence i
  if canBeHypervalent a eff then
    eff := a.z
    ev := ev - a.charge
  let valens := valences eff
  let some dv := valens.head? | return 0
  if m.isAromaticAtom i then
    return if ev ≤ dv then (dv - ev).toNat else 0
  match (valens.map Int.ofNat).find? (ev ≤ ·) with
  | some v => return (v - ev).toNat
  | none => return 0

/-- Total hydrogens: frozen if set, else written plus implicit. -/
def totalHs (i : ℕ) : ℕ := m.atoms[i]!.frozenHs.getD (m.atoms[i]!.explicitHs + m.implicitHs i)

/-- Fix every atom's total H count, as RDKit does before kekulization. -/
def freezeHs : Work :=
  { m with atoms := (List.range m.numAtoms).toArray.map fun i ↦
      { m.atoms[i]! with frozenHs := some (m.totalHs i) } }

/-- Cache explicit valence and implicit H count (`updatePropertyCache` before
kekulization) and mark the atoms `adjustHs` may touch (`MolOps.cpp:419`). -/
def cacheValences : Work :=
  { m with atoms := (List.range m.numAtoms).toArray.map fun i ↦
      { m.atoms[i]! with cachedValence := some (m.explicitValence i),
                         cachedImplicit := m.implicitHs i,
                         adjustHs := m.isAromaticAtom i } }

/-- RDKit's final H counts (`adjustHs`, `MolOps.cpp:380-415`, then the last
`updatePropertyCache`): implicit counts are recomputed on the final graph, and an
atom that is or was aromatic and would lose implicit hydrogens gets them back as
written ones (pyrrole's N–H). -/
def finalizeHs : Work := Id.run do
  let mut w := m
  for i in [0:w.numAtoms] do
    let a := w.atoms[i]!
    if a.adjustHs || w.isAromaticAtom i then
      let new := w.implicitHs i
      if new < a.cachedImplicit then
        w := w.modifyAtom i ({ · with explicitHs := a.explicitHs + (a.cachedImplicit - new) })
  let totals := (List.range w.numAtoms).map fun i ↦ w.atoms[i]!.explicitHs + w.implicitHs i
  return { w with atoms := (List.range w.numAtoms).toArray.map fun i ↦
      { w.atoms[i]! with frozenHs := some totals[i]! } }

/-- Explicit valence on the Kekulé graph: integer bond orders plus written Hs. -/
def kekuleValence (i : ℕ) : ℕ :=
  ((m.bondsOf i).foldl (fun s k ↦ s + halfOrder m.bonds[k]!.kind) 0) / 2 + m.atoms[i]!.explicitHs

/-- The explicit valence aromaticity sees (`Atom::getValence`): the cached one. -/
def cachedValence (i : ℕ) : ℕ := m.atoms[i]!.cachedValence.getD (m.kekuleValence i)

/-- Total hydrogens as aromaticity sees them: written plus cached implicit. -/
def cachedTotalHs (i : ℕ) : ℕ := m.atoms[i]!.explicitHs + m.atoms[i]!.cachedImplicit

/-- `MolOps::assignRadicals` (`MolOps.cpp:437`), for bracket atoms. -/
def assignRadicals : Work := Id.run do
  let mut w := m
  for i in [0:w.numAtoms] do
    let a := w.atoms[i]!
    if !a.noImplicit || a.z == 0 then continue
    let z := a.z
    let no : ℤ := outerElectrons z
    let tv : ℤ := w.kekuleValence i
    let base : ℤ := if z == 1 || z == 2 then 2 else 8
    let mut nr : ℤ := base - no - tv + a.charge
    if nr < 0 then
      nr := 0
      if (valences z).length > 1 then
        if let some v := ((valences z).map Int.ofNat).find? (fun v ↦ v - tv + a.charge ≥ 0) then
          nr := v - tv + a.charge
    let nr2 := no - tv - a.charge
    if nr2 ≥ 0 then nr := min nr nr2
    w := w.modifyAtom i ({ · with radicals := nr.toNat })
  return w

end Work

end LeanSMILES.Aromaticity
