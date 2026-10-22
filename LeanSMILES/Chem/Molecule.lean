/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.Chem.Atom
import LeanSMILES.Chem.Bond

/-!
# LeanSMILES.Chem.Molecule

A molecule with `n` atoms is a `Vector Atom n` together with a list of bonds
between distinct atoms, no two of which join the same pair — so the molecular
graph is a *simple* graph, which is what Mathlib's `SimpleGraph` is.  The size
is a type index: `Fin n` is the atom type, bonds cannot dangle, and relabeling
the atoms is a permutation `Equiv.Perm (Fin n)`.

The structure is RDKit-shaped (typed atoms and bonds, index-based) rather than
pysmiles-shaped (attribute dictionaries on an untyped graph), and the
invariants RDKit checks at runtime — endpoints in range, no self-bond, no
duplicate bond — are the type here: a `Molecule n` cannot violate them.

The one piece of chemistry in this file is `assignImplicitH`, the OpenSMILES
default-valence rule for bare organic-subset atoms.  Everything else is graph.
-/

namespace LeanSMILES

/-- A molecule with `n` atoms. -/
structure Molecule (n : ℕ) where
  /-- The atoms, numbered in order of appearance in the SMILES string. -/
  atoms : Vector Atom n
  /-- The bonds, in the order the SMILES string introduced them. -/
  bonds : List (Bond n)
  /-- No two bonds join the same pair of atoms: the molecular graph is simple. -/
  nodup : (bonds.map Bond.edge).Nodup

/-- A molecule whose size is not known at the type level — what a parser
returns. -/
structure Mol where
  /-- The number of atoms. -/
  n : ℕ
  /-- The molecule. -/
  mol : Molecule n

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-- The number of bonds. -/
def numBonds : ℕ := m.bonds.length

/-- The atom with index `i`. -/
def atom (i : Fin n) : Atom := m.atoms[i]

/-- The undirected edges, as Mathlib sees them. -/
def edges : List (Sym2 (Fin n)) := m.bonds.map Bond.edge

/-- The bonds at atom `i`. -/
def bondsAt (i : Fin n) : List (Bond n) := m.bonds.filter (·.touches i)

/-- The neighbors of atom `i`, in bond-list order. -/
def neighbors (i : Fin n) : List (Fin n) := (m.bondsAt i).map (·.other i)

/-- Number of bonds at atom `i` (heavy-atom degree; hydrogens are counts, not
atoms, unless written as `[H]`). -/
def degree (i : Fin n) : ℕ := (m.bondsAt i).length

/-- Sum of bond orders at atom `i`, exact. -/
def bondOrderSum (i : Fin n) : ℚ := ((m.bondsAt i).map (·.kind.order)).sum

/-- The bond joining `i` and `j`, if any. Unique by `nodup`. -/
def bondBetween (i j : Fin n) : Option (Bond n) :=
  m.bonds.find? fun b ↦ decide (b.edge = s(i, j))

/-- Whether some bond joins `i` and `j`. -/
def adjacent (i j : Fin n) : Bool := (m.bondBetween i j).isSome

/-- Replace every atom, keeping the bonds. -/
def mapAtoms (f : Fin n → Atom → Atom) : Molecule n :=
  { m with atoms := Vector.ofFn fun i ↦ f i m.atoms[i] }

/-! ### Implicit hydrogens

The OpenSMILES rule: a bare organic-subset atom has as many hydrogens as the
smallest default valence not below its bond-order sum requires; if no default
valence is large enough it has none.  Aromatic bonds count `3/2`, with the one
adjustment in `implicitHydrogens` that keeps three-connected aromatic atoms
Kekulé-consistent.  Bracket atoms, wildcards and every other element have
exactly the hydrogens that were written. -/

/-- Implicit hydrogen count for an atom with the given bond-order sum.

Aromatic bonds count `3/2`, so an aromatic atom bonded to three neighbors —
the nitrogen of `Cn1cccc1`, the sulfur of thiophene, a ring-fusion carbon —
sums past its lowest valence to a value no Kekulé structure realizes.  Such an
atom is snapped down to the largest valence not above its sum, when that is
within `3/2` of it (the rule RDKit applies); otherwise `Cn1cccc1` would get an
`NH` and thiophene an `SH`. -/
def implicitHydrogens (a : Atom) (orderSum : ℚ) : ℕ :=
  match a.element, a.explicitH with
  | some e, none =>
    let vs := e.defaultValences
    let sum :=
      match vs.head? with
      | some v₀ =>
        if a.aromatic && (v₀ : ℚ) < orderSum then
          let p := (vs.filter fun v ↦ decide ((v : ℚ) ≤ orderSum)).getLast?.getD v₀
          if orderSum - p ≤ (3 : ℚ) / 2 then (p : ℚ) else orderSum
        else orderSum
      | none => orderSum
    match vs.find? (fun v ↦ decide (sum ≤ (v : ℚ))) with
    | some v => (Rat.floor ((v : ℚ) - sum)).toNat
    | none => 0
  | _, _ => 0

/-- Fill in `Atom.implicitH` for every atom from its bonds. The RDKit
"sanitize" step, cut down to the one rule SMILES itself specifies. -/
def assignImplicitH : Molecule n :=
  m.mapAtoms fun i a ↦ { a with implicitH := implicitHydrogens a (m.bondOrderSum i) }

/-! ### Relabeling -/

/-- Relabel the atoms by a permutation: atom `i` becomes atom `σ i`. -/
def relabel (σ : Equiv.Perm (Fin n)) : Molecule n where
  atoms := Vector.ofFn fun i ↦ m.atoms[σ.symm i]
  bonds := m.bonds.map (Bond.map σ σ.injective)
  nodup := by
    have h : (m.bonds.map (Bond.map σ σ.injective)).map Bond.edge
        = (m.bonds.map Bond.edge).map (Sym2.map σ) := by
      simp [List.map_map, Function.comp_def]
    rw [h]
    exact m.nodup.map (Sym2.map.injective σ.injective)

lemma edges_relabel (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).edges = m.edges.map (Sym2.map σ) := by
  simp [edges, relabel, List.map_map, Function.comp_def]

@[simp] lemma atom_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (m.relabel σ).atom (σ i) = m.atom i := by
  simp [relabel, atom]

lemma numBonds_relabel (σ : Equiv.Perm (Fin n)) : (m.relabel σ).numBonds = m.numBonds := by
  simp [relabel, numBonds]

/-! ### Printing -/

instance : Repr (Molecule n) where
  reprPrec m _ :=
    "Molecule " ++ repr n ++ " " ++ repr (m.atoms.toList.map Atom.toSmiles) ++ " " ++ repr m.bonds

end Molecule

instance : Repr Mol := ⟨fun M _ ↦ repr M.mol⟩

end LeanSMILES
