/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
-/
module

public import LeanSMILES.SMILES.Canon
public import LeanSMILES.Chem.Graph
public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.Aromaticity.Perceive

/-!
# Pipelines.Representation

Molecular representations: where the SMILES toolkit meets the learning algorithms.

A representation turns a molecule (`Mol`, from the SMILES toolkit) into `d` exact rational
features. Exact, so that a certificate can compute with the data exactly
(`Pipelines/Certificates.lean`); the solvers read the features as `Float` or `ℝ` through
`RatEmbed`.

* `morgan radius fpSize`: the Morgan fingerprint bits of `Molecule.morganVector`, as `0/1`.
* `bondOrders k`: the bond-order matrix of the first `k` atoms (`Molecule.adjMatrix`,
  padded with zeros), flattened row by row. Entries are read with `Molecule.bondOrder`,
  which compares bond endpoints directly instead of deciding equality in `Sym2`, so the
  kernel can evaluate it; `bondOrder_eq_adjMatrix` proves it is `adjMatrix`.
* `counts`: atoms, bonds, hydrogens, aromatic atoms and heteroatoms, from the toolkit's
  `Molecule` and `Atom`.
* `canonical r`: `r` applied to the molecule read back from its canonical SMILES. By
  `Mol.canonicalSmiles_relabel` it does not depend on how the atoms are numbered
  (`canonical_relabel`).
* `clip c r`: every feature of `r` clamped to `[-c, c]`, so that any representation gets a
  feature bound.
* `r₁ ++ r₂`: both representations side by side.

Feature bounds, used by the gradient-descent certificate, are in
`Pipelines/Proofs/Representation.lean`.

For classification, `morganFeatures` gives a SMILES string's Morgan on-bits as a sparse
feature vector, the form `LeanLearn.Classification.fitLogistic` takes.

This file is the only place the toolkit's fingerprints are read (`Molecule.morganVector`,
`SMILES.parseAromatized` and `Mol.morganBits`).
-/

@[expose] public section

namespace LeanSMILES

/-! The first definitions extend the toolkit's own types, so they live in its namespace. -/

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-- The order of the bond between atoms `i` and `j`, or `0` if there is none: `m.adjMatrix i j`
(`bondOrder_eq_adjMatrix`), found by comparing endpoints so that the kernel can evaluate it. -/
def bondOrder (i j : Fin n) : ℚ :=
  ((m.bonds.find? fun b ↦ (b.src == i && b.dst == j) || (b.src == j && b.dst == i)).map
    (·.kind.order)).getD 0

end Molecule

/-- The molecule with no atoms (what `Mol.canonicalForm` falls back to). -/
def Mol.empty : Mol := ⟨0, ⟨#v[], [], List.nodup_nil⟩⟩

/-- The molecule read back from its canonical SMILES (the empty molecule if that string
does not parse). It depends only on the canonical SMILES. -/
def Mol.canonicalForm (M : Mol) : Mol :=
  match SMILES.parse M.canonicalSmiles with
  | .ok M' => M'
  | .error _ => Mol.empty

end LeanSMILES

namespace Pipelines

open LeanSMILES

/-- A molecular representation: `d` exact rational features for every molecule. -/
abbrev Representation (d : ℕ) := Mol → Vector ℚ d

namespace Representation

variable {a b d : ℕ}

/-- The `fpSize` Morgan (ECFP-style) fingerprint bits as `0/1` features (`Molecule.morganVector`;
RDKit's `GetMorganGenerator(radius, fpSize)` on an aromatized molecule). Bound: `morgan_bounded`. -/
def morgan (radius fpSize : ℕ) : Representation fpSize :=
  fun M ↦ (M.mol.morganVector radius fpSize).map fun bit ↦ if bit then 1 else 0

/-- The bond-order matrix (`Molecule.adjMatrix`) of the first `k` atoms, padded with zeros and
flattened row by row: `k * k` entries in `[0, 4]` (`bondOrders_getElem`, `bondOrders_bounded`). -/
def bondOrders (k : ℕ) : Representation (k * k) :=
  fun M ↦ Vector.ofFn fun idx ↦
    if h : idx.val / k < M.n ∧ idx.val % k < M.n then
      M.mol.bondOrder ⟨idx.val / k, h.1⟩ ⟨idx.val % k, h.2⟩
    else 0

/-- Five counts read off the toolkit's molecule: heavy atoms, bonds, hydrogens, aromatic atoms and
heteroatoms (heavy atoms other than carbon). No bound holds for all molecules; `clip` gives one. -/
def counts : Representation 5 :=
  fun M ↦
    let atoms := M.mol.atoms.toList
    #v[M.n, M.mol.numBonds, (atoms.map Atom.totalH).sum, (atoms.filter (·.aromatic)).length,
      (atoms.filter fun a ↦ a.atomicNumber ≠ 6).length]

/-- Every feature of `r` clamped to `[-c, c]`, which bounds any representation: for `0 ≤ c`,
`‖clip c r M‖² ≤ d c²` (`clip_bounded`). -/
def clip (c : ℚ) (r : Representation d) : Representation d :=
  fun M ↦ (r M).map fun x ↦ max (-c) (min c x)

/-- `r` on the molecule read back from its canonical SMILES: independent of atom numbering
(`canonical_relabel`), with the same feature bound as `r` (`canonical_bounded`). -/
def canonical (r : Representation d) : Representation d := fun M ↦ r M.canonicalForm

/-- The `a + b` features of `r₁` followed by those of `r₂`, written `r₁ ++ r₂`; their feature
bounds add (`append_bounded`). -/
def append (r₁ : Representation a) (r₂ : Representation b) : Representation (a + b) :=
  fun M ↦ r₁ M ++ r₂ M

instance : HAppend (Representation a) (Representation b) (Representation (a + b)) := ⟨append⟩

end Representation

/-! ## Sparse `0/1` features for classification -/

/-- The Morgan on-bits of a SMILES string, aromatized first so that they are RDKit's: the sparse
sample (`SparseBits`, the indices of the `1`s) that `LeanLearn.Classification.fitLogistic` takes. -/
def morganFeatures (s : String) (radius : ℕ := 2) (fpSize : ℕ := 2048) :
    Except String (Array ℕ) := do
  let M ← SMILES.parseAromatized s
  return (M.morganBits radius fpSize).toArray

end Pipelines
