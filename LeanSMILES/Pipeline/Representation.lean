/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph
import LeanSMILES.Fingerprint.Morgan

/-!
# Molecular representations

A representation turns a molecule (`Mol`, from the SMILES toolkit) into `d` exact rational
features. Exact, so that a certificate can compute with the data exactly
(`Pipeline/Certificates.lean`); the solvers read the features as `Float` or `ℝ` through
`RatEmbed`.

* `morgan radius fpSize`: the Morgan fingerprint bits of `Molecule.morganVector`, as `0/1`.
* `bondOrders k`: the bond-order matrix of the first `k` atoms (`Molecule.adjMatrix`,
  padded with zeros), flattened row by row. Entries are read with `Molecule.bondOrder`,
  which compares bond endpoints directly instead of deciding equality in `Sym2`, so the
  kernel can evaluate it; `bondOrder_eq_adjMatrix` proves it is `adjMatrix`.
* `canonical r`: `r` applied to the molecule read back from its canonical SMILES. By
  `Mol.canonicalSmiles_relabel` it does not depend on how the atoms are numbered
  (`canonical_relabel`).
* `r₁ ++ r₂`: both representations side by side.

Feature bounds, used by the gradient-descent certificate, are in
`Proofs/Pipeline/Representation.lean`.
-/

namespace LeanSMILES

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-- The order of the bond between atoms `i` and `j`, or `0` if there is none. Equal to
`m.adjMatrix i j` (`bondOrder_eq_adjMatrix`). -/
def bondOrder (i j : Fin n) : ℚ :=
  ((m.bonds.find? fun b => (b.src == i && b.dst == j) || (b.src == j && b.dst == i)).map
    (·.kind.order)).getD 0

end Molecule

/-- The molecule with no atoms. -/
def Mol.empty : Mol := ⟨0, ⟨#v[], [], List.nodup_nil⟩⟩

/-- The molecule read back from its canonical SMILES (the empty molecule if that string
does not parse). It depends only on the canonical SMILES. -/
def Mol.canonicalForm (M : Mol) : Mol :=
  match SMILES.parse M.canonicalSmiles with
  | .ok M' => M'
  | .error _ => Mol.empty

/-- A molecular representation with `d` exact features. -/
abbrev Representation (d : ℕ) := Mol → Vector ℚ d

namespace Representation

variable {a b d : ℕ}

/-- Morgan (ECFP-style) fingerprint bits as `0/1` features: RDKit's
`GetMorganGenerator(radius, fpSize)`, as `Molecule.morganVector` computes it. -/
def morgan (radius fpSize : ℕ) : Representation fpSize :=
  fun M => (M.mol.morganVector radius fpSize).map fun bit => if bit then 1 else 0

/-- The bond-order matrix (`Molecule.adjMatrix`) of the first `k` atoms, padded with zeros
and flattened row by row. -/
def bondOrders (k : ℕ) : Representation (k * k) :=
  fun M => Vector.ofFn fun idx =>
    if h : idx.val / k < M.n ∧ idx.val % k < M.n then
      M.mol.bondOrder ⟨idx.val / k, h.1⟩ ⟨idx.val % k, h.2⟩
    else 0

/-- `r` on the molecule read back from its canonical SMILES: independent of atom
numbering. -/
def canonical (r : Representation d) : Representation d := fun M => r M.canonicalForm

/-- Both representations' features, side by side. -/
def append (r₁ : Representation a) (r₂ : Representation b) : Representation (a + b) :=
  fun M => r₁ M ++ r₂ M

instance : HAppend (Representation a) (Representation b) (Representation (a + b)) := ⟨append⟩

end Representation

end LeanSMILES
