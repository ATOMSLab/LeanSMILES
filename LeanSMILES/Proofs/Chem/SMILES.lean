module

public import LeanSMILES.Proofs.Basic
public import LeanSMILES.Polymorphic.Chem.SMILES

/-!
# SMILES — Proofs

Theorems about parsing and canonical SMILES (`Polymorphic/Chem/SMILES.lean`).
-/

public section

namespace Chem

/-! ## Canonical SMILES -/

theorem canonicalize_of_parse {s : SMILES} {m : Molecule} (h : s.parse = .ok m) :
    s.canonicalize = .ok m.canonicalSMILES := by
  simp [SMILES.canonicalize, h]

/-- When both strings parse, `sameMolecule` compares their canonical SMILES. -/
theorem sameMolecule_eq {s t : SMILES} {a b : CanonicalSMILES}
    (hs : s.canonicalize = .ok a) (ht : t.canonicalize = .ok b) :
    s.sameMolecule t = (a == b) := by
  simp [SMILES.sameMolecule, hs, ht]

/-- A molecule's canonical SMILES depends only on the molecule, so equal molecules have
equal canonical SMILES. The converse (canonical SMILES determines the molecule up to atom
renumbering) is the main correctness theorem still to prove. -/
theorem canonicalSMILES_congr {m₁ m₂ : Molecule} (h : m₁ = m₂) :
    m₁.canonicalSMILES = m₂.canonicalSMILES := h ▸ rfl

end Chem

end
