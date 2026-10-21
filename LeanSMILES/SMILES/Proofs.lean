module

public import LeanSMILES.SMILES.Definitions
public import LeanSMILES.Primitives.Real

/-!
# SMILES — Proofs

Theorems about the definitions in `Definitions.lean`.
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

/-! ## Morgan fingerprints -/

/-- Bit `j` is set exactly when some environment identifier is `≡ j (mod nBits)`. -/
theorem morganFingerprint_bit_iff (m : Molecule) (radius nBits : ℕ) (j : Fin nBits) :
    (m.morganFingerprint radius nBits).bits[j] = true ↔
      ∃ h ∈ m.morganIds radius, h % nBits = j := by
  simp [Molecule.morganFingerprint]

/-- Every atom's radius-0 identifier sets a bit. -/
theorem morganIds_invariant_mem (m : Molecule) (radius : ℕ) (i : ℕ)
    (hi : i < m.atoms.size) : m.morganInvariant i ∈ m.morganIds radius := by
  have h₀ : m.morganInvariant i ∈ ((Array.range m.atoms.size).map m.morganInvariant).toList :=
    by simpa using (⟨i, hi, rfl⟩ : ∃ a < m.atoms.size, m.morganInvariant a = m.morganInvariant i)
  cases radius with
  | zero => exact h₀
  | succ k => exact List.mem_append_left _ h₀

theorem toFeatures_getElem {α : Type} [Primitives.Scalar α] {nBits : ℕ}
    (fp : MorganFingerprint nBits) (j : Fin nBits) :
    (fp.toFeatures (α := α))[j] = if fp.bits[j] then 1 else 0 := by
  simp [MorganFingerprint.toFeatures]

/-! ## Descriptors and similarity over `ℝ` -/

/-- Over `ℝ`, the molecular weight is exactly the sum of the decimal atomic masses. -/
theorem molecularWeight_real (m : Molecule) :
    m.molecularWeight (α := ℝ) = m.molecularWeightExact.toReal :=
  Primitives.Decimal.toScalar_eq_toReal _

theorem filter_zip_self_and_eq_or (l : List Bool) :
    (l.zip l).filter (fun x => x.1 && x.2) = (l.zip l).filter (fun x => x.1 || x.2) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih]

/-- A fingerprint is identical to itself. -/
theorem tanimoto_self {nBits : ℕ} (a : MorganFingerprint nBits) :
    a.tanimoto (α := ℝ) a = 1 := by
  unfold MorganFingerprint.tanimoto
  simp only [Vector.toList_zip, filter_zip_self_and_eq_or]
  split_ifs with h
  · rfl
  · exact div_self (Nat.cast_ne_zero.mpr h)

end Chem

end
