module

public import LeanSMILES.Proofs.ML.Basic
public import LeanSMILES.Polymorphic.Chem.Fingerprint

/-!
# Morgan fingerprints — Proofs

* Bit `j` is set exactly when some environment identifier is `≡ j (mod nBits)`
  (`morganFingerprint_bit_iff`), and every atom's own identifier sets a bit.
* As features, fingerprints are `0/1` vectors (`toFeatures_binary`), so
  `‖φ(mol)‖² ≤ nBits` for every molecule.
* The squared Euclidean distance between two fingerprints' feature vectors is their
  Hamming distance (`distSq_toFeatures`). Hence a linear model's predictions on two
  molecules differ by at most `‖w‖ √hamming` (`score_sub_sq_le_hamming`): molecules with
  similar fingerprints get similar predictions, whatever the training data.
* Tanimoto similarity of a fingerprint with itself is `1`.
-/

public section

namespace Chem

open Primitives

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

theorem toFeatures_getElem {α : Type} [Scalar α] {nBits : ℕ}
    (fp : MorganFingerprint nBits) (j : Fin nBits) :
    (fp.toFeatures (α := α))[j] = if fp.bits[j] then 1 else 0 := by
  simp [MorganFingerprint.toFeatures]

/-! ## Similarity over `ℝ` -/

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

theorem toFeatures_binary {nBits : ℕ} (fp : MorganFingerprint nBits) (j : Fin nBits) :
    (fp.toFeatures (α := ℝ))[j] = 0 ∨ (fp.toFeatures (α := ℝ))[j] = 1 := by
  rw [toFeatures_getElem]
  split_ifs <;> simp

theorem hammingDistance_eq_sum {nBits : ℕ} (a b : MorganFingerprint nBits) :
    a.hammingDistance b = ∑ j : Fin nBits, if a.bits[j] = b.bits[j] then 0 else 1 := by
  rw [MorganFingerprint.hammingDistance, foldl_add_eq_sum, zero_add]

/-- The squared distance between fingerprint features is the Hamming distance. -/
theorem distSq_toFeatures {nBits : ℕ} (a b : MorganFingerprint nBits) :
    distSq (a.toFeatures (α := ℝ)) b.toFeatures = a.hammingDistance b := by
  rw [distSq_eq_sum, hammingDistance_eq_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toFeatures_getElem, toFeatures_getElem]
  cases a.bits[j] <;> cases b.bits[j] <;> simp

/-- **Similar fingerprints, similar predictions.** For any linear model on fingerprint
features, `(score a - score b)² ≤ ‖w‖² · hamming(a, b)`. -/
theorem score_sub_sq_le_hamming {nBits : ℕ} (model : ML.LinearModel ℝ nBits)
    (a b : MorganFingerprint nBits) :
    (model.score a.toFeatures - model.score b.toFeatures) ^ 2 ≤
      normSq model.weights * a.hammingDistance b := by
  rw [← distSq_toFeatures]
  exact ML.score_sub_sq_le model _ _

end Chem

end
