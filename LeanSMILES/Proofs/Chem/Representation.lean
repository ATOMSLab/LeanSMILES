module

public import LeanSMILES.Proofs.Chem.Fingerprint
public import LeanSMILES.Proofs.Chem.Distance
public import LeanSMILES.Polymorphic.Chem.Representation

/-!
# Molecular representations — Feature bounds

The pipeline guarantees (`Proofs/Pipeline.lean`) hold for any data, provided the features
are bounded: `‖φ(mol)‖² ≤ R²` for every molecule. This file proves such bounds, and
they hold for **every** molecule, so checking them needs no data:

| representation | bound `R²` |
|---|---|
| `ofBits bits` (any bit representation) | `n` |
| `morgan radius nBits` | `nBits` |
| `adjacency k` | `k²` |
| `clip c r` | `n c²` |
| `normalize r` | `1` |
| `scale c r` | `c² R²` |
| `r₁ ++ r₂` | `R₁² + R₂²` |

The `0/1` representations (`morgan`, `adjacency`) are `Binary`, and every binary
representation with `n` features is bounded by `n`.
-/

public section

namespace Chem

open Primitives

namespace Representation

variable {n a b : ℕ}

/-- Every molecule's features have squared norm at most `R2`. -/
def Bounded (r : Representation ℝ n) (R2 : ℝ) : Prop :=
  ∀ mol : Molecule, normSq (r.featurize mol) ≤ R2

/-- Every feature of every molecule is `0` or `1`. -/
def Binary (r : Representation ℝ n) : Prop :=
  ∀ (mol : Molecule) (j : Fin n), (r.featurize mol)[j] = 0 ∨ (r.featurize mol)[j] = 1

theorem Bounded.nonneg {r : Representation ℝ n} {R2 : ℝ} (h : r.Bounded R2) : 0 ≤ R2 :=
  (normSq_nonneg _).trans (h default)

theorem Bounded.mono {r : Representation ℝ n} {R2 R2' : ℝ} (h : r.Bounded R2)
    (h' : R2 ≤ R2') : r.Bounded R2' :=
  fun mol => (h mol).trans h'

/-- With the constant feature `1` appended, as the learning algorithms see them. -/
theorem Bounded.augment {r : Representation ℝ n} {R2 : ℝ} (h : r.Bounded R2)
    (mol : Molecule) : normSq (Primitives.augment (r.featurize mol)) ≤ R2 + 1 := by
  rw [normSq_augment]
  linarith [h mol]

theorem Binary.bounded {r : Representation ℝ n} (h : r.Binary) : r.Bounded n :=
  fun mol => normSq_le_of_binary _ (h mol)

/-! ## Basic representations -/

@[simp] theorem ofBits_getElem (bits : Molecule → Vector Bool n) (mol : Molecule) (j : ℕ)
    (hj : j < n) :
    ((ofBits bits : Representation ℝ n).featurize mol)[j] = if (bits mol)[j] then 1 else 0 := by
  simp [ofBits]

theorem ofBits_binary (bits : Molecule → Vector Bool n) :
    (ofBits bits : Representation ℝ n).Binary := fun mol j => by
  simp only [Fin.getElem_fin, ofBits_getElem]
  split_ifs <;> simp

/-- The squared norm of a bit representation counts the set bits. -/
theorem normSq_ofBits (bits : Molecule → Vector Bool n) (mol : Molecule) :
    normSq ((ofBits bits : Representation ℝ n).featurize mol) =
      ∑ j : Fin n, if (bits mol)[j] then (1 : ℝ) else 0 := by
  rw [normSq_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.getElem_fin, ofBits_getElem]
  split_ifs <;> simp

theorem morgan_binary (radius nBits : ℕ) :
    (morgan radius nBits : Representation ℝ nBits).Binary :=
  fun _ j => toFeatures_binary _ j

/-- Morgan fingerprints: `‖φ(mol)‖² ≤ nBits`. -/
theorem morgan_bounded (radius nBits : ℕ) :
    (morgan radius nBits : Representation ℝ nBits).Bounded nBits :=
  (morgan_binary radius nBits).bounded

theorem adjacency_binary (k : ℕ) : (adjacency k : Representation ℝ (k * k)).Binary :=
  fun mol => flattenMat_binary _ (padMat_binary k _ mol.adjacencyBits_binary)

/-- Adjacency bits of `k` atoms: `‖φ(mol)‖² ≤ k²`. -/
theorem adjacency_bounded (k : ℕ) :
    (adjacency k : Representation ℝ (k * k)).Bounded (k * k) := by
  have := (adjacency_binary k).bounded
  simpa using this

/-! ## Combinators -/

theorem append_featurize (r₁ : Representation ℝ a) (r₂ : Representation ℝ b) (mol : Molecule) :
    (r₁ ++ r₂).featurize mol = r₁.featurize mol ++ r₂.featurize mol := rfl

/-- Concatenation adds the bounds. -/
theorem append_bounded {r₁ : Representation ℝ a} {r₂ : Representation ℝ b} {R₁ R₂ : ℝ}
    (h₁ : r₁.Bounded R₁) (h₂ : r₂.Bounded R₂) : (r₁ ++ r₂).Bounded (R₁ + R₂) := by
  intro mol
  rw [append_featurize, normSq_append]
  exact add_le_add (h₁ mol) (h₂ mol)

theorem scale_bounded {r : Representation ℝ n} {R2 : ℝ} (h : r.Bounded R2) (c : ℝ) :
    (scale c r).Bounded (c ^ 2 * R2) := by
  intro mol
  simp only [scale, normSq_smul]
  exact mul_le_mul_of_nonneg_left (h mol) (sq_nonneg c)

theorem clamp_sq_le {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : Scalar.clamp c x ^ 2 ≤ c ^ 2 := by
  have h : -c ≤ Scalar.clamp c x ∧ Scalar.clamp c x ≤ c := by
    simp only [Scalar.clamp, Scalar.max, Scalar.min]
    split_ifs <;> constructor <;> linarith
  exact sq_le_sq' h.1 h.2

/-- Clipping every feature to `[-c, c]` bounds `‖φ(mol)‖²` by `n c²`, whatever the
representation. -/
theorem clip_bounded {c : ℝ} (hc : 0 ≤ c) (r : Representation ℝ n) :
    (clip c r).Bounded (n * c ^ 2) := by
  intro mol
  refine normSq_le_of_sq_le _ fun j => ?_
  simp only [clip, Fin.getElem_fin, Vector.getElem_map]
  exact clamp_sq_le hc _

/-- Normalized features have norm at most `1`, whatever the representation. -/
theorem normalize_bounded (r : Representation ℝ n) : (normalize r).Bounded 1 := by
  intro mol
  simp only [normalize]
  split_ifs with h
  · linarith
  · push Not at h
    rw [normSq_smul, Primitives.norm, div_pow, one_pow]
    change 1 / Real.sqrt (normSq (r.featurize mol)) ^ 2 * normSq (r.featurize mol) ≤ 1
    rw [Real.sq_sqrt h.le, one_div_mul_cancel h.ne']

end Representation

end Chem

end
