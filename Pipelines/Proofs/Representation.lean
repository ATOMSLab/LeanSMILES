/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/
module

public import Pipelines.Representation
public import LeanSMILES.SMILES.Canonicity
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Pipelines.Proofs.Representation

Molecular representations — Proofs.

* `bondOrder_eq_adjMatrix`: the kernel-evaluable `Molecule.bondOrder` is the toolkit's
  bond-order matrix `Molecule.adjMatrix`. So `bondOrders k` is that matrix, padded and
  flattened (`bondOrders_getElem`).
* `canonical_relabel`: a canonical representation gives every relabeling of a molecule
  the same features (from `Mol.canonicalSmiles_relabel`).
* **Feature bounds** (`Bounded r R²`: `‖r M‖² ≤ R²` for **every** molecule), used by the
  gradient-descent certificate, which then needs no data:

  | representation | `R²` |
  |---|---|
  | `morgan radius fpSize` | `fpSize` |
  | `bondOrders k` | `16 k²` (bond orders are at most `4`) |
  | `clip c r` | `d c²` (for any `r`) |
  | `canonical r` | that of `r` |
  | `r₁ ++ r₂` | `R₁² + R₂²` |
-/

@[expose] public section

namespace LeanSMILES

/-! Facts about the toolkit's own types, in its namespace. -/

theorem BondKind.order_le_four (k : BondKind) : k.order ≤ 4 := by
  cases k <;> norm_num [BondKind.order]

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-- **`bondOrder` is the toolkit's bond-order matrix.** -/
theorem bondOrder_eq_adjMatrix (i j : Fin n) : m.bondOrder i j = m.adjMatrix i j := by
  rw [bondOrder, adjMatrix_apply, bondBetween]
  congr 3
  funext b
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Bond.edge_eq_mk_iff]

theorem bondOrder_nonneg (i j : Fin n) : 0 ≤ m.bondOrder i j := by
  rw [bondOrder]
  cases m.bonds.find? _ with
  | none => simp
  | some b => exact (BondKind.order_pos b.kind).le

theorem bondOrder_le_four (i j : Fin n) : m.bondOrder i j ≤ 4 := by
  rw [bondOrder]
  cases m.bonds.find? _ with
  | none => simp
  | some b => simpa using BondKind.order_le_four b.kind

end Molecule

end LeanSMILES

namespace Pipelines

open LeanSMILES Finset

namespace Representation

variable {a b d : ℕ}

theorem index_lt {i j k : ℕ} (hi : i < k) (hj : j < k) : i * k + j < k * k := by
  have := Nat.mul_le_mul_right k (show i + 1 ≤ k by omega)
  rw [Nat.succ_mul] at this
  omega

/-- `bondOrders k` lists the toolkit's bond-order matrix row by row. -/
theorem bondOrders_getElem (k : ℕ) (M : Mol) (i j : Fin M.n) (hi : i.val < k) (hj : j.val < k) :
    (bondOrders k M)[i.val * k + j.val]'(index_lt hi hj) = M.mol.adjMatrix i j := by
  have hk : 0 < k := by omega
  have hdiv : (i.val * k + j.val) / k = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (i.val * k + j.val) % k = j.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [bondOrders, Vector.getElem_ofFn, hdiv, hmod]
  rw [dif_pos ⟨i.isLt, j.isLt⟩]
  exact M.mol.bondOrder_eq_adjMatrix i j

/-- A canonical representation does not depend on how the atoms are numbered. -/
theorem canonical_relabel (r : Representation d) (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    canonical r (M.relabel σ) = canonical r M := by
  simp only [canonical, Mol.canonicalForm, Mol.canonicalSmiles_relabel]

/-! ## Feature bounds -/

/-- `‖r M‖² ≤ R²` for every molecule. -/
def Bounded (r : Representation d) (R2 : ℚ) : Prop :=
  ∀ M : Mol, ∑ i : Fin d, (r M)[i] ^ 2 ≤ R2

theorem Bounded.nonneg {r : Representation d} {R2 : ℚ} (h : r.Bounded R2) : 0 ≤ R2 :=
  (sum_nonneg fun _ _ ↦ sq_nonneg _).trans (h Mol.empty)

theorem Bounded.mono {r : Representation d} {R2 R2' : ℚ} (h : r.Bounded R2) (h' : R2 ≤ R2') :
    r.Bounded R2' := fun M ↦ (h M).trans h'

/-- Features bounded entrywise by `c` give `‖r M‖² ≤ d c²`. -/
theorem bounded_of_abs_le {r : Representation d} {c : ℚ}
    (h : ∀ M (i : Fin d), |(r M)[i]| ≤ c) : r.Bounded (d * c ^ 2) := by
  intro M
  calc ∑ i : Fin d, (r M)[i] ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := sum_le_sum fun i _ ↦ by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h M i) 2
    _ = d * c ^ 2 := by simp

/-- **Morgan fingerprints**: `‖r M‖² ≤ fpSize`. -/
theorem morgan_bounded (radius fpSize : ℕ) : (morgan radius fpSize).Bounded fpSize := by
  have := bounded_of_abs_le (r := morgan radius fpSize) (c := 1) fun _ i ↦ by
    simp only [morgan, Fin.getElem_fin, Vector.getElem_map]
    split_ifs <;> simp
  simpa using this

/-- **Bond-order matrices**: `‖r M‖² ≤ 16 k²`. -/
theorem bondOrders_bounded (k : ℕ) : (bondOrders k).Bounded (16 * (k * k)) := by
  have := bounded_of_abs_le (r := bondOrders k) (c := 4) fun M i ↦ by
    simp only [bondOrders, Fin.getElem_fin, Vector.getElem_ofFn]
    split_ifs
    · rw [abs_of_nonneg (M.mol.bondOrder_nonneg _ _)]
      exact M.mol.bondOrder_le_four _ _
    · norm_num
  refine this.mono (le_of_eq ?_)
  push_cast
  ring

/-- **Clipping bounds any representation**: `‖clip c r M‖² ≤ d c²`. -/
theorem clip_bounded {c : ℚ} (hc : 0 ≤ c) (r : Representation d) :
    (clip c r).Bounded (d * c ^ 2) :=
  bounded_of_abs_le fun M i ↦ by
    simp only [clip, Fin.getElem_fin, Vector.getElem_map]
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (neg_le_self hc) (min_le_left _ _)

theorem canonical_bounded {r : Representation d} {R2 : ℚ} (h : r.Bounded R2) :
    (canonical r).Bounded R2 := fun _ ↦ h _

theorem append_bounded {r₁ : Representation a} {r₂ : Representation b} {R₁ R₂ : ℚ}
    (h₁ : r₁.Bounded R₁) (h₂ : r₂.Bounded R₂) : (r₁ ++ r₂).Bounded (R₁ + R₂) := by
  intro M
  change ∑ i : Fin (a + b), (r₁ M ++ r₂ M)[i] ^ 2 ≤ R₁ + R₂
  rw [Fin.sum_univ_add]
  simp only [Fin.getElem_fin, Fin.val_castAdd, Fin.val_natAdd, Vector.getElem_append]
  refine add_le_add ((le_of_eq (sum_congr rfl fun i _ ↦ ?_)).trans (h₁ M))
    ((le_of_eq (sum_congr rfl fun i _ ↦ ?_)).trans (h₂ M))
  · simp [i.isLt]
  · simp

end Representation

end Pipelines
