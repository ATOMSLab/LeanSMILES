/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher
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

/-- Every bond order is at most `4`, the order of a quadruple bond: the upper companion of
`BondKind.order_pos`. -/
theorem BondKind.order_le_four (k : BondKind) : k.order ≤ 4 := by
  cases k <;> norm_num [order]

namespace Molecule

variable {n : ℕ} (m : Molecule n)

/-- **`bondOrder` is the toolkit's bond-order matrix.** -/
theorem bondOrder_eq_adjMatrix (i j : Fin n) : m.bondOrder i j = m.adjMatrix i j := by
  simp [bondOrder, adjMatrix_apply, bondBetween, Bond.edge_eq_mk_iff, Bool.beq_eq_decide_eq]

/-- A `bondOrder` entry is nonnegative: `0` where there is no bond, a positive order elsewhere. -/
theorem bondOrder_nonneg (i j : Fin n) : 0 ≤ m.bondOrder i j := by
  rw [bondOrder]
  cases m.bonds.find? _ <;> simp [(BondKind.order_pos _).le]

/-- A `bondOrder` entry is at most `4`; with `bondOrder_nonneg`, every entry is in `[0, 4]`. -/
theorem bondOrder_le_four (i j : Fin n) : m.bondOrder i j ≤ 4 := by
  rw [bondOrder]
  cases m.bonds.find? _ <;> simp [BondKind.order_le_four]

end Molecule

end LeanSMILES

namespace Pipelines

open LeanSMILES Finset

namespace Representation

variable {a b d : ℕ}

/-- Entry `(i, j)` of a `k × k` matrix flattened row by row sits at `i * k + j < k * k`: the
index `bondOrders_getElem` reads. -/
theorem index_lt {i j k : ℕ} (hi : i < k) (hj : j < k) : i * k + j < k * k := by
  grind [Nat.mul_le_mul_right k hi]

/-- `bondOrders k` lists the toolkit's bond-order matrix row by row. -/
theorem bondOrders_getElem (k : ℕ) (M : Mol) (i j : Fin M.n) (hi : i.val < k) (hj : j.val < k) :
    (bondOrders k M)[i.val * k + j.val]'(index_lt hi hj) = M.mol.adjMatrix i j := by
  have hdiv : (i.val * k + j.val) / k = i.val :=
    Nat.div_eq_of_lt_le (Nat.le_add_right _ _) (by lia)
  simp [bondOrders, hdiv, Nat.mul_add_mod_of_lt hj, Molecule.bondOrder_eq_adjMatrix]

/-- A canonical representation does not depend on how the atoms are numbered. -/
theorem canonical_relabel (r : Representation d) (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    canonical r (M.relabel σ) = canonical r M := by
  simp only [canonical, Mol.canonicalForm, Mol.canonicalSmiles_relabel]

/-! ## Feature bounds -/

/-- `‖r M‖² ≤ R²` for every molecule: a bound on the squared feature norm that holds without
looking at any data, which is what the gradient-descent certificate needs. -/
def Bounded (r : Representation d) (R2 : ℚ) : Prop :=
  ∀ M : Mol, ∑ i : Fin d, (r M)[i] ^ 2 ≤ R2

/-- A feature bound is nonnegative, as it bounds a sum of squares. -/
theorem Bounded.nonneg {r : Representation d} {R2 : ℚ} (h : r.Bounded R2) : 0 ≤ R2 :=
  (sum_nonneg fun _ _ ↦ sq_nonneg _).trans (h Mol.empty)

/-- A feature bound can be raised: any larger number is again a bound. -/
theorem Bounded.mono {r : Representation d} {R2 R2' : ℚ} (h : r.Bounded R2) (h' : R2 ≤ R2') :
    r.Bounded R2' := fun M ↦ (h M).trans h'

/-- Features bounded entrywise by `c` give `‖r M‖² ≤ d c²`. -/
theorem bounded_of_abs_le {r : Representation d} {c : ℚ} (h : ∀ M (i : Fin d), |(r M)[i]| ≤ c) :
    r.Bounded (d * c ^ 2) := fun M ↦
  (sum_le_sum fun i _ ↦ sq_le_sq.2 ((h M i).trans (le_abs_self c))).trans_eq (by simp)

/-- **Morgan fingerprints**: `‖r M‖² ≤ fpSize`. -/
theorem morgan_bounded (radius fpSize : ℕ) : (morgan radius fpSize).Bounded fpSize := by
  simpa using bounded_of_abs_le (r := morgan radius fpSize) (c := 1) fun _ _ ↦ by grind [morgan]

/-- **Bond-order matrices**: `‖r M‖² ≤ 16 k²`. -/
theorem bondOrders_bounded (k : ℕ) : (bondOrders k).Bounded (16 * (k * k)) := by
  simpa [mul_comm] using bounded_of_abs_le (r := bondOrders k) (c := 4) fun _ _ ↦ by
    grind [bondOrders, Molecule.bondOrder_nonneg, Molecule.bondOrder_le_four]

/-- **Clipping bounds any representation**: `‖clip c r M‖² ≤ d c²`. -/
theorem clip_bounded {c : ℚ} (hc : 0 ≤ c) (r : Representation d) : (clip c r).Bounded (d * c ^ 2) :=
  bounded_of_abs_le fun _ _ ↦ by simp [clip, abs_le, hc]

/-- **Canonical forms** keep the feature bound of `r`. -/
theorem canonical_bounded {r : Representation d} {R2 : ℚ} (h : r.Bounded R2) :
    (canonical r).Bounded R2 := fun _ ↦ h _

/-- **Concatenation**: the feature bounds of `r₁` and `r₂` add up. -/
theorem append_bounded {r₁ : Representation a} {r₂ : Representation b} {R₁ R₂ : ℚ}
    (h₁ : r₁.Bounded R₁) (h₂ : r₂.Bounded R₂) : (r₁ ++ r₂).Bounded (R₁ + R₂) := fun M ↦ by
  change ∑ i : Fin (a + b), (r₁ M ++ r₂ M)[i] ^ 2 ≤ R₁ + R₂
  simpa [Fin.sum_univ_add, Vector.getElem_append] using add_le_add (h₁ M) (h₂ M)

end Representation

end Pipelines
