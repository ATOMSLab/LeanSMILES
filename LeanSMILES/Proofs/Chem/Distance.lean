/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/

module

public import LeanSMILES.Proofs.Chem.Matrices
public import LeanSMILES.Polymorphic.Chem.Distance

/-!
# Topological distance — Proofs

Theorems about `Polymorphic/Chem/Distance.lean`. `ball k i` is the set of atoms at most
`k` bonds from atom `i`, and `distance i j` is the first `k ≤ N` with `j ∈ ball k i`
(`N + 1` if there is none).

* **Balls** grow with `k` (`ball_mono`), compose (`mem_ball_add`: a path of `a` bonds then
  one of `b` bonds is a path of `a + b` bonds), and are symmetric
  (`mem_ball_symm`, because bonds are undirected: `mem_nbrs_symm`).
* **`distance` is a metric on atoms**: `distance_self`, `distance_eq_zero_iff`,
  `distance_symm`, `distance_triangle`. It is `1` across every bond of a well-formed
  molecule (`distance_bond`).
* **Matrices**: `distanceMatrix` is symmetric for every `Scalar`; over `ℝ` it has zero
  diagonal, satisfies the triangle inequality entrywise, and the Wiener index is
  non-negative. The topological Coulomb matrix is symmetric.
-/

public section

namespace Chem

open Primitives

namespace Molecule

variable (m : Molecule)

/-! ## Neighbours -/

theorem mem_neighbors {i : ℕ} {p : ℕ × BondOrder} :
    p ∈ m.neighbors i ↔ ∃ b ∈ m.bonds.toList,
      (if b.src = i then some (b.dst, b.order)
        else if b.dst = i then some (b.src, b.order) else none) = some p := by
  simp [neighbors]

/-- Bonds are undirected: `j` is a neighbour of `i` iff `i` is a neighbour of `j`. -/
theorem mem_nbrs_symm {i j : ℕ} (h : j ∈ m.nbrs i) : i ∈ m.nbrs j := by
  simp only [nbrs, List.mem_map] at h ⊢
  obtain ⟨⟨j', o⟩, hp, rfl⟩ := h
  obtain ⟨b, hb, hsome⟩ := (m.mem_neighbors).mp hp
  by_cases h1 : b.src = i
  · simp only [h1, if_true, Option.some.injEq, Prod.mk.injEq] at hsome
    obtain ⟨rfl, rfl⟩ := hsome
    refine ⟨(i, b.order), (m.mem_neighbors).mpr ⟨b, hb, ?_⟩, rfl⟩
    by_cases h2 : b.src = b.dst
    · simp [← h2, h1]
    · rw [if_neg h2, if_pos rfl, h1]
  · simp only [h1, if_false] at hsome
    by_cases h2 : b.dst = i
    · simp only [h2, if_true, Option.some.injEq, Prod.mk.injEq] at hsome
      obtain ⟨rfl, rfl⟩ := hsome
      exact ⟨(i, b.order), (m.mem_neighbors).mpr ⟨b, hb, by simp [h2]⟩, rfl⟩
    · simp [h2] at hsome

theorem mem_nbrs_of_bond {b : Bond} (hb : b ∈ m.bonds.toList) : b.dst ∈ m.nbrs b.src := by
  simp only [nbrs, List.mem_map]
  exact ⟨(b.dst, b.order), (m.mem_neighbors).mpr ⟨b, hb, by simp⟩, rfl⟩

/-! ## Balls -/

theorem mem_ballStep {S : List ℕ} {x : ℕ} :
    x ∈ m.ballStep S ↔ x ∈ S ∨ ∃ v ∈ S, x ∈ m.nbrs v := by
  simp [ballStep, List.mem_eraseDups]

theorem mem_ballStep_of_mem {S : List ℕ} {x : ℕ} (h : x ∈ S) : x ∈ m.ballStep S :=
  (m.mem_ballStep).mpr (Or.inl h)

theorem ballStep_subset {S T : List ℕ} (h : ∀ x ∈ S, x ∈ T) {x : ℕ} (hx : x ∈ m.ballStep S) :
    x ∈ m.ballStep T := by
  rcases (m.mem_ballStep).mp hx with hx | ⟨v, hv, hxv⟩
  · exact m.mem_ballStep_of_mem (h x hx)
  · exact (m.mem_ballStep).mpr (Or.inr ⟨v, h v hv, hxv⟩)

theorem iterate_subset (k : ℕ) {S T : List ℕ} (h : ∀ x ∈ S, x ∈ T) {x : ℕ}
    (hx : x ∈ iterate m.ballStep k S) : x ∈ iterate m.ballStep k T := by
  induction k generalizing S T with
  | zero => exact h x hx
  | succ k ih => exact ih (fun y hy => m.ballStep_subset h hy) hx

theorem mem_iterate_succ {k : ℕ} {S : List ℕ} {x : ℕ} (hx : x ∈ iterate m.ballStep k S) :
    x ∈ iterate m.ballStep (k + 1) S := by
  rw [iterate_succ']
  exact m.mem_ballStep_of_mem hx

theorem mem_iterate_of_le {k k' : ℕ} (hk : k ≤ k') {S : List ℕ} {x : ℕ}
    (hx : x ∈ iterate m.ballStep k S) : x ∈ iterate m.ballStep k' S := by
  induction hk with
  | refl => exact hx
  | step _ ih => exact m.mem_iterate_succ ih

theorem iterate_add (a b : ℕ) (S : List ℕ) :
    iterate m.ballStep (a + b) S = iterate m.ballStep b (iterate m.ballStep a S) := by
  simp only [iterate_eq_iterate]
  rw [add_comm, Function.iterate_add_apply]

theorem mem_ball_zero {i j : ℕ} : j ∈ m.ball 0 i ↔ j = i := by
  simp [ball, iterate]

/-- Balls grow with the radius. -/
theorem ball_mono {k k' : ℕ} (hk : k ≤ k') {i j : ℕ} (h : j ∈ m.ball k i) : j ∈ m.ball k' i :=
  m.mem_iterate_of_le hk h

/-- Paths compose: if `j` is within `a` bonds of `i` and `l` within `b` bonds of `j`, then
`l` is within `a + b` bonds of `i`. -/
theorem mem_ball_add {a b i j l : ℕ} (hj : j ∈ m.ball a i) (hl : l ∈ m.ball b j) :
    l ∈ m.ball (a + b) i := by
  rw [ball, m.iterate_add]
  exact m.iterate_subset b (fun x hx => by rw [List.mem_singleton] at hx; exact hx ▸ hj) hl

theorem mem_ball_one_of_nbrs {i j : ℕ} (h : j ∈ m.nbrs i) : j ∈ m.ball 1 i := by
  simp only [ball, iterate]
  exact (m.mem_ballStep).mpr (Or.inr ⟨i, by simp, h⟩)

/-- Balls are symmetric: `j` is within `k` bonds of `i` iff `i` is within `k` bonds of
`j`. -/
theorem mem_ball_symm {k i j : ℕ} (h : j ∈ m.ball k i) : i ∈ m.ball k j := by
  induction k generalizing i j with
  | zero => rw [m.mem_ball_zero] at h ⊢; exact h.symm
  | succ k ih =>
    have h' : j ∈ m.ballStep (m.ball k i) := by rw [ball, iterate_succ'] at h; exact h
    rcases (m.mem_ballStep).mp h' with hj | ⟨v, hv, hjv⟩
    · exact m.ball_mono (Nat.le_succ k) (ih hj)
    · -- `i ⋯ v` in `k` bonds and `v - j` one bond: so `j - v ⋯ i` in `1 + k` bonds
      have := m.mem_ball_add (m.mem_ball_one_of_nbrs (m.mem_nbrs_symm hjv)) (ih hv)
      rwa [add_comm] at this

/-! ## The first ball containing an atom -/

/-- `firstContaining j (ballsFrom S K)` is the first `t ≤ K` with `j ∈ step^t S`, or
`K + 1`. -/
theorem firstContaining_ballsFrom (K : ℕ) (S : List ℕ) (j : ℕ) :
    firstContaining j (m.ballsFrom S K) ≤ K + 1 ∧
      (firstContaining j (m.ballsFrom S K) ≤ K →
        j ∈ iterate m.ballStep (firstContaining j (m.ballsFrom S K)) S) ∧
      (∀ t ≤ K, j ∈ iterate m.ballStep t S → firstContaining j (m.ballsFrom S K) ≤ t) := by
  induction K generalizing S with
  | zero =>
    by_cases hj : j ∈ S
    · simp [ballsFrom, firstContaining, hj, iterate]
    · simp [ballsFrom, firstContaining, hj, iterate]
  | succ K ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih (m.ballStep S)
    by_cases hj : j ∈ S
    · simp [ballsFrom, firstContaining, hj, iterate]
    · simp only [ballsFrom, firstContaining, hj, if_false]
      refine ⟨by omega, fun h => ih2 (by omega), fun t ht hjt => ?_⟩
      cases t with
      | zero => exact absurd hjt hj
      | succ t => exact Nat.succ_le_succ (ih3 t (by omega) hjt)

theorem distance_le_succ (i j : ℕ) : m.distance i j ≤ m.size + 1 :=
  (m.firstContaining_ballsFrom _ _ j).1

theorem mem_ball_distance {i j : ℕ} (h : m.distance i j ≤ m.size) :
    j ∈ m.ball (m.distance i j) i :=
  (m.firstContaining_ballsFrom _ _ j).2.1 h

theorem distance_le_of_mem_ball {i j k : ℕ} (hk : k ≤ m.size) (h : j ∈ m.ball k i) :
    m.distance i j ≤ k :=
  (m.firstContaining_ballsFrom _ _ j).2.2 k hk h

/-! ## `distance` is a metric -/

@[simp] theorem distance_self (i : ℕ) : m.distance i i = 0 :=
  Nat.le_zero.mp (m.distance_le_of_mem_ball (Nat.zero_le _) ((m.mem_ball_zero).mpr rfl))

theorem distance_eq_zero_iff {i j : ℕ} : m.distance i j = 0 ↔ i = j := by
  constructor
  · intro h
    have := m.mem_ball_distance (i := i) (j := j) (by omega)
    rw [h, m.mem_ball_zero] at this
    exact this.symm
  · rintro rfl
    exact m.distance_self i

theorem distance_symm_le (i j : ℕ) : m.distance j i ≤ m.distance i j := by
  by_cases h : m.distance i j ≤ m.size
  · exact m.distance_le_of_mem_ball h (m.mem_ball_symm (m.mem_ball_distance h))
  · have := m.distance_le_succ j i
    omega

theorem distance_symm (i j : ℕ) : m.distance i j = m.distance j i :=
  le_antisymm (m.distance_symm_le j i) (m.distance_symm_le i j)

/-- **Triangle inequality** for topological distance. -/
theorem distance_triangle (i j l : ℕ) :
    m.distance i l ≤ m.distance i j + m.distance j l := by
  have hle := m.distance_le_succ i l
  by_cases ha : m.distance i j ≤ m.size
  · by_cases hb : m.distance j l ≤ m.size
    · have hpath := m.mem_ball_add (m.mem_ball_distance ha) (m.mem_ball_distance hb)
      by_cases hab : m.distance i j + m.distance j l ≤ m.size
      · exact m.distance_le_of_mem_ball hab hpath
      · omega
    · omega
  · omega

/-- Atoms joined by a bond of a well-formed molecule are at distance `1`. -/
theorem distance_bond (hwf : m.WellFormed) {b : Bond} (hb : b ∈ m.bonds.toList) :
    m.distance b.src b.dst = 1 := by
  obtain ⟨hs, _, hne⟩ := hwf b hb
  have hsize : 1 ≤ m.size := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hs)
  have h1 : m.distance b.src b.dst ≤ 1 :=
    m.distance_le_of_mem_ball hsize (m.mem_ball_one_of_nbrs (m.mem_nbrs_of_bond hb))
  have h0 : m.distance b.src b.dst ≠ 0 := fun h => hne ((m.distance_eq_zero_iff).mp h)
  omega

/-! ## Matrices -/

theorem distanceMatrix_getElem {α : Type} [Scalar α] (i j : Fin m.size) :
    (m.distanceMatrix (α := α))[i][j] = Scalar.fromNat (m.distance i j) := by
  simp [distanceMatrix, distance]

/-- The distance matrix is symmetric, for every `Scalar`. -/
theorem distanceMatrix_symm {α : Type} [Scalar α] (i j : Fin m.size) :
    (m.distanceMatrix (α := α))[i][j] = m.distanceMatrix[j][i] := by
  rw [distanceMatrix_getElem, distanceMatrix_getElem, distance_symm]

theorem distanceMatrix_diag (i : Fin m.size) : (m.distanceMatrix (α := ℝ))[i][i] = 0 := by
  rw [distanceMatrix_getElem, distance_self, fromNat_real, Nat.cast_zero]

theorem distanceMatrix_triangle (i j l : Fin m.size) :
    (m.distanceMatrix (α := ℝ))[i][l] ≤ m.distanceMatrix[i][j] + m.distanceMatrix[j][l] := by
  simp only [distanceMatrix_getElem, fromNat_real]
  exact_mod_cast m.distance_triangle i j l

theorem wienerIndex_nonneg : 0 ≤ m.wienerIndex (α := ℝ) := by
  simp only [wienerIndex, fromNat_real, Nat.cast_ofNat, sumFin_eq_sum, vsum_eq_sum]
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) zero_le_two
  rw [distanceMatrix_getElem, fromNat_real]
  exact Nat.cast_nonneg _

/-- The topological Coulomb matrix is symmetric. -/
theorem coulombMatrix_symm (i j : Fin m.size) :
    (m.coulombMatrix (α := ℝ))[i][j] = m.coulombMatrix[j][i] := by
  have hd := m.distanceMatrix_symm (α := ℝ) i j
  simp only [Fin.getElem_fin] at hd
  simp only [coulombMatrix, Fin.getElem_fin, Vector.getElem_ofFn]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), hd, mul_comm]

end Molecule

end Chem

end
