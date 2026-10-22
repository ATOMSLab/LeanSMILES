/-
Copyright (c) 2026 DeMarko Fulcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeMarko Fulcher, Claude (Anthropic)
-/

module

public import LeanSMILES.Proofs.LinAlg
public import LeanSMILES.Polymorphic.Chem.Matrices

/-!
# Matrix representations — Proofs

Theorems about `Polymorphic/Chem/Matrices.lean`. Fix a molecule with `N` atoms and a bond
weighting `w`, and write `W` for its weighted adjacency matrix, `A` for the adjacency
matrix (`w = 1`) and `B` for the bond-order matrix.

For every molecule:

* `W` is symmetric (`weightedAdjacency_symm`), over any `Scalar`.

For well-formed molecules (every bond joins two distinct existing atoms), over `ℝ`:

* **Bond sums** (`sum_sum_weightedAdjacency`): `∑ᵢ ∑ⱼ Wᵢⱼ g(i, j) = ∑_b w_b (g(s, d) + g(d, s))`
  over the bonds `b = (s, d)`. Everything below is an instance.
* `W` has a zero diagonal (`weightedAdjacency_diag`); `A[i][j]` is the number of bonds
  between `i` and `j` (`adjacencyMatrix_getElem`).
* **Degrees** (`rowSums_adjacencyMatrix`): the row sums of `A` are the atom degrees, and
  the row sums of `B` are the bond orders around each atom (`rowSums_bondOrderMatrix`).
* **Handshake lemma** (`sum_degree`): `∑ᵢ deg(i) = 2 · #bonds`.
* **Laplacian** `L = diag(W 𝟙) - W`: symmetric, `L 𝟙 = 0`, `tr L = 2 ∑_b w_b`, and
  `xᵀ L x = ∑_b w_b (x_s - x_d)²` (`quadForm_laplacian`). So `L` is positive semidefinite
  for non-negative weights (`quadForm_laplacian_nonneg`, which covers `laplacianMatrix`
  and `bondOrderLaplacian`), and `xᵀ L x = 0` forces `x` to be equal at the two ends of
  every bond (`eq_of_quadForm_laplacian_eq_zero`): the kernel of `L` is spanned by the
  connected components.
* **Zagreb indices**: `M₁ = ∑ᵢ deg(i)²` and `M₂ = ∑_b deg(s) deg(d)`.
-/

public section

namespace Chem

open Primitives

/-! ## Bonds -/

theorem Bond.joins_comm (b : Bond) (i j : ℕ) : b.joins i j = b.joins j i := by
  simp only [Bond.joins, Bool.or_comm]

/-- The value of `x` at atom `k`, or `0` past the end. -/
abbrev vget {n : ℕ} (x : Vec ℝ n) (k : ℕ) : ℝ := x[k]?.getD 0

@[simp] theorem vget_fin {n : ℕ} (x : Vec ℝ n) (i : Fin n) : vget x i = x[i] := by
  simp [vget]

theorem sum_fin_ite_val_eq {N : ℕ} (d : ℕ) (hd : d < N) (g : ℕ → ℝ) :
    ∑ j : Fin N, (if (j : ℕ) = d then g j else 0) = g d := by
  rw [Finset.sum_eq_single ⟨d, hd⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

/-- For a bond `b = (s, d)` with `s ≠ d`, the indicator of "`b` joins `i` and `j`"
splits into its two orientations. -/
theorem ite_joins (b : Bond) (hne : b.src ≠ b.dst) (i j : ℕ) (c : ℝ) :
    (if b.joins i j then c else 0) =
      (if j = b.dst then (if b.src = i then c else 0) else 0) +
        (if j = b.src then (if b.dst = i then c else 0) else 0) := by
  simp only [Bond.joins, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  by_cases h1 : b.src = i <;> by_cases h2 : b.dst = i <;> by_cases h3 : j = b.dst <;>
    by_cases h4 : j = b.src <;> simp_all <;> omega

/-- Summing over the atoms `j` joined to `i` by a bond `b = (s, d)` picks out the other
end of `b`. -/
theorem sum_ite_joins {N : ℕ} (b : Bond) (hs : b.src < N) (hd : b.dst < N)
    (hne : b.src ≠ b.dst) (i : ℕ) (f : ℕ → ℝ) :
    ∑ j : Fin N, (if b.joins i j then f j else 0) =
      (if b.src = i then f b.dst else 0) + (if b.dst = i then f b.src else 0) := by
  have : ∀ j : Fin N, (if b.joins i j then f j else 0) =
      (if (j : ℕ) = b.dst then (if b.src = i then f j else 0) else 0) +
        (if (j : ℕ) = b.src then (if b.dst = i then f j else 0) else 0) :=
    fun j => ite_joins b hne i j (f j)
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib,
    sum_fin_ite_val_eq _ hd (fun j => if b.src = i then f j else 0),
    sum_fin_ite_val_eq _ hs (fun j => if b.dst = i then f j else 0)]

/-- `(l.map fun b => if p b then 1 else 0).sum` counts the elements satisfying `p`. -/
theorem sum_map_ite_one (l : List Bond) (p : Bond → Bool) :
    (l.map fun b => if p b then (1 : ℝ) else 0).sum = l.countP p := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons]
    split_ifs <;> simp [add_comm]

theorem BondOrder.weight_pos (o : BondOrder) : 0 < (o.weight : ℝ) := by
  cases o <;> simp [BondOrder.weight]

namespace Molecule

variable (m : Molecule)

/-! ## Symmetry -/

/-- The weighted adjacency matrix is symmetric, for every molecule and every `Scalar`. -/
theorem weightedAdjacency_symm {α : Type} [Scalar α] (w : Bond → α) (i j : Fin m.size) :
    (m.weightedAdjacency w)[i][j] = (m.weightedAdjacency w)[j][i] := by
  simp only [weightedAdjacency, Fin.getElem_fin, Vector.getElem_ofFn]
  congr 2
  funext b
  rw [Bond.joins_comm]

theorem adjacencyMatrix_symm {α : Type} [Scalar α] (i j : Fin m.size) :
    (m.adjacencyMatrix (α := α))[i][j] = m.adjacencyMatrix[j][i] :=
  m.weightedAdjacency_symm _ i j

theorem bondOrderMatrix_symm {α : Type} [Scalar α] (i j : Fin m.size) :
    (m.bondOrderMatrix (α := α))[i][j] = m.bondOrderMatrix[j][i] :=
  m.weightedAdjacency_symm _ i j

/-! ## Entries over `ℝ` -/

theorem weightedAdjacency_getElem (w : Bond → ℝ) (i j : Fin m.size) :
    (m.weightedAdjacency w)[i][j] =
      (m.bonds.toList.map fun b => if b.joins i j then w b else 0).sum := by
  simp [weightedAdjacency, listSum_eq_sum]

/-- `A[i][j]` is the number of bonds between atoms `i` and `j`. -/
theorem adjacencyMatrix_getElem (i j : Fin m.size) :
    (m.adjacencyMatrix (α := ℝ))[i][j] = m.bondCount i j := by
  rw [adjacencyMatrix, weightedAdjacency_getElem, bondCount, ← sum_map_ite_one]

theorem wf_mem {m : Molecule} (hwf : m.WellFormed) {b : Bond} (hb : b ∈ m.bonds.toList) :
    b.src < m.size ∧ b.dst < m.size ∧ b.src ≠ b.dst :=
  hwf b hb

/-- The diagonal of `W` is zero: no bond joins an atom to itself. -/
theorem weightedAdjacency_diag (hwf : m.WellFormed) (w : Bond → ℝ) (i : Fin m.size) :
    (m.weightedAdjacency w)[i][i] = 0 := by
  rw [weightedAdjacency_getElem]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
  have hne := (wf_mem hwf hb).2.2
  rw [if_neg]
  simp only [Bond.joins, Bool.or_self, Bool.and_eq_true, beq_iff_eq]
  omega

/-! ## Bond sums -/

/-- **Row sums against a test function**: `∑ⱼ W[i][j] f(j)` adds, over the bonds at `i`,
the weight times `f` at the other end. -/
theorem sum_weightedAdjacency_row (hwf : m.WellFormed) (w : Bond → ℝ) (i : Fin m.size)
    (f : ℕ → ℝ) :
    ∑ j : Fin m.size, (m.weightedAdjacency w)[i][j] * f j =
      (m.bonds.toList.map fun b =>
        w b * ((if b.src = i then f b.dst else 0) + (if b.dst = i then f b.src else 0))).sum := by
  simp only [weightedAdjacency_getElem, ← List.sum_map_mul_right]
  rw [sum_list_map_sum]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  obtain ⟨hs, hd, hne⟩ := wf_mem hwf hb
  have : ∀ j : Fin m.size, (if b.joins i j then w b else 0) * f j =
      w b * (if b.joins i j then f j else 0) := fun j => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.mul_sum, sum_ite_joins b hs hd hne]

/-- **Bond sums**: `∑ᵢ ∑ⱼ W[i][j] g(i, j) = ∑_b w_b (g(s, d) + g(d, s))`. -/
theorem sum_sum_weightedAdjacency (hwf : m.WellFormed) (w : Bond → ℝ) (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin m.size, ∑ j : Fin m.size, (m.weightedAdjacency w)[i][j] * g i j =
      (m.bonds.toList.map fun b => w b * (g b.src b.dst + g b.dst b.src)).sum := by
  simp only [fun i : Fin m.size => m.sum_weightedAdjacency_row hwf w i (g i)]
  rw [sum_list_map_sum]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  obtain ⟨hs, hd, hne⟩ := wf_mem hwf hb
  rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin m.size, (if b.src = (i : ℕ) then g i b.dst else 0) = g b.src b.dst := by
    simpa only [eq_comm] using sum_fin_ite_val_eq b.src hs (fun i => g i b.dst)
  have h2 : ∑ i : Fin m.size, (if b.dst = (i : ℕ) then g i b.src else 0) = g b.dst b.src := by
    simpa only [eq_comm] using sum_fin_ite_val_eq b.dst hd (fun i => g i b.src)
  rw [h1, h2]

/-! ## Degrees -/

/-- Neighbour lists, summed: each bond at atom `i` contributes once. -/
theorem sum_map_neighbors (l : List Bond) (hl : ∀ b ∈ l, b.src ≠ b.dst) (i : ℕ)
    (g : BondOrder → ℝ) :
    ((l.filterMap fun b =>
        if b.src = i then some (b.dst, b.order)
        else if b.dst = i then some (b.src, b.order) else none).map fun p => g p.2).sum =
      (l.map fun b =>
        g b.order * ((if b.src = i then 1 else 0) + (if b.dst = i then 1 else 0))).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    have hne := hl b (List.mem_cons_self ..)
    rw [List.filterMap_cons, List.map_cons, List.sum_cons,
      ← ih fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')]
    by_cases h1 : b.src = i
    · have h2 : ¬ b.dst = i := fun h => hne (h1.trans h.symm)
      simp [h1, h2]
    · by_cases h2 : b.dst = i <;> simp [h1, h2]

theorem sum_map_neighbors_mol (hwf : m.WellFormed) (i : ℕ) (g : BondOrder → ℝ) :
    ((m.neighbors i).map fun p => g p.2).sum =
      (m.bonds.toList.map fun b =>
        g b.order * ((if b.src = i then 1 else 0) + (if b.dst = i then 1 else 0))).sum :=
  sum_map_neighbors _ (fun _ hb => (wf_mem hwf hb).2.2) i g

/-- Row `i` of `W` sums to the total weight of the bonds at atom `i`. -/
theorem rowSums_weightedAdjacency (hwf : m.WellFormed) (w : Bond → ℝ) (i : Fin m.size) :
    (rowSums (m.weightedAdjacency w))[i] =
      (m.bonds.toList.map fun b =>
        w b * ((if b.src = i then 1 else 0) + (if b.dst = i then 1 else 0))).sum := by
  have := m.sum_weightedAdjacency_row hwf w i fun _ => 1
  simp only [mul_one] at this
  rw [Fin.getElem_fin, rowSums_getElem]
  exact this

/-- **The row sums of `A` are the atom degrees.** -/
theorem rowSums_adjacencyMatrix (hwf : m.WellFormed) (i : Fin m.size) :
    (rowSums (m.adjacencyMatrix (α := ℝ)))[i] = m.degree i := by
  rw [adjacencyMatrix, rowSums_weightedAdjacency m hwf, degree]
  have := m.sum_map_neighbors_mol hwf i fun _ => 1
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one] at this
  rw [← this]

/-- **The row sums of `B` are the bond orders around each atom.** -/
theorem rowSums_bondOrderMatrix (hwf : m.WellFormed) (i : Fin m.size) :
    (rowSums (m.bondOrderMatrix (α := ℝ)))[i] =
      ((m.neighbors i).map fun p => p.2.weight).sum := by
  rw [bondOrderMatrix, rowSums_weightedAdjacency m hwf, m.sum_map_neighbors_mol hwf]

/-- `∑ᵢ (W 𝟙)ᵢ = 2 ∑_b w_b`. -/
theorem sum_rowSums_weightedAdjacency (hwf : m.WellFormed) (w : Bond → ℝ) :
    ∑ i : Fin m.size, (rowSums (m.weightedAdjacency w))[i] =
      2 * (m.bonds.toList.map w).sum := by
  have := m.sum_sum_weightedAdjacency hwf w fun _ _ => 1
  simp only [mul_one, Fin.getElem_fin] at this
  simp only [Fin.getElem_fin, rowSums_getElem, this, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun b _ => by ring)

/-- **Handshake lemma**: the degrees add up to twice the number of bonds. -/
theorem sum_degree (hwf : m.WellFormed) :
    ∑ i : Fin m.size, (m.degree i : ℝ) = 2 * m.bonds.size := by
  have := m.sum_rowSums_weightedAdjacency hwf fun _ => 1
  simp only [List.map_const', List.sum_replicate, nsmul_eq_mul, mul_one,
    Array.length_toList] at this
  rw [← this]
  exact Finset.sum_congr rfl fun i _ => (m.rowSums_adjacencyMatrix hwf i).symm

/-! ## Laplacians -/

/-- **The Laplacian quadratic form**: `xᵀ L x = ∑_b w_b (x_s - x_d)²`. -/
theorem quadForm_laplacian (hwf : m.WellFormed) (w : Bond → ℝ) (x : Vec ℝ m.size) :
    quadForm (laplacianOf (m.weightedAdjacency w)) x =
      (m.bonds.toList.map fun b => w b * (vget x b.src - vget x b.dst) ^ 2).sum := by
  set W := m.weightedAdjacency w with hWdef
  have hW := m.sum_sum_weightedAdjacency hwf w fun a b => vget x a * vget x b
  have hD := m.sum_sum_weightedAdjacency hwf w fun a _ => vget x a * vget x a
  rw [← hWdef] at hW hD
  simp only [Fin.getElem_fin, vget_fin] at hW hD
  rw [quadForm_eq_sum]
  simp only [Fin.getElem_fin, laplacianOf_getElem, sub_mul, Finset.sum_sub_distrib]
  -- the degree part: `∑ᵢ (W 𝟙)ᵢ xᵢ²`
  have hdeg : ∑ i : Fin m.size, ∑ j : Fin m.size,
      (if (i : ℕ) = j then ∑ k : Fin m.size, W[(i : ℕ)][(k : ℕ)] else 0) *
        (x[(i : ℕ)] * x[(j : ℕ)]) =
      ∑ i : Fin m.size, ∑ k : Fin m.size, W[(i : ℕ)][(k : ℕ)] * (x[(i : ℕ)] * x[(i : ℕ)]) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun h => hj (Fin.ext h).symm),
      zero_mul]) (by simp)]
    simp [Finset.sum_mul]
  rw [hdeg, hD, hW, list_sum_map_sub]
  exact congrArg List.sum (List.map_congr_left fun b _ => by ring)

/-- **Laplacians with non-negative weights are positive semidefinite.** -/
theorem quadForm_laplacian_nonneg (hwf : m.WellFormed) (w : Bond → ℝ)
    (hw : ∀ b ∈ m.bonds.toList, 0 ≤ w b) (x : Vec ℝ m.size) :
    0 ≤ quadForm (laplacianOf (m.weightedAdjacency w)) x := by
  rw [m.quadForm_laplacian hwf]
  exact List.sum_nonneg fun t ht => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact mul_nonneg (hw b hb) (sq_nonneg _)

/-- **The kernel of a Laplacian is constant along bonds.** With positive weights,
`xᵀ L x = 0` forces `x` to take the same value at both ends of every bond, so `x` is
constant on each connected fragment. -/
theorem eq_of_quadForm_laplacian_eq_zero (hwf : m.WellFormed) (w : Bond → ℝ)
    (hw : ∀ b ∈ m.bonds.toList, 0 < w b) (x : Vec ℝ m.size)
    (h : quadForm (laplacianOf (m.weightedAdjacency w)) x = 0) :
    ∀ b ∈ m.bonds.toList, vget x b.src = vget x b.dst := by
  rw [m.quadForm_laplacian hwf] at h
  intro b hb
  have hnn : ∀ t ∈ m.bonds.toList.map (fun b => w b * (vget x b.src - vget x b.dst) ^ 2),
      0 ≤ t := fun t ht => by
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp ht
    exact mul_nonneg (hw b' hb').le (sq_nonneg _)
  have hle := List.single_le_sum hnn _ (List.mem_map_of_mem (f := fun b =>
    w b * (vget x b.src - vget x b.dst) ^ 2) hb)
  have hzero : w b * (vget x b.src - vget x b.dst) ^ 2 = 0 :=
    le_antisymm (h ▸ hle) (mul_nonneg (hw b hb).le (sq_nonneg _))
  have := (mul_eq_zero.mp hzero).resolve_left (hw b hb).ne'
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

theorem laplacianOf_weightedAdjacency_symm (w : Bond → ℝ) (i j : Fin m.size) :
    (laplacianOf (m.weightedAdjacency w))[i][j] = (laplacianOf (m.weightedAdjacency w))[j][i] :=
  laplacianOf_symm _ (m.weightedAdjacency_symm w) i j

/-- `tr L = 2 ∑_b w_b`. -/
theorem trace_laplacian (hwf : m.WellFormed) (w : Bond → ℝ) :
    trace (laplacianOf (m.weightedAdjacency w)) = 2 * (m.bonds.toList.map w).sum := by
  rw [trace_eq_sum, ← m.sum_rowSums_weightedAdjacency hwf w]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd := m.weightedAdjacency_diag hwf w i
  simp only [Fin.getElem_fin] at hd
  simp [laplacianOf_getElem, hd]

/-- The Kirchhoff Laplacian `D - A` is positive semidefinite. -/
theorem quadForm_laplacianMatrix_nonneg (hwf : m.WellFormed) (x : Vec ℝ m.size) :
    0 ≤ quadForm m.laplacianMatrix x :=
  m.quadForm_laplacian_nonneg hwf _ (fun _ _ => zero_le_one) x

/-- `xᵀ (D - A) x = ∑_bonds (x_s - x_d)²`. -/
theorem quadForm_laplacianMatrix (hwf : m.WellFormed) (x : Vec ℝ m.size) :
    quadForm m.laplacianMatrix x =
      (m.bonds.toList.map fun b => (vget x b.src - vget x b.dst) ^ 2).sum := by
  rw [laplacianMatrix, adjacencyMatrix, m.quadForm_laplacian hwf]
  simp

/-- The bond-order Laplacian is positive semidefinite. -/
theorem quadForm_bondOrderLaplacian_nonneg (hwf : m.WellFormed) (x : Vec ℝ m.size) :
    0 ≤ quadForm m.bondOrderLaplacian x :=
  m.quadForm_laplacian_nonneg hwf _ (fun b _ => (BondOrder.weight_pos b.order).le) x

/-- `tr (D - A) = 2 · #bonds`. -/
theorem trace_laplacianMatrix (hwf : m.WellFormed) :
    trace (m.laplacianMatrix (α := ℝ)) = 2 * m.bonds.size := by
  rw [laplacianMatrix, adjacencyMatrix, m.trace_laplacian hwf]
  simp

/-! ## Zagreb indices -/

/-- `M₁ = ∑ᵢ deg(i)²`. -/
theorem firstZagreb_eq (hwf : m.WellFormed) :
    m.firstZagreb (α := ℝ) = ∑ i : Fin m.size, (m.degree i : ℝ) ^ 2 := by
  rw [firstZagreb, normSq_eq_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [m.rowSums_adjacencyMatrix hwf i]

/-- `M₂ = ∑_bonds deg(s) deg(d)`. -/
theorem secondZagreb_eq (hwf : m.WellFormed) :
    m.secondZagreb (α := ℝ) =
      (m.bonds.toList.map fun b => vget (rowSums (m.adjacencyMatrix (α := ℝ))) b.src *
        vget (rowSums (m.adjacencyMatrix (α := ℝ))) b.dst).sum := by
  simp only [secondZagreb, adjacencyMatrix, quadForm_eq_sum, fromNat_real, Nat.cast_ofNat]
  set d := rowSums (m.weightedAdjacency fun _ => (1 : ℝ))
  have h := m.sum_sum_weightedAdjacency hwf (fun _ => 1) fun a b => vget d a * vget d b
  simp only [Fin.getElem_fin, vget_fin, one_mul] at h
  simp only [Fin.getElem_fin]
  rw [h, div_eq_iff two_ne_zero, ← List.sum_map_mul_right]
  exact congrArg List.sum (List.map_congr_left fun b _ => by ring)

/-! ## Bits -/

theorem adjacencyBits_binary (i j : Fin m.size) :
    (m.adjacencyBits (α := ℝ))[i][j] = 0 ∨ (m.adjacencyBits (α := ℝ))[i][j] = 1 := by
  simp only [adjacencyBits, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs <;> simp

end Molecule

/-- Padding keeps `0/1` entries `0/1`. -/
theorem padMat_binary {N : ℕ} (k : ℕ) (A : Mat ℝ N N)
    (hA : ∀ i j : Fin N, A[i][j] = 0 ∨ A[i][j] = 1) (i j : Fin k) :
    (padMat k A)[i][j] = 0 ∨ (padMat k A)[i][j] = 1 := by
  simp only [padMat, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs with h
  · exact hA ⟨i, h.1⟩ ⟨j, h.2⟩
  · exact Or.inl rfl

/-- Flattening keeps `0/1` entries `0/1`. -/
theorem flattenMat_binary {a b : ℕ} (A : Mat ℝ a b)
    (hA : ∀ (i : Fin a) (j : Fin b), A[i][j] = 0 ∨ A[i][j] = 1) (k : Fin (a * b)) :
    (flattenMat A)[k] = 0 ∨ (flattenMat A)[k] = 1 := by
  have hb : 0 < b := Nat.pos_of_ne_zero fun h => by simp [h] at k; exact k.elim0
  have h1 : (k : ℕ) / b < a := (Nat.div_lt_iff_lt_mul hb).mpr k.isLt
  have h2 : (k : ℕ) % b < b := Nat.mod_lt _ hb
  simp only [flattenMat, Fin.getElem_fin, Vector.getElem_flatten]
  exact hA ⟨_, h1⟩ ⟨_, h2⟩

/-- Every entry of a flattened matrix bounded entrywise in absolute value is bounded. -/
theorem flattenMat_sq_le {a b : ℕ} (A : Mat ℝ a b) {c : ℝ}
    (hA : ∀ (i : Fin a) (j : Fin b), A[i][j] ^ 2 ≤ c) (k : Fin (a * b)) :
    (flattenMat A)[k] ^ 2 ≤ c := by
  have hb : 0 < b := Nat.pos_of_ne_zero fun h => by simp [h] at k; exact k.elim0
  have h1 : (k : ℕ) / b < a := (Nat.div_lt_iff_lt_mul hb).mpr k.isLt
  have h2 : (k : ℕ) % b < b := Nat.mod_lt _ hb
  simp only [flattenMat, Fin.getElem_fin, Vector.getElem_flatten]
  exact hA ⟨_, h1⟩ ⟨_, h2⟩

end Chem

end
