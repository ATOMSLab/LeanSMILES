/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.Canon

/-!
# LeanSMILES.SMILES.Canonicity

The canonical SMILES is canonical: relabeling the atoms of a molecule does
not change the string (`Molecule.canonicalSmiles_relabel`), with no
hypothesis.

The proof follows the algorithm.  A relabeling `σ` acts on rank vectors by
`relabelVec σ` and on the search data by `MolData.relabel`, and every stage of
the search commutes with that action: the atom invariants
(`atomInvariant_relabel`), the ranking of invariants (`ranksOf_relabel`), one
refinement step and refinement to a fixed point (`refineOnce_relabel`,
`refine_relabel`), individualization, the lowest tied class and its atoms
(`firstTie_relabel`, `tiedAtoms_relabel_perm`).  So the leaves of the full
tie-breaking search are, up to order, the relabeled leaves of the original
(`leavesAll_relabel_perm`), and the lexicographically smallest string over a
list is the same for any list with the same members (`List.min?_eq_of_mem_iff`).

That each leaf writes the same string under relabeling is where the shape of
the writer pays off: `writeRanked d r` is `d` relabeled into rank order and
written in index order, so `writeRanked_relabel` is `relabel_relabel` — two
relabelings compose — once a discrete ranking is known to be a permutation
(`bijective_rankPos_of_isDiscrete`).  With `n` levels of tie-breaking every
leaf is discrete (`isDiscrete_of_mem_leavesAll`) and there is at least one
(`leavesAll_ne_nil`).

Pruning is sound because it only ever acts on a *verified* symmetry
(`isSymmetry_spec`): an automorphism of the data that fixes the current
ranking and sends an explored tied atom `e` to the atom `a` being skipped.
Such a symmetry carries the subtree under `e` onto the subtree under `a`,
string for string (`leavesAll_symmetry`), so every leaf of the full search
writes the same string as some leaf the pruned search keeps
(`exists_mem_search`), while every leaf the pruned search keeps is a leaf of
the full search (`search_subset_leavesAll`); the two minima agree
(`min?_search_eq`).

Tetrahedral configurations ride along: relabeling moves each one with its
ligands (`relabelStereo`), an automorphism must preserve them, and the steps
that first drop redundant brackets and erase meaningless marks are made of
label-independent tests — a bond-order sum, a canonical string, ranks, a
configuration equal to its own mirror image — so they commute with
relabeling too (`reduce_relabel`).
-/

public section

namespace LeanSMILES

variable {n : ℕ}

/-! ### Permuting `finRange` and vectors -/

/-- `finRange n` mapped by a permutation is a permutation of `finRange n`. -/
lemma map_finRange_perm (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map σ).Perm (List.finRange n) :=
  σ.map_finRange_perm

/-- Counting over `finRange` is invariant under precomposing the predicate with a
permutation. -/
lemma length_filter_finRange_comp (σ : Equiv.Perm (Fin n)) (p : Fin n → Bool) :
    ((List.finRange n).filter fun j ↦ p (σ j)).length = ((List.finRange n).filter p).length := by
  simpa [List.filter_map, Function.comp_def] using ((map_finRange_perm σ).filter p).length_eq

/-- A vector is `relabelVec σ v` iff it has `v[i]` at position `σ i` for every `i`. -/
lemma eq_relabelVec_of_apply {α : Type*} (σ : Equiv.Perm (Fin n)) {v' v : Vector α n}
    (h : ∀ i, v'[σ i] = v[i]) : v' = relabelVec σ v :=
  Vector.ext fun j hj ↦ by simpa using h (σ.symm ⟨j, hj⟩)

/-- A vector's list is its entries in index order. -/
lemma toList_eq_map_finRange {α : Type*} (v : Vector α n) :
    v.toList = (List.finRange n).map fun i ↦ v[i] :=
  List.ext_getElem (by simp) fun i _ _ ↦ by simp

/-- Relabeling permutes the entries. -/
lemma toList_relabelVec_perm {α : Type*} (σ : Equiv.Perm (Fin n)) (v : Vector α n) :
    (relabelVec σ v).toList.Perm v.toList := by
  rw [toList_eq_map_finRange, toList_eq_map_finRange]
  refine (List.Perm.of_eq ?_).trans ((map_finRange_perm σ.symm).map _)
  simp [Function.comp_def]

/-- Counting over `finRange` as a `Finset` cardinality. -/
lemma length_filter_finRange_eq_card (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter fun i ↦ p i = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter p)]
  exact congrArg Finset.card (Finset.ext fun i ↦ by simp)

/-! ### The minimum of a list depends only on its members -/

/-- Lists with the same members have the same minimum. -/
lemma _root_.List.min?_eq_of_mem_iff {α : Type*} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] {l₁ l₂ : List α} (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.min? = l₂.min? := by
  rcases h₁ : l₁.min? with _ | a
  · obtain rfl := List.min?_eq_none_iff.mp h₁
    exact (List.min?_eq_none_iff.mpr (List.eq_nil_iff_forall_not_mem.mpr fun x hx ↦
      List.not_mem_nil ((h x).mpr hx))).symm
  · rw [List.min?_eq_some_iff] at h₁
    exact (List.min?_eq_some_iff.mpr ⟨(h a).mp h₁.1, fun b hb ↦ h₁.2 b ((h b).mpr hb)⟩).symm

/-- The minimum of a list is invariant under permutation. -/
lemma _root_.List.Perm.min?_eq {α : Type*} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] {l₁ l₂ : List α} (h : l₁.Perm l₂) : l₁.min? = l₂.min? :=
  List.min?_eq_of_mem_iff fun _ ↦ h.mem_iff

/-! ### Sorting is determined by the multiset -/

/-- `pairLE` is total; with `pairLE_trans` this is what `List.pairwise_mergeSort` needs for
`mergeSort pairLE` to sort. -/
lemma pairLE_total (p q : ℤ × ℤ) : (pairLE p q || pairLE q p) = true := by
  grind [pairLE]

/-- `pairLE` is transitive, as `List.pairwise_mergeSort` requires. -/
lemma pairLE_trans (p q s : ℤ × ℤ) : pairLE p q = true → pairLE q s = true → pairLE p s = true := by
  grind [pairLE]

/-- `pairLE` is antisymmetric, so a list sorted by it is determined by its multiset
(`mergeSort_pairLE_eq_of_perm`). -/
lemma pairLE_antisymm {p q : ℤ × ℤ} (h₁ : pairLE p q = true) (h₂ : pairLE q p = true) : p = q := by
  grind [pairLE]

/-- Sorting two lists that are permutations of each other gives the same list. -/
lemma mergeSort_pairLE_eq_of_perm {l₁ l₂ : List (ℤ × ℤ)} (h : l₁.Perm l₂) :
    l₁.mergeSort pairLE = l₂.mergeSort pairLE :=
  List.Perm.eq_of_pairwise (fun _ _ _ _ h₁ h₂ ↦ pairLE_antisymm h₁ h₂)
    (List.pairwise_mergeSort pairLE_trans pairLE_total l₁)
    (List.pairwise_mergeSort pairLE_trans pairLE_total l₂)
    ((List.mergeSort_perm l₁ pairLE).trans (h.trans (List.mergeSort_perm l₂ pairLE).symm))

/-! ### Ranks commute with relabeling -/

/-- Ranking invariants commutes with relabeling. -/
lemma ranksOf_relabel (σ : Equiv.Perm (Fin n)) (inv : Vector (List ℤ) n) :
    ranksOf (relabelVec σ inv) = relabelVec σ (ranksOf inv) :=
  eq_relabelVec_of_apply σ fun i ↦ by
    simpa [ranksOf] using length_filter_finRange_comp σ.symm fun j ↦ lexLt inv[j] inv[i]

/-- Relabeling keeps the number of classes. -/
lemma numClasses_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    numClasses (relabelVec σ r) = numClasses r :=
  ((toList_relabelVec_perm σ r).dedup).length_eq

/-- Relabeling keeps discreteness. -/
lemma isDiscrete_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    isDiscrete (relabelVec σ r) = isDiscrete r := by
  simp [isDiscrete, numClasses_relabel]

/-- Individualizing commutes with relabeling. -/
lemma individualize_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) (a : Fin n) :
    individualize (relabelVec σ r) (σ a) = relabelVec σ (individualize r a) :=
  eq_relabelVec_of_apply σ fun i ↦ by simp [individualize, σ.injective.eq_iff]

/-- The lowest tied rank does not depend on labels. -/
lemma firstTie_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    firstTie (relabelVec σ r) = firstTie r := by
  unfold firstTie
  refine List.Perm.min?_eq
    ((List.Perm.of_eq ?_).trans (((map_finRange_perm σ.symm).filter _).map _))
  simp [List.filter_map, Function.comp_def, (toList_relabelVec_perm σ r).count_eq]

/-- The atoms of a rank after relabeling are the relabeled atoms of that rank, up to order. -/
lemma tiedAtoms_relabel_perm (σ : Equiv.Perm (Fin n)) (r : Ranks n) (c : ℕ) :
    (tiedAtoms (relabelVec σ r) c).Perm ((tiedAtoms r c).map σ) := by
  unfold tiedAtoms
  refine ((map_finRange_perm σ).filter _).symm.trans (List.Perm.of_eq ?_)
  simp [List.filter_map, Function.comp_def]

/-! ### Classes and ties -/

/-- There are at most `n` classes. -/
lemma numClasses_le (r : Ranks n) : numClasses r ≤ n := by
  simpa [numClasses] using (List.dedup_sublist r.toList).length_le

/-- Discrete means `n` classes. -/
lemma isDiscrete_iff (r : Ranks n) : isDiscrete r = true ↔ numClasses r = n := by
  simp [isDiscrete]

/-- The atoms of rank `c` are exactly those ranked `c`. -/
lemma mem_tiedAtoms {r : Ranks n} {c : ℕ} {a : Fin n} : a ∈ tiedAtoms r c ↔ r[a] = c := by
  simp [tiedAtoms]

/-- `tiedAtoms` lists each atom once. -/
lemma nodup_tiedAtoms (r : Ranks n) (c : ℕ) : (tiedAtoms r c).Nodup :=
  (List.nodup_finRange n).filter _

/-- The number of atoms of rank `c` is the multiplicity of `c`. -/
lemma length_tiedAtoms (r : Ranks n) (c : ℕ) : (tiedAtoms r c).length = r.toList.count c := by
  rw [tiedAtoms, List.count_eq_countP, List.countP_eq_length_filter, toList_eq_map_finRange,
    List.filter_map, List.length_map]
  rfl

/-- A tie is a rank shared by at least two atoms. -/
lemma two_le_length_tiedAtoms {r : Ranks n} {c : ℕ} (h : firstTie r = some c) :
    2 ≤ (tiedAtoms r c).length := by
  unfold firstTie at h
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.min?_mem h)
  simpa [length_tiedAtoms] using (List.mem_filter.mp ha).2

/-- A tied rank has an atom. -/
lemma exists_mem_tiedAtoms {r : Ranks n} {c : ℕ} (h : firstTie r = some c) :
    ∃ a, a ∈ tiedAtoms r c :=
  List.exists_mem_of_length_pos (Nat.zero_lt_two.trans_le (two_le_length_tiedAtoms h))

/-- A tied rank has an atom other than any given one. -/
lemma exists_ne_of_firstTie {r : Ranks n} {c : ℕ} (h : firstTie r = some c) (a : Fin n) :
    ∃ b, b ≠ a ∧ r[b] = c := by
  by_contra! hne
  -- otherwise `a` is the only atom of rank `c`, but a tied class has two
  have hsub : tiedAtoms r c ⊆ [a] := fun b hb ↦
    List.mem_singleton.mpr (not_not.mp fun hba ↦ hne b hba (mem_tiedAtoms.mp hb))
  have h1 := ((nodup_tiedAtoms r c).subperm hsub).length_le
  have h2 := two_le_length_tiedAtoms h
  rw [List.length_singleton] at h1
  lia

/-- No tie means every atom has its own rank. -/
lemma isDiscrete_of_firstTie_eq_none {r : Ranks n} (h : firstTie r = none) :
    isDiscrete r = true := by
  unfold firstTie at h
  simp only [List.min?_eq_none_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff, List.mem_finRange,
    true_implies, decide_eq_true_eq, not_le] at h
  -- no rank is shared, so the ranks are pairwise distinct and `dedup` keeps all `n` of them
  have hnd : r.toList.Nodup := List.nodup_iff_count_le_one.mpr fun x ↦ by
    by_cases hx : x ∈ r.toList
    · rw [toList_eq_map_finRange, List.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact Nat.lt_succ_iff.mp (h a)
    · simp [List.count_eq_zero.mpr hx]
  rw [isDiscrete_iff, numClasses, hnd.dedup, Vector.length_toList]

/-- The number of classes is the number of distinct ranks. -/
lemma numClasses_eq_card_image (r : Ranks n) :
    numClasses r = (Finset.univ.image fun i : Fin n ↦ r[i]).card := by
  rw [numClasses, ← List.card_toFinset]
  exact congrArg Finset.card (Finset.ext fun x ↦ by simp [toList_eq_map_finRange])

/-- Individualizing an atom of a tied class splits that class. -/
lemma numClasses_lt_numClasses_individualize {r : Ranks n} {c : ℕ} (hc : firstTie r = some c)
    {a : Fin n} (ha : r[a] = c) : numClasses r < numClasses (individualize r a) := by
  obtain ⟨b, hba, hb⟩ := exists_ne_of_firstTie hc a
  simp only [Fin.getElem_fin] at ha hb
  -- the new ranks are `2 * c` for `a` and `2 * v + 1` for the others, so every old rank `v` still
  -- occurs (through `a`'s classmate `b` when `v = c`) and the even rank `2 * c` is new
  have himg : (Finset.univ.image fun i : Fin n ↦ (individualize r a)[i])
      = insert (2 * c) ((Finset.univ.image fun i : Fin n ↦ r[i]).image fun v ↦ 2 * v + 1) := by
    ext x
    simp only [individualize, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_insert]
    grind
  have hinj : Function.Injective fun v : ℕ ↦ 2 * v + 1 :=
    fun x y (h : 2 * x + 1 = 2 * y + 1) ↦ by lia
  rw [numClasses_eq_card_image, numClasses_eq_card_image, himg, Finset.card_insert_of_notMem,
    Finset.card_image_of_injective _ hinj]
  · exact Nat.lt_succ_self _
  · grind

/-! ### Discrete ranks are permutations -/

/-- Position in rank order respects rank. -/
lemma rankPos_lt_rankPos {r : Ranks n} {i j : Fin n} (h : r[i] < r[j]) :
    rankPos r i < rankPos r j := by
  simp only [Fin.lt_def, rankPos, length_filter_finRange_eq_card]
  refine Finset.card_lt_card
    ((Finset.ssubset_iff_of_subset fun k hk ↦ ?_).mpr ⟨i, by simpa using h, by simp⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hk ⊢
  lia

/-- A discrete ranking gives distinct atoms distinct ranks. -/
lemma injective_getElem_of_isDiscrete {r : Ranks n} (h : isDiscrete r = true) :
    Function.Injective fun i : Fin n ↦ r[i] := by
  rw [isDiscrete_iff, numClasses] at h
  -- `dedup` drops nothing, so the ranks are pairwise distinct
  have hnd : r.toList.Nodup := List.dedup_eq_self.mp <|
    (List.dedup_sublist _).eq_of_length (h.trans Vector.length_toList.symm)
  rwa [toList_eq_map_finRange, ← List.ofFn_eq_map, List.nodup_ofFn] at hnd

/-- A discrete ranking's positions form a permutation. -/
lemma bijective_rankPos_of_isDiscrete {r : Ranks n} (h : isDiscrete r = true) :
    Function.Bijective (rankPos r) :=
  Finite.injective_iff_bijective.mp fun _ _ hij ↦ injective_getElem_of_isDiscrete h <|
    le_antisymm (not_lt.mp fun hlt ↦ (rankPos_lt_rankPos hlt).ne hij.symm)
      (not_lt.mp fun hlt ↦ (rankPos_lt_rankPos hlt).ne hij)

/-- Position in rank order does not depend on labels. -/
lemma rankPos_relabel_apply (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    rankPos (relabelVec σ r) (σ i) = rankPos r i :=
  Fin.ext <| by
    simpa [rankPos] using length_filter_finRange_comp σ.symm fun j ↦ decide (r[j] < r[i])

/-- Positions after relabeling are positions before, read through the relabeling. -/
lemma rankPos_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    rankPos (relabelVec σ r) = rankPos r ∘ σ.symm :=
  funext fun j ↦ by simpa using rankPos_relabel_apply σ r (σ.symm j)

/-- The position table is a permutation table exactly when `rankPos` is a bijection. -/
lemma isPermTable_ofFn_rankPos_iff (r : Ranks n) :
    isPermTable (Vector.ofFn (rankPos r)) = true ↔ Function.Bijective (rankPos r) :=
  ⟨fun h ↦ Finite.surjective_iff_bijective.mp (by simpa using surjective_of_isPermTable h),
    fun h ↦ by simpa [isPermTable, Function.Surjective] using h.2⟩

/-- On a discrete ranking, `permOfRanks` is `rankPos`. -/
lemma permOfRanks_apply {r : Ranks n} (h : Function.Bijective (rankPos r)) (i : Fin n) :
    permOfRanks r i = rankPos r i := by
  simp only [permOfRanks, dif_pos ((isPermTable_ofFn_rankPos_iff r).mpr h), Equiv.coe_fn_mk,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- Relabeling by `σ` and then into rank order is going into rank order directly. -/
lemma permOfRanks_relabel (σ : Equiv.Perm (Fin n)) {r : Ranks n}
    (h : Function.Bijective (rankPos r)) :
    σ.trans (permOfRanks (relabelVec σ r)) = permOfRanks r := by
  have h' : Function.Bijective (rankPos (relabelVec σ r)) :=
    rankPos_relabel σ r ▸ h.comp σ.symm.bijective
  refine Equiv.ext fun i ↦ ?_
  rw [Equiv.trans_apply, permOfRanks_apply h', permOfRanks_apply h, rankPos_relabel_apply]

namespace MolData

variable (d : MolData n)

/-! ### The search commutes with relabeling -/

/-- Degree does not depend on labels. -/
lemma degree_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).degree (σ i) = d.degree i := by
  simpa [degree, bonds_relabel] using length_filter_finRange_comp σ.symm fun j ↦ d.bonds i j != 0

/-- An atom's invariant does not depend on its label. -/
lemma atomInvariant_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).atomInvariant (σ i) = d.atomInvariant i := by
  simp [atomInvariant, degree_relabel, Function.comp_def]

/-- The invariant vector of the relabeled data is the relabeled invariant vector. -/
lemma ofFn_atomInvariant_relabel (σ : Equiv.Perm (Fin n)) :
    Vector.ofFn (d.relabel σ).atomInvariant = relabelVec σ (Vector.ofFn d.atomInvariant) :=
  eq_relabelVec_of_apply σ fun i ↦ by simp [atomInvariant_relabel]

/-- An atom's sorted neighbor pairs do not depend on labels. -/
lemma neighborInvariant_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    (d.relabel σ).neighborInvariant (relabelVec σ r) (σ i) = d.neighborInvariant r i := by
  unfold neighborInvariant
  refine mergeSort_pairLE_eq_of_perm
    ((List.Perm.of_eq ?_).trans ((map_finRange_perm σ.symm).filterMap _))
  simp [List.filterMap_map, bonds_relabel, BondMatrix.kindAt]

/-- One refinement step's invariants commute with relabeling. -/
lemma refineInvariant_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    (d.relabel σ).refineInvariant (relabelVec σ r) = relabelVec σ (d.refineInvariant r) :=
  eq_relabelVec_of_apply σ fun i ↦ by simp [refineInvariant, neighborInvariant_relabel]

/-- One refinement step commutes with relabeling. -/
lemma refineOnce_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    (d.relabel σ).refineOnce (relabelVec σ r) = relabelVec σ (d.refineOnce r) := by
  simp only [refineOnce, refineInvariant_relabel, ranksOf_relabel]

/-- Refinement commutes with relabeling. -/
lemma refine_relabel (σ : Equiv.Perm (Fin n)) (fuel : ℕ) (r : Ranks n) :
    (d.relabel σ).refine fuel (relabelVec σ r) = relabelVec σ (d.refine fuel r) := by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    simp only [refine, refineOnce_relabel, numClasses_relabel]
    split_ifs <;> simp [ih]

/-- The initial ranks of the relabeled data are the relabeled initial ranks. -/
lemma initialRanks_relabel (σ : Equiv.Perm (Fin n)) :
    (d.relabel σ).initialRanks = relabelVec σ d.initialRanks := by
  simp only [initialRanks, ofFn_atomInvariant_relabel, ranksOf_relabel, refine_relabel]

/-- Refinement never merges classes. -/
lemma numClasses_le_numClasses_refine (fuel : ℕ) (r : Ranks n) :
    numClasses r ≤ numClasses (d.refine fuel r) := by
  induction fuel generalizing r with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [refine]
    split_ifs with h
    · exact le_rfl
    · exact (not_le.mp h).le.trans (ih _)

-- One level of tie-breaking spends one unit of fuel: individualizing a tied atom adds a class and
-- refining never merges any, so `n ≤ numClasses + fuel` survives the descent.
private lemma le_numClasses_refine_individualize_add {r : Ranks n} {c : ℕ}
    (hc : firstTie r = some c) {a : Fin n} (ha : a ∈ tiedAtoms r c) {fuel : ℕ}
    (hf : n ≤ numClasses r + (fuel + 1)) :
    n ≤ numClasses (d.refine n (individualize r a)) + fuel := by
  have h1 := numClasses_lt_numClasses_individualize hc (mem_tiedAtoms.mp ha)
  have h2 := d.numClasses_le_numClasses_refine n (individualize r a)
  lia

/-- The leaves of the relabeled data are the relabeled leaves, up to order. -/
theorem leavesAll_relabel_perm (σ : Equiv.Perm (Fin n)) (fuel : ℕ) (r : Ranks n) :
    ((d.relabel σ).leavesAll fuel (relabelVec σ r)).Perm
      ((d.leavesAll fuel r).map (relabelVec σ)) := by
  induction fuel generalizing r with
  | zero => simp [leavesAll]
  | succ fuel ih =>
    simp only [leavesAll, isDiscrete_relabel, firstTie_relabel]
    split_ifs with hd
    · simp
    · rcases hc : firstTie r with _ | c
      · simp
      · dsimp only
        rw [List.map_flatMap]
        refine ((tiedAtoms_relabel_perm σ r c).flatMap_right _).trans ?_
        rw [List.flatMap_map]
        refine List.Perm.flatMap_left _ fun a _ ↦ ?_
        rw [individualize_relabel, refine_relabel]
        exact ih _

/-- Each level of tie-breaking adds a class, so with `n` levels every leaf is discrete. -/
theorem isDiscrete_of_mem_leavesAll : ∀ (fuel : ℕ) (r : Ranks n),
    n ≤ numClasses r + fuel → ∀ l ∈ d.leavesAll fuel r, isDiscrete l = true
  | 0, r, h, l, hl => by
    obtain rfl : l = r := by simpa [leavesAll] using hl
    exact (isDiscrete_iff _).mpr (le_antisymm (numClasses_le _) (by simpa using h))
  | fuel + 1, r, h, l, hl => by
    simp only [leavesAll] at hl
    split_ifs at hl with hd
    · exact List.mem_singleton.mp hl ▸ hd
    · rcases hc : firstTie r with _ | c
      · simp only [hc, List.mem_singleton] at hl
        exact hl ▸ isDiscrete_of_firstTie_eq_none hc
      · simp only [hc, List.mem_flatMap] at hl
        obtain ⟨a, ha, hl⟩ := hl
        exact isDiscrete_of_mem_leavesAll fuel _ (d.le_numClasses_refine_individualize_add hc ha h)
          l hl

/-- The search always finds a leaf. -/
theorem leavesAll_ne_nil : ∀ (fuel : ℕ) (r : Ranks n), d.leavesAll fuel r ≠ []
  | 0, r => by simp [leavesAll]
  | fuel + 1, r => by
    simp only [leavesAll]
    split_ifs
    · simp
    · rcases hc : firstTie r with _ | c
      · simp
      · obtain ⟨x, hx⟩ := exists_mem_tiedAtoms hc
        exact fun h ↦ leavesAll_ne_nil fuel _ (List.flatMap_eq_nil_iff.mp h x hx)

/-- The string a discrete ranking writes does not depend on labels. -/
lemma writeRanked_relabel (σ : Equiv.Perm (Fin n)) {r : Ranks n}
    (h : Function.Bijective (rankPos r)) :
    (d.relabel σ).writeRanked (relabelVec σ r) = d.writeRanked r := by
  simp only [writeRanked, relabel_relabel, permOfRanks_relabel σ h]

/-! ### Pruning is sound -/

/-- What `isAutomorphism` certifies. -/
lemma relabel_eq_self_of_isAutomorphism {γ : Equiv.Perm (Fin n)} (h : d.isAutomorphism γ = true) :
    d.relabel γ = d := by
  simp only [isAutomorphism, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at h
  refine ext ?_ ?_ ?_
  · ext j hj
    simpa using (h (γ.symm ⟨j, hj⟩)).1.1.symm
  · ext i hi j hj
    simpa [relabel] using ((h (γ.symm ⟨i, hi⟩)).2 (γ.symm ⟨j, hj⟩)).symm
  · exact (eq_relabelStereo_of_apply γ fun i ↦ by simpa using (h i).1.2).symm

/-- What `isSymmetry` certifies: an automorphism fixing the ranking and sending `e` to `a`. -/
lemma isSymmetry_spec {r : Ranks n} {e a : Fin n} {γ : Equiv.Perm (Fin n)}
    (h : d.isSymmetry r e a γ = true) : d.relabel γ = d ∧ relabelVec γ r = r ∧ γ e = a := by
  simp only [isSymmetry, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨relabel_eq_self_of_isAutomorphism d h.2, h.1.2, h.1.1⟩

/-- A symmetry carries the subtree under `e` onto the subtree under `a`, string for
string. -/
lemma leavesAll_symmetry {r : Ranks n} {c : ℕ} (hc : firstTie r = some c) {e a : Fin n}
    (he : e ∈ tiedAtoms r c) {γ : Equiv.Perm (Fin n)} (hγ : d.isSymmetry r e a γ = true)
    (fuel : ℕ) (hf : n ≤ numClasses r + (fuel + 1)) :
    ∀ l ∈ d.leavesAll fuel (d.refine n (individualize r a)),
      ∃ l' ∈ d.leavesAll fuel (d.refine n (individualize r e)),
        d.writeRanked l' = d.writeRanked l := by
  obtain ⟨hd, hr, hea⟩ := d.isSymmetry_spec hγ
  -- the subtree under `a` is the subtree under `e` relabeled by `γ`, leaf by leaf
  have hleaves := d.leavesAll_relabel_perm γ fuel (d.refine n (individualize r e))
  rw [← d.refine_relabel, ← individualize_relabel, hr, hea, hd] at hleaves
  intro l hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp (hleaves.mem_iff.mp hl)
  refine ⟨l', hl', ?_⟩
  have hdisc := d.isDiscrete_of_mem_leavesAll fuel _
    (d.le_numClasses_refine_individualize_add hc he hf) l' hl'
  have := (d.writeRanked_relabel γ (bijective_rankPos_of_isDiscrete hdisc)).symm
  rwa [hd] at this

/-- Everything `exploreChildren` returns is a leaf of the full search. -/
theorem exploreChildren_subset (r : Ranks n) (sub : Ranks n → List (Ranks n))
    (first : Ranks n → Ranks n) (L : List (Ranks n)) (T : List (Fin n))
    (hsub : ∀ a ∈ T, ∀ l ∈ sub (d.refine n (individualize r a)), l ∈ L) :
    ∀ (pending : List (Fin n)) (reps : List (Fin n × Equiv.Perm (Fin n))) (acc : List (Ranks n)),
      (∀ a ∈ pending, a ∈ T) → (∀ l ∈ acc, l ∈ L) →
      ∀ l ∈ d.exploreChildren r sub first pending reps acc, l ∈ L
  | [], _, acc, _, hacc, l, hl => hacc l hl
  | a :: pending, reps, acc, hp, hacc, l, hl => by
    obtain ⟨ha, hp⟩ := List.forall_mem_cons.mp hp
    simp only [exploreChildren] at hl
    split_ifs at hl
    · exact exploreChildren_subset r sub first L T hsub pending reps acc hp hacc l hl
    · exact exploreChildren_subset r sub first L T hsub pending _ _ hp
        (fun l' hl' ↦ (List.mem_append.mp hl').elim (hacc l') (hsub a ha l')) l hl

/-- Every leaf under a pending atom writes the same string as something
`exploreChildren` returns, provided the representatives are covered by `acc`. -/
theorem exploreChildren_cover {r : Ranks n} {c : ℕ} (hc : firstTie r = some c) (fuel : ℕ)
    (hf : n ≤ numClasses r + (fuel + 1)) (sub : Ranks n → List (Ranks n))
    (first : Ranks n → Ranks n)
    (hsub : ∀ a ∈ tiedAtoms r c, ∀ l ∈ d.leavesAll fuel (d.refine n (individualize r a)),
      ∃ l' ∈ sub (d.refine n (individualize r a)), d.writeRanked l' = d.writeRanked l) :
    ∀ (pending : List (Fin n)) (reps : List (Fin n × Equiv.Perm (Fin n))) (acc : List (Ranks n)),
      (∀ a ∈ pending, a ∈ tiedAtoms r c) →
      (∀ p ∈ reps, p.1 ∈ tiedAtoms r c ∧
        ∀ l ∈ d.leavesAll fuel (d.refine n (individualize r p.1)),
          ∃ l' ∈ acc, d.writeRanked l' = d.writeRanked l) →
      (∀ l ∈ acc, l ∈ d.exploreChildren r sub first pending reps acc) ∧
      (∀ a ∈ pending, ∀ l ∈ d.leavesAll fuel (d.refine n (individualize r a)),
        ∃ l' ∈ d.exploreChildren r sub first pending reps acc,
          d.writeRanked l' = d.writeRanked l)
  | [], _, acc, _, _ => ⟨fun _ hl ↦ hl, nofun⟩
  | a :: pending, reps, acc, hp, hreps => by
    obtain ⟨ha, hp⟩ := List.forall_mem_cons.mp hp
    simp only [exploreChildren]
    split_ifs with hany
    · -- skipped: the subtree under `a` is the image of a representative's
      obtain ⟨p, hpmem, hsym⟩ := List.any_eq_true.mp hany
      obtain ⟨ih₁, ih₂⟩ := exploreChildren_cover hc fuel hf sub first hsub pending reps acc hp hreps
      refine ⟨ih₁, List.forall_mem_cons.mpr ⟨fun l hl ↦ ?_, ih₂⟩⟩
      obtain ⟨l'', hl'', hw⟩ := d.leavesAll_symmetry hc (hreps p hpmem).1 hsym fuel hf l hl
      exact ((hreps p hpmem).2 l'' hl'').imp fun l' ⟨hl', hw'⟩ ↦ ⟨ih₁ l' hl', hw'.trans hw⟩
    · -- explored: `a` becomes a representative, covered by the new `acc`
      obtain ⟨ih₁, ih₂⟩ := exploreChildren_cover hc fuel hf sub first hsub pending
        ((a, permOfRanks (first (d.refine n (individualize r a)))) :: reps)
        (acc ++ sub (d.refine n (individualize r a))) hp
        (List.forall_mem_cons.mpr
          ⟨⟨ha, fun l hl ↦ (hsub a ha l hl).imp fun _ ↦ And.imp_left (List.mem_append_right _)⟩,
            fun p hpmem ↦ ⟨(hreps p hpmem).1, fun l hl ↦
              ((hreps p hpmem).2 l hl).imp fun _ ↦ And.imp_left (List.mem_append_left _)⟩⟩)
      refine ⟨fun l hl ↦ ih₁ l (List.mem_append_left _ hl),
        List.forall_mem_cons.mpr ⟨fun l hl ↦ ?_, ih₂⟩⟩
      exact (hsub a ha l hl).imp fun l' ⟨hl', hw⟩ ↦ ⟨ih₁ l' (List.mem_append_right _ hl'), hw⟩

/-- The pruned search returns leaves of the full search. -/
theorem search_subset_leavesAll : ∀ (fuel : ℕ) (r : Ranks n),
    ∀ l ∈ d.search fuel r, l ∈ d.leavesAll fuel r
  | 0, r, l, hl => by simpa [search, leavesAll] using hl
  | fuel + 1, r, l, hl => by
    simp only [search, leavesAll] at hl ⊢
    split_ifs at hl ⊢ with hd
    · exact hl
    · rcases hc : firstTie r with _ | c
      · simpa [hc] using hl
      · simp only [hc] at hl ⊢
        exact d.exploreChildren_subset r (d.search fuel) (d.firstLeaf fuel)
          ((tiedAtoms r c).flatMap fun a ↦ d.leavesAll fuel (d.refine n (individualize r a)))
          (tiedAtoms r c)
          (fun a ha l' hl' ↦ List.mem_flatMap.mpr ⟨a, ha, search_subset_leavesAll fuel _ l' hl'⟩)
          (tiedAtoms r c) [] [] (fun _ h ↦ h) nofun l hl

/-- Every leaf of the full search writes the same string as a leaf of the pruned search. -/
theorem exists_mem_search : ∀ (fuel : ℕ) (r : Ranks n), n ≤ numClasses r + fuel →
    ∀ l ∈ d.leavesAll fuel r, ∃ l' ∈ d.search fuel r, d.writeRanked l' = d.writeRanked l
  | 0, r, _, l, hl => ⟨l, by simpa [search, leavesAll] using hl, rfl⟩
  | fuel + 1, r, hf, l, hl => by
    simp only [search, leavesAll] at hl ⊢
    split_ifs at hl ⊢ with hd
    · exact ⟨l, hl, rfl⟩
    · rcases hc : firstTie r with _ | c
      · simp only [hc] at hl ⊢
        exact ⟨l, hl, rfl⟩
      · simp only [hc, List.mem_flatMap] at hl ⊢
        obtain ⟨a, ha, hl⟩ := hl
        exact (d.exploreChildren_cover hc fuel hf (d.search fuel) (d.firstLeaf fuel)
          (fun a ha l hl ↦
            exists_mem_search fuel _ (d.le_numClasses_refine_individualize_add hc ha hf) l hl)
          (tiedAtoms r c) [] [] (fun _ h ↦ h) nofun).2 a ha l hl

/-- The pruned search finds a leaf. -/
lemma search_ne_nil (r : Ranks n) : d.search n r ≠ [] := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (d.leavesAll_ne_nil n r)
  obtain ⟨l', hl', -⟩ := d.exists_mem_search n r (Nat.le_add_left n _) l hl
  exact List.ne_nil_of_mem hl'

/-- Pruning keeps the minimum. -/
theorem min?_search_eq (r : Ranks n) :
    ((d.search n r).map d.writeRanked).min? = ((d.leavesAll n r).map d.writeRanked).min? := by
  refine List.min?_eq_of_mem_iff fun s ↦ ?_
  simp only [List.mem_map]
  exact ⟨fun ⟨l, hl, hw⟩ ↦ ⟨l, d.search_subset_leavesAll n r l hl, hw⟩, fun ⟨l, hl, hw⟩ ↦
    (d.exists_mem_search n r (Nat.le_add_left n _) l hl).imp fun _ ↦ And.imp_right (·.trans hw)⟩

/-! ### The theorem -/

/-- The canonical string of the relabeled data is the canonical string of the data. -/
theorem canonical_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).canonical.2 = d.canonical.2 := by
  -- the smallest string over the search is label-independent …
  have hmin : (((d.relabel σ).search n (d.relabel σ).initialRanks).map
      (d.relabel σ).writeRanked).min? = ((d.search n d.initialRanks).map d.writeRanked).min? := by
    rw [min?_search_eq, min?_search_eq, initialRanks_relabel]
    refine List.Perm.min?_eq (((d.leavesAll_relabel_perm σ n _).map _).trans (List.Perm.of_eq ?_))
    rw [List.map_map]
    exact List.map_congr_left fun l hl ↦ d.writeRanked_relabel σ (bijective_rankPos_of_isDiscrete
      (d.isDiscrete_of_mem_leavesAll n _ (Nat.le_add_left n _) l hl))
  -- … and it exists, since the search finds a leaf
  simp only [canonical, hmin]
  rcases hm : ((d.search n d.initialRanks).map d.writeRanked).min? with _ | s
  · exact absurd (List.map_eq_nil_iff.mp (List.min?_eq_none_iff.mp hm)) (d.search_ne_nil _)
  · rfl

/-! ### Erasing meaningless marks commutes with relabeling

Each test `dropFake` makes is about the data up to relabeling — a canonical
string, a rank, whether a configuration is its own mirror image — so the set
of marks it erases moves with the atoms. -/

lemma _root_.LeanSMILES.all_finRange_comp (σ : Equiv.Perm (Fin n)) (p : Fin n → Bool) :
    ((List.finRange n).all fun i ↦ p (σ i)) = (List.finRange n).all p := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_finRange, true_implies]
  exact ⟨fun h i ↦ by simpa using h (σ.symm i), fun h i ↦ h (σ i)⟩

lemma _root_.LeanSMILES.any_finRange_comp (σ : Equiv.Perm (Fin n)) (p : Fin n → Bool) :
    ((List.finRange n).any fun i ↦ p (σ i)) = (List.finRange n).any p := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_finRange, true_and]
  exact ⟨fun ⟨i, h⟩ ↦ ⟨σ i, h⟩, fun ⟨i, h⟩ ↦ ⟨σ.symm i, by simpa using h⟩⟩

lemma stereo_eraseStereo_apply (p : Fin n → Bool) (i : Fin n) :
    (d.eraseStereo p).stereo[i] = if p i then none else d.stereo[i] := by
  simp [eraseStereo]

lemma stereo_mirrorAt_apply (i j : Fin n) :
    (d.mirrorAt i).stereo[j] = if d.sameUnit i j then d.stereo[j].map Stereo.mirror
      else d.stereo[j] := by
  simp [mirrorAt]

lemma sameUnit_relabel (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (d.relabel σ).sameUnit (σ i) (σ j) = d.sameUnit i j := by
  simp only [sameUnit, stereo_relabel, relabelStereo_apply]
  congr 1
  · rw [beq_eq_decide, beq_eq_decide, decide_eq_decide.mpr σ.injective.eq_iff]
  · congr 1
    · rcases d.stereo[i] with _ | t <;> simp
    · rw [decide_eq_decide.mpr (Option.map_injective (Stereo.map_injective σ)).eq_iff]

lemma eraseStereo_relabel (σ : Equiv.Perm (Fin n)) {p' p : Fin n → Bool}
    (hp : ∀ i, p' (σ i) = p i) : (d.relabel σ).eraseStereo p' = (d.eraseStereo p).relabel σ := by
  refine ext rfl rfl (eq_relabelStereo_of_apply σ fun i ↦ ?_)
  simp only [stereo_eraseStereo_apply, stereo_relabel, relabelStereo_apply, hp]
  split_ifs <;> rfl

lemma mirrorAt_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).mirrorAt (σ i) = (d.mirrorAt i).relabel σ := by
  refine ext rfl rfl (eq_relabelStereo_of_apply σ fun j ↦ ?_)
  simp only [stereo_mirrorAt_apply, stereo_relabel, relabelStereo_apply]
  rw [sameUnit_relabel]
  split_ifs
  · simp only [Option.map_map]
    congr 1
    funext t
    exact (Stereo.map_mirror σ t).symm
  · rfl

lemma selfMirror_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).selfMirror (σ i) = d.selfMirror i := by
  simp only [selfMirror, stereo_relabel, relabelStereo_apply]
  rcases d.stereo[i] with _ | t
  · rfl
  · simp only [Option.map_some, Option.any_some, ← Stereo.map_mirror,
      (Stereo.map_injective σ).eq_iff]

lemma tiedNeighbors_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    (d.relabel σ).tiedNeighbors (relabelVec σ r) (σ i) = d.tiedNeighbors r i := by
  unfold tiedNeighbors
  have h := ((map_finRange_perm σ.symm).filter fun j ↦ d.bonds i j != 0).map fun j ↦ r[j]
  rw [List.filter_map, List.map_map] at h
  have hp : (fun j ↦ (d.relabel σ).bonds (σ i) j != 0) = (fun j ↦ d.bonds i j != 0) ∘ σ.symm := by
    funext j
    simp [bonds_relabel]
  have hf : (fun j : Fin n ↦ (relabelVec σ r)[j]) = (fun j ↦ r[j]) ∘ σ.symm := by
    funext j
    simp
  rw [hp, hf, decide_eq_decide.mpr h.nodup_iff]

lemma candidate_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    (d.relabel σ).candidate (relabelVec σ r) (σ i) = d.candidate r i := by
  unfold candidate
  rw [← any_finRange_comp σ]
  simp only [sameUnit_relabel, tiedNeighbors_relabel]
  simp only [stereo_relabel, relabelStereo_apply, Option.isSome_map]

lemma mirrorInvisible_relabel (σ : Equiv.Perm (Fin n)) (s : String) (i : Fin n) :
    (d.relabel σ).mirrorInvisible s (σ i) = d.mirrorInvisible s i := by
  simp only [mirrorInvisible, mirrorAt_relabel, canonical_relabel]

lemma invisible_relabel (σ : Equiv.Perm (Fin n)) (s : String) (r : Ranks n) :
    (d.relabel σ).invisible s (relabelVec σ r) = relabelVec σ (d.invisible s r) := by
  apply eq_relabelVec_of_apply
  intro i
  simp only [invisible, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  rw [candidate_relabel, mirrorInvisible_relabel]

lemma droppable_relabel (σ : Equiv.Perm (Fin n)) (D : Vector Bool n) (i : Fin n) :
    (d.relabel σ).droppable (relabelVec σ D) (σ i) = d.droppable D i := by
  have e : (d.relabel σ).eraseStereo
        (fun j ↦ (relabelVec σ D)[j] && !(d.relabel σ).sameUnit (σ i) j)
      = (d.eraseStereo fun j ↦ D[j] && !d.sameUnit i j).relabel σ :=
    eraseStereo_relabel d σ fun j ↦ by rw [relabelVec_apply, sameUnit_relabel]
  simp only [droppable, relabelVec_apply, e, mirrorInvisible_relabel, canonical_relabel]

lemma stripStereo_relabel (σ : Equiv.Perm (Fin n)) :
    (d.relabel σ).stripStereo = relabelStereo σ d.stripStereo := by
  have hall : ((List.finRange n).all fun i ↦ (d.relabel σ).stereo[i].isNone)
      = (List.finRange n).all fun i ↦ d.stereo[i].isNone := by
    rw [← all_finRange_comp σ]
    simp
  have hany : ∀ r, (List.finRange n).any ((d.relabel σ).candidate (relabelVec σ r))
      = (List.finRange n).any (d.candidate r) := fun r ↦ by
    rw [← any_finRange_comp σ]
    simp only [candidate_relabel]
  simp only [stripStereo, hall, initialRanks_relabel, hany, invisible_relabel, canonical_relabel]
  split_ifs
  · rfl
  · rw [eraseStereo_relabel d σ (p := d.droppable (d.invisible d.canonical.2 d.initialRanks))
      fun i ↦ droppable_relabel d σ _ i]
    rfl
  · rfl

lemma keptStereo_relabel (σ : Equiv.Perm (Fin n)) :
    (d.relabel σ).keptStereo = relabelStereo σ d.keptStereo := by
  unfold keptStereo
  rw [eraseStereo_relabel d σ fun i ↦ selfMirror_relabel d σ i, stripStereo_relabel]

/-- Erasing the meaningless marks commutes with relabeling. -/
theorem dropFake_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).dropFake = d.dropFake.relabel σ :=
  ext rfl rfl (d.keptStereo_relabel σ)

lemma orderSum_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).orderSum (σ i) = d.orderSum i := by
  simp only [orderSum, bonds_relabel, BondMatrix.relabel_apply, Equiv.symm_apply_apply]
  have h := ((map_finRange_perm σ.symm).map fun j ↦ d.bonds i j).sum_eq
  rwa [List.map_map] at h

lemma normalizeBrackets_relabel (σ : Equiv.Perm (Fin n)) :
    (d.relabel σ).normalizeBrackets = d.normalizeBrackets.relabel σ := by
  refine ext (eq_relabelVec_of_apply σ fun i ↦ ?_) rfl rfl
  simp only [normalizeBrackets, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, atoms_relabel,
    orderSum_relabel]
  rw [← Fin.getElem_fin, relabelVec_apply]
  rfl

/-- Reducing — redundant brackets, then meaningless marks — commutes with
relabeling. -/
theorem reduce_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).reduce = d.reduce.relabel σ := by
  unfold reduce
  rw [normalizeBrackets_relabel, dropFake_relabel]

end MolData

/-- The canonical SMILES does not depend on how the atoms are numbered: every
relabeling of the molecule writes the same string. -/
theorem Molecule.canonicalSmiles_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).canonicalSmiles = m.canonicalSmiles := by
  simp only [canonicalSmiles, MolData.reduceAndCanonical_snd, toMolData_relabel,
    MolData.reduce_relabel, MolData.canonical_relabel]

/-- The canonical SMILES of a bundled molecule does not depend on its atom order. -/
theorem Mol.canonicalSmiles_relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    (M.relabel σ).canonicalSmiles = M.canonicalSmiles :=
  M.mol.canonicalSmiles_relabel σ

end LeanSMILES
