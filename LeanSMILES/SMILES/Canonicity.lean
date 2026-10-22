/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import LeanSMILES.SMILES.Canon

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
-/

namespace LeanSMILES

variable {n : ℕ}

/-! ### Permuting `finRange` and vectors -/

/-- `finRange n` mapped by a permutation is a permutation of `finRange n`. -/
lemma map_finRange_perm (σ : Equiv.Perm (Fin n)) :
    ((List.finRange n).map σ).Perm (List.finRange n) :=
  (List.perm_ext_iff_of_nodup ((List.nodup_finRange n).map σ.injective)
    (List.nodup_finRange n)).mpr fun a ↦ ⟨fun _ ↦ List.mem_finRange a,
      fun _ ↦ List.mem_map.mpr ⟨σ.symm a, List.mem_finRange _, by simp⟩⟩

/-- Counting over `finRange` is invariant under precomposing the predicate with a
permutation. -/
lemma length_filter_finRange_comp (σ : Equiv.Perm (Fin n)) (p : Fin n → Bool) :
    ((List.finRange n).filter fun j ↦ p (σ j)).length = ((List.finRange n).filter p).length := by
  have h := ((map_finRange_perm σ).filter p).length_eq
  rwa [List.filter_map, List.length_map] at h

/-- A vector is `relabelVec σ v` iff it has `v[i]` at position `σ i` for every `i`. -/
lemma eq_relabelVec_of_apply {α : Type*} (σ : Equiv.Perm (Fin n)) {v' v : Vector α n}
    (h : ∀ i, v'[σ i] = v[i]) : v' = relabelVec σ v := by
  ext j hj
  have := h (σ.symm ⟨j, hj⟩)
  simpa using this

/-- A vector's list is its entries in index order. -/
lemma toList_eq_map_finRange {α : Type*} (v : Vector α n) :
    v.toList = (List.finRange n).map fun i ↦ v[i] := by
  conv_lhs => rw [← Vector.ofFn_getElem (xs := v)]
  rw [Vector.toList_ofFn, List.ofFn_eq_map]
  simp only [Fin.getElem_fin]

/-- Relabeling permutes the entries. -/
lemma toList_relabelVec_perm {α : Type*} (σ : Equiv.Perm (Fin n)) (v : Vector α n) :
    (relabelVec σ v).toList.Perm v.toList := by
  rw [toList_eq_map_finRange, toList_eq_map_finRange]
  have := (map_finRange_perm σ.symm).map fun i ↦ v[i]
  rw [List.map_map] at this
  refine (List.Perm.of_eq ?_).trans this
  apply List.map_congr_left
  intro i _
  simp

/-- Counting over `finRange` as a `Finset` cardinality. -/
lemma length_filter_finRange_eq_card (p : Fin n → Bool) :
    ((List.finRange n).filter p).length = (Finset.univ.filter fun i ↦ p i = true).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter p)]
  congr 1
  ext i
  simp

/-! ### The minimum of a list depends only on its members -/

/-- Lists with the same members have the same minimum. -/
lemma _root_.List.min?_eq_of_mem_iff {α : Type*} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] {l₁ l₂ : List α} (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.min? = l₂.min? := by
  rcases h₁ : l₁.min? with _ | a
  · rw [List.min?_eq_none_iff] at h₁
    have h₂ : l₂ = [] := by
      rcases l₂ with _ | ⟨b, l₂⟩
      · rfl
      · exact absurd ((h b).mpr (List.mem_cons_self)) (by simp [h₁])
    exact (List.min?_eq_none_iff.mpr h₂).symm
  · rw [List.min?_eq_some_iff] at h₁
    exact (List.min?_eq_some_iff.mpr
      ⟨(h a).mp h₁.1, fun b hb ↦ h₁.2 b ((h b).mpr hb)⟩).symm

/-- The minimum of a list is invariant under permutation. -/
lemma _root_.List.Perm.min?_eq {α : Type*} [Min α] [LE α] [Std.IsLinearOrder α]
    [Std.LawfulOrderMin α] {l₁ l₂ : List α} (h : l₁.Perm l₂) : l₁.min? = l₂.min? :=
  List.min?_eq_of_mem_iff fun _ ↦ h.mem_iff

/-! ### Sorting is determined by the multiset -/

lemma pairLE_total (p q : ℤ × ℤ) : (pairLE p q || pairLE q p) = true := by
  simp only [pairLE, Bool.or_eq_true, decide_eq_true_eq]
  omega

lemma pairLE_trans (p q s : ℤ × ℤ) : pairLE p q = true → pairLE q s = true → pairLE p s = true := by
  simp only [pairLE, decide_eq_true_eq]
  omega

lemma pairLE_antisymm {p q : ℤ × ℤ} (h₁ : pairLE p q = true) (h₂ : pairLE q p = true) : p = q := by
  simp only [pairLE, decide_eq_true_eq] at h₁ h₂
  exact Prod.ext (by omega) (by omega)

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
    ranksOf (relabelVec σ inv) = relabelVec σ (ranksOf inv) := by
  apply eq_relabelVec_of_apply
  intro i
  simp only [ranksOf]
  simpa using length_filter_finRange_comp σ.symm fun j ↦ lexLt inv[j] inv[i]

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
    individualize (relabelVec σ r) (σ a) = relabelVec σ (individualize r a) := by
  apply eq_relabelVec_of_apply
  intro i
  simp [individualize, Vector.getElem_ofFn, σ.injective.eq_iff]

/-- The lowest tied rank does not depend on labels. -/
lemma firstTie_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    firstTie (relabelVec σ r) = firstTie r := by
  unfold firstTie
  apply List.Perm.min?_eq
  have hc : ∀ x, (relabelVec σ r).toList.count x = r.toList.count x :=
    fun x ↦ (toList_relabelVec_perm σ r).count_eq x
  have h := ((map_finRange_perm σ.symm).filter fun a ↦ decide (2 ≤ r.toList.count r[a])).map
    fun a ↦ r[a]
  rw [List.filter_map, List.map_map] at h
  refine (List.Perm.of_eq ?_).trans h
  simp only [Function.comp_def, hc, Fin.getElem_fin, getElem_relabelVec, Fin.eta]

/-- The atoms of a rank after relabeling are the relabeled atoms of that rank, up to order. -/
lemma tiedAtoms_relabel_perm (σ : Equiv.Perm (Fin n)) (r : Ranks n) (c : ℕ) :
    (tiedAtoms (relabelVec σ r) c).Perm ((tiedAtoms r c).map σ) := by
  unfold tiedAtoms
  have h := (map_finRange_perm σ).filter fun a ↦ (relabelVec σ r)[a] == c
  rw [List.filter_map] at h
  refine h.symm.trans (List.Perm.of_eq ?_)
  congr 1
  simp [Function.comp_def]

/-! ### Classes and ties -/

/-- There are at most `n` classes. -/
lemma numClasses_le (r : Ranks n) : numClasses r ≤ n := by
  unfold numClasses
  calc r.toList.dedup.length ≤ r.toList.length := (List.dedup_sublist _).length_le
    _ = n := by simp

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
  have := (List.mem_filter.mp ha).2
  rw [length_tiedAtoms]
  simpa using this

/-- A tied rank has an atom. -/
lemma exists_mem_tiedAtoms {r : Ranks n} {c : ℕ} (h : firstTie r = some c) :
    ∃ a, a ∈ tiedAtoms r c := by
  have h2 := two_le_length_tiedAtoms h
  cases hl : tiedAtoms r c with
  | nil => simp [hl] at h2
  | cons x _ => exact ⟨x, List.mem_cons_self⟩

/-- A tied rank has an atom other than any given one. -/
lemma exists_ne_of_firstTie {r : Ranks n} {c : ℕ} (h : firstTie r = some c) (a : Fin n) :
    ∃ b, b ≠ a ∧ r[b] = c := by
  have h2 := two_le_length_tiedAtoms h
  obtain ⟨x, y, rest, hxy⟩ : ∃ x y rest, tiedAtoms r c = x :: y :: rest := by
    match hl : tiedAtoms r c with
    | [] => simp [hl] at h2
    | [_] => simp [hl] at h2
    | x :: y :: rest => exact ⟨x, y, rest, rfl⟩
  have hnd := nodup_tiedAtoms r c
  rw [hxy, List.nodup_cons] at hnd
  have hxney : x ≠ y := fun e ↦ hnd.1 (e ▸ List.mem_cons_self ..)
  have hx : r[x] = c := mem_tiedAtoms.mp (hxy ▸ List.mem_cons_self ..)
  have hy : r[y] = c := mem_tiedAtoms.mp (hxy ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
  by_cases hxa : x = a
  · exact ⟨y, fun e ↦ hxney (hxa.trans e.symm), hy⟩
  · exact ⟨x, hxa, hx⟩

/-- No tie means every atom has its own rank. -/
lemma isDiscrete_of_firstTie_eq_none {r : Ranks n} (h : firstTie r = none) :
    isDiscrete r = true := by
  rw [isDiscrete_iff]
  unfold firstTie at h
  rw [List.min?_eq_none_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have hnd : r.toList.Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro x
    by_cases hx : x ∈ r.toList
    · rw [toList_eq_map_finRange, List.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      have := h a (List.mem_finRange a)
      simp only [decide_eq_true_eq, not_le] at this
      exact Nat.lt_succ_iff.mp this
    · rw [List.count_eq_zero_of_not_mem hx]
      exact Nat.zero_le _
  unfold numClasses
  rw [hnd.dedup]
  simp

/-- The number of classes is the number of distinct ranks. -/
lemma numClasses_eq_card_image (r : Ranks n) :
    numClasses r = (Finset.univ.image fun i : Fin n ↦ r[i]).card := by
  rw [numClasses, ← List.card_toFinset]
  congr 1
  ext x
  simp [toList_eq_map_finRange]

/-- Individualizing an atom of a tied class splits that class. -/
lemma numClasses_lt_numClasses_individualize {r : Ranks n} {c : ℕ} (hc : firstTie r = some c)
    {a : Fin n} (ha : r[a] = c) : numClasses r < numClasses (individualize r a) := by
  obtain ⟨b, hba, hb⟩ := exists_ne_of_firstTie hc a
  simp only [Fin.getElem_fin] at ha hb
  rw [numClasses_eq_card_image, numClasses_eq_card_image]
  have himg : (Finset.univ.image fun i : Fin n ↦ (individualize r a)[i])
      = insert (2 * c) ((Finset.univ.image fun i : Fin n ↦ r[i]).image fun v ↦ 2 * v + 1) := by
    ext x
    simp only [individualize, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨i, rfl⟩
      split_ifs with hia
      · left
        rw [hia, ha]
      · right
        exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro (rfl | ⟨v, ⟨i, rfl⟩, rfl⟩)
      · exact ⟨a, by simp [ha]⟩
      · by_cases hia : i = a
        · subst hia
          exact ⟨b, by simp [hba, hb, ha]⟩
        · exact ⟨i, by simp [hia]⟩
  have hinj : Function.Injective fun v : ℕ ↦ 2 * v + 1 :=
    fun x y (h : 2 * x + 1 = 2 * y + 1) ↦ by omega
  rw [himg, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ hinj]
  · exact Nat.lt_succ_self _
  · simp only [Finset.mem_image, not_exists, not_and]
    intro v _ h
    omega

/-! ### Discrete ranks are permutations -/

/-- Position in rank order respects rank. -/
lemma rankPos_lt_rankPos {r : Ranks n} {i j : Fin n} (h : r[i] < r[j]) :
    rankPos r i < rankPos r j := by
  rw [Fin.lt_def]
  simp only [rankPos]
  rw [length_filter_finRange_eq_card, length_filter_finRange_eq_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨i, by simpa using h, by simp⟩
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hk ⊢
    omega

/-- A discrete ranking gives distinct atoms distinct ranks. -/
lemma injective_getElem_of_isDiscrete {r : Ranks n} (h : isDiscrete r = true) :
    Function.Injective fun i : Fin n ↦ r[i] := by
  rw [isDiscrete_iff, numClasses] at h
  have hnd : r.toList.Nodup := by
    have hsub := List.dedup_sublist r.toList
    have hlen : r.toList.dedup.length = r.toList.length := by
      rw [h]
      simp
    rw [← hsub.eq_of_length hlen]
    exact List.nodup_dedup _
  rw [toList_eq_map_finRange] at hnd
  intro i j hij
  exact List.inj_on_of_nodup_map hnd (List.mem_finRange i) (List.mem_finRange j) hij

/-- A discrete ranking's positions form a permutation. -/
lemma bijective_rankPos_of_isDiscrete {r : Ranks n} (h : isDiscrete r = true) :
    Function.Bijective (rankPos r) := by
  rw [← Finite.injective_iff_bijective]
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne fun e ↦ hne (injective_getElem_of_isDiscrete h e) with hlt | hlt
  · exact absurd hij (rankPos_lt_rankPos hlt).ne
  · exact absurd hij (rankPos_lt_rankPos hlt).ne'

/-- Position in rank order does not depend on labels. -/
lemma rankPos_relabel_apply (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    rankPos (relabelVec σ r) (σ i) = rankPos r i := by
  apply Fin.ext
  simp only [rankPos]
  simpa using length_filter_finRange_comp σ.symm fun j ↦ decide (r[j] < r[i])

/-- Positions after relabeling are positions before, read through the relabeling. -/
lemma rankPos_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    rankPos (relabelVec σ r) = rankPos r ∘ σ.symm := by
  funext j
  have := rankPos_relabel_apply σ r (σ.symm j)
  simpa using this

/-- The position table is a permutation table exactly when `rankPos` is a bijection. -/
lemma isPermTable_ofFn_rankPos_iff (r : Ranks n) :
    isPermTable (Vector.ofFn (rankPos r)) = true ↔ Function.Bijective (rankPos r) := by
  constructor
  · intro h
    have hs := surjective_of_isPermTable h
    simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at hs
    exact Finite.surjective_iff_bijective.mp hs
  · intro h
    simp only [isPermTable, List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and,
      true_implies, beq_iff_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
    exact h.2

/-- On a discrete ranking, `permOfRanks` is `rankPos`. -/
lemma permOfRanks_apply {r : Ranks n} (h : Function.Bijective (rankPos r)) (i : Fin n) :
    permOfRanks r i = rankPos r i := by
  simp only [permOfRanks, dif_pos ((isPermTable_ofFn_rankPos_iff r).mpr h), Equiv.coe_fn_mk,
    Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]

/-- Relabeling by `σ` and then into rank order is going into rank order directly. -/
lemma permOfRanks_relabel (σ : Equiv.Perm (Fin n)) {r : Ranks n}
    (h : Function.Bijective (rankPos r)) :
    σ.trans (permOfRanks (relabelVec σ r)) = permOfRanks r := by
  have h' : Function.Bijective (rankPos (relabelVec σ r)) := by
    rw [rankPos_relabel]
    exact h.comp σ.symm.bijective
  refine Equiv.ext fun i ↦ ?_
  rw [Equiv.trans_apply, permOfRanks_apply h', permOfRanks_apply h, rankPos_relabel_apply]

namespace MolData

variable (d : MolData n)

/-! ### The search commutes with relabeling -/

/-- Degree does not depend on labels. -/
lemma degree_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).degree (σ i) = d.degree i := by
  simp only [degree, bonds_relabel, BondMatrix.relabel_apply, Equiv.symm_apply_apply]
  exact length_filter_finRange_comp σ.symm fun j ↦ d.bonds i j != 0

/-- An atom's invariant does not depend on its label. -/
lemma atomInvariant_relabel (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (d.relabel σ).atomInvariant (σ i) = d.atomInvariant i := by
  simp [atomInvariant, degree_relabel]

/-- The invariant vector of the relabeled data is the relabeled invariant vector. -/
lemma ofFn_atomInvariant_relabel (σ : Equiv.Perm (Fin n)) :
    Vector.ofFn (d.relabel σ).atomInvariant = relabelVec σ (Vector.ofFn d.atomInvariant) := by
  apply eq_relabelVec_of_apply
  intro i
  simp [atomInvariant_relabel]

/-- An atom's sorted neighbor pairs do not depend on labels. -/
lemma neighborInvariant_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) (i : Fin n) :
    (d.relabel σ).neighborInvariant (relabelVec σ r) (σ i) = d.neighborInvariant r i := by
  unfold neighborInvariant
  apply mergeSort_pairLE_eq_of_perm
  have h := (map_finRange_perm σ.symm).filterMap fun j ↦
    (d.bonds.kindAt i j).map fun k ↦ (((r[j] : ℕ) : ℤ), kindIdx k)
  rw [List.filterMap_map] at h
  refine (List.Perm.of_eq ?_).trans h
  congr 1
  funext j
  simp [bonds_relabel, BondMatrix.kindAt]

/-- One refinement step's invariants commute with relabeling. -/
lemma refineInvariant_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    (d.relabel σ).refineInvariant (relabelVec σ r) = relabelVec σ (d.refineInvariant r) := by
  apply eq_relabelVec_of_apply
  intro i
  simp [refineInvariant, neighborInvariant_relabel]

/-- One refinement step commutes with relabeling. -/
lemma refineOnce_relabel (σ : Equiv.Perm (Fin n)) (r : Ranks n) :
    (d.relabel σ).refineOnce (relabelVec σ r) = relabelVec σ (d.refineOnce r) := by
  unfold refineOnce
  rw [refineInvariant_relabel, ranksOf_relabel]

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
  unfold initialRanks
  rw [ofFn_atomInvariant_relabel, ranksOf_relabel, refine_relabel]

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
        apply List.Perm.flatMap_left
        intro a _
        rw [individualize_relabel, refine_relabel]
        exact ih _

/-- Each level of tie-breaking adds a class, so with `n` levels every leaf is discrete. -/
theorem isDiscrete_of_mem_leavesAll : ∀ (fuel : ℕ) (r : Ranks n),
    n ≤ numClasses r + fuel → ∀ l ∈ d.leavesAll fuel r, isDiscrete l = true
  | 0, r, h, l, hl => by
    simp only [leavesAll, List.mem_singleton] at hl
    subst hl
    rw [isDiscrete_iff]
    exact le_antisymm (numClasses_le l) (by simpa using h)
  | fuel + 1, r, h, l, hl => by
    simp only [leavesAll] at hl
    split_ifs at hl with hd
    · rw [List.mem_singleton] at hl
      subst hl
      exact hd
    · rcases hc : firstTie r with _ | c
      · simp only [hc, List.mem_singleton] at hl
        subst hl
        exact isDiscrete_of_firstTie_eq_none hc
      · simp only [hc, List.mem_flatMap] at hl
        obtain ⟨a, ha, hl⟩ := hl
        refine isDiscrete_of_mem_leavesAll fuel _ ?_ l hl
        have h1 := numClasses_lt_numClasses_individualize hc (mem_tiedAtoms.mp ha)
        have h2 := d.numClasses_le_numClasses_refine n (individualize r a)
        omega

/-- The search always finds a leaf. -/
theorem leavesAll_ne_nil : ∀ (fuel : ℕ) (r : Ranks n), d.leavesAll fuel r ≠ []
  | 0, r => by simp [leavesAll]
  | fuel + 1, r => by
    simp only [leavesAll]
    split_ifs
    · simp
    · rcases hc : firstTie r with _ | c
      · simp
      · rw [Ne, List.flatMap_eq_nil_iff, not_forall]
        obtain ⟨x, hx⟩ := exists_mem_tiedAtoms hc
        exact ⟨x, fun hf ↦ leavesAll_ne_nil fuel _ (hf hx)⟩

/-- The string a discrete ranking writes does not depend on labels. -/
lemma writeRanked_relabel (σ : Equiv.Perm (Fin n)) {r : Ranks n}
    (h : Function.Bijective (rankPos r)) :
    (d.relabel σ).writeRanked (relabelVec σ r) = d.writeRanked r := by
  unfold writeRanked
  rw [relabel_relabel, permOfRanks_relabel σ h]

/-! ### Pruning is sound -/

/-- What `isAutomorphism` certifies. -/
lemma relabel_eq_self_of_isAutomorphism {γ : Equiv.Perm (Fin n)}
    (h : d.isAutomorphism γ = true) : d.relabel γ = d := by
  simp only [isAutomorphism, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    beq_iff_eq, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at h
  refine ext ?_ ?_
  · ext j hj
    have := (h (γ.symm ⟨j, hj⟩)).1
    simpa using this.symm
  · ext i hi j hj
    have := (h (γ.symm ⟨i, hi⟩)).2 (γ.symm ⟨j, hj⟩)
    simp only [bonds_apply] at this
    simpa [relabel, Vector.getElem_ofFn] using this.symm

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
  have hind : individualize r a = relabelVec γ (individualize r e) := by
    rw [← hea, ← individualize_relabel, hr]
  have href : d.refine n (relabelVec γ (individualize r e))
      = relabelVec γ (d.refine n (individualize r e)) := by
    have := d.refine_relabel γ n (individualize r e)
    rwa [hd] at this
  have hleaves := d.leavesAll_relabel_perm γ fuel (d.refine n (individualize r e))
  rw [hd] at hleaves
  intro l hl
  rw [hind, href] at hl
  obtain ⟨l', hl', rfl⟩ := List.mem_map.mp (hleaves.mem_iff.mp hl)
  refine ⟨l', hl', ?_⟩
  have hdisc : isDiscrete l' = true := by
    refine d.isDiscrete_of_mem_leavesAll fuel _ ?_ l' hl'
    have h1 := numClasses_lt_numClasses_individualize hc (mem_tiedAtoms.mp he)
    have h2 := d.numClasses_le_numClasses_refine n (individualize r e)
    omega
  have := d.writeRanked_relabel γ (bijective_rankPos_of_isDiscrete hdisc)
  rw [hd] at this
  exact this.symm

/-- Everything `exploreChildren` returns is a leaf of the full search. -/
theorem exploreChildren_subset (r : Ranks n) (sub : Ranks n → List (Ranks n))
    (first : Ranks n → Ranks n) (L : List (Ranks n)) (T : List (Fin n))
    (hsub : ∀ a ∈ T, ∀ l ∈ sub (d.refine n (individualize r a)), l ∈ L) :
    ∀ (pending : List (Fin n)) (reps : List (Fin n × Equiv.Perm (Fin n))) (acc : List (Ranks n)),
      (∀ a ∈ pending, a ∈ T) → (∀ l ∈ acc, l ∈ L) →
      ∀ l ∈ d.exploreChildren r sub first pending reps acc, l ∈ L
  | [], _, acc, _, hacc, l, hl => hacc l hl
  | a :: pending, reps, acc, hp, hacc, l, hl => by
    simp only [exploreChildren] at hl
    split_ifs at hl
    · exact exploreChildren_subset r sub first L T hsub pending reps acc
        (fun b hb ↦ hp b (List.mem_cons_of_mem _ hb)) hacc l hl
    · refine exploreChildren_subset r sub first L T hsub pending _ _
        (fun b hb ↦ hp b (List.mem_cons_of_mem _ hb)) ?_ l hl
      intro l' hl'
      rcases List.mem_append.mp hl' with h | h
      · exact hacc l' h
      · exact hsub a (hp a List.mem_cons_self) l' h

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
  | [], _, acc, _, _ => ⟨fun l hl ↦ hl, fun a ha ↦ absurd ha (List.not_mem_nil)⟩
  | a :: pending, reps, acc, hp, hreps => by
    simp only [exploreChildren]
    split_ifs with hany
    · -- skipped: the subtree under `a` is the image of a representative's
      obtain ⟨p, hpmem, hsym⟩ := List.any_eq_true.mp hany
      obtain ⟨ih₁, ih₂⟩ := exploreChildren_cover hc fuel hf sub first hsub pending reps acc
        (fun b hb ↦ hp b (List.mem_cons_of_mem _ hb)) hreps
      refine ⟨ih₁, fun b hb l hl ↦ ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨l'', hl'', hw⟩ := d.leavesAll_symmetry hc (hreps p hpmem).1 hsym fuel hf l hl
        obtain ⟨l', hl', hw'⟩ := (hreps p hpmem).2 l'' hl''
        exact ⟨l', ih₁ l' hl', hw'.trans hw⟩
      · exact ih₂ b hb l hl
    · -- explored: `a` becomes a representative, covered by the new `acc`
      have ha : a ∈ tiedAtoms r c := hp a List.mem_cons_self
      obtain ⟨ih₁, ih₂⟩ := exploreChildren_cover hc fuel hf sub first hsub pending
        ((a, permOfRanks (first (d.refine n (individualize r a)))) :: reps)
        (acc ++ sub (d.refine n (individualize r a)))
        (fun b hb ↦ hp b (List.mem_cons_of_mem _ hb)) (by
          intro p hpmem
          rcases List.mem_cons.mp hpmem with rfl | hpmem
          · refine ⟨ha, fun l hl ↦ ?_⟩
            obtain ⟨l', hl', hw⟩ := hsub a ha l hl
            exact ⟨l', List.mem_append_right _ hl', hw⟩
          · refine ⟨(hreps p hpmem).1, fun l hl ↦ ?_⟩
            obtain ⟨l', hl', hw⟩ := (hreps p hpmem).2 l hl
            exact ⟨l', List.mem_append_left _ hl', hw⟩)
      refine ⟨fun l hl ↦ ih₁ l (List.mem_append_left _ hl), fun b hb l hl ↦ ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · obtain ⟨l', hl', hw⟩ := hsub b ha l hl
        exact ⟨l', ih₁ l' (List.mem_append_right _ hl'), hw⟩
      · exact ih₂ b hb l hl

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
        refine d.exploreChildren_subset r (d.search fuel) (d.firstLeaf fuel)
          ((tiedAtoms r c).flatMap fun a ↦ d.leavesAll fuel (d.refine n (individualize r a)))
          (tiedAtoms r c) ?_ (tiedAtoms r c) [] [] (fun _ h ↦ h)
          (fun _ h ↦ absurd h List.not_mem_nil) l hl
        intro a ha l' hl'
        exact List.mem_flatMap.mpr ⟨a, ha, search_subset_leavesAll fuel _ l' hl'⟩

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
        have hsub : ∀ a ∈ tiedAtoms r c, ∀ l ∈ d.leavesAll fuel (d.refine n (individualize r a)),
            ∃ l' ∈ d.search fuel (d.refine n (individualize r a)),
              d.writeRanked l' = d.writeRanked l := by
          intro a ha l hl
          refine exists_mem_search fuel _ ?_ l hl
          have h1 := numClasses_lt_numClasses_individualize hc (mem_tiedAtoms.mp ha)
          have h2 := d.numClasses_le_numClasses_refine n (individualize r a)
          omega
        exact (d.exploreChildren_cover hc fuel hf (d.search fuel) (d.firstLeaf fuel) hsub
          (tiedAtoms r c) [] [] (fun _ h ↦ h) (fun _ h ↦ absurd h List.not_mem_nil)).2 a ha l hl

/-- The pruned search finds a leaf. -/
lemma search_ne_nil (r : Ranks n) : d.search n r ≠ [] := by
  intro h
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (d.leavesAll_ne_nil n r)
  obtain ⟨l', hl', -⟩ := d.exists_mem_search n r (Nat.le_add_left n _) l hl
  rw [h] at hl'
  exact List.not_mem_nil hl'

/-- Pruning keeps the minimum. -/
theorem min?_search_eq (r : Ranks n) :
    ((d.search n r).map d.writeRanked).min? = ((d.leavesAll n r).map d.writeRanked).min? := by
  apply List.min?_eq_of_mem_iff
  intro s
  simp only [List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, d.search_subset_leavesAll n r l hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨l', hl', hw⟩ := d.exists_mem_search n r (Nat.le_add_left n _) l hl
    exact ⟨l', hl', hw⟩

/-! ### The theorem -/

/-- The canonical string of the relabeled data is the canonical string of the data. -/
theorem canonical_relabel (σ : Equiv.Perm (Fin n)) : (d.relabel σ).canonical.2 = d.canonical.2 := by
  have hmin : (((d.relabel σ).search n (d.relabel σ).initialRanks).map
      (d.relabel σ).writeRanked).min? = ((d.search n d.initialRanks).map d.writeRanked).min? := by
    rw [min?_search_eq, min?_search_eq, initialRanks_relabel]
    refine List.Perm.min?_eq (((d.leavesAll_relabel_perm σ n _).map _).trans (List.Perm.of_eq ?_))
    rw [List.map_map]
    apply List.map_congr_left
    intro l hl
    exact d.writeRanked_relabel σ (bijective_rankPos_of_isDiscrete
      (d.isDiscrete_of_mem_leavesAll n _ (Nat.le_add_left n _) l hl))
  simp only [canonical, hmin]
  rcases hm : ((d.search n d.initialRanks).map d.writeRanked).min? with _ | s
  · rw [List.min?_eq_none_iff, List.map_eq_nil_iff] at hm
    exact absurd hm (d.search_ne_nil _)
  · rfl

end MolData

/-- The canonical SMILES does not depend on how the atoms are numbered: every
relabeling of the molecule writes the same string. -/
theorem Molecule.canonicalSmiles_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).canonicalSmiles = m.canonicalSmiles := by
  unfold canonicalSmiles
  rw [toMolData_relabel]
  exact m.toMolData.canonical_relabel σ

/-- The canonical SMILES of a bundled molecule does not depend on its atom order. -/
theorem Mol.canonicalSmiles_relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) :
    (M.relabel σ).canonicalSmiles = M.canonicalSmiles :=
  M.mol.canonicalSmiles_relabel σ

end LeanSMILES
