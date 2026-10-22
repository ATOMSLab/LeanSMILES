/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Fingerprint.Morgan
public import LeanSMILES.SMILES.Canonicity

/-!
# LeanSMILES.Fingerprint.MorganInvariance

The Morgan fingerprint does not depend on the order of the atoms, up to radius 2
(`Molecule.morganBits_relabel`): relabeling the atoms of a molecule leaves the
folded bits, and the unfolded identifiers with their counts, unchanged.

The proof follows the algorithm, as `LeanSMILES.SMILES.Canonicity` does.  A
relabeling `σ` keeps the bond list in order and moves every atom, so every
per-atom quantity moves with its atom: the adjacency lists
(`adjacency_relabel`), ring membership (`reachableWithout_relabel`,
`inRingVector_relabel`), the radius-0 invariants
(`morganAtomInvariants_relabel`), and one step of growth of an environment and
its identifier (`growEnv_relabel`, `growId_relabel`).  So the live atoms of a
round, as (identifier, atom, bond set) triples, are the relabeled triples of the
original (`roundTriples_relabel`).

Duplicate removal emits, for every bond set not seen before, the identifier of
its first triple (`emitted_ids`).  The triples are sorted by identifier, so that
identifier is the smallest one with that bond set (`firstId_eq_of_mem_iff`) and
does not depend on how atoms with equal identifiers are ordered.

What can depend on the order is which atom of a tied pair *dies*: two atoms
whose environments cover the same bonds with the same identifier are broken by
atom index, and the loser stops growing.  At radius 1 such a pair covers a
single bond, so it is a two-atom fragment (`eq_of_env1_eq`), and at radius 2
its environment is that same bond again, already seen; it emits nothing
whichever atom died (`grown_mem_seen_of_killed`).  That is why the theorem
stops at radius 2.  At radius 3 it is false, for RDKit as well:
`C1=C(CO)C=C1CC` and `C1(CC)=CC(CO)=C1` are one molecule with different
radius-3 fingerprints (README, "Findings about external tools").
-/

@[expose] public section

namespace LeanSMILES.Molecule

variable {n : ℕ} (m : Molecule n) (σ : Equiv.Perm (Fin n))

/-! ### Folds and vectors under relabeling -/

/-- A fold commutes with a map of its state that commutes with each step. -/
lemma foldl_map_hom {α γ β β' : Type*} (g : α → γ) (h : β → β') (f : α → β → α)
    (f' : γ → β' → γ) (hstep : ∀ a b, f' (g a) (h b) = g (f a b)) (l : List β) (init : α) :
    (l.map h).foldl f' (g init) = g (l.foldl f init) := by
  induction l generalizing init with
  | nil => rfl
  | cons b bs ih => simp only [List.map_cons, List.foldl_cons, hstep, ih]

lemma relabelVec_set {α : Type*} (v : Vector α n) (x : Fin n) (a : α) :
    (relabelVec σ v).set (σ x).val a (σ x).isLt = relabelVec σ (v.set x.val a x.isLt) := by
  ext j hj
  simp only [Vector.getElem_set, getElem_relabelVec, Fin.getElem_fin]
  have key : ((σ x : ℕ) = j) ↔ ((x : ℕ) = (σ.symm ⟨j, hj⟩ : ℕ)) := by
    constructor
    · intro e
      have : σ x = ⟨j, hj⟩ := Fin.ext e
      simp [← this]
    · intro e
      have : x = σ.symm ⟨j, hj⟩ := Fin.ext e
      simp [this]
  by_cases h : (σ x : ℕ) = j
  · rw [if_pos h, if_pos (key.mp h)]
  · rw [if_neg h, if_neg (fun e ↦ h (key.mpr e))]

lemma relabelVec_replicate {α : Type*} (a : α) :
    relabelVec σ (Vector.replicate n a) = Vector.replicate n a := by
  ext j hj; simp

/-! ### Ring membership under relabeling -/

lemma reachStep_relabel (skip : Sym2 (Fin n)) (seen : Vector Bool n) :
    (m.relabel σ).reachStep (Sym2.map σ skip) (relabelVec σ seen)
      = relabelVec σ (m.reachStep skip seen) := by
  unfold reachStep
  rw [bonds_relabel]
  refine foldl_map_hom _ _ _ _ (fun v b ↦ ?_) _ _
  have hskip : (Sym2.map σ b.edge != Sym2.map σ skip) = (b.edge != skip) := by
    rcases eq_or_ne b.edge skip with h | h
    · rw [h]; simp
    · have h' : Sym2.map σ b.edge ≠ Sym2.map σ skip := (Sym2.map.injective σ.injective).ne h
      rw [bne_iff_ne.mpr h', bne_iff_ne.mpr h]
  simp only [Bond.edge_map, hskip]
  simp only [Bond.map, Fin.getElem_fin, getElem_relabelVec, Fin.eta, Equiv.symm_apply_apply]
  split_ifs <;> first | rfl | simp [relabelVec_set]

lemma iterate_reachStep_relabel (skip : Sym2 (Fin n)) (k : ℕ) (v : Vector Bool n) :
    ((m.relabel σ).reachStep (Sym2.map σ skip))^[k] (relabelVec σ v)
      = relabelVec σ ((m.reachStep skip)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      reachStep_relabel]

lemma reachableWithout_relabel (skip : Sym2 (Fin n)) (start : Fin n) :
    (m.relabel σ).reachableWithout (Sym2.map σ skip) (σ start)
      = relabelVec σ (m.reachableWithout skip start) := by
  unfold reachableWithout
  conv_lhs => rw [← relabelVec_replicate σ false, relabelVec_set, iterate_reachStep_relabel]

lemma bondInRing_relabel (b : Bond n) :
    (m.relabel σ).bondInRing (b.map σ σ.injective) = m.bondInRing b := by
  unfold bondInRing
  rw [Bond.edge_map, show (b.map σ σ.injective).src = σ b.src from rfl, reachableWithout_relabel]
  exact relabelVec_apply σ _ b.dst

lemma ringEdges_relabel : (m.relabel σ).ringEdges = m.ringEdges.map (Sym2.map σ) := by
  unfold ringEdges
  rw [bonds_relabel, List.filter_map]
  simp only [Function.comp_def, bondInRing_relabel, List.map_map, Bond.edge_map]

lemma inRingVector_relabel (i : Fin n) :
    (m.relabel σ).inRingVector[σ i] = m.inRingVector[i] := by
  unfold inRingVector
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, bondsAt_relabel, List.any_map,
    Function.comp_def, ringEdges_relabel, Bond.edge_map]
  congr 1
  funext b
  rw [Bool.eq_iff_iff]
  simp [(Sym2.map.injective σ.injective).eq_iff]

/-! ### Neighbors, adjacency and bond types under relabeling -/

lemma neighbors_relabel (i : Fin n) :
    (m.relabel σ).neighbors (σ i) = (m.neighbors i).map σ := by
  unfold neighbors
  rw [bondsAt_relabel, List.map_map, List.map_map]
  congr 1
  funext b
  simp only [Function.comp_apply, Bond.other, Bond.map, σ.injective.eq_iff]
  split_ifs <;> rfl

lemma adjacency_relabel (i : Fin n) :
    (m.relabel σ).adjacency[σ i] = m.adjacency[i].map fun p ↦ (p.1, σ p.2) := by
  unfold adjacency
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, bonds_relabel, List.zipIdx_map,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, Bond.map,
    σ.injective.eq_iff]
  split_ifs <;> rfl

lemma bondKinds_relabel : (m.relabel σ).bondKinds = m.bondKinds := by
  simp [bondKinds, bonds_relabel, Bond.map, Function.comp_def]

lemma morganAtomInvariants_relabel (i : Fin n) :
    (m.relabel σ).morganAtomInvariants[σ i] = m.morganAtomInvariants[i] := by
  unfold morganAtomInvariants
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, atom_relabel, degree_relabel,
    neighbors_relabel, List.filter_map, Function.comp_def, List.length_map]
  rw [← Fin.getElem_fin, ← Fin.getElem_fin, inRingVector_relabel]

/-! ### One step of growth under relabeling -/

/-- An atom's adjacency list is empty exactly when it is after relabeling. -/
lemma isEmpty_adjacency_relabel (a : Fin n) :
    (m.relabel σ).adjacency[σ a].isEmpty = m.adjacency[a].isEmpty := by
  rw [adjacency_relabel, List.isEmpty_map]

lemma growEnv_relabel (pe : Vector ℕ n) (a : Fin n) :
    growEnv (m.relabel σ).adjacency (relabelVec σ pe) (σ a) = growEnv m.adjacency pe a := by
  unfold growEnv
  rw [adjacency_relabel, List.foldl_map, relabelVec_apply]
  simp only [relabelVec_apply]

lemma growId_relabel (cur : Vector UInt32 n) (layer : ℕ) (a : Fin n) :
    growId (m.relabel σ).adjacency (m.relabel σ).bondKinds (relabelVec σ cur) layer (σ a)
      = growId m.adjacency m.bondKinds cur layer a := by
  unfold growId
  rw [adjacency_relabel, bondKinds_relabel, List.map_map, relabelVec_apply]
  simp only [Function.comp_def, relabelVec_apply]

/-! ### Duplicate removal

`emitted layer l seen` is what the duplicate-removal fold over `l` appends to
the result: the first triple of every bond set not in `seen`. -/

/-- The environments the fold emits. -/
def emitted (layer : ℕ) : List (UInt32 × Fin n × ℕ) → List ℕ → List (UInt32 × Fin n × ℕ)
  | [], _ => []
  | t :: l, seen =>
    if seen.contains t.2.2 then emitted layer l seen
    else (t.1, t.2.1, layer + 1) :: emitted layer l (t.2.2 :: seen)

lemma foldl_dedupStep_result (layer : ℕ) (l : List (UInt32 × Fin n × ℕ)) (d : Vector Bool n)
    (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) :
    (l.foldl (dedupStep layer) (d, r, seen)).2.1 = r ++ emitted layer l seen := by
  induction l generalizing d r seen with
  | nil => simp [emitted]
  | cons t l ih =>
    rw [List.foldl_cons, emitted]
    by_cases h : seen.contains t.2.2 = true
    · simp only [dedupStep, h, if_true]; rw [ih]
    · simp only [dedupStep, h, if_false, Bool.false_eq_true]; rw [ih]; simp

lemma mem_foldl_dedupStep_seen (layer : ℕ) (l : List (UInt32 × Fin n × ℕ)) (d : Vector Bool n)
    (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) (e : ℕ) :
    e ∈ (l.foldl (dedupStep layer) (d, r, seen)).2.2 ↔ e ∈ seen ∨ ∃ t ∈ l, t.2.2 = e := by
  induction l generalizing d r seen with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons]
    have hex : (∃ u ∈ t :: l, u.2.2 = e) ↔ t.2.2 = e ∨ ∃ u ∈ l, u.2.2 = e := by
      simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    rw [hex]
    by_cases h : seen.contains t.2.2 = true
    · simp only [dedupStep, h, if_true]
      rw [ih]
      have : t.2.2 ∈ seen := by simpa using h
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inl (h1 ▸ this)
        · exact Or.inr h1
    · simp only [dedupStep, h, if_false, Bool.false_eq_true]
      rw [ih, List.mem_cons]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inr (Or.inl h1.symm)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inl (Or.inl h1.symm)
        · exact Or.inr h1

/-- An atom the fold kills was dead already, or shares its bond set with `seen`
or with another atom's triple. -/
lemma dead_of_foldl_dedupStep (layer : ℕ) (l : List (UInt32 × Fin n × ℕ))
    (hl : (l.map (·.2.1)).Nodup) (d : Vector Bool n) (r : List (UInt32 × Fin n × ℕ))
    (seen : List ℕ) (a : Fin n) (ha : (l.foldl (dedupStep layer) (d, r, seen)).1[a] = true) :
    d[a] = true ∨ ∃ t ∈ l, t.2.1 = a ∧
      (t.2.2 ∈ seen ∨ ∃ t' ∈ l, t'.2.1 ≠ a ∧ t'.2.2 = t.2.2) := by
  induction l generalizing d r seen with
  | nil => exact Or.inl ha
  | cons t l ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    rw [List.foldl_cons] at ha
    by_cases h : seen.contains t.2.2 = true
    · simp only [dedupStep, h, if_true] at ha
      rcases ih hl.2 _ _ _ ha with h1 | ⟨u, hu, hua, hu'⟩
      · simp only [Fin.getElem_fin, Vector.getElem_set] at h1
        split_ifs at h1 with hta
        · exact Or.inr ⟨t, List.mem_cons_self, Fin.ext hta, Or.inl (by simpa using h)⟩
        · exact Or.inl h1
      · refine Or.inr ⟨u, List.mem_cons_of_mem _ hu, hua, ?_⟩
        rcases hu' with h2 | ⟨u', hu'm, hu'a, hu'e⟩
        · exact Or.inl h2
        · exact Or.inr ⟨u', List.mem_cons_of_mem _ hu'm, hu'a, hu'e⟩
    · simp only [dedupStep, h, if_false, Bool.false_eq_true] at ha
      rcases ih hl.2 _ _ _ ha with h1 | ⟨u, hu, hua, hu'⟩
      · exact Or.inl h1
      · refine Or.inr ⟨u, List.mem_cons_of_mem _ hu, hua, ?_⟩
        rcases hu' with h2 | ⟨u', hu'm, hu'a, hu'e⟩
        · rcases List.mem_cons.mp h2 with h3 | h3
          · refine Or.inr ⟨t, List.mem_cons_self, ?_, h3.symm⟩
            rintro hta
            exact hl.1 (hta ▸ hua ▸ List.mem_map_of_mem hu)
          · exact Or.inl h3
        · exact Or.inr ⟨u', List.mem_cons_of_mem _ hu'm, hu'a, hu'e⟩

/-- The identifier of the first triple with bond set `e`. -/
def firstId : List (UInt32 × Fin n × ℕ) → ℕ → UInt32
  | [], _ => 0
  | t :: l, e => if t.2.2 = e then t.1 else firstId l e

/-- The fold emits, for every bond set not in `seen`, the identifier of its first triple. -/
lemma emitted_ids (layer : ℕ) (l : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) :
    (((emitted layer l seen).map (·.1) : List UInt32) : Multiset UInt32)
      = (((l.map (·.2.2)).toFinset \ seen.toFinset).val.map (firstId l)) := by
  induction l generalizing seen with
  | nil => simp [emitted]
  | cons t l ih =>
    rw [emitted, List.map_cons, List.toFinset_cons]
    by_cases h : seen.contains t.2.2 = true
    · have hs : t.2.2 ∈ seen.toFinset := by simpa using h
      rw [if_pos h, ih, Finset.insert_sdiff_of_mem _ hs]
      refine Multiset.map_congr rfl fun x hx ↦ ?_
      have hx' : x ∉ seen.toFinset := (Finset.mem_sdiff.mp (Finset.mem_val.mp hx)).2
      have : t.2.2 ≠ x := fun e ↦ hx' (e ▸ hs)
      simp [firstId, this]
    · have hs : t.2.2 ∉ seen.toFinset := by simpa using h
      rw [if_neg h, List.map_cons, ← Multiset.cons_coe, ih, Finset.insert_sdiff_of_notMem _ hs]
      have hset : (l.map (·.2.2)).toFinset \ (t.2.2 :: seen).toFinset
          = ((l.map (·.2.2)).toFinset \ seen.toFinset).erase t.2.2 := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset, List.mem_cons]
        tauto
      have hins : insert t.2.2 ((l.map (·.2.2)).toFinset \ seen.toFinset)
          = insert t.2.2 (((l.map (·.2.2)).toFinset \ seen.toFinset).erase t.2.2) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [hset, hins, Finset.insert_val_of_notMem (Finset.notMem_erase _ _), Multiset.map_cons]
      congr 1
      · simp [firstId]
      · refine Multiset.map_congr rfl fun x hx ↦ ?_
        have : t.2.2 ≠ x := fun e ↦ (Finset.mem_erase.mp (Finset.mem_val.mp hx)).1 e.symm
        simp [firstId, this]

/-! ### Sorted by identifier, the first identifier is the smallest -/

/-- Sorted by identifier, ignoring atoms. -/
def IdSorted (l : List (UInt32 × Fin n × ℕ)) : Prop := l.Pairwise fun p q ↦ p.1 ≤ q.1

lemma envLE_iff (p q : UInt32 × Fin n × ℕ) :
    envLE p q = true ↔ p.1.toNat < q.1.toNat ∨ (p.1.toNat = q.1.toNat ∧ p.2.1.val ≤ q.2.1.val) := by
  simp [envLE, UInt32.lt_iff_toNat_lt, ← UInt32.toNat_inj]

lemma idSorted_sortBy_envLE (l : List (UInt32 × Fin n × ℕ)) : IdSorted (sortBy envLE l) := by
  have h := pairwise_sortBy (le := envLE)
    (fun a b ↦ by
      rw [Bool.or_eq_true, envLE_iff, envLE_iff]; omega)
    (fun a b c hab hbc ↦ by rw [envLE_iff] at *; omega) l
  refine h.imp fun {p q} hpq ↦ ?_
  rw [envLE_iff] at hpq
  rw [UInt32.le_iff_toNat_le]
  omega

lemma firstId_spec (l : List (UInt32 × Fin n × ℕ)) (e : ℕ) (he : ∃ t ∈ l, t.2.2 = e) :
    ∃ t ∈ l, t.2.2 = e ∧ t.1 = firstId l e := by
  induction l with
  | nil => simp at he
  | cons u l ih =>
    by_cases hu : u.2.2 = e
    · exact ⟨u, List.mem_cons_self, hu, by simp [firstId, hu]⟩
    · obtain ⟨v, hv, hve⟩ := he
      rcases List.mem_cons.mp hv with rfl | hv
      · exact absurd hve hu
      · obtain ⟨w, hw, hwe, hw1⟩ := ih ⟨v, hv, hve⟩
        exact ⟨w, List.mem_cons_of_mem _ hw, hwe, by simp [firstId, hu, hw1]⟩

lemma firstId_le (l : List (UInt32 × Fin n × ℕ)) (hs : IdSorted l) (t : UInt32 × Fin n × ℕ)
    (ht : t ∈ l) : firstId l t.2.2 ≤ t.1 := by
  induction l with
  | nil => simp at ht
  | cons u l ih =>
    unfold IdSorted at hs
    rw [List.pairwise_cons] at hs
    by_cases hu : u.2.2 = t.2.2
    · simp only [firstId, hu, if_true]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact UInt32.le_refl _
      · exact hs.1 t ht
    · simp only [firstId, hu, if_false]
      rcases List.mem_cons.mp ht with rfl | ht
      · exact absurd rfl hu
      · exact ih hs.2 ht

/-- Two sorted lists with the same identifiers on bond set `e` have the same
first identifier there. -/
lemma firstId_eq_of_mem_iff {l₁ l₂ : List (UInt32 × Fin n × ℕ)} (hs₁ : IdSorted l₁)
    (hs₂ : IdSorted l₂) (e : ℕ)
    (h : ∀ x, (∃ t ∈ l₁, t.2.2 = e ∧ t.1 = x) ↔ (∃ t ∈ l₂, t.2.2 = e ∧ t.1 = x))
    (he : ∃ t ∈ l₁, t.2.2 = e) : firstId l₁ e = firstId l₂ e := by
  obtain ⟨t₁, ht₁, ht₁e, ht₁x⟩ := firstId_spec l₁ e he
  obtain ⟨u₂, hu₂, hu₂e, hu₂x⟩ := (h _).mp ⟨t₁, ht₁, ht₁e, rfl⟩
  obtain ⟨t₂, ht₂, ht₂e, ht₂x⟩ := firstId_spec l₂ e ⟨u₂, hu₂, hu₂e⟩
  obtain ⟨u₁, hu₁, hu₁e, hu₁x⟩ := (h _).mpr ⟨t₂, ht₂, ht₂e, rfl⟩
  apply UInt32.le_antisymm
  · have := firstId_le l₁ hs₁ u₁ hu₁
    rw [hu₁e, hu₁x] at this
    rw [← ht₂x]
    exact this
  · have := firstId_le l₂ hs₂ u₂ hu₂
    rw [hu₂e, hu₂x] at this
    rw [← ht₁x]
    exact this

/-- Duplicate removal over two sorted lists that agree, on every bond set not
yet seen, about which identifiers carry it emits the same identifiers. -/
lemma emitted_ids_eq (layer : ℕ) {l₁ l₂ : List (UInt32 × Fin n × ℕ)} (hs₁ : IdSorted l₁)
    (hs₂ : IdSorted l₂) {seen₁ seen₂ : List ℕ} (hseen : ∀ e, e ∈ seen₁ ↔ e ∈ seen₂)
    (h : ∀ e x, e ∉ seen₁ →
      ((∃ t ∈ l₁, t.2.2 = e ∧ t.1 = x) ↔ (∃ t ∈ l₂, t.2.2 = e ∧ t.1 = x))) :
    (((emitted layer l₁ seen₁).map (·.1) : List UInt32) : Multiset UInt32)
      = (((emitted layer l₂ seen₂).map (·.1) : List UInt32) : Multiset UInt32) := by
  rw [emitted_ids, emitted_ids]
  have hset : (l₁.map (·.2.2)).toFinset \ seen₁.toFinset
      = (l₂.map (·.2.2)).toFinset \ seen₂.toFinset := by
    ext e
    simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_map, ← hseen]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hn⟩
      obtain ⟨u, hu, hue, -⟩ := (h _ _ hn).mp ⟨t, ht, rfl, rfl⟩
      exact ⟨⟨u, hu, hue⟩, hn⟩
    · rintro ⟨⟨t, ht, rfl⟩, hn⟩
      obtain ⟨u, hu, hue, -⟩ := (h _ _ hn).mpr ⟨t, ht, rfl, rfl⟩
      exact ⟨⟨u, hu, hue⟩, hn⟩
  refine Multiset.map_congr (congrArg Finset.val hset) fun e he ↦ ?_
  rw [← hset] at he
  obtain ⟨he₁, hn⟩ := Finset.mem_sdiff.mp (Finset.mem_val.mp he)
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp (List.mem_toFinset.mp he₁)
  exact firstId_eq_of_mem_iff hs₁ hs₂ e (fun x ↦ h e x (by simpa using hn)) ⟨t, ht, hte⟩

/-! ### One round -/

section Round

variable {adj : Vector (List (ℕ × Fin n)) n} {kinds : Array UInt32} {layer : ℕ}

lemma morganLayer_result (s : MorganState n) :
    (morganLayer adj kinds layer s).result
      = s.result ++ emitted layer (sortBy envLE (roundTriples adj kinds layer s)) s.seen :=
  foldl_dedupStep_result _ _ _ _ _

lemma mem_morganLayer_seen (s : MorganState n) (e : ℕ) :
    e ∈ (morganLayer adj kinds layer s).seen
      ↔ e ∈ s.seen ∨ ∃ t ∈ roundTriples adj kinds layer s, t.2.2 = e := by
  unfold morganLayer
  dsimp only
  rw [mem_foldl_dedupStep_seen]
  simp only [mem_sortBy]

lemma mem_roundTriples {s : MorganState n} {t : UInt32 × Fin n × ℕ} :
    t ∈ roundTriples adj kinds layer s ↔ (roundAlive adj s)[t.2.1] = true ∧
      t = (growId adj kinds s.cur layer t.2.1, t.2.1, growEnv adj s.prevEnv t.2.1) := by
  unfold roundTriples
  simp only [List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨a, ha⟩
    split_ifs at ha with h
    · cases ha; exact ⟨h, rfl⟩
  · rintro ⟨h, ht⟩
    exact ⟨t.2.1, by rw [if_pos h, ← ht]⟩

lemma nodup_roundTriples (s : MorganState n) :
    ((roundTriples adj kinds layer s).map (·.2.1)).Nodup := by
  unfold roundTriples
  rw [List.map_filterMap]
  refine (List.nodup_finRange n).filterMap fun a a' b ha ha' ↦ ?_
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' <;> simp_all

lemma getElem_roundAlive (s : MorganState n) (a : Fin n) :
    (roundAlive adj s)[a] = (!s.dead[a] && !adj[a].isEmpty) := by
  simp [roundAlive]

/-- The dead atoms only grow during duplicate removal. -/
lemma foldl_dedupStep_dead_mono (l : List (UInt32 × Fin n × ℕ)) (d : Vector Bool n)
    (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) (a : Fin n) (ha : d[a] = true) :
    (l.foldl (dedupStep layer) (d, r, seen)).1[a] = true := by
  induction l generalizing d r seen with
  | nil => exact ha
  | cons t l ih =>
    rw [List.foldl_cons]
    unfold dedupStep
    split_ifs
    · refine ih _ _ _ ?_
      simp only [Fin.getElem_fin, Vector.getElem_set] at ha ⊢
      split_ifs <;> simp_all
    · exact ih _ _ _ ha

/-- A round's triples, with fewer atoms dead, minus those atoms. -/
lemma roundTriples_eq_filter (s : MorganState n) (d' : Vector Bool n)
    (hd : ∀ a : Fin n, d'[a] = true → s.dead[a] = true) :
    roundTriples adj kinds layer s
      = (roundTriples adj kinds layer { s with dead := d' }).filter fun t ↦ !s.dead[t.2.1] := by
  unfold roundTriples
  rw [List.filter_filterMap]
  refine List.filterMap_congr fun a _ ↦ ?_
  have hd' := hd a
  simp only [roundAlive, Vector.getElem_ofFn, Fin.getElem_fin] at hd' ⊢
  cases h1 : s.dead[(a : ℕ)] <;> cases h2 : d'[(a : ℕ)] <;> by_cases h3 : adj[(a : ℕ)] = [] <;>
    simp_all [Option.filter]

lemma morganLayer_cur (s : MorganState n) :
    (morganLayer adj kinds layer s).cur
      = Vector.ofFn fun a ↦ if (roundAlive adj s)[a] then growId adj kinds s.cur layer a else 0 :=
  rfl

lemma morganLayer_prevEnv (s : MorganState n) :
    (morganLayer adj kinds layer s).prevEnv
      = Vector.ofFn fun a ↦
        if (roundAlive adj s)[a] then growEnv adj s.prevEnv a else s.prevEnv[a] :=
  rfl

lemma morganLayer_dead (s : MorganState n) :
    (morganLayer adj kinds layer s).dead
      = ((sortBy envLE (roundTriples adj kinds layer s)).foldl (dedupStep layer)
          (Vector.ofFn fun a ↦ s.dead[a] || adj[a].isEmpty, s.result, s.seen)).1 :=
  rfl

end Round

/-! ### One round under relabeling -/

section RoundRelabel

/-- What relabeling does to a triple: move its atom. -/
def relabelTriple (t : UInt32 × Fin n × ℕ) : UInt32 × Fin n × ℕ := (t.1, σ t.2.1, t.2.2)

variable {s s' : MorganState n}

lemma roundAlive_relabel (hdead : s'.dead = relabelVec σ s.dead) :
    roundAlive (m.relabel σ).adjacency s' = relabelVec σ (roundAlive m.adjacency s) := by
  refine eq_relabelVec_of_apply σ fun a ↦ ?_
  rw [getElem_roundAlive, getElem_roundAlive, hdead, relabelVec_apply,
    isEmpty_adjacency_relabel]

lemma roundTriples_relabel (layer : ℕ) (hcur : s'.cur = relabelVec σ s.cur)
    (hprev : s'.prevEnv = relabelVec σ s.prevEnv) (hdead : s'.dead = relabelVec σ s.dead) :
    (roundTriples (m.relabel σ).adjacency (m.relabel σ).bondKinds layer s').Perm
      ((roundTriples m.adjacency m.bondKinds layer s).map (relabelTriple σ)) := by
  unfold roundTriples
  dsimp only
  refine ((map_finRange_perm σ).symm.filterMap _).trans ?_
  rw [List.filterMap_map, List.map_filterMap]
  refine List.Perm.of_eq (List.filterMap_congr fun a _ ↦ ?_)
  rw [Function.comp_apply, roundAlive_relabel m σ hdead, relabelVec_apply, hcur, hprev,
    growId_relabel, growEnv_relabel]
  split_ifs <;> rfl

lemma morganLayer_cur_relabel (layer : ℕ) (hcur : s'.cur = relabelVec σ s.cur)
    (hdead : s'.dead = relabelVec σ s.dead) :
    (morganLayer (m.relabel σ).adjacency (m.relabel σ).bondKinds layer s').cur
      = relabelVec σ (morganLayer m.adjacency m.bondKinds layer s).cur := by
  refine eq_relabelVec_of_apply σ fun a ↦ ?_
  rw [morganLayer_cur, morganLayer_cur]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, roundAlive_relabel m σ hdead, hcur,
    getElem_relabelVec, Equiv.symm_apply_apply, growId_relabel]

lemma morganLayer_prevEnv_relabel (layer : ℕ) (hprev : s'.prevEnv = relabelVec σ s.prevEnv)
    (hdead : s'.dead = relabelVec σ s.dead) :
    (morganLayer (m.relabel σ).adjacency (m.relabel σ).bondKinds layer s').prevEnv
      = relabelVec σ (morganLayer m.adjacency m.bondKinds layer s).prevEnv := by
  refine eq_relabelVec_of_apply σ fun a ↦ ?_
  rw [morganLayer_prevEnv, morganLayer_prevEnv]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, roundAlive_relabel m σ hdead, hprev,
    getElem_relabelVec, Equiv.symm_apply_apply, growEnv_relabel]

end RoundRelabel

/-! ### Bond sets as bitmasks -/

lemma testBit_growEnv (adj : Vector (List (ℕ × Fin n)) n) (pe : Vector ℕ n) (a : Fin n) (j : ℕ) :
    (growEnv adj pe a).testBit j
      = (pe[a].testBit j || adj[a].any fun p ↦ decide (p.1 = j) || pe[p.2].testBit j) := by
  unfold growEnv
  generalize pe[a] = init
  induction adj[a] generalizing init with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    simp only [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_assoc]

/-- An adjacency entry `(k, o)` of atom `x` is a bond `k` joining `x` and `o`. -/
lemma mem_adjacency {x : Fin n} {p : ℕ × Fin n} (hp : p ∈ m.adjacency[x]) :
    ∃ bd, m.bonds[p.1]? = some bd ∧
      ((bd.src = x ∧ bd.dst = p.2) ∨ (bd.dst = x ∧ bd.src = p.2)) := by
  unfold adjacency at hp
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, List.mem_filterMap] at hp
  obtain ⟨⟨bd, k⟩, hq, hf⟩ := hp
  rw [List.mem_zipIdx_iff_getElem?] at hq
  split_ifs at hf with h1 h2
  · cases hf; exact ⟨bd, hq, Or.inl ⟨h1, rfl⟩⟩
  · cases hf; exact ⟨bd, hq, Or.inr ⟨h2, rfl⟩⟩

/-! ### Radius 1: the only tied atoms are two-atom fragments -/

/-- Radius-1 bond sets: an atom's own bonds. -/
abbrev env1 (x : Fin n) : ℕ := growEnv m.adjacency (Vector.replicate n 0) x

lemma testBit_env1 (x : Fin n) (j : ℕ) :
    (m.env1 x).testBit j = true ↔ ∃ p ∈ m.adjacency[x], p.1 = j := by
  rw [env1, testBit_growEnv]
  simp

/-- Two atoms with the same radius-1 bond set: every neighbor of one is the other. -/
lemma eq_of_env1_eq {a b : Fin n} (hab : a ≠ b) (he : m.env1 a = m.env1 b) {p : ℕ × Fin n}
    (hp : p ∈ m.adjacency[a]) : p.2 = b := by
  have hk : (m.env1 a).testBit p.1 = true := (m.testBit_env1 a _).mpr ⟨p, hp, rfl⟩
  rw [he, testBit_env1] at hk
  obtain ⟨p', hp', hp'k⟩ := hk
  obtain ⟨bd, hbd, hbda⟩ := m.mem_adjacency hp
  obtain ⟨bd', hbd', hbdb⟩ := m.mem_adjacency hp'
  rw [hp'k, hbd] at hbd'
  cases hbd'
  rcases hbda with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hbdb with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact absurd (h1.symm.trans h3) hab
  · exact h2.symm.trans h3
  · exact h2.symm.trans h3
  · exact absurd (h1.symm.trans h3) hab

/-- The state after radius 1. -/
abbrev layer1 : MorganState n := morganLayer m.adjacency m.bondKinds 0 m.morganInit

/-- The state after radius 1 with only the atoms that have no neighbors dead: what
the state would be if duplicate removal killed nobody. -/
abbrev layer1Full : MorganState n :=
  { m.layer1 with dead := Vector.ofFn fun a ↦ m.morganInit.dead[a] || m.adjacency[a].isEmpty }

lemma roundAlive_morganInit (x : Fin n) :
    (roundAlive m.adjacency m.morganInit)[x] = !m.adjacency[x].isEmpty := by
  simp [roundAlive, morganInit, Vector.getElem_ofFn]

lemma layer1_prevEnv_apply {x : Fin n} (hx : m.adjacency[x].isEmpty = false) :
    m.layer1.prevEnv[x] = m.env1 x := by
  rw [layer1, morganLayer_prevEnv, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [Fin.eta, roundAlive_morganInit, hx, Bool.not_false, if_true]
  rfl

/-- An atom alive at radius 2 only because duplicate removal at radius 1 did not
kill it covers, at radius 2, a bond set already seen. -/
lemma grown_mem_seen_of_killed (t : UInt32 × Fin n × ℕ)
    (ht : t ∈ roundTriples m.adjacency m.bondKinds 1 m.layer1Full)
    (hdead : m.layer1.dead[t.2.1] = true) : t.2.2 ∈ m.layer1.seen := by
  obtain ⟨halive, hteq⟩ := mem_roundTriples.mp ht
  have ha : m.adjacency[t.2.1].isEmpty = false := by
    rw [getElem_roundAlive] at halive
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at halive
    exact halive.2
  have hnodup := (perm_sortBy (le := envLE)
    (roundTriples m.adjacency m.bondKinds 0 m.morganInit)).map (·.2.1)
    |>.nodup_iff.mpr (nodup_roundTriples _)
  rw [layer1, morganLayer_dead] at hdead
  rcases dead_of_foldl_dedupStep 0 _ hnodup _ _ _ t.2.1 hdead with h0 | ⟨t₀, ht₀, ht₀a, h⟩
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, morganInit, Vector.getElem_replicate,
      Bool.false_or] at h0
    rw [Fin.getElem_fin] at ha
    rw [ha] at h0
    exact absurd h0 Bool.false_ne_true
  rcases h with h | ⟨t₁, ht₁, ht₁a, ht₁e⟩
  · simp [morganInit] at h
  rw [mem_sortBy] at ht₀ ht₁
  obtain ⟨-, ht₀eq⟩ := mem_roundTriples.mp ht₀
  obtain ⟨hb, ht₁eq⟩ := mem_roundTriples.mp ht₁
  have hb' : m.adjacency[t₁.2.1].isEmpty = false := by
    rw [roundAlive_morganInit] at hb
    simpa using hb
  have henv : m.env1 t.2.1 = m.env1 t₁.2.1 := by
    rw [ht₀eq, ht₁eq] at ht₁e
    simp only [morganInit] at ht₁e
    rw [ht₀a] at ht₁e
    exact ht₁e.symm
  -- the radius-2 bond set is the radius-1 one
  have hgrow : growEnv m.adjacency m.layer1.prevEnv t.2.1 = m.env1 t.2.1 := by
    refine Nat.eq_of_testBit_eq fun j ↦ ?_
    rw [testBit_growEnv]
    refine Bool.eq_iff_iff.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases Bool.or_eq_true _ _ |>.mp h with h | h
      · rwa [m.layer1_prevEnv_apply ha] at h
      obtain ⟨p, hp, hpj⟩ := List.any_eq_true.mp h
      rcases Bool.or_eq_true _ _ |>.mp hpj with hpj | hpj
      · exact (m.testBit_env1 _ j).mpr ⟨p, hp, by simpa using hpj⟩
      · have hpb : p.2 = t₁.2.1 := m.eq_of_env1_eq (Ne.symm (ht₀a ▸ ht₁a)) henv hp
        simp only [hpb] at hpj
        rw [m.layer1_prevEnv_apply hb', ← henv] at hpj
        exact hpj
    · rw [Bool.or_eq_true]
      left
      rwa [m.layer1_prevEnv_apply ha]
  rw [hteq, mem_morganLayer_seen]
  refine Or.inr ⟨t₀, ht₀, ?_⟩
  rw [ht₀eq]
  simp only [morganInit]
  rw [ht₀a]
  exact hgrow.symm

/-- Radius 2 emits from the live atoms exactly what it would emit if radius 1 had
killed no duplicates. -/
lemma mem_layer2_iff {e : ℕ} (he : e ∉ m.layer1.seen) (x : UInt32) :
    (∃ t ∈ sortBy envLE (roundTriples m.adjacency m.bondKinds 1 m.layer1),
        t.2.2 = e ∧ t.1 = x)
      ↔ ∃ t ∈ roundTriples m.adjacency m.bondKinds 1 m.layer1Full, t.2.2 = e ∧ t.1 = x := by
  have hd : ∀ a : Fin n, m.layer1Full.dead[a] = true → m.layer1.dead[a] = true := fun a ha ↦ by
    rw [layer1, morganLayer_dead]
    exact foldl_dedupStep_dead_mono _ _ _ _ _ ha
  simp only [mem_sortBy]
  rw [roundTriples_eq_filter m.layer1 m.layer1Full.dead hd]
  simp only [List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨t, ⟨ht, -⟩, hte, htx⟩
    exact ⟨t, ht, hte, htx⟩
  · rintro ⟨t, ht, hte, htx⟩
    refine ⟨t, ⟨ht, ?_⟩, hte, htx⟩
    cases hdt : m.layer1.dead[t.2.1]
    · rfl
    · exact absurd (hte ▸ m.grown_mem_seen_of_killed t ht hdt) he

/-! ### The radius-≤ 2 theorem -/

lemma morganInit_cur_relabel :
    (m.relabel σ).morganInit.cur = relabelVec σ m.morganInit.cur :=
  eq_relabelVec_of_apply σ fun a ↦ by
    simpa [morganInit] using m.morganAtomInvariants_relabel σ a

lemma morganInit_prevEnv_relabel :
    (m.relabel σ).morganInit.prevEnv = relabelVec σ m.morganInit.prevEnv := by
  simp [morganInit, relabelVec_replicate]

lemma morganInit_dead_relabel :
    (m.relabel σ).morganInit.dead = relabelVec σ m.morganInit.dead := by
  simp [morganInit, relabelVec_replicate]

lemma layer1Full_dead_relabel :
    (m.relabel σ).layer1Full.dead = relabelVec σ m.layer1Full.dead := by
  refine eq_relabelVec_of_apply σ fun a ↦ ?_
  have h := m.isEmpty_adjacency_relabel σ a
  simp only [Fin.getElem_fin] at h
  simp [morganInit, Vector.getElem_ofFn, h]

lemma roundTriples_init_relabel :
    (roundTriples (m.relabel σ).adjacency (m.relabel σ).bondKinds 0 (m.relabel σ).morganInit).Perm
      ((roundTriples m.adjacency m.bondKinds 0 m.morganInit).map (relabelTriple σ)) :=
  roundTriples_relabel m σ 0 (m.morganInit_cur_relabel σ) (m.morganInit_prevEnv_relabel σ)
    (m.morganInit_dead_relabel σ)

lemma layer1_cur_relabel : (m.relabel σ).layer1.cur = relabelVec σ m.layer1.cur :=
  morganLayer_cur_relabel m σ 0 (m.morganInit_cur_relabel σ) (m.morganInit_dead_relabel σ)

lemma layer1_prevEnv_relabel : (m.relabel σ).layer1.prevEnv = relabelVec σ m.layer1.prevEnv :=
  morganLayer_prevEnv_relabel m σ 0 (m.morganInit_prevEnv_relabel σ) (m.morganInit_dead_relabel σ)

lemma mem_layer1_seen_relabel (e : ℕ) : e ∈ (m.relabel σ).layer1.seen ↔ e ∈ m.layer1.seen := by
  rw [layer1, layer1, mem_morganLayer_seen, mem_morganLayer_seen]
  simp only [morganInit, List.not_mem_nil, false_or]
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ((m.roundTriples_init_relabel σ).mem_iff.mp ht)
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨relabelTriple σ u, (m.roundTriples_init_relabel σ).mem_iff.mpr
      (List.mem_map_of_mem hu), rfl⟩

/-- Identifiers and bond sets of a list of triples, as a predicate. -/
lemma exists_mem_map_relabelTriple (l : List (UInt32 × Fin n × ℕ)) (e : ℕ) (x : UInt32) :
    (∃ t ∈ l.map (relabelTriple σ), t.2.2 = e ∧ t.1 = x) ↔ ∃ t ∈ l, t.2.2 = e ∧ t.1 = x := by
  simp [relabelTriple]

lemma ids_init_relabel :
    ((((m.relabel σ).morganInit.result.map (·.1)) : List UInt32) : Multiset UInt32)
      = ((m.morganInit.result.map (·.1) : List UInt32) : Multiset UInt32) := by
  simp only [morganInit, List.map_map, Function.comp_def]
  rw [Multiset.coe_eq_coe]
  have h := ((map_finRange_perm σ).map fun i ↦ (m.relabel σ).morganAtomInvariants[i]).symm
  rw [List.map_map] at h
  refine h.trans (List.Perm.of_eq (List.map_congr_left fun i _ ↦ ?_))
  exact m.morganAtomInvariants_relabel σ i

lemma ids_layer1_relabel :
    ((((m.relabel σ).layer1.result.map (·.1)) : List UInt32) : Multiset UInt32)
      = ((m.layer1.result.map (·.1) : List UInt32) : Multiset UInt32) := by
  rw [layer1, layer1, morganLayer_result, morganLayer_result, List.map_append, List.map_append,
    ← Multiset.coe_add, ← Multiset.coe_add, ids_init_relabel]
  congr 1
  refine emitted_ids_eq 0 (idSorted_sortBy_envLE _) (idSorted_sortBy_envLE _)
    (by simp [morganInit]) fun e x _ ↦ ?_
  simp only [mem_sortBy]
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ((m.roundTriples_init_relabel σ).mem_iff.mp ht)
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨relabelTriple σ u, (m.roundTriples_init_relabel σ).mem_iff.mpr
      (List.mem_map_of_mem hu), h⟩

lemma ids_layer2_relabel :
    (((morganLayer (m.relabel σ).adjacency (m.relabel σ).bondKinds 1
        (m.relabel σ).layer1).result.map (·.1) : List UInt32) : Multiset UInt32)
      = ((morganLayer m.adjacency m.bondKinds 1 m.layer1).result.map (·.1) : List UInt32) := by
  rw [morganLayer_result (layer := 1) (m.relabel σ).layer1,
    morganLayer_result (layer := 1) m.layer1, List.map_append, List.map_append,
    ← Multiset.coe_add, ← Multiset.coe_add, ids_layer1_relabel]
  congr 1
  have hfull := roundTriples_relabel m σ 1 (s := m.layer1Full) (s' := (m.relabel σ).layer1Full)
    (m.layer1_cur_relabel σ) (m.layer1_prevEnv_relabel σ) (m.layer1Full_dead_relabel σ)
  refine emitted_ids_eq 1 (idSorted_sortBy_envLE _) (idSorted_sortBy_envLE _)
    (m.mem_layer1_seen_relabel σ) fun e x he ↦ ?_
  have he' : e ∉ m.layer1.seen := fun h ↦ he ((m.mem_layer1_seen_relabel σ e).mpr h)
  rw [(m.relabel σ).mem_layer2_iff he, m.mem_layer2_iff he']
  constructor
  · rintro ⟨t, ht, h⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (hfull.mem_iff.mp ht)
    exact ⟨u, hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨relabelTriple σ u, hfull.mem_iff.mpr (List.mem_map_of_mem hu), h⟩

/-- Up to radius 2, relabeling the atoms permutes the emitted identifiers. -/
theorem morganEnvironments_ids_relabel {radius : ℕ} (hr : radius ≤ 2) :
    ((((m.relabel σ).morganEnvironments radius).map (·.1) : List UInt32) : Multiset UInt32)
      = ((m.morganEnvironments radius).map (·.1) : List UInt32) := by
  unfold morganEnvironments
  rcases radius with _ | _ | _ | r
  · exact m.ids_init_relabel σ
  · exact m.ids_layer1_relabel σ
  · exact m.ids_layer2_relabel σ
  · omega

/-- Up to radius 2, the unfolded Morgan fingerprint does not depend on the atom order. -/
theorem morganIds_relabel {radius : ℕ} (hr : radius ≤ 2) :
    (m.relabel σ).morganIds radius = m.morganIds radius := by
  have hperm := Multiset.coe_eq_coe.mp (m.morganEnvironments_ids_relabel σ hr)
  have hsort : ∀ l : List UInt32, (sortBy (fun a b ↦ decide (a ≤ b)) l).Pairwise
      fun a b ↦ decide (a ≤ b) = true :=
    pairwise_sortBy
      (fun a b ↦ by
        rcases UInt32.le_total a b with h | h <;> simp [h])
      (fun a b c hab hbc ↦ by
        simp only [decide_eq_true_eq] at *; exact UInt32.le_trans hab hbc)
  have heq : sortBy (fun a b ↦ decide (a ≤ b)) (((m.relabel σ).morganEnvironments radius).map (·.1))
      = sortBy (fun a b ↦ decide (a ≤ b)) ((m.morganEnvironments radius).map (·.1)) :=
    List.Perm.eq_of_pairwise (le := fun a b ↦ decide (a ≤ b) = true)
      (fun a b _ _ hab hba ↦ UInt32.le_antisymm (by simpa using hab) (by simpa using hba))
      (hsort _) (hsort _)
      (((perm_sortBy _).trans hperm).trans (perm_sortBy _).symm)
  unfold morganIds
  simp only [heq]

/-- **Up to radius 2, the Morgan fingerprint does not depend on the atom order.**
At radius 3 it can (see the module docstring). -/
theorem morganBits_relabel {radius : ℕ} (hr : radius ≤ 2) (fpSize : ℕ) :
    (m.relabel σ).morganBits radius fpSize = m.morganBits radius fpSize := by
  unfold morganBits
  rw [m.morganIds_relabel σ hr]

end LeanSMILES.Molecule

namespace LeanSMILES

/-- The bundled form: up to radius 2, a molecule and any relabeling of it have
the same Morgan fingerprint. -/
theorem Mol.morganBits_relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) {radius : ℕ}
    (hr : radius ≤ 2) (fpSize : ℕ) :
    (⟨M.n, M.mol.relabel σ⟩ : Mol).morganBits radius fpSize = M.morganBits radius fpSize :=
  M.mol.morganBits_relabel σ hr fpSize

end LeanSMILES
