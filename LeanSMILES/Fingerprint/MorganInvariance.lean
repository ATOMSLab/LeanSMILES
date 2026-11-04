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
lemma foldl_map_hom {α γ β β' : Type*} (g : α → γ) (h : β → β') (f : α → β → α) (f' : γ → β' → γ)
    (hstep : ∀ a b, f' (g a) (h b) = g (f a b)) (l : List β) (init : α) :
    (l.map h).foldl f' (g init) = g (l.foldl f init) :=
  List.foldl_map.trans (List.foldl_hom g hstep)

/-- Setting entry `σ x` of a relabeled vector is relabeling the vector with entry `x` set. -/
lemma relabelVec_set {α : Type*} (v : Vector α n) (x : Fin n) (a : α) :
    (relabelVec σ v).set (σ x).val a (σ x).isLt = relabelVec σ (v.set x.val a x.isLt) :=
  eq_relabelVec_of_apply σ fun i ↦ by simp [Vector.getElem_set, Fin.val_inj]

/-- Relabeling a constant vector leaves it unchanged. -/
lemma relabelVec_replicate {α : Type*} (a : α) :
    relabelVec σ (Vector.replicate n a) = Vector.replicate n a :=
  Vector.ext fun _ _ ↦ by simp

/-! ### Ring membership under relabeling -/

/-- One reachability sweep commutes with relabeling the atoms, the skipped bond and the
reached set. -/
lemma reachStep_relabel (skip : Sym2 (Fin n)) (seen : Vector Bool n) :
    (m.relabel σ).reachStep (Sym2.map σ skip) (relabelVec σ seen)
      = relabelVec σ (m.reachStep skip seen) := by
  unfold reachStep
  rw [bonds_relabel]
  refine foldl_map_hom _ _ _ _ (fun v b ↦ ?_) _ _
  simp only [Bond.edge_map, bne, (Sym2.map.injective σ.injective).beq_eq]
  simp only [Bond.map, Fin.getElem_fin, getElem_relabelVec, Fin.eta, Equiv.symm_apply_apply]
  split_ifs <;> first | rfl | simp [relabelVec_set]

/-- Any number of reachability sweeps commutes with relabeling. -/
lemma iterate_reachStep_relabel (skip : Sym2 (Fin n)) (k : ℕ) (v : Vector Bool n) :
    ((m.relabel σ).reachStep (Sym2.map σ skip))^[k] (relabelVec σ v)
      = relabelVec σ ((m.reachStep skip)^[k] v) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, reachStep_relabel]

/-- The atoms reachable from `σ start` without the bond `σ skip` are the relabeled
atoms reachable from `start` without `skip`. -/
lemma reachableWithout_relabel (skip : Sym2 (Fin n)) (start : Fin n) :
    (m.relabel σ).reachableWithout (Sym2.map σ skip) (σ start)
      = relabelVec σ (m.reachableWithout skip start) := by
  unfold reachableWithout
  conv_lhs => rw [← relabelVec_replicate σ false, relabelVec_set, iterate_reachStep_relabel]

/-- A relabeled bond lies on a ring exactly when the original bond does. -/
lemma bondInRing_relabel (b : Bond n) :
    (m.relabel σ).bondInRing (b.map σ σ.injective) = m.bondInRing b := by
  unfold bondInRing
  rw [Bond.edge_map, show (b.map σ σ.injective).src = σ b.src from rfl, reachableWithout_relabel]
  exact relabelVec_apply σ _ b.dst

/-- The ring edges of a relabeled molecule are the relabeled ring edges, in order. -/
lemma ringEdges_relabel : (m.relabel σ).ringEdges = m.ringEdges.map (Sym2.map σ) := by
  simp [ringEdges, bonds_relabel, List.filter_map, Function.comp_def, bondInRing_relabel]

/-- Atom `σ i` touches a ring bond after relabeling exactly when atom `i` did before. -/
lemma inRingVector_relabel (i : Fin n) : (m.relabel σ).inRingVector[σ i] = m.inRingVector[i] := by
  simp [inRingVector, bondsAt_relabel, ringEdges_relabel, List.any_map, Function.comp_def,
    (Sym2.map.injective σ.injective).eq_iff]

/-! ### Neighbors, adjacency and bond types under relabeling -/

/-- The neighbors of `σ i` after relabeling are the relabeled neighbors of `i`, in order. -/
lemma neighbors_relabel (i : Fin n) : (m.relabel σ).neighbors (σ i) = (m.neighbors i).map σ := by
  simp [neighbors, bondsAt_relabel, Function.comp_def, Bond.other, Bond.map, apply_ite]

/-- The adjacency list of `σ i` after relabeling is that of `i` with the neighbors
relabeled; the bond indices do not change. -/
lemma adjacency_relabel (i : Fin n) :
    (m.relabel σ).adjacency[σ i] = m.adjacency[i].map fun p ↦ (p.1, σ p.2) := by
  unfold adjacency
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, bonds_relabel, List.zipIdx_map,
    List.filterMap_map, List.map_filterMap]
  congr 1
  funext p
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, Bond.map, σ.injective.eq_iff]
  split_ifs <;> rfl

/-- Relabeling keeps the bond list in order, so the bond kinds by index do not change. -/
lemma bondKinds_relabel : (m.relabel σ).bondKinds = m.bondKinds := by
  simp [bondKinds, bonds_relabel, Bond.map, Function.comp_def]

/-- The radius-0 identifier of atom `σ i` after relabeling is that of atom `i`. -/
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

/-- Growing the environment of `σ a` after relabeling gives the bond set that growing
`a` gave before. -/
lemma growEnv_relabel (pe : Vector ℕ n) (a : Fin n) :
    growEnv (m.relabel σ).adjacency (relabelVec σ pe) (σ a) = growEnv m.adjacency pe a := by
  simp only [growEnv, adjacency_relabel, List.foldl_map, relabelVec_apply]

/-- Growing the identifier of `σ a` after relabeling gives the identifier that growing
`a` gave before. -/
lemma growId_relabel (cur : Vector UInt32 n) (layer : ℕ) (a : Fin n) :
    growId (m.relabel σ).adjacency (m.relabel σ).bondKinds (relabelVec σ cur) layer (σ a)
      = growId m.adjacency m.bondKinds cur layer a := by
  simp only [growId, adjacency_relabel, bondKinds_relabel, List.map_map, Function.comp_def,
    relabelVec_apply]

/-! ### Duplicate removal

`emitted layer l seen` is what the duplicate-removal fold over `l` appends to
the result: the first triple of every bond set not in `seen`. -/

/-- The environments the fold emits. -/
def emitted (layer : ℕ) : List (UInt32 × Fin n × ℕ) → List ℕ → List (UInt32 × Fin n × ℕ)
  | [], _ => []
  | t :: l, seen =>
    if seen.contains t.2.2 then emitted layer l seen
    else (t.1, t.2.1, layer + 1) :: emitted layer l (t.2.2 :: seen)

/-- The duplicate-removal fold appends `emitted layer l seen` to the result. -/
lemma foldl_dedupStep_result (layer : ℕ) (l : List (UInt32 × Fin n × ℕ)) (d : Vector Bool n)
    (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) :
    (l.foldl (dedupStep layer) (d, r, seen)).2.1 = r ++ emitted layer l seen := by
  induction l generalizing d r seen <;> grind [emitted, dedupStep]

/-- After the duplicate-removal fold, the bond sets seen are the old ones and those of `l`. -/
lemma mem_foldl_dedupStep_seen (layer : ℕ) (l : List (UInt32 × Fin n × ℕ)) (d : Vector Bool n)
    (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ) (e : ℕ) :
    e ∈ (l.foldl (dedupStep layer) (d, r, seen)).2.2 ↔ e ∈ seen ∨ ∃ t ∈ l, t.2.2 = e := by
  induction l generalizing d r seen <;> grind [dedupStep]

/-- An atom the fold kills was dead already, or shares its bond set with `seen`
or with another atom's triple. -/
lemma dead_of_foldl_dedupStep (layer : ℕ) (l : List (UInt32 × Fin n × ℕ))
    (hl : (l.map (·.2.1)).Nodup) (d : Vector Bool n) (r : List (UInt32 × Fin n × ℕ)) (seen : List ℕ)
    (a : Fin n) (ha : (l.foldl (dedupStep layer) (d, r, seen)).1[a] = true) :
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
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hua,
          hu'.imp_right fun ⟨u', h₁, h₂⟩ ↦ ⟨u', List.mem_cons_of_mem _ h₁, h₂⟩⟩
    · simp only [dedupStep, h, if_false, Bool.false_eq_true] at ha
      rcases ih hl.2 _ _ _ ha with h1 | ⟨u, hu, hua, hu'⟩
      · exact Or.inl h1
      · refine Or.inr ⟨u, List.mem_cons_of_mem _ hu, hua, ?_⟩
        rcases hu' with h2 | ⟨u', h₁, h₂⟩
        · rcases List.mem_cons.mp h2 with h3 | h3
          · exact Or.inr ⟨t, List.mem_cons_self,
              fun hta ↦ hl.1 (hta ▸ hua ▸ List.mem_map_of_mem hu), h3.symm⟩
          · exact Or.inl h3
        · exact Or.inr ⟨u', List.mem_cons_of_mem _ h₁, h₂⟩

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
      grind [firstId]
    · have hs : t.2.2 ∉ seen.toFinset := by simpa using h
      rw [if_neg h, List.map_cons, ← Multiset.cons_coe, ih, Finset.insert_sdiff_of_notMem _ hs,
        List.toFinset_cons, Finset.sdiff_insert, ← Finset.insert_erase (Finset.mem_insert_self _ _),
        Finset.erase_insert_eq_erase, Finset.insert_val_of_notMem (Finset.notMem_erase _ _),
        Multiset.map_cons]
      congr 1
      · simp [firstId]
      · refine Multiset.map_congr rfl fun x hx ↦ ?_
        grind [firstId]

/-! ### Sorted by identifier, the first identifier is the smallest -/

/-- Sorted by identifier, ignoring atoms. -/
def IdSorted (l : List (UInt32 × Fin n × ℕ)) : Prop := l.Pairwise fun p q ↦ p.1 ≤ q.1

/-- `envLE` compares identifiers as natural numbers, then atom indices. -/
lemma envLE_iff (p q : UInt32 × Fin n × ℕ) :
    envLE p q = true ↔ p.1.toNat < q.1.toNat ∨ (p.1.toNat = q.1.toNat ∧ p.2.1.val ≤ q.2.1.val) := by
  simp [envLE, UInt32.lt_iff_toNat_lt, ← UInt32.toNat_inj]

/-- Sorting by `envLE` sorts by identifier. -/
lemma idSorted_sortBy_envLE (l : List (UInt32 × Fin n × ℕ)) : IdSorted (sortBy envLE l) := by
  refine (pairwise_sortBy (le := envLE) (by grind [envLE_iff]) (by grind [envLE_iff]) l).imp ?_
  grind [envLE_iff, UInt32.le_iff_toNat_le]

/-- A list with a triple on bond set `e` has one carrying the identifier `firstId l e`. -/
lemma firstId_spec (l : List (UInt32 × Fin n × ℕ)) (e : ℕ) (he : ∃ t ∈ l, t.2.2 = e) :
    ∃ t ∈ l, t.2.2 = e ∧ t.1 = firstId l e := by
  induction l with
  | nil => simp at he
  | cons u l ih =>
    by_cases hu : u.2.2 = e
    · exact ⟨u, List.mem_cons_self, hu, by simp [firstId, hu]⟩
    · obtain ⟨w, hw, hwe, hw1⟩ := ih (by simpa [hu] using he)
      exact ⟨w, List.mem_cons_of_mem _ hw, hwe, by simp [firstId, hu, hw1]⟩

/-- In a list sorted by identifier, `firstId` on a triple's bond set is at most the
triple's identifier. -/
lemma firstId_le (l : List (UInt32 × Fin n × ℕ)) (hs : IdSorted l) (t : UInt32 × Fin n × ℕ)
    (ht : t ∈ l) : firstId l t.2.2 ≤ t.1 := by
  induction l <;> grind [firstId, IdSorted, List.pairwise_cons]

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
  exact UInt32.le_antisymm (by simpa [hu₁e, hu₁x, ht₂x] using firstId_le l₁ hs₁ u₁ hu₁)
    (by simpa [hu₂e, hu₂x, ht₁x] using firstId_le l₂ hs₂ u₂ hu₂)

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
    constructor <;> rintro ⟨⟨t, ht, rfl⟩, hn⟩
    · obtain ⟨u, hu, hue, -⟩ := (h _ _ hn).mp ⟨t, ht, rfl, rfl⟩
      exact ⟨⟨u, hu, hue⟩, hn⟩
    · obtain ⟨u, hu, hue, -⟩ := (h _ _ hn).mpr ⟨t, ht, rfl, rfl⟩
      exact ⟨⟨u, hu, hue⟩, hn⟩
  refine Multiset.map_congr (congrArg Finset.val hset) fun e he ↦ ?_
  rw [← hset] at he
  obtain ⟨he₁, hn⟩ := Finset.mem_sdiff.mp (Finset.mem_val.mp he)
  obtain ⟨t, ht, hte⟩ := List.mem_map.mp (List.mem_toFinset.mp he₁)
  exact firstId_eq_of_mem_iff hs₁ hs₂ e (fun x ↦ h e x (by simpa using hn)) ⟨t, ht, hte⟩

/-! ### One round -/

section Round

variable {adj : Vector (List (ℕ × Fin n)) n} {kinds : Array UInt32} {layer : ℕ}

/-- A round appends to the result what duplicate removal emits from its sorted triples. -/
lemma morganLayer_result (s : MorganState n) :
    (morganLayer adj kinds layer s).result
      = s.result ++ emitted layer (sortBy envLE (roundTriples adj kinds layer s)) s.seen :=
  foldl_dedupStep_result _ _ _ _ _

/-- After a round, the bond sets seen are the old ones and those of the round's triples. -/
lemma mem_morganLayer_seen (s : MorganState n) (e : ℕ) :
    e ∈ (morganLayer adj kinds layer s).seen
      ↔ e ∈ s.seen ∨ ∃ t ∈ roundTriples adj kinds layer s, t.2.2 = e := by
  simp only [morganLayer, mem_foldl_dedupStep_seen, mem_sortBy]

/-- The round's triples are the live atoms, each with its grown identifier and bond set. -/
lemma mem_roundTriples {s : MorganState n} {t : UInt32 × Fin n × ℕ} :
    t ∈ roundTriples adj kinds layer s ↔ (roundAlive adj s)[t.2.1] = true ∧
      t = (growId adj kinds s.cur layer t.2.1, t.2.1, growEnv adj s.prevEnv t.2.1) := by
  simp only [roundTriples, List.mem_filterMap, List.mem_finRange, true_and,
    Option.ite_none_right_eq_some, Option.some.injEq]
  constructor
  · rintro ⟨a, h, rfl⟩
    exact ⟨h, rfl⟩
  · rintro ⟨h, ht⟩
    exact ⟨_, h, ht.symm⟩

/-- A round has at most one triple per atom. -/
lemma nodup_roundTriples (s : MorganState n) :
    ((roundTriples adj kinds layer s).map (·.2.1)).Nodup := by
  unfold roundTriples
  rw [List.map_filterMap]
  refine (List.nodup_finRange n).filterMap fun a a' b ha ha' ↦ ?_
  simp only [Option.mem_def] at ha ha'
  split_ifs at ha ha' <;> simp_all

/-- An atom grows this round iff it is not dead and has a neighbor. -/
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
    rw [List.foldl_cons, dedupStep]
    split_ifs
    · exact ih _ _ _ (by simp_all [Vector.getElem_set])
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

/-- The identifiers after a round: grown for the live atoms, `0` for the others. -/
lemma morganLayer_cur (s : MorganState n) :
    (morganLayer adj kinds layer s).cur
      = Vector.ofFn fun a ↦ if (roundAlive adj s)[a] then growId adj kinds s.cur layer a else 0 :=
  rfl

/-- The bond sets after a round: grown for the live atoms, unchanged for the others. -/
lemma morganLayer_prevEnv (s : MorganState n) :
    (morganLayer adj kinds layer s).prevEnv
      = Vector.ofFn fun a ↦
        if (roundAlive adj s)[a] then growEnv adj s.prevEnv a else s.prevEnv[a] :=
  rfl

/-- The dead atoms after a round: the atoms without neighbors and the old dead atoms, run
through the duplicate-removal fold. -/
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

/-- If the dead atoms move with the relabeling, so do the atoms that grow this round. -/
lemma roundAlive_relabel (hdead : s'.dead = relabelVec σ s.dead) :
    roundAlive (m.relabel σ).adjacency s' = relabelVec σ (roundAlive m.adjacency s) :=
  eq_relabelVec_of_apply σ fun a ↦ by
    rw [getElem_roundAlive, getElem_roundAlive, hdead, relabelVec_apply, isEmpty_adjacency_relabel]

/-- If the state moves with the relabeling, the round's triples are the relabeled
triples, up to order. -/
lemma roundTriples_relabel (layer : ℕ) (hcur : s'.cur = relabelVec σ s.cur)
    (hprev : s'.prevEnv = relabelVec σ s.prevEnv) (hdead : s'.dead = relabelVec σ s.dead) :
    (roundTriples (m.relabel σ).adjacency (m.relabel σ).bondKinds layer s').Perm
      ((roundTriples m.adjacency m.bondKinds layer s).map (relabelTriple σ)) := by
  unfold roundTriples
  dsimp only
  refine (σ.map_finRange_perm.symm.filterMap _).trans ?_
  rw [List.filterMap_map, List.map_filterMap]
  refine List.Perm.of_eq (List.filterMap_congr fun a _ ↦ ?_)
  rw [Function.comp_apply, roundAlive_relabel m σ hdead, relabelVec_apply, hcur, hprev,
    growId_relabel, growEnv_relabel]
  split_ifs <;> rfl

/-- If the identifiers and dead atoms move with the relabeling, so do the identifiers
after a round. -/
lemma morganLayer_cur_relabel (layer : ℕ) (hcur : s'.cur = relabelVec σ s.cur)
    (hdead : s'.dead = relabelVec σ s.dead) :
    (morganLayer (m.relabel σ).adjacency (m.relabel σ).bondKinds layer s').cur
      = relabelVec σ (morganLayer m.adjacency m.bondKinds layer s).cur := by
  refine eq_relabelVec_of_apply σ fun a ↦ ?_
  rw [morganLayer_cur, morganLayer_cur]
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, roundAlive_relabel m σ hdead, hcur,
    getElem_relabelVec, Equiv.symm_apply_apply, growId_relabel]

/-- If the bond sets and dead atoms move with the relabeling, so do the bond sets after
a round. -/
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

/-- Bond `j` is in the grown bond set of `a` iff it was already, or it joins `a` to a
neighbor, or that neighbor's bond set has it. -/
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
  split_ifs at hf with h1 h2 <;> cases hf
  · exact ⟨bd, hq, Or.inl ⟨h1, rfl⟩⟩
  · exact ⟨bd, hq, Or.inr ⟨h2, rfl⟩⟩

/-! ### Radius 1: the only tied atoms are two-atom fragments -/

/-- Radius-1 bond sets: an atom's own bonds. -/
abbrev env1 (x : Fin n) : ℕ := growEnv m.adjacency (Vector.replicate n 0) x

/-- Bond `j` is in the radius-1 bond set of `x` iff it is one of `x`'s bonds. -/
lemma testBit_env1 (x : Fin n) (j : ℕ) :
    (m.env1 x).testBit j = true ↔ ∃ p ∈ m.adjacency[x], p.1 = j := by
  simp [env1, testBit_growEnv]

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
  rcases hbda with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hbdb with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    first | exact absurd (h1.symm.trans h3) hab | exact h2.symm.trans h3

/-- The state after radius 1. -/
abbrev layer1 : MorganState n := morganLayer m.adjacency m.bondKinds 0 m.morganInit

/-- The state after radius 1 with only the atoms that have no neighbors dead: what
the state would be if duplicate removal killed nobody. -/
abbrev layer1Full : MorganState n :=
  { m.layer1 with dead := Vector.ofFn fun a ↦ m.morganInit.dead[a] || m.adjacency[a].isEmpty }

/-- Before radius 1, an atom grows iff it has a neighbor. -/
lemma roundAlive_morganInit (x : Fin n) :
    (roundAlive m.adjacency m.morganInit)[x] = !m.adjacency[x].isEmpty := by
  simp [roundAlive, morganInit, Vector.getElem_ofFn]

/-- After radius 1, an atom with a neighbor carries its radius-1 bond set. -/
lemma layer1_prevEnv_apply {x : Fin n} (hx : m.adjacency[x].isEmpty = false) :
    m.layer1.prevEnv[x] = m.env1 x := by
  rw [layer1, morganLayer_prevEnv, Fin.getElem_fin, Vector.getElem_ofFn]
  simp only [Fin.eta, roundAlive_morganInit, hx, Bool.not_false, if_true]
  rfl

-- An atom with a neighbor has its radius-1 bond set seen after radius 1.
private lemma env1_mem_layer1_seen {x : Fin n} (hx : m.adjacency[x].isEmpty = false) :
    m.env1 x ∈ m.layer1.seen := by
  rw [layer1, mem_morganLayer_seen]
  refine Or.inr ⟨(growId m.adjacency m.bondKinds m.morganInit.cur 0 x, x, m.env1 x),
    mem_roundTriples.mpr ⟨(m.roundAlive_morganInit x).trans (congrArg (!·) hx), ?_⟩, rfl⟩
  simp [morganInit]

-- An atom with a neighbor that radius 1 killed shares its radius-1 bond set with another
-- atom with a neighbor.
private lemma exists_env1_eq_of_layer1_dead {x : Fin n} (hx : m.adjacency[x].isEmpty = false)
    (hdead : m.layer1.dead[x] = true) :
    ∃ y, x ≠ y ∧ m.adjacency[y].isEmpty = false ∧ m.env1 x = m.env1 y := by
  have hnodup := (perm_sortBy (le := envLE)
    (roundTriples m.adjacency m.bondKinds 0 m.morganInit)).map (·.2.1)
    |>.nodup_iff.mpr (nodup_roundTriples _)
  rw [layer1, morganLayer_dead] at hdead
  rcases dead_of_foldl_dedupStep 0 _ hnodup _ _ _ x hdead with h0 | ⟨t₀, ht₀, rfl, h⟩
  · simp only [Fin.getElem_fin, Vector.getElem_ofFn, morganInit, Vector.getElem_replicate,
      Bool.false_or] at h0
    simp_all
  rcases h with h | ⟨t₁, ht₁, ht₁a, ht₁e⟩
  · simp [morganInit] at h
  rw [mem_sortBy] at ht₀ ht₁
  obtain ⟨-, ht₀eq⟩ := mem_roundTriples.mp ht₀
  obtain ⟨hb, ht₁eq⟩ := mem_roundTriples.mp ht₁
  refine ⟨t₁.2.1, ht₁a.symm, by simpa using (m.roundAlive_morganInit _).symm.trans hb, ?_⟩
  rw [ht₀eq, ht₁eq] at ht₁e
  exact ht₁e.symm

-- Of two atoms with the same radius-1 bond set, each has only the other as neighbor, so
-- its radius-2 bond set is its radius-1 one.
private lemma growEnv_layer1_of_env1_eq {x y : Fin n} (hxy : x ≠ y) (he : m.env1 x = m.env1 y)
    (hx : m.adjacency[x].isEmpty = false) (hy : m.adjacency[y].isEmpty = false) :
    growEnv m.adjacency m.layer1.prevEnv x = m.env1 x := by
  refine Nat.eq_of_testBit_eq fun j ↦ Bool.eq_iff_iff.mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [testBit_growEnv, m.layer1_prevEnv_apply hx] at h
    simp only [Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨p, hp, rfl | hpj⟩
    · exact h
    · exact (m.testBit_env1 _ _).mpr ⟨p, hp, rfl⟩
    · simp only [m.eq_of_env1_eq hxy he hp] at hpj
      rwa [m.layer1_prevEnv_apply hy, ← he] at hpj
  · rw [testBit_growEnv, m.layer1_prevEnv_apply hx, h, Bool.true_or]

/-- An atom alive at radius 2 only because duplicate removal at radius 1 did not
kill it covers, at radius 2, a bond set already seen. -/
lemma grown_mem_seen_of_killed (t : UInt32 × Fin n × ℕ)
    (ht : t ∈ roundTriples m.adjacency m.bondKinds 1 m.layer1Full)
    (hdead : m.layer1.dead[t.2.1] = true) : t.2.2 ∈ m.layer1.seen := by
  obtain ⟨halive, hteq⟩ := mem_roundTriples.mp ht
  have ha : m.adjacency[t.2.1].isEmpty = false := by
    simp only [getElem_roundAlive, Bool.and_eq_true, Bool.not_eq_true'] at halive
    exact halive.2
  obtain ⟨y, hxy, hy, henv⟩ := m.exists_env1_eq_of_layer1_dead ha hdead
  rw [hteq]
  change growEnv m.adjacency m.layer1.prevEnv t.2.1 ∈ m.layer1.seen
  -- the radius-2 bond set is the radius-1 one
  rw [m.growEnv_layer1_of_env1_eq hxy henv ha hy]
  exact m.env1_mem_layer1_seen ha

/-- Radius 2 emits from the live atoms exactly what it would emit if radius 1 had
killed no duplicates. -/
lemma mem_layer2_iff {e : ℕ} (he : e ∉ m.layer1.seen) (x : UInt32) :
    (∃ t ∈ sortBy envLE (roundTriples m.adjacency m.bondKinds 1 m.layer1), t.2.2 = e ∧ t.1 = x)
      ↔ ∃ t ∈ roundTriples m.adjacency m.bondKinds 1 m.layer1Full, t.2.2 = e ∧ t.1 = x := by
  have hd : ∀ a : Fin n, m.layer1Full.dead[a] = true → m.layer1.dead[a] = true :=
    fun a ha ↦ foldl_dedupStep_dead_mono _ _ _ _ _ ha
  rw [roundTriples_eq_filter m.layer1 m.layer1Full.dead hd]
  simp only [mem_sortBy, List.mem_filter, Bool.not_eq_true']
  constructor
  · rintro ⟨t, ⟨ht, -⟩, hte, htx⟩
    exact ⟨t, ht, hte, htx⟩
  · rintro ⟨t, ht, hte, htx⟩
    refine ⟨t, ⟨ht, Bool.eq_false_iff.mpr fun hdt ↦ ?_⟩, hte, htx⟩
    exact he (hte ▸ m.grown_mem_seen_of_killed t ht hdt)

/-! ### The radius-≤ 2 theorem -/

/-- The radius-0 identifiers move with the relabeling. -/
lemma morganInit_cur_relabel : (m.relabel σ).morganInit.cur = relabelVec σ m.morganInit.cur :=
  eq_relabelVec_of_apply σ fun a ↦ by
    simpa [morganInit] using m.morganAtomInvariants_relabel σ a

/-- The initial bond sets, all empty, move with the relabeling. -/
lemma morganInit_prevEnv_relabel :
    (m.relabel σ).morganInit.prevEnv = relabelVec σ m.morganInit.prevEnv := by
  simp [morganInit, relabelVec_replicate]

/-- The initial dead atoms, none, move with the relabeling. -/
lemma morganInit_dead_relabel : (m.relabel σ).morganInit.dead = relabelVec σ m.morganInit.dead := by
  simp [morganInit, relabelVec_replicate]

/-- The atoms without neighbors move with the relabeling. -/
lemma layer1Full_dead_relabel : (m.relabel σ).layer1Full.dead = relabelVec σ m.layer1Full.dead :=
  eq_relabelVec_of_apply σ fun a ↦ by
    simpa [morganInit, Vector.getElem_ofFn] using m.isEmpty_adjacency_relabel σ a

/-- The radius-1 triples of a relabeled molecule are the relabeled triples, up to order. -/
lemma roundTriples_init_relabel :
    (roundTriples (m.relabel σ).adjacency (m.relabel σ).bondKinds 0 (m.relabel σ).morganInit).Perm
      ((roundTriples m.adjacency m.bondKinds 0 m.morganInit).map (relabelTriple σ)) :=
  roundTriples_relabel m σ 0 (m.morganInit_cur_relabel σ) (m.morganInit_prevEnv_relabel σ)
    (m.morganInit_dead_relabel σ)

/-- The radius-1 identifiers move with the relabeling. -/
lemma layer1_cur_relabel : (m.relabel σ).layer1.cur = relabelVec σ m.layer1.cur :=
  morganLayer_cur_relabel m σ 0 (m.morganInit_cur_relabel σ) (m.morganInit_dead_relabel σ)

/-- The radius-1 bond sets move with the relabeling. -/
lemma layer1_prevEnv_relabel : (m.relabel σ).layer1.prevEnv = relabelVec σ m.layer1.prevEnv :=
  morganLayer_prevEnv_relabel m σ 0 (m.morganInit_prevEnv_relabel σ) (m.morganInit_dead_relabel σ)

/-- Radius 1 sees the same bond sets in a relabeled molecule: bond indices do not move. -/
lemma mem_layer1_seen_relabel (e : ℕ) : e ∈ (m.relabel σ).layer1.seen ↔ e ∈ m.layer1.seen := by
  simp only [layer1, mem_morganLayer_seen, (m.roundTriples_init_relabel σ).mem_iff]
  simp [relabelTriple, morganInit]

/-- Relabeling the atoms of a list of triples does not change which identifiers occur on
which bond sets. -/
lemma exists_mem_map_relabelTriple (l : List (UInt32 × Fin n × ℕ)) (e : ℕ) (x : UInt32) :
    (∃ t ∈ l.map (relabelTriple σ), t.2.2 = e ∧ t.1 = x) ↔ ∃ t ∈ l, t.2.2 = e ∧ t.1 = x := by
  simp [relabelTriple]

/-- The radius-0 identifiers of a relabeled molecule are the same multiset. -/
lemma ids_init_relabel :
    ((((m.relabel σ).morganInit.result.map (·.1)) : List UInt32) : Multiset UInt32)
      = ((m.morganInit.result.map (·.1) : List UInt32) : Multiset UInt32) := by
  simp only [morganInit, List.map_map, Function.comp_def, Multiset.coe_eq_coe]
  refine (σ.map_finRange_perm.map _).symm.trans (.of_eq ?_)
  rw [List.map_map]
  exact List.map_congr_left fun i _ ↦ m.morganAtomInvariants_relabel σ i

/-- Up to radius 1, relabeling the atoms permutes the emitted identifiers. -/
lemma ids_layer1_relabel :
    ((((m.relabel σ).layer1.result.map (·.1)) : List UInt32) : Multiset UInt32)
      = ((m.layer1.result.map (·.1) : List UInt32) : Multiset UInt32) := by
  rw [layer1, layer1, morganLayer_result, morganLayer_result, List.map_append, List.map_append,
    ← Multiset.coe_add, ← Multiset.coe_add, ids_init_relabel]
  congr 1
  refine emitted_ids_eq 0 (idSorted_sortBy_envLE _) (idSorted_sortBy_envLE _)
    (by simp [morganInit]) fun e x _ ↦ ?_
  simp only [mem_sortBy, (m.roundTriples_init_relabel σ).mem_iff]
  exact exists_mem_map_relabelTriple σ _ e x

/-- Up to radius 2, relabeling the atoms permutes the emitted identifiers. -/
lemma ids_layer2_relabel :
    (((morganLayer (m.relabel σ).adjacency (m.relabel σ).bondKinds 1
        (m.relabel σ).layer1).result.map (·.1) : List UInt32) : Multiset UInt32)
      = ((morganLayer m.adjacency m.bondKinds 1 m.layer1).result.map (·.1) : List UInt32) := by
  rw [morganLayer_result (m.relabel σ).layer1, morganLayer_result m.layer1, List.map_append,
    List.map_append, ← Multiset.coe_add, ← Multiset.coe_add, ids_layer1_relabel]
  congr 1
  refine emitted_ids_eq 1 (idSorted_sortBy_envLE _) (idSorted_sortBy_envLE _)
    (m.mem_layer1_seen_relabel σ) fun e x he ↦ ?_
  rw [(m.relabel σ).mem_layer2_iff he,
    m.mem_layer2_iff ((m.mem_layer1_seen_relabel σ e).not.mp he)]
  simp only [(roundTriples_relabel m σ 1 (s := m.layer1Full) (s' := (m.relabel σ).layer1Full)
    (m.layer1_cur_relabel σ) (m.layer1_prevEnv_relabel σ) (m.layer1Full_dead_relabel σ)).mem_iff]
  exact exists_mem_map_relabelTriple σ _ e x

/-- Up to radius 2, relabeling the atoms permutes the emitted identifiers. -/
theorem morganEnvironments_ids_relabel {radius : ℕ} (hr : radius ≤ 2) :
    ((((m.relabel σ).morganEnvironments radius).map (·.1) : List UInt32) : Multiset UInt32)
      = ((m.morganEnvironments radius).map (·.1) : List UInt32) := by
  unfold morganEnvironments
  rcases radius with _ | _ | _ | r
  · exact m.ids_init_relabel σ
  · exact m.ids_layer1_relabel σ
  · exact m.ids_layer2_relabel σ
  · lia

/-- Up to radius 2, the unfolded Morgan fingerprint does not depend on the atom order. -/
theorem morganIds_relabel {radius : ℕ} (hr : radius ≤ 2) :
    (m.relabel σ).morganIds radius = m.morganIds radius := by
  have hperm := Multiset.coe_eq_coe.mp (m.morganEnvironments_ids_relabel σ hr)
  have hsort : ∀ l : List UInt32, (sortBy (fun a b ↦ decide (a ≤ b)) l).Pairwise
      fun a b ↦ decide (a ≤ b) = true :=
    pairwise_sortBy (fun a b ↦ by rcases UInt32.le_total a b with h | h <;> simp [h])
      fun a b c hab hbc ↦
        decide_eq_true <| UInt32.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)
  have heq : sortBy (fun a b ↦ decide (a ≤ b)) (((m.relabel σ).morganEnvironments radius).map (·.1))
      = sortBy (fun a b ↦ decide (a ≤ b)) ((m.morganEnvironments radius).map (·.1)) :=
    List.Perm.eq_of_pairwise (le := fun a b ↦ decide (a ≤ b) = true)
      (fun a b _ _ hab hba ↦ UInt32.le_antisymm (by simpa using hab) (by simpa using hba))
      (hsort _) (hsort _)
      (((perm_sortBy _).trans hperm).trans (perm_sortBy _).symm)
  simp only [morganIds, heq]

/-- **Up to radius 2, the Morgan fingerprint does not depend on the atom order.**
At radius 3 it can (see the module docstring). -/
theorem morganBits_relabel {radius : ℕ} (hr : radius ≤ 2) (fpSize : ℕ) :
    (m.relabel σ).morganBits radius fpSize = m.morganBits radius fpSize := by
  simp only [morganBits, m.morganIds_relabel σ hr]

end LeanSMILES.Molecule

namespace LeanSMILES

/-- The bundled form: up to radius 2, a molecule and any relabeling of it have
the same Morgan fingerprint. -/
theorem Mol.morganBits_relabel (M : Mol) (σ : Equiv.Perm (Fin M.n)) {radius : ℕ} (hr : radius ≤ 2)
    (fpSize : ℕ) :
    (⟨M.n, M.mol.relabel σ⟩ : Mol).morganBits radius fpSize = M.morganBits radius fpSize :=
  M.mol.morganBits_relabel σ hr fpSize

end LeanSMILES
