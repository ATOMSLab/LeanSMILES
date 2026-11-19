/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.WorkRelabel
public import LeanSMILES.Aromaticity.HsRestoreK

/-!
# LeanSMILES.Aromaticity.RelabelPerceive

Perception commutes with renumbering the atoms

Donor types and candidacies are read at an atom and across its first exocyclic multiple bond, so
they follow the renaming (`Work.ringDonor_relabelW`); the first pass of perception over the renamed
rings is the renamed first pass, and Hückel's rule reads only the donor types of a group's atoms,
so the bonds perception marks are the same bonds (`Work.aromaticBondList_relabelW`), and marking
them commutes with the renaming (`Work.setAromaticity_relabelW`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

variable {w : Work} {σ ψ : ℕ → ℕ}

lemma cachedValence_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).cachedValence (σ i) = w.cachedValence i := by
  rw [cachedValence_eq_loc, cachedValence_eq_loc, kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

lemma countAtomElec_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).countAtomElec (σ i) = w.countAtomElec i := by
  rw [countAtomElec_eq_loc, countAtomElec_eq_loc, kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

lemma exocyclicMultiple?_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {i : ℕ} (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).exocyclicMultiple? B (σ i) = (w.exocyclicMultiple? B i).map σ := by
  unfold exocyclicMultiple?
  rw [neighbors_relabelW hwf hb hi, List.find?_map, Option.map_map, Option.map_map]
  congr 1
  · congr 1
    funext e
    simp only [Function.comp, kind_relabelW]

lemma hasMultipleBond_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).hasMultipleBond (σ i) = w.hasMultipleBond i := by
  simp only [hasMultipleBond, bondsOf_relabelW hwf hb hi, kind_relabelW]

lemma donorType_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ) {i : ℕ}
    (hi : i < w.atoms.size) : (w.relabelW σ ψ).donorType B (σ i) = w.donorType B i := by
  have hex := exocyclicMultiple?_relabelW hwf hb B hi
  have hz : ∀ j, w.exocyclicMultiple? B i = some j →
      ((w.relabelW σ ψ).atoms[σ j]! : WAtom) = w.atoms[j]! := fun j hj ↦ by
    have : j < w.atoms.size := by
      unfold exocyclicMultiple? at hj
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hj
      exact (Adj.lt hwf (adj_of_mem_neighbors (k := e.1)
        (List.mem_of_find?_eq_some he))).2
    exact atom_relabelW hb this
  unfold donorType
  simp only [Id.run, countAtomElec_relabelW hwf hb hi, hex, atom_relabelW hb hi,
    bondsOf_relabelW hwf hb hi, kind_relabelW, cachedValence_relabelW hwf hb hi,
    degree_relabelW hwf hb hi]
  cases h : w.exocyclicMultiple? B i with
  | none => rfl
  | some j => simp [hz j h]

lemma ringDonor_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ) (len : ℕ)
    {i : ℕ} (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).ringDonor B len (σ i) = w.ringDonor B len i := by
  simp only [ringDonor, donorType_relabelW hwf hb B hi, atom_relabelW hb hi,
    degree_relabelW hwf hb hi, hasMultipleBond_relabelW hwf hb hi]

lemma isAromaticCandidate_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) (d : Donor) :
    (w.relabelW σ ψ).isAromaticCandidate (σ i) d = w.isAromaticCandidate i d := by
  by_cases hd : d = .none
  · subst hd
    have hnn : (Donor.none == Donor.none) = true := rfl
    simp [isAromaticCandidate, Id.run, hnn]
  · rw [isAromaticCandidate_eq_loc _ _ hd, isAromaticCandidate_eq_loc _ _ hd,
      kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

/-- The bonds of a ring of atoms in range are the same bonds once renamed. -/
lemma ringBonds_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {r : List ℕ}
    (hr : ∀ a ∈ r, a < w.atoms.size) : (w.relabelW σ ψ).ringBonds (r.map σ) = w.ringBonds r := by
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.length_map]
  apply List.filterMap_congr
  intro t ht
  rw [List.mem_range] at ht
  have h2 : (t + 1) % r.length < r.length := Nat.mod_lt _ (by omega)
  rw [getElem!_pos _ t (by simpa using ht), getElem!_pos _ _ (by simpa using h2),
    List.getElem_map, List.getElem_map, bondBetween?_relabelW hwf hb (hr _ (List.getElem_mem _))
      (hr _ (List.getElem_mem _)), ← getElem!_pos r t ht, ← getElem!_pos r _ h2]

/-! ### The first pass -/

lemma contains_map_σ (hb : IdxBij w.numAtoms σ ψ) {r : List ℕ} (hr : ∀ a ∈ r, a < w.atoms.size)
    {i : ℕ} (hi : i < w.atoms.size) : (r.map σ).contains (σ i) = r.contains i := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
  exact ⟨fun ⟨a, ha, e⟩ ↦ hb.inj (hr a ha) hi e ▸ ha, fun h ↦ ⟨i, h, rfl⟩⟩

lemma find?_map_σ (hb : IdxBij w.numAtoms σ ψ) {L : List (List ℕ)}
    (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ} (hi : i < w.atoms.size) :
    (L.map (List.map σ)).find? (·.contains (σ i)) = (L.find? (·.contains i)).map (List.map σ) := by
  rw [List.find?_map]
  congr 1
  exact find?_congr_mem fun r hr ↦ by
    simp only [Function.comp]
    exact contains_map_σ hb (hL r hr) hi

lemma firstDonor_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {L : List (List ℕ)} (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ}
    (hi : i < w.atoms.size) :
    firstDonor (w.relabelW σ ψ) B (L.map (List.map σ)) (σ i) = firstDonor w B L i := by
  unfold firstDonor
  rw [find?_map_σ hb hL hi]
  cases L.find? (·.contains i) with
  | none => rfl
  | some r => simp only [Option.map_some, List.length_map, ringDonor_relabelW hwf hb B _ hi]

lemma firstCand_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) (B : List ℕ)
    {L : List (List ℕ)} (hL : ∀ r ∈ L, ∀ a ∈ r, a < w.atoms.size) {i : ℕ}
    (hi : i < w.atoms.size) :
    firstCand (w.relabelW σ ψ) B (L.map (List.map σ)) (σ i) = firstCand w B L i := by
  unfold firstCand
  rw [find?_map_σ hb hL hi]
  cases L.find? (·.contains i) with
  | none => rfl
  | some r => simp only [Option.map_some, List.length_map, ringDonor_relabelW hwf hb B _ hi,
      isAromaticCandidate_relabelW hwf hb hi]

/-- **The first pass of perception follows the renaming**: over the renamed rings, the renamed
atoms get the same donor types, and the candidate rings are the renamed ones. -/
theorem donorData_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {R : Array (List ℕ)}
    (hR : ∀ r ∈ R.toList, ∀ a ∈ r, a < w.atoms.size) :
    (∀ i < w.atoms.size, ((w.relabelW σ ψ).donorData (R.map (List.map σ))).donor[σ i]! =
      (w.donorData R).donor[i]!) ∧
    ((w.relabelW σ ψ).donorData (R.map (List.map σ))).donor.size = w.atoms.size ∧
    ((w.relabelW σ ψ).donorData (R.map (List.map σ))).candRings.toList =
      (w.donorData R).candRings.toList.map (List.map σ) := by
  have I := donorData_inv w R
  have I' := donorData_inv (w.relabelW σ ψ) (R.map (List.map σ))
  have hB : ((R.map (List.map σ)).toList.flatMap (w.relabelW σ ψ).ringBonds).eraseDups =
      (R.toList.flatMap w.ringBonds).eraseDups := by
    rw [Array.toList_map, List.flatMap_map]
    congr 1
    exact flatMap_congr_mem _ fun r hr ↦ ringBonds_relabelW hwf hb (hR r hr)
  rw [hB] at I'
  rw [Array.toList_map] at I'
  refine ⟨fun i hi ↦ ?_, by rw [I'.donor_size]; simp [numAtoms], ?_⟩
  · rw [I'.donor _ (by simpa [numAtoms] using hb.lt i hi), I.donor _ hi,
      firstDonor_relabelW hwf hb _ hR hi]
  · rw [I'.candRings, I.candRings, List.filter_map]
    congr 1
    apply List.filter_congr
    intro r hr
    simp only [Function.comp_apply, List.all_map, numAtoms_relabelW]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun a ha ↦ ?_
    have hra := hR r hr a ha
    simp only [Function.comp_apply]
    rw [firstCand_relabelW hwf hb _ hR hra]
    have h1 : σ a < w.atoms.size := hb.lt a hra
    simp [numAtoms, h1, hra]

/-! ### The second pass -/

lemma foldl_add_sum {α : Type} (f : α → ℕ) : ∀ (l : List α) (c : ℕ),
    l.foldl (fun s a ↦ s + f a) c = c + (l.map f).sum
  | [], c => by simp
  | a :: l, c => by rw [List.foldl_cons, foldl_add_sum f l, List.map_cons, List.sum_cons]; omega

/-- **Hückel's rule reads only the donor types of the atoms**, in any order. -/
lemma huckel_perm {A A' : List ℕ} {d d' : Array Donor}
    (h : (A'.map (d'[·]!)).Perm (A.map (d[·]!))) : huckel A' d' = huckel A d := by
  have h1 : (A'.filter (d'[·]! == .any)).length = (A.filter (d[·]! == .any)).length := by
    have e : ∀ (B : List ℕ) (e : Array Donor), (B.filter (e[·]! == .any)).length =
        ((B.map (e[·]!)).filter (· == .any)).length := fun B e ↦ by
      rw [List.filter_map, List.length_map]; rfl
    rw [e, e]
    exact (h.filter _).length_eq
  have h2 : ∀ g : Donor → ℕ, A'.foldl (fun s a ↦ s + g (d'[a]!)) 0 =
      A.foldl (fun s a ↦ s + g (d[a]!)) 0 := fun g ↦ by
    rw [foldl_add_sum, foldl_add_sum]
    have := (h.map g).sum_eq
    simp only [List.map_map] at this
    simp only [Function.comp_def] at this ⊢
    omega
  unfold huckel
  simp only [Id.run]
  rw [h1, h2 (·.range.1), h2 (·.range.2)]

lemma foldl_modify_count : ∀ (l : List ℕ) (acc : Array ℕ) (x : ℕ), x < acc.size →
    (l.foldl (fun acc a ↦ acc.modify a (· + 1)) acc)[x]! = acc[x]! + l.count x ∧
      (l.foldl (fun acc a ↦ acc.modify a (· + 1)) acc).size = acc.size
  | [], acc, x, _ => by simp
  | a :: l, acc, x, hx => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_modify_count l (acc.modify a (· + 1)) x (by simpa using hx)
    refine ⟨?_, by rw [h2]; simp⟩
    rw [h1, List.count_cons]
    rw [getElem!_pos _ x (by simpa using hx), getElem!_pos acc x hx, Array.getElem_modify]
    by_cases hax : a = x
    · subst hax; simp; omega
    · simp [hax]

/-- The atom counts of a group of rings: how many of its rings hold each atom. -/
lemma groupCounts {N : ℕ} (C : Array (List ℕ)) : ∀ (cur : List ℕ) (acc : Array ℕ), acc.size = N →
    ∀ x < N, (cur.foldl (fun acc r ↦ C[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc) acc)[x]! =
      acc[x]! + (cur.flatMap (C[·]!)).count x ∧
    (cur.foldl (fun acc r ↦ C[r]!.foldl (fun acc a ↦ acc.modify a (· + 1)) acc) acc).size = N
  | [], acc, hs, x, _ => by simp [hs]
  | r :: cur, acc, hs, x, hx => by
    rw [List.foldl_cons]
    obtain ⟨g1, g2⟩ := foldl_modify_count (C[r]!) acc x (hs ▸ hx)
    obtain ⟨i1, i2⟩ := groupCounts C cur _ (g2.trans hs) x hx
    refine ⟨?_, i2⟩
    rw [i1, g1, List.flatMap_cons, List.count_append]
    omega

lemma count_map_σ (hb : IdxBij w.numAtoms σ ψ) : ∀ {l : List ℕ}, (∀ a ∈ l, a < w.atoms.size) →
    ∀ {x : ℕ}, x < w.atoms.size → (l.map σ).count (σ x) = l.count x
  | [], _, _, _ => rfl
  | a :: l, hl, x, hx => by
    rw [List.map_cons, List.count_cons, List.count_cons,
      count_map_σ hb (fun b hb' ↦ hl b (List.mem_cons_of_mem _ hb')) hx]
    have ha := hl a List.mem_cons_self
    have : (σ a == σ x) = (a == x) := beq_σ hb ha hx
    rw [this]

lemma getElem!_map_list (C : Array (List ℕ)) (f : List ℕ → List ℕ) (hf : f [] = []) (r : ℕ) :
    (C.map f)[r]! = f C[r]! := by
  by_cases hr : r < C.size
  · rw [getElem!_pos _ r (by simpa using hr), getElem!_pos C r hr, Array.getElem_map]
  · rw [getElem!_neg _ r (by simpa using hr), getElem!_neg C r hr]; exact hf.symm

/-- **A group of renamed candidate rings makes the same bonds aromatic**, the donor types
renamed with them. -/
lemma groupBonds_relabel (hb : IdxBij w.numAtoms σ ψ) {rb C : Array (List ℕ)}
    {d d' : Array Donor} (hC : ∀ r ∈ C.toList, ∀ a ∈ r, a < w.atoms.size)
    (hd : ∀ a < w.atoms.size, d'[σ a]! = d[a]!) (nbrs : Array (List ℕ)) (cur : List ℕ) :
    groupBonds w.numAtoms rb (C.map (List.map σ)) d' nbrs cur =
      groupBonds w.numAtoms rb C d nbrs cur := by
  have hCr : ∀ r, ∀ a ∈ C[r]!, a < w.atoms.size := fun r a ha ↦ by
    by_cases hr : r < C.size
    · rw [getElem!_pos C r hr] at ha; exact hC _ (Array.getElem_mem_toList hr) a ha
    · rw [getElem!_neg C r hr] at ha; cases ha
  have hflat : cur.flatMap ((C.map (List.map σ))[·]!) = (cur.flatMap (C[·]!)).map σ := by
    rw [List.map_flatMap]
    exact flatMap_congr_mem cur fun r _ ↦ getElem!_map_list C _ rfl r
  have hlt : ∀ a ∈ cur.flatMap (C[·]!), a < w.atoms.size := fun a ha ↦ by
    obtain ⟨r, -, ha⟩ := List.mem_flatMap.1 ha
    exact hCr r a ha
  unfold groupBonds
  dsimp only
  set cnt := List.foldl (fun acc r ↦ List.foldl (fun acc a ↦ acc.modify a (· + 1)) acc C[r]!)
    (Array.replicate w.numAtoms 0) cur with hcnt
  set cnt' := List.foldl (fun acc r ↦
    List.foldl (fun acc a ↦ acc.modify a (· + 1)) acc (C.map (List.map σ))[r]!)
    (Array.replicate w.numAtoms 0) cur with hcnt'
  have e : ∀ x < w.atoms.size, cnt'[σ x]! = cnt[x]! := fun x hx ↦ by
    obtain ⟨c1, -⟩ := groupCounts (N := w.numAtoms) (C.map (List.map σ)) cur
      (Array.replicate w.numAtoms 0) (by simp) (σ x) (hb.lt x hx)
    obtain ⟨c2, -⟩ := groupCounts (N := w.numAtoms) C cur (Array.replicate w.numAtoms 0)
      (by simp) x hx
    have r0 : ∀ y < w.atoms.size, (Array.replicate w.numAtoms 0)[y]! = 0 := fun y hy ↦ by
      rw [getElem!_pos _ y (by simpa [numAtoms] using hy)]; simp
    calc cnt'[σ x]! = (Array.replicate w.numAtoms 0)[σ x]! +
          (cur.flatMap ((C.map (List.map σ))[·]!)).count (σ x) := c1
      _ = (Array.replicate w.numAtoms 0)[x]! + (cur.flatMap (C[·]!)).count x := by
          rw [hflat, count_map_σ hb hlt hx, r0 _ (hb.lt x hx), r0 x hx]
      _ = cnt[x]! := c2.symm
  have hh : huckel ((List.range w.numAtoms).filter fun a ↦ cnt'[a]! == 1 || cnt'[a]! == 2) d' =
      huckel ((List.range w.numAtoms).filter fun a ↦ cnt[a]! == 1 || cnt[a]! == 2) d := by
    apply huckel_perm
    set A := (List.range w.numAtoms).filter fun a ↦ cnt[a]! == 1 || cnt[a]! == 2
    have hA : ∀ x ∈ A, x < w.atoms.size := fun x hx ↦
      List.mem_range.1 (List.mem_filter.1 hx).1
    have hp : ((List.range w.numAtoms).filter fun a ↦ cnt'[a]! == 1 || cnt'[a]! == 2).Perm
        (A.map σ) := by
      refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
        ((List.nodup_range.filter _).map_on fun a ha c hc e ↦ hb.inj (hA a ha) (hA c hc) e)).2
        fun y ↦ ?_
      simp only [List.mem_filter, List.mem_range, List.mem_map, A]
      constructor
      · rintro ⟨hy, h⟩
        refine ⟨ψ y, ⟨hb.lt' y hy, ?_⟩, hb.right y hy⟩
        rw [← e _ (hb.lt' y hy), hb.right y hy]
        exact h
      · rintro ⟨x, ⟨hx, h⟩, rfl⟩
        refine ⟨hb.lt x hx, ?_⟩
        rw [e x hx]
        exact h
    refine (hp.map _).trans ?_
    rw [List.map_map]
    exact (List.map_congr_left fun x hx ↦ hd x (hA x hx)) ▸ List.Perm.refl _
  rw [hh]

end Work

end LeanSMILES.Aromaticity
