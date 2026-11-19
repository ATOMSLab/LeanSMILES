/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RelabelOutput

/-!
# LeanSMILES.Aromaticity.Relist

Relisting the bonds of a working copy

`Work.Relisted w w' π ρ`: `w'` has `w`'s atoms, and bond `π k` of `w'` is bond `k` of `w`, perhaps
turned round (`ρ` the inverse). The bonds at an atom are the same bonds renumbered
(`Work.Relisted.bondsOf_perm`), so their kinds are the same up to order
(`Work.Relisted.kindsAt_perm`), and everything read at an atom from its record and the kinds of its
bonds is unchanged. With no two bonds between the same atoms, the bond between two atoms is
renumbered by `π` (`Work.Relisted.bondBetween?`), so the relisting is a `Work.WorkIso`.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- `w'` is `w` with bond `k` listed as `π k`, perhaps turned round. -/
structure Relisted (w w' : Work) (π ρ : ℕ → ℕ) : Prop where
  atoms : w'.atoms = w.atoms
  size : w'.bonds.size = w.bonds.size
  bij : IdxBij w.bonds.size π ρ
  kind : ∀ k < w.bonds.size, (w'.bonds[π k]! : WBond).kind = (w.bonds[k]! : WBond).kind
  ends : ∀ k < w.bonds.size,
    ((w'.bonds[π k]! : WBond).src = (w.bonds[k]! : WBond).src ∧
      (w'.bonds[π k]! : WBond).dst = (w.bonds[k]! : WBond).dst) ∨
    ((w'.bonds[π k]! : WBond).src = (w.bonds[k]! : WBond).dst ∧
      (w'.bonds[π k]! : WBond).dst = (w.bonds[k]! : WBond).src)

namespace Relisted

variable {w w' : Work} {π ρ : ℕ → ℕ}

lemma touches (h : Relisted w w' π ρ) {k : ℕ} (hk : k < w.bonds.size) (i : ℕ) :
    (w'.bonds[π k]! : WBond).touches i = (w.bonds[k]! : WBond).touches i := by
  simp only [WBond.touches]
  rcases h.ends k hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1, e2]
  · rw [e1, e2, Bool.or_comm]

lemma mem_bondsOf (h : Relisted w w' π ρ) {k : ℕ} (hk : k < w.bonds.size) (i : ℕ) :
    π k ∈ w'.bondsOf i ↔ k ∈ w.bondsOf i := by
  simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, h.size, h.touches hk,
    h.bij.lt k hk, hk, true_and]

/-- **The bonds at an atom are the same bonds, renumbered.** -/
lemma bondsOf_perm (h : Relisted w w' π ρ) (i : ℕ) :
    (w'.bondsOf i).Perm ((w.bondsOf i).map π) := by
  have hlt : ∀ k ∈ w.bondsOf i, k < w.bonds.size := fun k hk ↦ by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  refine (List.perm_ext_iff_of_nodup (List.nodup_range.filter _)
    ((List.nodup_range.filter _).map_on fun a ha b hb e ↦
      h.bij.inj (hlt a ha) (hlt b hb) e)).2 fun k' ↦ ?_
  rw [List.mem_map]
  constructor
  · intro hk'
    have hk's : k' < w.bonds.size := by
      simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, h.size] at hk'; exact hk'.1
    refine ⟨ρ k', ?_, h.bij.right k' hk's⟩
    rw [← h.mem_bondsOf (h.bij.lt' k' hk's), h.bij.right k' hk's]
    exact hk'
  · rintro ⟨k, hk, rfl⟩
    exact (h.mem_bondsOf (hlt k hk) i).2 hk

/-- **The kinds at an atom are the same, in some order.** -/
lemma kindsAt_perm (h : Relisted w w' π ρ) (i : ℕ) : (w'.kindsAt i).Perm (w.kindsAt i) := by
  unfold kindsAt
  refine ((h.bondsOf_perm i).map _).trans ?_
  rw [List.map_map]
  refine List.Perm.of_eq (List.map_congr_left fun k hk ↦ ?_)
  have : k < w.bonds.size := by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  exact h.kind k this

lemma atom (h : Relisted w w' π ρ) (i : ℕ) : (w'.atoms[i]! : WAtom) = w.atoms[i]! := by
  rw [h.atoms]

lemma bhs_perm {ks ks' : List BondKind} (h : ks'.Perm ks) : Loc.bhs ks' = Loc.bhs ks :=
  (h.map _).sum_eq

lemma bondHalfSum (h : Relisted w w' π ρ) (i : ℕ) : w'.bondHalfSum i = w.bondHalfSum i := by
  rw [bondHalfSum_eq_loc, bondHalfSum_eq_loc, bhs_perm (h.kindsAt_perm i)]

lemma degree (h : Relisted w w' π ρ) (i : ℕ) : w'.degree i = w.degree i := by
  rw [degree_eq_loc, degree_eq_loc, (h.kindsAt_perm i).length_eq]

lemma isAromaticAtom (h : Relisted w w' π ρ) (i : ℕ) :
    w'.isAromaticAtom i = w.isAromaticAtom i := by
  rw [isAromaticAtom_eq_loc, isAromaticAtom_eq_loc, h.atom, (h.kindsAt_perm i).any_eq']

lemma explicitValence (h : Relisted w w' π ρ) (i : ℕ) :
    w'.explicitValence i = w.explicitValence i := by
  rw [explicitValence_eq_loc, explicitValence_eq_loc, h.atom, h.bondHalfSum, h.isAromaticAtom]

lemma implicitHs (h : Relisted w w' π ρ) (i : ℕ) : w'.implicitHs i = w.implicitHs i := by
  rw [implicitHs_eq_loc, implicitHs_eq_loc, h.atom, h.bondHalfSum, h.isAromaticAtom]

lemma totalHs (h : Relisted w w' π ρ) (i : ℕ) : w'.totalHs i = w.totalHs i := by
  simp only [Work.totalHs, h.implicitHs, h.atom]

lemma kekuleValence (h : Relisted w w' π ρ) (i : ℕ) :
    w'.kekuleValence i = w.kekuleValence i := by
  simp only [Work.kekuleValence, h.bondHalfSum, h.atom]

lemma cachedValence (h : Relisted w w' π ρ) (i : ℕ) :
    w'.cachedValence i = w.cachedValence i := by
  simp only [Work.cachedValence, h.kekuleValence, h.atom]

lemma radicalCount (h : Relisted w w' π ρ) (i : ℕ) :
    w'.radicalCount i = w.radicalCount i := by
  simp only [Work.radicalCount, h.kekuleValence, h.atom]

lemma countAtomElec (h : Relisted w w' π ρ) (i : ℕ) :
    w'.countAtomElec i = w.countAtomElec i := by
  unfold Work.countAtomElec
  simp only [h.degree, Work.cachedTotalHs, h.cachedValence, h.atom]
  rfl

lemma isAromaticCandidate (h : Relisted w w' π ρ) (i : ℕ) (d : Donor) :
    w'.isAromaticCandidate i d = w.isAromaticCandidate i d := by
  unfold Work.isAromaticCandidate
  have hf : ((w'.bondsOf i).filter fun k ↦ isMultiple (w'.bonds[k]! : WBond).kind).length =
      ((w.bondsOf i).filter fun k ↦ isMultiple (w.bonds[k]! : WBond).kind).length := by
    have e : ∀ (x : Work) (j : ℕ), ((x.bondsOf j).filter
        fun k ↦ isMultiple (x.bonds[k]! : WBond).kind).length =
        ((x.kindsAt j).filter isMultiple).length := fun x j ↦ by
      simp only [kindsAt, List.filter_map, List.length_map]; rfl
    rw [e, e]
    exact ((h.kindsAt_perm i).filter _).length_eq
  simp only [h.degree, h.cachedValence, h.atom, hf]

lemma wf (h : Relisted w w' π ρ) (hwf : w.WF) : w'.WF := by
  intro k' hk'
  have hk's : k' < w.bonds.size := by simpa [numBonds, h.size] using hk'
  have := hwf _ (h.bij.lt' k' hk's)
  have e := h.ends _ (h.bij.lt' k' hk's)
  rw [h.bij.right k' hk's] at e
  simp only [numAtoms, h.atoms] at this ⊢
  rcases e with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> omega

lemma other (h : Relisted w w' π ρ) (hwf : w.WF) {k i : ℕ} (hk : k ∈ w.bondsOf i) :
    (w'.bonds[π k]! : WBond).other i = (w.bonds[k]! : WBond).other i := by
  have hks : k < w.bonds.size := by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  have ht := touches_of_mem_bondsOf hk
  have hne := (hwf k hks).2.2
  simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
  simp only [WBond.other, beq_iff_eq]
  rcases h.ends k hks with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> split_ifs <;> omega

/-- **The neighbours of an atom are the same, the bonds renumbered.** -/
lemma neighbors_perm (h : Relisted w w' π ρ) (hwf : w.WF) (i : ℕ) :
    (w'.neighbors i).Perm ((w.neighbors i).map fun e ↦ (π e.1, e.2)) := by
  unfold neighbors
  refine ((h.bondsOf_perm i).map _).trans ?_
  rw [List.map_map, List.map_map]
  exact List.Perm.of_eq (List.map_congr_left fun k hk ↦ by
    simp only [Function.comp_apply, h.other hwf hk])

lemma bondBetween?_eq_some_iff {x : Work} (hwf : x.WF) (hnd : x.NbrsDistinct) {u v k : ℕ} :
    x.bondBetween? u v = some k ↔ k < x.bonds.size ∧
      (((x.bonds[k]! : WBond).src = u ∧ (x.bonds[k]! : WBond).dst = v) ∨
        ((x.bonds[k]! : WBond).src = v ∧ (x.bonds[k]! : WBond).dst = u)) := by
  constructor
  · intro hk
    exact ⟨bondBetween?_lt hk, bondBetween?_ends hk⟩
  · rintro ⟨hks, hj⟩
    cases h0 : x.bondBetween? u v with
    | none =>
      exfalso
      unfold bondBetween? at h0
      have := List.find?_eq_none.1 h0 k (List.mem_range.2 hks)
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
      exact this hj
    | some j =>
      have hjs := bondBetween?_lt h0
      have hje := bondBetween?_ends h0
      have hne := (hwf k hks).2.2
      -- both are bonds at `u` whose other end is `v`
      have hmem : ∀ q, q < x.bonds.size → (((x.bonds[q]! : WBond).src = u ∧
          (x.bonds[q]! : WBond).dst = v) ∨ ((x.bonds[q]! : WBond).src = v ∧
          (x.bonds[q]! : WBond).dst = u)) → q ∈ x.bondsOf u ∧ (x.bonds[q]! : WBond).other u = v :=
        fun q hq e ↦ by
          have hne' := (hwf q hq).2.2
          refine ⟨?_, ?_⟩
          · simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, WBond.touches,
              Bool.or_eq_true, beq_iff_eq]
            exact ⟨hq, by omega⟩
          · simp only [WBond.other, beq_iff_eq]; split_ifs <;> omega
      obtain ⟨a1, b1⟩ := hmem j hjs hje
      obtain ⟨a2, b2⟩ := hmem k hks hj
      rw [hnd u j k a1 a2 (b1.trans b2.symm)]

/-- **The bond between two atoms is renumbered**, with no two bonds between the same atoms. -/
lemma bondBetween? (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) (u v : ℕ) :
    w'.bondBetween? u v = (w.bondBetween? u v).map π := by
  have hwf' := h.wf hwf
  have hendsiff : ∀ k < w.bonds.size, ((((w'.bonds[π k]! : WBond).src = u ∧
      (w'.bonds[π k]! : WBond).dst = v) ∨ ((w'.bonds[π k]! : WBond).src = v ∧
      (w'.bonds[π k]! : WBond).dst = u)) ↔ (((w.bonds[k]! : WBond).src = u ∧
      (w.bonds[k]! : WBond).dst = v) ∨ ((w.bonds[k]! : WBond).src = v ∧
      (w.bonds[k]! : WBond).dst = u))) := fun k hk ↦ by
    rcases h.ends k hk with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] <;> tauto
  cases h0 : w.bondBetween? u v with
  | some k =>
    obtain ⟨hks, he⟩ := (bondBetween?_eq_some_iff hwf hnd).1 h0
    exact (bondBetween?_eq_some_iff hwf' hnd').2
      ⟨by rw [h.size]; exact h.bij.lt k hks, (hendsiff k hks).2 he⟩
  | none =>
    cases h1 : w'.bondBetween? u v with
    | none => rfl
    | some k' =>
      exfalso
      obtain ⟨hks', he'⟩ := (bondBetween?_eq_some_iff hwf' hnd').1 h1
      have hk's : k' < w.bonds.size := h.size ▸ hks'
      rw [← h.bij.right k' hk's] at he'
      have := (bondBetween?_eq_some_iff hwf hnd).2
        ⟨h.bij.lt' k' hk's, (hendsiff _ (h.bij.lt' k' hk's)).1 he'⟩
      rw [h0] at this
      cases this

/-- **A relisting is a renumbering**, the atoms kept. -/
lemma workIso (h : Relisted w w' π ρ) (hwf : w.WF) (hnd : w.NbrsDistinct)
    (hnd' : w'.NbrsDistinct) : WorkIso w w' id id π ρ :=
  ⟨⟨fun _ h ↦ h, fun _ h ↦ h, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩, h.bij,
    by simp [numAtoms, h.atoms], by simp [numBonds, h.size],
    fun u v _ _ ↦ h.bondBetween? hwf hnd hnd' u v⟩

/-- Changing only the atoms, alike on both sides, keeps the relisting. -/
lemma of_atoms (h : Relisted w w' π ρ) {v v' : Work} (hb : v.bonds = w.bonds)
    (hb' : v'.bonds = w'.bonds) (ha : v'.atoms = v.atoms) : Relisted v v' π ρ :=
  ⟨ha, by rw [hb, hb', h.size], hb ▸ h.bij, fun k hk ↦ by rw [hb, hb']; exact h.kind k (hb ▸ hk),
    fun k hk ↦ by rw [hb, hb']; exact h.ends k (hb ▸ hk)⟩

lemma freezeHs (h : Relisted w w' π ρ) : Relisted w.freezeHs w'.freezeHs π ρ := by
  refine h.of_atoms rfl rfl ?_
  simp only [Work.freezeHs, numAtoms, h.atoms, h.totalHs]

lemma cacheValences (h : Relisted w w' π ρ) : Relisted w.cacheValences w'.cacheValences π ρ := by
  refine h.of_atoms rfl rfl ?_
  simp only [Work.cacheValences, numAtoms, h.atoms, h.explicitValence, h.implicitHs,
    h.isAromaticAtom]

lemma radicalStep (h : Relisted w w' π ρ) (j : ℕ) :
    Relisted (Work.radicalStep w j) (Work.radicalStep w' j) π ρ := by
  unfold Work.radicalStep
  dsimp only
  rw [h.atom j, h.radicalCount j]
  split
  · exact h
  · exact h.of_atoms rfl rfl (by simp only [modifyAtom, h.atoms])

lemma assignRadicals (h : Relisted w w' π ρ) : Relisted w.assignRadicals w'.assignRadicals π ρ := by
  unfold Work.assignRadicals
  rw [show w'.numAtoms = w.numAtoms by simp [numAtoms, h.atoms]]
  generalize List.range w.numAtoms = l
  induction l generalizing w w' with
  | nil => exact h
  | cons j l ih => exact ih (h.radicalStep j)

lemma adjustHsStep (h : Relisted w w' π ρ) (j : ℕ) :
    Relisted (Work.adjustHsStep w j) (Work.adjustHsStep w' j) π ρ := by
  unfold Work.adjustHsStep
  dsimp only
  rw [h.atom j, h.isAromaticAtom j, h.implicitHs j]
  split
  · split
    · exact h.of_atoms rfl rfl (by simp only [modifyAtom, h.atoms])
    · exact h
  · exact h

lemma finalizeHs (h : Relisted w w' π ρ) : Relisted w.finalizeHs w'.finalizeHs π ρ := by
  unfold Work.finalizeHs
  dsimp only
  rw [show w'.numAtoms = w.numAtoms by simp [numAtoms, h.atoms]]
  have h1 : Relisted ((List.range w.numAtoms).foldl Work.adjustHsStep w)
      ((List.range w.numAtoms).foldl Work.adjustHsStep w') π ρ := by
    generalize List.range w.numAtoms = l
    induction l generalizing w w' with
    | nil => exact h
    | cons j l ih => exact ih (h.adjustHsStep j)
  generalize (List.range w.numAtoms).foldl Work.adjustHsStep w = u at h1
  generalize (List.range w.numAtoms).foldl Work.adjustHsStep w' = u' at h1
  refine h1.of_atoms rfl rfl ?_
  simp only [numAtoms, h1.atoms, h1.implicitHs]

end Relisted

end LeanSMILES.Aromaticity.Work
