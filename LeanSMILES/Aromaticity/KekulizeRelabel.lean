/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RelabelPipeline

/-!
# LeanSMILES.Aromaticity.KekulizeRelabel

Two kekulizations of one copy, up to renumbering

Kekulization picks its double bonds by a walk whose order depends on the numbering, but every
atom ends with the same sum of bond orders: each candidate atom gets exactly one double bond
(`Work.kekulize_prepare_correct`). So the kekulization of a relabeled copy is the relabeled
kekulization with some single and double bonds swapped (`Work.kekulize_relabel_swapped`).
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- After `clearAromatic`, an aromatic `[nH]`/`[pH]` is never merely unflagged. -/
def NotCleared (a0 : WAtom) (w : Work) (i : ℕ) : Prop :=
  IsBranch a0 → (w.atoms[i]! : WAtom) ≠ { a0 with aromatic := false }

lemma clearAromatic_notCleared {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} {w w' : Work}
    {j : ℕ} (hw : clearAromatic ra w j = .ok w') (i : ℕ) (hok : ClearOk a0 bs w i)
    (h : NotCleared a0 w i) : NotCleared a0 w' i := by
  intro hbr
  have he1 : ({ a0 with aromatic := false } : WAtom).explicitHs = 1 := hbr.2.2.2
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · cases hw; exact h hbr
  split at hw
  · cases hw
  split at hw
  · cases hw
    by_cases hji : j = i
    · subst hji
      rw [modifyAtom_atom_self]
      split
      · rename_i hpos
        rw [modifyAtom_atom_self, if_pos (by simpa [modifyAtom] using hpos)]
        intro e
        have := congrArg WAtom.explicitHs e
        rw [he1] at this
        simp at this
      · rename_i hneg
        rw [modifyAtom_atom_self, if_neg (by simpa [modifyAtom] using hneg)]
        exact h hbr
    · rw [modifyAtom_atom_of_ne _ hji, modifyAtom_atom_of_ne _ hji]
      exact h hbr
  · cases hw
    by_cases hji : j = i
    · subst hji
      rename_i hnar _ hbr'
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hnar
      rw [modifyAtom_atom_self]
      split
      · -- the atom was `a0`, aromatic, and its branch test failed: impossible
        exfalso
        obtain ⟨-, ha⟩ := hok
        have ha0 : (w.atoms[j]! : WAtom) = a0 := by
          rcases ha with h' | h' | ⟨-, h'⟩
          · exact h'
          · rw [h'] at hnar; cases hnar
          · rw [h'] at hnar; cases hnar
        apply hbr'
        simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.mem_cons,
          List.not_mem_nil, or_false, ha0]
        obtain ⟨-, hz, hc, he⟩ := hbr
        exact ⟨⟨hz, hc⟩, he⟩
      · exact h hbr
    · rw [modifyAtom_atom_of_ne _ hji]
      exact h hbr

lemma foldlM_clearAromatic_notCleared {ra : List ℕ} {a0 : WAtom} {bs : Array WBond} (i : ℕ) :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ra) w = .ok w' →
      ClearOk a0 bs w i → NotCleared a0 w i → NotCleared a0 w' i
  | [], w, w', hw, _, h => by cases hw; exact h
  | x :: l, w, w', hw, hok, h => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ra w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      exact foldlM_clearAromatic_notCleared i l v w' hw (clearAromatic_clearOk hx i hok)
        (clearAromatic_notCleared hx i hok h)

/-- **Kekulization rewrites an aromatic `[nH]`/`[pH]`** (`branchRec`). -/
theorem kekulize_atom_branch {m K : Work} {rings : Array (List ℕ)}
    (hK : m.kekulize rings = .ok K) {i : ℕ} (hbr : IsBranch m.atoms[i]!) :
    (K.atoms[i]! : WAtom) = branchRec m.atoms[i]! (K.bondHalfSum i)
      ((K.kindsAt i).any (· == .aromatic)) := by
  have hnc : NotCleared m.atoms[i]! K i := by
    unfold kekulize at hK
    dsimp only at hK
    split at hK
    · rename_i hnone
      exfalso
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hnone
      have := hnone.2
      have hi : i < m.atoms.size := by
        by_contra hi
        rw [getElem!_neg m.atoms i hi] at hbr
        exact absurd hbr.1 (by decide)
      rw [Array.any_eq_false] at this
      exact absurd hbr.1 (by
        have := this i hi
        rw [← getElem!_pos m.atoms i hi] at this
        simpa using this)
    · simp only [pure, Except.pure, bind, Except.bind] at hK
      split at hK
      · cases hK
      · rename_i out1 h1
        have q1 := foldlM_except_of (fun w ↦ w.atoms = m.atoms) _
          (fun _ _ _ hq hx ↦ kekulizeSystem_m (Q := fun w ↦ w.atoms = m.atoms)
            (fun _ _ _ h ↦ h) hq hx) _ _ _ rfl h1
        split at hK
        · cases hK
        · rename_i out2 h2
          split at hK
          · cases hK
          · cases hK
            have hb := foldlM_clearAromatic_bonds _ h2
            simp only at q1
            refine foldlM_clearAromatic_notCleared i _ _ _ h2 ⟨hb.symm, .inl (by rw [q1])⟩ ?_
            intro hbr' e
            rw [q1] at e
            have := congrArg WAtom.aromatic e
            rw [hbr'.1] at this
            cases this
  rcases kekulize_atom hK i with h | ⟨-, h⟩
  · exact absurd h (hnc hbr)
  · exact h

/-! ### Bond-order sums after kekulization -/

/-- An atom's bond-order sum with the bonds written aromatic made single. -/
def kekBase (m : Work) (x : ℕ) : ℕ :=
  ((m.bondsOf x).map fun k ↦ if m.kekWa k then 2 else halfOrder (m.bonds[k]! : WBond).kind).sum

lemma bondsOf_of_kindsRel {o w : Work} (h : KindsRel o w) : w.bondsOf = o.bondsOf := by
  have hs : w.bonds.size = o.bonds.size := by
    have := h.bonds
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := this w.bonds.size
      rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
      simp at this
    · have := this o.bonds.size
      rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
      simp at this
  funext x
  unfold bondsOf
  rw [show w.numBonds = o.numBonds from hs]
  apply List.filter_congr
  intro k hk
  have hk' : k < o.bonds.size := List.mem_range.1 hk
  have := h.bonds k
  rw [Array.getElem?_eq_getElem (hs ▸ hk'), Array.getElem?_eq_getElem hk'] at this
  simp only [Option.map_some, Option.some.injEq, WBond.mk.injEq] at this
  rw [getElem!_pos _ k (hs ▸ hk'), getElem!_pos _ k hk']
  simp only [WBond.touches, this.1, this.2.1]

lemma sum_ite_two (l : List ℕ) (D : ℕ → Bool) :
    (l.map fun k ↦ if D k = true then 2 else 0).sum = 2 * (l.filter D).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.filter_cons]
    split <;> simp [*]; omega

/-- **An atom's bond-order sum after kekulization**: the base, plus one double bond if it is a
candidate. -/
theorem bondHalfSum_of_matching {m K : Work} (hwf : WF m) (hKR : KindsRel m K) {D : ℕ → Bool}
    (hkind : ∀ k, (K.bonds[k]! : WBond).kind = if D k = true then .double else
        if m.kekWa k = true then .single else (m.bonds[k]! : WBond).kind)
    (hdok : ∀ k, D k = true → k < m.bonds.size ∧ m.kekWa k = true ∧
        ∀ x, (m.bonds[k]! : WBond).touches x = true → candOf m m.kekWa m.kekEv0 x = true)
    (hmatch : ∀ k₁ k₂ x, D k₁ = true → D k₂ = true → (m.bonds[k₁]! : WBond).touches x = true →
        (m.bonds[k₂]! : WBond).touches x = true → k₁ = k₂)
    (hcover : ∀ x < m.atoms.size, candOf m m.kekWa m.kekEv0 x = true →
        ∃ k, D k = true ∧ (m.bonds[k]! : WBond).touches x = true) (x : ℕ) :
    K.bondHalfSum x = kekBase m x +
      if x < m.atoms.size ∧ candOf m m.kekWa m.kekEv0 x = true then 2 else 0 := by
  unfold bondHalfSum kekBase
  rw [bondsOf_of_kindsRel hKR]
  have e : ∀ k ∈ m.bondsOf x, halfOrder (K.bonds[k]! : WBond).kind =
      (if m.kekWa k = true then 2 else halfOrder (m.bonds[k]! : WBond).kind) +
        if D k = true then 2 else 0 := fun k _ ↦ by
    rw [hkind k]
    by_cases hD : D k = true
    · rw [if_pos hD, if_pos (hdok k hD).2.1, if_pos hD]; rfl
    · rw [if_neg hD, if_neg hD]
      split <;> rfl
  rw [List.map_congr_left e, List.sum_map_add, sum_ite_two]
  congr 1
  have hmem : ∀ k, k ∈ m.bondsOf x ↔ k < m.bonds.size ∧ (m.bonds[k]! : WBond).touches x = true :=
    fun k ↦ by simp [bondsOf, numBonds]
  split
  · rename_i hc
    obtain ⟨k, hk, ht⟩ := hcover x hc.1 hc.2
    rw [length_filter_eq_one (show (m.bondsOf x).Nodup from List.nodup_range.filter _)
      (fun a ha b hb hpa hpb ↦ hmatch a b x hpa hpb ((hmem a).1 ha).2 ((hmem b).1 hb).2)
      ⟨k, (hmem k).2 ⟨(hdok k hk).1, ht⟩, hk⟩]
  · rename_i hc
    suffices ((m.bondsOf x).filter D).length = 0 by rw [this]
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro k hk hD
    obtain ⟨hks, ht⟩ := (hmem k).1 hk
    apply hc
    refine ⟨?_, (hdok k hD).2.2 x ht⟩
    have := hwf k hks
    simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
    rcases ht with rfl | rfl
    · exact this.1
    · exact this.2.1

/-! ### Up to renumbering -/

variable {σ ψ : ℕ → ℕ}

lemma kekWa_relabelW (P : Work) : (P.relabelW σ ψ).kekWa = P.kekWa := by
  rw [kekWa_eq, kekWa_eq]
  funext k
  rw [kind_relabelW]

lemma kekBase_relabelW {P : Work} (hwf : WF P) (hb : IdxBij P.numAtoms σ ψ) {i : ℕ}
    (hi : i < P.atoms.size) : kekBase (P.relabelW σ ψ) (σ i) = kekBase P i := by
  simp only [kekBase, bondsOf_relabelW hwf hb hi, kekWa_relabelW, kind_relabelW]

lemma candOf_relabelW {P : Work} (hwf : WF P) (hb : IdxBij P.numAtoms σ ψ) {i : ℕ}
    (hi : i < P.atoms.size) :
    candOf (P.relabelW σ ψ) (P.relabelW σ ψ).kekWa (P.relabelW σ ψ).kekEv0 (σ i) =
      candOf P P.kekWa P.kekEv0 i := by
  have hev : (P.relabelW σ ψ).kekEv0[σ i]! = P.kekEv0[i]! := by
    simp only [kekEv0, numAtoms_relabelW]
    rw [getElem!_listRangeMap _ (hb.lt i hi), getElem!_listRangeMap _ (show i < P.numAtoms from hi),
      explicitValence_relabelW hwf hb hi]
  unfold candOf
  rw [hev, kekWa_eq, kekWa_eq, needsDoubleBond_eq_loc, needsDoubleBond_eq_loc,
    kindsAt_relabelW hwf hb hi, atom_relabelW hb hi]

/-- What `kekulize_correct` says of a kekulization. -/
def KekData (m K : Work) : Prop :=
  ∃ D : ℕ → Bool,
    (∀ k, (K.bonds[k]! : WBond).kind = if D k = true then .double else
      if m.kekWa k = true then .single else (m.bonds[k]! : WBond).kind) ∧
    (∀ k, D k = true → k < m.bonds.size ∧ m.kekWa k = true ∧
      ∀ x, (m.bonds[k]! : WBond).touches x = true → candOf m m.kekWa m.kekEv0 x = true) ∧
    (∀ k₁ k₂ x, D k₁ = true → D k₂ = true → (m.bonds[k₁]! : WBond).touches x = true →
      (m.bonds[k₂]! : WBond).touches x = true → k₁ = k₂) ∧
    ∀ x < m.atoms.size, candOf m m.kekWa m.kekEv0 x = true →
      ∃ k, D k = true ∧ (m.bonds[k]! : WBond).touches x = true

lemma KekData.bondHalfSum {m K : Work} (hwf : WF m) (hKR : KindsRel m K) (h : KekData m K)
    (x : ℕ) : K.bondHalfSum x = kekBase m x +
      if x < m.atoms.size ∧ candOf m m.kekWa m.kekEv0 x = true then 2 else 0 := by
  obtain ⟨D, h1, h2, h3, h4⟩ := h
  exact bondHalfSum_of_matching hwf hKR h1 h2 h3 h4 x

lemma KekData.kind_of_not {m K : Work} (h : KekData m K) {k : ℕ} (hk : m.kekWa k = false) :
    (K.bonds[k]! : WBond).kind = (m.bonds[k]! : WBond).kind := by
  obtain ⟨D, h1, h2, -, -⟩ := h
  rw [h1 k]
  have hD : D k = false := by
    by_contra hD
    have := (h2 k (by simpa using hD)).2.1
    rw [hk] at this; cases this
  simp [hD, hk]

lemma KekData.sd {m K : Work} (h : KekData m K) {k : ℕ} (hk : m.kekWa k = true) :
    IsSD (K.bonds[k]! : WBond).kind := by
  obtain ⟨D, h1, -, -, -⟩ := h
  rw [h1 k]
  by_cases hD : D k = true
  · rw [if_pos hD]; exact .inr rfl
  · rw [if_neg hD, if_pos hk]; exact .inl rfl

lemma size_of_kindsRel {o w : Work} (h : KindsRel o w) : w.bonds.size = o.bonds.size := by
  have := h.bonds
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := this w.bonds.size
    rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
    simp at this
  · have := this o.bonds.size
    rw [Array.getElem?_eq_none (le_refl _), Array.getElem?_eq_getElem hlt] at this
    simp at this

lemma ends_of_kindsRel {o w : Work} (h : KindsRel o w) (k : ℕ) :
    w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      o.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) := by
  have := congrArg (Option.map fun b : WBond ↦ (b.src, b.dst)) (h.bonds k)
  simpa [Option.map_map, Function.comp_def] using this

lemma wf_of_kindsRel {o w : Work} (hwf : WF o) (h : KindsRel o w) : WF w := by
  intro k hk
  have hs := size_of_kindsRel h
  have hk' : k < o.bonds.size := hs ▸ hk
  have e := ends_of_kindsRel h k
  rw [Array.getElem?_eq_getElem hk, Array.getElem?_eq_getElem hk'] at e
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
  have := hwf k hk'
  rw [getElem!_pos o.bonds k hk'] at this
  rw [getElem!_pos w.bonds k hk]
  simp only [numAtoms, h.atoms_size, e.1, e.2] at this ⊢
  exact this

lemma noArom_kindsAt {K : Work} (h : K.NoArom) (i : ℕ) :
    (K.kindsAt i).any (· == .aromatic) = false := by
  rw [Bool.eq_false_iff]
  intro hc
  obtain ⟨t, ht, he⟩ := List.any_eq_true.1 hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
  have hks : k < K.bonds.size := by
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds] at hk; exact hk.1
  rw [getElem!_pos _ k hks] at he
  exact h.2 _ (Array.getElem_mem hks) (by simpa using he)

lemma bondHalfSum_of_ge {w : Work} (hwf : WF w) {j : ℕ} (hj : w.atoms.size ≤ j) :
    w.bondHalfSum j = 0 := by
  have : w.bondsOf j = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro k hk
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, WBond.touches,
      Bool.or_eq_true, beq_iff_eq] at hk
    have := hwf k hk.1
    simp only [numAtoms] at this
    omega
  simp [bondHalfSum, this]

/-- **Kekulizing a relabeled copy gives the relabeled kekulization, up to a swap** of single and
double bonds among those written aromatic: the same atoms, and every atom with the same sum of
bond orders. -/
theorem kekulize_relabel_swapped {P K K' : Work} {R R' : Array (List ℕ)} (hwf : WF P)
    (hb : IdxBij P.numAtoms σ ψ) (hK : P.kekulize R = .ok K)
    (hK' : (P.relabelW σ ψ).kekulize R' = .ok K') (hd : KekData P K)
    (hd' : KekData (P.relabelW σ ψ) K') : Swapped P.kekWa (K.relabelW σ ψ) K' := by
  have hKR := kekulize_kindsRel hK
  have hKR' := kekulize_kindsRel hK'
  have hwfK : WF K := wf_of_kindsRel hwf hKR
  have hwfP' : WF (P.relabelW σ ψ) := wf_relabelW hwf hb
  have hwfK' : WF K' := wf_of_kindsRel hwfP' hKR'
  have hbK : IdxBij K.numAtoms σ ψ := by rw [numAtoms, hKR.atoms_size]; exact hb
  have hsK : K.bonds.size = P.bonds.size := size_of_kindsRel hKR
  have hsK' : K'.bonds.size = P.bonds.size := by rw [size_of_kindsRel hKR']; simp
  have haK' : K'.atoms.size = P.atoms.size := by rw [hKR'.atoms_size]; simp
  -- the sums at renamed atoms
  have hsum : ∀ i < P.atoms.size, K'.bondHalfSum (σ i) = K.bondHalfSum i := fun i hi ↦ by
    rw [hd'.bondHalfSum hwfP' hKR', hd.bondHalfSum hwf hKR, kekBase_relabelW hwf hb hi,
      candOf_relabelW hwf hb hi]
    have h1 : σ i < P.atoms.size := hb.lt i hi
    simp only [relabelW_atoms_size, h1, hi, true_and]
  refine ⟨?_, by rw [relabelW_bonds_size, hsK, hsK'], fun k ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_,
    fun j ↦ ?_⟩
  · -- the atoms
    apply array_ext_of_getElem! (n := P.atoms.size) haK' (by simp [hKR.atoms_size])
    intro j hj
    have hpj := hb.lt' j hj
    rw [atom_relabelW' (by rw [hKR.atoms_size]; exact hj)]
    conv_lhs => rw [← hb.right j hj]
    have hat : ((P.relabelW σ ψ).atoms[σ (ψ j)]! : WAtom) = P.atoms[ψ j]! := atom_relabelW hb hpj
    by_cases hbr : IsBranch (P.atoms[ψ j]! : WAtom)
    · rw [kekulize_atom_branch hK' (hat ▸ hbr), kekulize_atom_branch hK hbr, hat,
        hsum _ hpj, noArom_kindsAt (kekulize_noArom hK'), noArom_kindsAt (kekulize_noArom hK)]
    · have e1 := kekulize_atom hK' (σ (ψ j))
      have e2 := kekulize_atom hK (ψ j)
      rw [hat] at e1
      rcases e1 with e1 | ⟨h1, -⟩
      · rcases e2 with e2 | ⟨h2, -⟩
        · rw [e1, e2]
        · exact absurd h2 hbr
      · exact absurd h1 hbr
  · -- the ends
    rw [ends_of_kindsRel hKR', getElem?_relabelW_bonds, getElem?_relabelW_bonds, Option.map_map,
      Option.map_map]
    have := ends_of_kindsRel hKR k
    cases hP : P.bonds[k]? with
    | none =>
      rw [hP] at this
      rw [Option.map_eq_none_iff.1 this]
    | some b =>
      rw [hP] at this
      obtain ⟨b', hb', e⟩ := Option.map_eq_some_iff.1 this
      rw [hb']
      simp only [Option.map_some, Function.comp_apply, Prod.mk.injEq] at e ⊢
      rw [e.1, e.2]
  · -- off the aromatic bonds, the same kinds
    by_cases hks : k < P.bonds.size
    · rw [kind?_eq_of_lt _ (by rw [hsK']; exact hks),
        kind?_eq_of_lt _ (by rw [relabelW_bonds_size, hsK]; exact hks), kind_relabelW,
        hd'.kind_of_not (by rw [kekWa_relabelW]; exact hk), hd.kind_of_not hk, kind_relabelW]
    · simp only [kind?]
      rw [Array.getElem?_eq_none (by rw [hsK']; omega),
        Array.getElem?_eq_none (by rw [relabelW_bonds_size, hsK]; omega)]
  · -- on them, single or double
    have hks : k < P.bonds.size := (kekWa_iff.1 hk).1
    refine ⟨⟨_, kind?_eq_of_lt _ (by rw [relabelW_bonds_size, hsK]; exact hks), ?_⟩,
      ⟨_, kind?_eq_of_lt _ (by rw [hsK']; exact hks), hd'.sd (by rw [kekWa_relabelW]; exact hk)⟩⟩
    rw [kind_relabelW]
    exact hd.sd hk
  · -- the same sums
    by_cases hj : j < P.atoms.size
    · rw [← hb.right j hj, hsum _ (hb.lt' j hj),
        bondHalfSum_relabelW hwfK hbK (by rw [hKR.atoms_size]; exact hb.lt' j hj)]
    · rw [bondHalfSum_of_ge hwfK' (by rw [haK']; omega),
        bondHalfSum_of_ge (wf_relabelW hwfK hbK) (by simp [hKR.atoms_size]; omega)]

end LeanSMILES.Aromaticity.Work
