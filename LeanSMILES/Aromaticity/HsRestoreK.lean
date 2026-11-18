/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.PrepareFacts
public import LeanSMILES.Aromaticity.HsDecide
public import LeanSMILES.Aromaticity.PerceiveFacts
public import LeanSMILES.Aromaticity.MarkFacts

/-!
# LeanSMILES.Aromaticity.HsRestoreK

**`adjustHs` gives back the cached hydrogens on the kekulized copy** (`Work.hsRestored_kekulize`):
at every atom of `aromatize`'s kekulized working copy, after radicals and perception, the final
hydrogen step restores the total cached before kekulization.  The atom-level arithmetic is
`Loc.bare_ok` and `Loc.branch_ok`; this file carries each atom of the pipeline to the finitely
many cases they check.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-! ### Setting up -/

lemma ofMolecule_bond {n : ℕ} (m : Molecule n) {k : ℕ} (hk : k < m.bonds.length) :
    ((ofMolecule m).bonds[k]! : WBond) =
      { src := m.bonds[k].src.val, dst := m.bonds[k].dst.val, kind := m.bonds[k].kind } := by
  simp [ofMolecule, hk]

/-- An atom of `prepare m` is aromatic exactly when the molecule writes it lowercase. -/
lemma aromatic_prepare {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((prepare m).atoms[i.val]! : WAtom).aromatic = (m.atom i).aromatic := by
  rw [prepare_atom, cleaned_atom, ofMolecule_atom]

lemma aromatic_prepare_of_ge {n : ℕ} (m : Molecule n) {x : ℕ} (hx : n ≤ x) :
    ((prepare m).atoms[x]! : WAtom).aromatic = false := by
  have : (prepare m).atoms.size = n := by
    rw [prepare_eq, size_cacheValences_atoms, size_cleaned]
  rw [getElem!_neg _ x (by omega)]
  rfl

/-- The bonds at an atom of `prepare m`: as many as the molecule's, and as many aromatic. -/
lemma kindsAt_prepare_counts {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((prepare m).kindsAt i).length = (m.bonds.filter (·.touches i)).length ∧
      (((prepare m).kindsAt i).filter (· == .aromatic)).length =
        (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length := by
  have h := kindsAt_prepare m i
  refine ⟨by simpa using h.length_eq, ?_⟩
  have e : (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length =
      (((m.bonds.filter (·.touches i)).map (·.kind)).filter (· == .aromatic)).length := by
    rw [List.filter_map, List.length_map, List.filter_filter]
    congr 1
    apply List.filter_congr
    intro b _
    simp [Bool.and_comm]
  rw [e]
  clear e
  generalize (m.bonds.filter (·.touches i)).map (·.kind) = l at h
  generalize (prepare m).kindsAt i = l' at h
  induction h with
  | nil => rfl
  | @cons p o _ _ hpo _ ih =>
    by_cases hp : p = .aromatic
    · have ho : o = .aromatic := hpo.1 hp
      simp [hp, ho, ih]
    · have ho : o ≠ .aromatic := fun h ↦ hp (hpo.2 h)
      simp [hp, ho, ih]

/-- `kekulize_correct` for `aromatize`'s working copy, when aromatic bonds are written as
`Molecule.AromaticWritten` asks. -/
theorem kekulize_prepare_correct {n : ℕ} {m : Molecule n} {K : Work}
    (hw1 : ∀ i, (m.atom i).aromatic = true →
      2 ≤ (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length ∧
        (m.bonds.filter (·.touches i)).length ≤ 3)
    (hw2 : ∀ b ∈ m.bonds, b.kind = .aromatic →
      (m.atom b.src).aromatic = true ∧ (m.atom b.dst).aromatic = true)
    (hK : (prepare m).kekulize (prepare m).relevantCycles = .ok K) :
    ∃ D : ℕ → Bool,
      (∀ k, (K.bonds[k]! : WBond).kind = if D k = true then .double else
        if (prepare m).kekWa k = true then .single else ((prepare m).bonds[k]! : WBond).kind) ∧
      (∀ k, D k = true → k < (prepare m).bonds.size ∧ (prepare m).kekWa k = true ∧
        ∀ x, ((prepare m).bonds[k]! : WBond).touches x = true →
          candOf (prepare m) (prepare m).kekWa (prepare m).kekEv0 x = true) ∧
      (∀ k₁ k₂ x, D k₁ = true → D k₂ = true → ((prepare m).bonds[k₁]! : WBond).touches x = true →
        ((prepare m).bonds[k₂]! : WBond).touches x = true → k₁ = k₂) ∧
      ∀ x < (prepare m).atoms.size, candOf (prepare m) (prepare m).kekWa (prepare m).kekEv0 x =
        true → ∃ k, D k = true ∧ ((prepare m).bonds[k]! : WBond).touches x = true := by
  obtain ⟨hwf, hnd⟩ := wf_nbrsDistinct_prepare m
  refine kekulize_correct hwf hnd (fun ring hr ↦ isRing_of_mem_relevantCycles _ hr) ?_ ?_ hK
  · intro x hx
    by_cases hxn : x < n
    · rw [aromatic_prepare m ⟨x, hxn⟩] at hx
      have := (hw1 ⟨x, hxn⟩ hx).2
      have hl : ((prepare m).bondsOf x).length = ((prepare m).kindsAt x).length := by
        simp [kindsAt]
      rw [hl]
      exact (kindsAt_prepare_counts m ⟨x, hxn⟩).1 ▸ this
    · rw [aromatic_prepare_of_ge m (by omega)] at hx
      cases hx
  · intro k hk ha
    have hkl : k < m.bonds.length := by
      have := (sameSkel_prepare m).numBonds
      simp only [numBonds, ofMolecule, List.size_toArray, Array.size_map] at this
      omega
    have hO : ((ofMolecule m).bonds[k]! : WBond).kind = .aromatic := by
      have := (cleanFine_cleaned m).arom k
      rw [prepare_eq, cacheValences_bonds] at ha
      exact this.1 ha
    rw [ofMolecule_bond m hkl] at hO
    have hs := (sameSkel_prepare m).src k
    rw [ofMolecule_bond m hkl] at hs
    rw [hs]
    exact (aromatic_prepare m m.bonds[k].src).trans (hw2 _ (List.getElem_mem hkl) hO).1

lemma length_filter_eq_one {l : List ℕ} {p : ℕ → Bool} (hnd : l.Nodup)
    (hu : ∀ a ∈ l, ∀ b ∈ l, p a = true → p b = true → a = b) (he : ∃ a ∈ l, p a = true) :
    (l.filter p).length = 1 := by
  induction l with
  | nil => obtain ⟨a, ha, -⟩ := he; cases ha
  | cons x t ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.1 hnd
    by_cases hp : p x = true
    · have h0 : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hpb
        exact hx ((hu x List.mem_cons_self b (List.mem_cons_of_mem _ hb) hp hpb) ▸ hb)
      simp [hp, h0]
    · have he' : ∃ a ∈ t, p a = true := by
        obtain ⟨a, ha, hpa⟩ := he
        rcases List.mem_cons.1 ha with rfl | ha
        · exact absurd hpa hp
        · exact ⟨a, ha, hpa⟩
      simp only [List.filter_cons, hp, Bool.false_eq_true, if_false]
      exact ih ht (fun a ha b hb ↦ hu a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        he'

lemma zip_map_map {α β γ : Type*} (l : List α) (f : α → β) (g : α → γ) :
    (l.map f).zip (l.map g) = l.map fun a ↦ (f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- **The kinds kekulization gives the bonds at an atom** are one of `Loc.kekAll`'s: the aromatic
ones single, but one double if the atom needs a double bond. -/
theorem kindsAt_kekulize_mem {n : ℕ} {m : Molecule n} {K : Work}
    (hw1 : ∀ i, (m.atom i).aromatic = true →
      2 ≤ (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length ∧
        (m.bonds.filter (·.touches i)).length ≤ 3)
    (hw2 : ∀ b ∈ m.bonds, b.kind = .aromatic →
      (m.atom b.src).aromatic = true ∧ (m.atom b.dst).aromatic = true)
    (hK : (prepare m).kekulize (prepare m).relevantCycles = .ok K) (i : Fin n) :
    K.kindsAt i ∈ Loc.kekAll (candOf (prepare m) (prepare m).kekWa (prepare m).kekEv0 i)
      ((prepare m).kindsAt i) := by
  obtain ⟨D, hkind, hdok, hmatch, hcover⟩ := kekulize_prepare_correct hw1 hw2 hK
  have hsk : SameSkel K (prepare m) := (kekulize_kindsRel hK).sameSkel
  set P := prepare m with hP
  have hrel : ∀ k ∈ P.bondsOf i, Loc.KekRel (P.bonds[k]! : WBond).kind (K.bonds[k]! : WBond).kind ∧
      ((P.bonds[k]! : WBond).kind == .aromatic && (K.bonds[k]! : WBond).kind == .double) = D k := by
    intro k hk
    have hks : k < P.bonds.size := lt_of_mem_bondsOf hk
    rw [hkind k]
    unfold Loc.KekRel
    by_cases hD : D k = true
    · have hwa := (kekWa_iff.1 (hdok k hD).2.1).2
      simp [hD, hwa]
    · by_cases hpa : (P.bonds[k]! : WBond).kind = .aromatic
      · have hwa : P.kekWa k = true := kekWa_iff.2 ⟨hks, hpa⟩
        simp [hD, hwa, hpa]
      · have hwa : P.kekWa k = false := by
          cases h : P.kekWa k
          · rfl
          · exact absurd (kekWa_iff.1 h).2 hpa
        simp [hD, hwa, hpa]
  have hf : List.Forall₂ Loc.KekRel (P.kindsAt i) (K.kindsAt i) := by
    have := kindsAt_forall₂ hsk (fun k p ↦ Loc.KekRel p k) i fun k hk ↦ (hrel k hk).1
    exact this.flip
  refine Loc.mem_kekAll _ _ hf _ ?_
  unfold kindsAt
  rw [hsk.bondsOf, zip_map_map, List.filter_map, List.length_map]
  have hnd : (P.bondsOf i).Nodup := (List.nodup_range).filter _
  rw [List.filter_congr (fun k hk ↦ by simp only [Function.comp_def]; exact (hrel k hk).2)]
  split
  · rename_i hc
    refine length_filter_eq_one hnd (fun a ha b hb hDa hDb ↦ ?_) ?_
    · exact hmatch a b i hDa hDb (touches_of_mem_bondsOf ha) (touches_of_mem_bondsOf hb)
    · have hi : i.val < P.atoms.size := by
        rw [hP, prepare_eq, size_cacheValences_atoms, size_cleaned]; exact i.isLt
      obtain ⟨k, hDk, htk⟩ := hcover i hi hc
      refine ⟨k, ?_, hDk⟩
      simp only [bondsOf, List.mem_filter, List.mem_range, numBonds]
      exact ⟨(hdok k hDk).1, htk⟩
  · rename_i hc
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro k hk hDk
    exact hc ((hdok k hDk).2.2 i (touches_of_mem_bondsOf hk))

/-! ### Radicals and perception, at one atom -/

/-- An atom read with `!` agrees with another on everything but `radicals` when the arrays do. -/
lemma getElem!_eq_of_map_radicals {a b : Array WAtom} (h : ∀ j : ℕ,
    a[j]?.map (fun x : WAtom ↦ { x with radicals := 0 }) =
      b[j]?.map (fun x : WAtom ↦ { x with radicals := 0 })) (j : ℕ) :
    ({ (a[j]! : WAtom) with radicals := 0 } : WAtom) = { (b[j]! : WAtom) with radicals := 0 } := by
  have := h j
  simp only [getElem!_def]
  cases h1 : a[j]? <;> cases h2 : b[j]? <;> simp_all

/-- `assignRadicals` leaves an atom without bracket hydrogens alone. -/
lemma assignRadicals_atom_of_not_noImplicit (w : Work) {j : ℕ}
    (hj : (w.atoms[j]! : WAtom).noImplicit = false) :
    (w.assignRadicals.atoms[j]! : WAtom) = w.atoms[j]! := by
  unfold assignRadicals
  refine foldl_induction (fun x : Work ↦ (x.atoms[j]! : WAtom) = w.atoms[j]!) _ _ _ rfl ?_
  intro x i _ hx
  unfold radicalStep
  dsimp only
  split
  · exact hx
  · rename_i h
    by_cases hij : i = j
    · subst hij
      simp only [hx, hj, Bool.not_false, Bool.true_or] at h
      exact absurd trivial h
    · rw [modifyAtom_atom_of_ne x hij]
      exact hx

/-- Perception changes nothing about the atoms but their aromatic flags. -/
lemma setAromaticity_atom (w : Work) (rings : Array (List ℕ)) (j : ℕ) :
    ({ ((w.setAromaticity rings).atoms[j]! : WAtom) with aromatic := false } : WAtom) =
      { (w.atoms[j]! : WAtom) with aromatic := false } := by
  unfold setAromaticity
  refine foldl_induction (fun x : Work ↦
    ({ (x.atoms[j]! : WAtom) with aromatic := false } : WAtom) =
    { (w.atoms[j]! : WAtom) with aromatic := false }) _ _ _ rfl ?_
  intro x b _ hx
  unfold markAromatic
  dsimp only
  split
  · rw [atom_modifyAtom, atom_modifyAtom]
    simp only [atoms_setKind, size_atoms_modifyAtom]
    split <;> split <;> simp_all
  · exact hx

/-- Every bond perception marks is a bond. -/
lemma lt_of_mem_aromaticBondList (w : Work) (rings : Array (List ℕ)) {b : ℕ}
    (hb : b ∈ w.aromaticBondList rings) : b < w.bonds.size := by
  obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 (mem_flatMap_ringBonds_of_mem_aromaticBondList w rings hb)
  exact (mem_ringBonds hr).1

/-- An atom perception flags aromatic has a bond it made aromatic, when nothing was flagged
before. -/
lemma setAromaticity_flag (w : Work) (rings : Array (List ℕ))
    (h0 : ∀ j : ℕ, (w.atoms[j]! : WAtom).aromatic = false) (j : ℕ)
    (hj : ((w.setAromaticity rings).atoms[j]! : WAtom).aromatic = true) :
    ∃ k ∈ (w.setAromaticity rings).bondsOf j,
      ((w.setAromaticity rings).bonds[k]! : WBond).kind = .aromatic := by
  have key : ∀ (l : List ℕ) (x : Work), (∀ b ∈ l, b < x.bonds.size) →
      (∀ j : ℕ, (x.atoms[j]! : WAtom).aromatic = true →
        ∃ k ∈ x.bondsOf j, (x.bonds[k]! : WBond).kind = .aromatic) →
      ∀ j : ℕ, ((l.foldl markAromatic x).atoms[j]! : WAtom).aromatic = true →
        ∃ k ∈ (l.foldl markAromatic x).bondsOf j,
          ((l.foldl markAromatic x).bonds[k]! : WBond).kind = .aromatic := by
    intro l
    induction l with
    | nil => intro x _ hx; exact hx
    | cons b l ih =>
      intro x hl hx
      have hb : b < x.bonds.size := hl b List.mem_cons_self
      apply ih
      · intro b' hb'
        have := hl b' (List.mem_cons_of_mem _ hb')
        unfold markAromatic
        dsimp only
        split <;> simpa using this
      intro j hj
      unfold markAromatic at hj ⊢
      dsimp only at hj ⊢
      split at hj
      · rename_i hsd
        rw [if_pos hsd]
        have hkb : (((x.setKind b .aromatic).modifyAtom (x.bonds[b]! : WBond).src
            ({ · with aromatic := true })).modifyAtom (x.bonds[b]! : WBond).dst
              ({ · with aromatic := true })).bonds[b]!.kind = .aromatic := by
          change ((x.setKind b .aromatic).bonds[b]! : WBond).kind = .aromatic
          rw [kind_setKind, if_pos ⟨rfl, hb⟩]
        have hmem : ∀ c, (x.bonds[b]! : WBond).touches c = true →
            b ∈ (((x.setKind b .aromatic).modifyAtom (x.bonds[b]! : WBond).src
              ({ · with aromatic := true })).modifyAtom (x.bonds[b]! : WBond).dst
                ({ · with aromatic := true })).bondsOf c := by
          intro c hc
          simp only [bondsOf, List.mem_filter, List.mem_range, numBonds, bonds_modifyAtom,
            size_setKind_bonds]
          refine ⟨hb, ?_⟩
          simpa [WBond.touches] using hc
        rw [atom_modifyAtom, atom_modifyAtom] at hj
        simp only [atoms_setKind, size_atoms_modifyAtom] at hj
        by_cases hd : (x.bonds[b]! : WBond).dst = j ∧ j < x.atoms.size
        · exact ⟨b, hmem j (by simp [WBond.touches, hd.1]), hkb⟩
        by_cases hs : (x.bonds[b]! : WBond).src = j ∧ j < x.atoms.size
        · exact ⟨b, hmem j (by simp [WBond.touches, hs.1]), hkb⟩
        rw [if_neg hd, if_neg hs] at hj
        obtain ⟨k, hk, hka⟩ := hx j hj
        refine ⟨k, by simpa [bondsOf, numBonds, WBond.touches] using hk, ?_⟩
        simp only [bonds_modifyAtom, kind_setKind]
        split <;> simp_all
      · rename_i hsd
        rw [if_neg hsd]
        exact hx j hj
  exact key _ w (fun b hb ↦ lt_of_mem_aromaticBondList w rings hb)
    (fun j hj ↦ by rw [h0 j] at hj; cases hj) j hj

/-- A candidate for the donor type a ring gave it has a non-negative electron count. -/
lemma countAtomElec_nonneg_of_cand (w : Work) {i : ℕ} {rbs : List ℕ} {len : ℕ}
    (h : w.isAromaticCandidate i (w.ringDonor rbs len i) = true) : 0 ≤ w.countAtomElec i := by
  by_contra hneg
  push Not at hneg
  have hd : w.donorType rbs i = .none := by
    unfold donorType
    simp [Id.run, hneg]
    rfl
  have hr : w.ringDonor rbs len i = .none := by
    unfold ringDonor
    simp [hd]
  rw [hr] at h
  unfold isAromaticCandidate at h
  have e : (Donor.none == Donor.none) = true := rfl
  simp [Id.run, e] at h

/-! ### Small facts for the assembly -/

lemma restore_of_noImplicit {a : WAtom} (hn : a.noImplicit = true) (hc : a.cachedImplicit = 0)
    (ks : List BondKind) (ar : Bool) : Loc.restore a ks ar = true := by
  have h0 : Loc.impl a (Loc.bhs ks) ar = 0 := by simp [Loc.impl, hn]
  simp [Loc.restore, h0, hc]

lemma restore_of_quiet {a : WAtom} {ks : List BondKind} (hadj : a.adjustHs = false)
    (h : Loc.impl a (Loc.bhs ks) false = a.cachedImplicit) : Loc.restore a ks false = true := by
  simp [Loc.restore, hadj, h]

/-- The elements that may be written bare and lowercase, or that perception may make aromatic. -/
lemma organic_aromatic_z : ∀ e : Element, e.inOrganicSubset = true →
    (1 < defaultValence e.atomicNumber ∨ e.aromaticAllowed = true) →
    e.atomicNumber ∈ ([5, 6, 7, 8, 15, 16] : List ℕ) := by
  decide +kernel

lemma isAromaticCandidate_donor_ne {w : Work} {i : ℕ} {d : Donor}
    (h : w.isAromaticCandidate i d = true) : d ≠ .none := by
  rintro rfl
  unfold isAromaticCandidate at h
  have e : (Donor.none == Donor.none) = true := rfl
  simp [Id.run, e] at h

lemma two_le_length_of_ne {l : List ℕ} {a b : ℕ} (hab : a ≠ b) (ha : a ∈ l) (hb : b ∈ l) :
    2 ≤ l.length := by
  match l, ha, hb with
  | [x], ha, hb =>
    simp only [List.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  | [], ha, _ => cases ha
  | _ :: _ :: _, _, _ => simp

lemma marks_eq_of_noArom : ∀ {kk sk : List BondKind}, sk ∈ Loc.marks kk →
    sk.any (· == .aromatic) = false → sk = kk
  | [], sk, h, _ => by simpa [Loc.marks] using h
  | k :: ks, sk, h, ha => by
    unfold Loc.marks at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨t, ht, rfl⟩ | h
    · simp only [List.any_cons, Bool.or_eq_false_iff] at ha
      rw [marks_eq_of_noArom ht ha.2]
    · split at h
      · obtain ⟨t, -, rfl⟩ := List.mem_map.1 h
        simp at ha
      · cases h

lemma length_of_mem_marks : ∀ {kk sk : List BondKind}, sk ∈ Loc.marks kk → sk.length = kk.length
  | [], sk, h => by simp_all [Loc.marks]
  | k :: ks, sk, h => by
    unfold Loc.marks at h
    simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨t, ht, rfl⟩ | h
    · simp [length_of_mem_marks ht]
    · split at h
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
        simp [length_of_mem_marks ht]
      · cases h

lemma kekAll_eq_of_noArom : ∀ {need : Bool} {pk kk : List BondKind}, kk ∈ Loc.kekAll need pk →
    pk.any (· == .aromatic) = false → kk = pk
  | need, [], kk, h, _ => by cases need <;> simp_all [Loc.kekAll]
  | need, p :: ps, kk, h, ha => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at ha
    unfold Loc.kekAll at h
    rw [if_neg (by simpa using ha.1)] at h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
    rw [kekAll_eq_of_noArom ht ha.2]

lemma length_of_mem_kekAll : ∀ {need : Bool} {pk kk : List BondKind},
    kk ∈ Loc.kekAll need pk → kk.length = pk.length
  | need, [], kk, h => by cases need <;> simp_all [Loc.kekAll]
  | need, p :: ps, kk, h => by
    unfold Loc.kekAll at h
    split at h
    · simp only [List.mem_append, List.mem_map] at h
      rcases h with ⟨t, ht, rfl⟩ | h
      · simp [length_of_mem_kekAll ht]
      · split at h
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
          simp [length_of_mem_kekAll ht]
        · cases h
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      simp [length_of_mem_kekAll ht]

lemma kekWa_eq (w : Work) : w.kekWa = fun k ↦ (w.bonds[k]! : WBond).kind == .aromatic := by
  funext k
  by_cases hk : k < w.bonds.size
  · cases h : w.kekWa k
    · have : ¬ (w.bonds[k]! : WBond).kind = .aromatic := fun e ↦ by
        have := kekWa_iff.2 ⟨hk, e⟩; rw [h] at this; cases this
      simp [this]
    · simp [(kekWa_iff.1 h).2]
  · have h1 : w.kekWa k = false := by
      cases h : w.kekWa k
      · rfl
      · exact absurd (kekWa_iff.1 h).1 hk
    rw [h1, getElem!_neg w.bonds k hk]
    rfl

lemma kekEv0_getElem! (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    w.kekEv0[i]! = w.explicitValence i := by
  have : i < w.kekEv0.length := by simpa [kekEv0, numAtoms] using hi
  rw [getElem!_pos w.kekEv0 i this]
  simp [kekEv0]

lemma elec_nonneg_dv {a : WAtom} {ks : List BondKind} (h : 0 ≤ Loc.elec a ks) :
    1 < defaultValence a.z := by
  by_contra hd
  push Not at hd
  have : Loc.elec a ks = -1 := by
    unfold Loc.elec
    have : (defaultValence a.z : ℤ) ≤ 1 := by exact_mod_cast hd
    simp [Id.run, this]
    rfl
  omega

lemma elec_nonneg_length {a : WAtom} {ks : List BondKind} (h : 0 ≤ Loc.elec a ks) :
    ks.length ≤ 3 := by
  by_contra hl
  push Not at hl
  have : Loc.elec a ks = -1 := by
    unfold Loc.elec
    have h3 : (3 : ℤ) < ks.length + ((a.explicitHs : ℤ) + a.cachedImplicit) := by
      have : (3 : ℤ) < ks.length := by exact_mod_cast hl
      omega
    by_cases hd : (defaultValence a.z : ℤ) ≤ 1
    · simp [Id.run, hd]; rfl
    · simp [Id.run, hd, h3]; rfl
  omega

lemma forall₂_exists_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ x ∈ l₁, ∃ y ∈ l₂, R x y
  | _, _, .nil, _, hx => by cases hx
  | _, _, .cons h hr, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hxy⟩ := forall₂_exists_right hr x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

/-! ### The assembly -/

set_option maxHeartbeats 4000000 in -- one long case analysis over the pipeline's records
/-- **`adjustHs` gives back the cached hydrogens at every atom of the kekulized copy**, after
radicals and perception, when aromatic bonds are written as `Molecule.AromaticWritten` asks and
every bare atom could be written bare (`Molecule.BareWritable`). -/
theorem hsRestored_kekulize {n : ℕ} {m : Molecule n} {K : Work}
    (hw1 : ∀ i, (m.atom i).aromatic = true →
      2 ≤ (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length ∧
        (m.bonds.filter (·.touches i)).length ≤ 3)
    (hw2 : ∀ b ∈ m.bonds, b.kind = .aromatic →
      (m.atom b.src).aromatic = true ∧ (m.atom b.dst).aromatic = true)
    (hbw : ∀ i, (m.atom i).explicitH = none → (m.atom i).canBeBare = true ∧
      ((m.atom i).aromatic = true → (m.atom i).element.all Element.aromaticAllowed = true))
    (hK : (prepare m).kekulize (prepare m).relevantCycles = .ok K) (i : Fin n) :
    HsRestored (K.assignRadicals.setAromaticity (prepare m).relevantCycles) i := by
  set P := prepare m with hP
  set R := P.relevantCycles with hR
  set KR := K.assignRadicals with hKR
  set S := KR.setAromaticity R with hS
  have hKP := kekulize_kindsRel hK
  have hna := kekulize_noArom hK
  have hsKP : SameSkel K P := hKP.sameSkel
  have hsKRK : SameSkel KR K := (afterRel_assignRadicals (w := K)).sameSkel
  have hsSKR : SameSkel S KR := (afterRel_setAromaticity KR R).sameSkel
  have hnP : P.atoms.size = n := by rw [hP, prepare_eq, size_cacheValences_atoms, size_cleaned]
  have hnS : S.atoms.size = n := by
    rw [(afterRel_setAromaticity KR R).atoms_size, (afterRel_assignRadicals (w := K)).atoms_size,
      hKP.atoms_size, hnP]
  rw [hsRestored_iff_loc S (by rw [hnS]; exact i.isLt)]
  -- the kinds at `i`
  have hKRk : KR.kindsAt i = K.kindsAt i := by
    simp only [kindsAt, bondsOf, numBonds, hKR, assignRadicals_bonds]
  have hmarks : S.kindsAt i ∈ Loc.marks (K.kindsAt i) := by
    rw [← hKRk]
    refine Loc.mem_marks _ _ (kindsAt_forall₂ hsSKR (fun s k ↦ Loc.MarkRel k s) i
      fun k hk ↦ ?_).flip
    have hk' : k < KR.bonds.size := lt_of_mem_bondsOf hk
    change Loc.MarkRel (KR.bonds[k]! : WBond).kind (S.bonds[k]! : WBond).kind
    rw [hS, setAromaticity, kind_foldl_markAromatic KR _ k hk']
    unfold Loc.MarkRel
    split
    · rename_i h
      right
      refine ⟨rfl, ?_⟩
      simpa [isSD] using h.2
    · left; rfl
  have hkek := kindsAt_kekulize_mem hw1 hw2 hK i
  -- K has no aromatic bond, so `KR`'s flags are all down
  have hKnoar : ∀ k : ℕ, (K.bonds[k]! : WBond).kind ≠ .aromatic := by
    intro k
    by_cases hk : k < K.bonds.size
    · rw [getElem!_pos K.bonds k hk]; exact hna.2 _ (Array.getElem_mem hk)
    · rw [getElem!_neg K.bonds k hk]; decide
  have hKRflag : ∀ j : ℕ, (KR.atoms[j]! : WAtom).aromatic = false := by
    intro j
    have e := congrArg WAtom.aromatic
      (getElem!_eq_of_map_radicals (getElem?_assignRadicals_atoms K) j)
    simp only at e
    rw [e]
    by_cases hj : j < K.atoms.size
    · rw [getElem!_pos K.atoms j hj]; exact hna.1 _ (Array.getElem_mem hj)
    · rw [getElem!_neg K.atoms j hj]; rfl
  have harS : S.isAromaticAtom i = (S.kindsAt i).any (· == .aromatic) := by
    rw [isAromaticAtom_eq_loc]
    cases hf : (S.atoms[i.val]! : WAtom).aromatic
    · rfl
    · obtain ⟨k, hk, hka⟩ := setAromaticity_flag KR R hKRflag i hf
      symm
      simp only [Bool.true_or, List.any_eq_true, beq_iff_eq]
      exact ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, hka⟩
  -- what perception tells about an atom it makes aromatic
  have hperc : (S.kindsAt i).any (· == .aromatic) = true →
      2 ≤ (S.kindsAt i).length ∧ 0 ≤ Loc.elec KR.atoms[i.val]! (K.kindsAt i) ∧
        Loc.cand KR.atoms[i.val]! (K.kindsAt i) = true := by
    intro har
    simp only [List.any_eq_true, beq_iff_eq, kindsAt, List.mem_map] at har
    obtain ⟨_, ⟨k, hk, rfl⟩, hka⟩ := har
    have hkS : k < S.bonds.size := lt_of_mem_bondsOf hk
    have hkKR : k < KR.bonds.size := by simpa [hsSKR.numBonds] using lt_of_mem_bondsOf hk
    have h1 : S.kind? k = some .aromatic := by
      simp [kind?, Array.getElem?_eq_getElem hkS, ← getElem!_pos S.bonds k hkS, hka]
    have h0 : KR.kind? k ≠ some .aromatic := by
      have hb : KR.bonds = K.bonds := assignRadicals_bonds K
      have hkK : k < K.bonds.size := by rwa [← hb]
      simp only [kind?, hb, Array.getElem?_eq_getElem hkK, Option.map_some, ne_eq,
        Option.some.injEq]
      rw [← getElem!_pos K.bonds k hkK]
      exact hKnoar k
    obtain ⟨_, ring, hring, hsrc, hdst, ⟨r₁, l₁, c₁⟩, ⟨r₂, l₂, c₂⟩⟩ :=
      of_kind?_setAromaticity_donor KR R h1 h0
    have ht := touches_of_mem_bondsOf hk
    rw [WBond.touches, hsSKR.src, hsSKR.dst, getElem!_pos KR.bonds k hkKR] at ht
    simp only [Bool.or_eq_true, beq_iff_eq] at ht
    have hcand : ∃ rbs len, KR.isAromaticCandidate i (KR.ringDonor rbs len i) = true := by
      rcases ht with ht | ht
      · exact ⟨r₁, l₁, ht ▸ c₁⟩
      · exact ⟨r₂, l₂, ht ▸ c₂⟩
    have hir : i.val ∈ ring := by rcases ht with ht | ht <;> [exact ht ▸ hsrc; exact ht ▸ hdst]
    obtain ⟨rbs, len, hc⟩ := hcand
    refine ⟨?_, ?_, ?_⟩
    · have hIs : P.IsRing ring := isRing_of_mem_relevantCycles P (by simpa [hR] using hring)
      obtain ⟨k₁, k₂, hne, -, -, hk₁, hk₂⟩ := hIs.two_bonds hir
      have := two_le_length_of_ne hne hk₁ hk₂
      have hl : (S.kindsAt i).length = (P.bondsOf i).length := by
        simp only [kindsAt, List.length_map, hsSKR.bondsOf, hsKRK.bondsOf, hsKP.bondsOf]
      omega
    · rw [← hKRk, ← countAtomElec_eq_loc]
      exact countAtomElec_nonneg_of_cand KR hc
    · rw [← hKRk, ← isAromaticCandidate_eq_loc KR i (isAromaticCandidate_donor_ne hc)]
      exact hc
  -- the record at `i`: `S`'s is `K`'s but for flags and radicals
  have eqS := setAromaticity_atom KR R i
  have eqKR := getElem!_eq_of_map_radicals (getElem?_assignRadicals_atoms K) i.val
  have tr : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with aromatic := false } = f x) →
      (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f (S.atoms[i.val]! : WAtom) = f (K.atoms[i.val]! : WAtom) := by
    intro α f h1 h2
    rw [← h1, eqS, h1, ← h2, eqKR, h2]
  rw [harS, Loc.restore_congr (b := (K.atoms[i.val]! : WAtom))
    (tr WAtom.z (fun _ ↦ rfl) (fun _ ↦ rfl)) (tr WAtom.charge (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.explicitHs (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.noImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.cachedImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.adjustHs (fun _ ↦ rfl) (fun _ ↦ rfl))]
  -- the record of `P` at `i`, from the molecule's atom
  set a := m.atom i with ha
  set C := cleaned m with hC
  have hPa : (P.atoms[i.val]! : WAtom) =
      { z := a.atomicNumber, aromatic := a.aromatic, charge := (C.atoms[i.val]! : WAtom).charge,
        explicitHs := a.explicitH.getD 0, noImplicit := a.explicitH.isSome || a.element.isNone,
        frozenHs := (C.atoms[i.val]! : WAtom).frozenHs,
        cachedValence := some (C.explicitValence i), cachedImplicit := C.implicitHs i,
        adjustHs := C.isAromaticAtom i } := by
    rw [hP, prepare_atom, hC]
    conv_lhs => rw [cleaned_atom, ofMolecule_atom]
  have hCa : (C.atoms[i.val]! : WAtom) =
      { z := a.atomicNumber, aromatic := a.aromatic, charge := (C.atoms[i.val]! : WAtom).charge,
        explicitHs := a.explicitH.getD 0, noImplicit := a.explicitH.isSome || a.element.isNone,
        frozenHs := (C.atoms[i.val]! : WAtom).frozenHs } := by
    conv_lhs => rw [hC, cleaned_atom, ofMolecule_atom]
  have hCz : (C.atoms[i.val]! : WAtom).z = a.atomicNumber := by rw [hCa]
  have hCe : (C.atoms[i.val]! : WAtom).explicitHs = a.explicitH.getD 0 := by rw [hCa]
  have hCn : (C.atoms[i.val]! : WAtom).noImplicit = (a.explicitH.isSome || a.element.isNone) := by
    rw [hCa]
  have hCar0 : (C.atoms[i.val]! : WAtom).aromatic = a.aromatic := by rw [hCa]
  have hCk : C.kindsAt i = P.kindsAt i := by
    simp only [kindsAt, bondsOf, numBonds, hP, prepare_eq, cacheValences_bonds, hC]
  -- an aromatic bond at `i` makes `i` lowercase
  have hflag : (P.kindsAt i).any (· == .aromatic) = true → a.aromatic = true := by
    intro h
    have hf := kindsAt_prepare m i
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨y, hy, hxy⟩ := forall₂_exists_right hf _ hx
    have hy' : y = .aromatic := hxy.1 rfl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hbm, hbt⟩ := List.mem_filter.1 hb
    obtain ⟨h1, h2⟩ := hw2 b hbm hy'
    simp only [Bond.touches, Bool.or_eq_true, beq_iff_eq] at hbt
    rcases hbt with rfl | rfl
    · exact h1
    · exact h2
  have hCar : C.isAromaticAtom i = a.aromatic := by
    rw [isAromaticAtom_eq_loc, hCar0, hCk]
    cases hfa : a.aromatic
    · cases hany : (P.kindsAt i).any (· == .aromatic)
      · rfl
      · rw [hflag hany] at hfa; cases hfa
    · rfl
  have hCimpl : C.implicitHs i = Loc.impl (C.atoms[i.val]! : WAtom) (Loc.bhs (P.kindsAt i))
      a.aromatic := by
    rw [implicitHs_eq_loc, bondHalfSum_eq_loc, hCk, hCar]
  have hPar : P.isAromaticAtom i = a.aromatic := by
    rw [isAromaticAtom_eq_loc, ← hCk]
    have : (P.atoms[i.val]! : WAtom).aromatic = a.aromatic := by rw [hPa]
    rw [this]
    rw [hCk]
    cases hfa : a.aromatic
    · cases hany : (P.kindsAt i).any (· == .aromatic)
      · rfl
      · rw [hflag hany] at hfa; cases hfa
    · rfl
  have hcandOf : candOf P P.kekWa P.kekEv0 i = (a.aromatic &&
      Loc.ndb P.atoms[i.val]! (P.kindsAt i)
        (Loc.ev P.atoms[i.val]! (Loc.bhs (P.kindsAt i)) a.aromatic)) := by
    unfold candOf
    rw [kekWa_eq, needsDoubleBond_eq_loc, kekEv0_getElem! P (by rw [hnP]; exact i.isLt),
      explicitValence_eq_loc, hPar, bondHalfSum_eq_loc]
    have : (P.atoms[i.val]! : WAtom).aromatic = a.aromatic := by rw [hPa]
    rw [this]
  -- the counts the molecule fixes at a lowercase atom
  have hcnt : a.aromatic = true → 2 ≤ ((P.kindsAt i).filter (· == .aromatic)).length ∧
      (P.kindsAt i).length ≤ 3 := by
    intro hfa
    obtain ⟨c1, c2⟩ := kindsAt_prepare_counts m i
    obtain ⟨h1, h2⟩ := hw1 i hfa
    exact ⟨c2 ▸ h1, c1 ▸ h2⟩
  have hnf : a.aromatic = false → ((P.kindsAt i).filter (· == .aromatic)).length = 0 := by
    intro hfa
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx hxa
    have : (P.kindsAt i).any (· == .aromatic) = true := List.any_eq_true.2 ⟨x, hx, hxa⟩
    rw [hflag this] at hfa
    cases hfa
  have hlenS : (S.kindsAt i).length = (P.kindsAt i).length :=
    (length_of_mem_marks hmarks).trans (length_of_mem_kekAll hkek)
  -- `P`'s record at `i`, field by field
  have hPz : (P.atoms[i.val]! : WAtom).z = a.atomicNumber := by rw [hPa]
  have hPc : (P.atoms[i.val]! : WAtom).charge = (C.atoms[i.val]! : WAtom).charge := by rw [hPa]
  have hPe : (P.atoms[i.val]! : WAtom).explicitHs = a.explicitH.getD 0 := by rw [hPa]
  have hPn : (P.atoms[i.val]! : WAtom).noImplicit = (a.explicitH.isSome || a.element.isNone) := by
    rw [hPa]
  have hPr : (P.atoms[i.val]! : WAtom).radicals = 0 := by rw [hPa]
  have hPar0 : (P.atoms[i.val]! : WAtom).aromatic = a.aromatic := by rw [hPa]
  have hPv : (P.atoms[i.val]! : WAtom).cachedValence = some (C.explicitValence i) := by rw [hPa]
  have hPi : (P.atoms[i.val]! : WAtom).cachedImplicit = C.implicitHs i := by rw [hPa]
  have hPadj : (P.atoms[i.val]! : WAtom).adjustHs = C.isAromaticAtom i := by rw [hPa]
  have hPev : C.explicitValence i =
      Loc.ev (C.atoms[i.val]! : WAtom) (Loc.bhs (P.kindsAt i)) a.aromatic := by
    rw [explicitValence_eq_loc, bondHalfSum_eq_loc, hCk, hCar]
  rcases kekulize_atom hK i with hKa | ⟨hbr, hKa⟩
  · rw [hKa]
    by_cases hni : (a.explicitH.isSome || a.element.isNone) = true
    · -- an atom in brackets (or `*`): no implicit hydrogens anywhere
      refine restore_of_noImplicit (by simp [hPn, hni]) ?_ _ _
      change (P.atoms[i.val]! : WAtom).cachedImplicit = 0
      rw [hPi, hCimpl]
      simp [Loc.impl, hCn, hni]
    · simp only [Bool.not_eq_true, Bool.or_eq_false_iff, Option.isSome_eq_false_iff,
        Option.isNone_eq_false_iff, Option.isNone_iff_eq_none] at hni
      obtain ⟨hnone, hel⟩ := hni
      by_cases hq : a.aromatic = false ∧ (S.kindsAt i).any (· == .aromatic) = false
      · -- nothing aromatic before or after: nothing changes
        have hpk : (P.kindsAt i).any (· == .aromatic) = false := by
          cases h : (P.kindsAt i).any (· == .aromatic)
          · rfl
          · rw [hflag h] at hq; exact absurd hq.1 (by decide)
        have hsk : S.kindsAt i = P.kindsAt i :=
          (marks_eq_of_noArom hmarks hq.2).trans (kekAll_eq_of_noArom hkek hpk)
        rw [hq.2, hsk]
        refine restore_of_quiet (by change (P.atoms[i.val]! : WAtom).adjustHs = false
                                    rw [hPadj, hCar, hq.1]) ?_
        change _ = (P.atoms[i.val]! : WAtom).cachedImplicit
        rw [hPi, hCimpl, hq.1]
        apply Loc.impl_congr
        · change (P.atoms[i.val]! : WAtom).z = _; rw [hPz, hCz]
        · change (P.atoms[i.val]! : WAtom).charge = _; rw [hPc]
        · change (P.atoms[i.val]! : WAtom).explicitHs = _; rw [hPe, hCe]
        · change (P.atoms[i.val]! : WAtom).noImplicit = _; rw [hPn, hCn]
      · -- written lowercase, or made aromatic: the decided check
        obtain ⟨hcb, haro⟩ := hbw i hnone
        rw [← ha] at hcb haro
        cases hae : a.element with
        | none => simp [hae] at hel
        | some e =>
        have hcb' := hcb
        simp only [Atom.canBeBare, hnone, hae, Option.isNone_none, Bool.true_and,
          Bool.and_eq_true, beq_iff_eq] at hcb'
        obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
        have hz : a.atomicNumber = e.atomicNumber := by simp [Atom.atomicNumber, hae]
        have hKnI : (K.atoms[i.val]! : WAtom).noImplicit = false := by
          rw [hKa]; change (P.atoms[i.val]! : WAtom).noImplicit = false; rw [hPn]; simp [hnone, hae]
        have hKRa : (KR.atoms[i.val]! : WAtom) = K.atoms[i.val]! :=
          assignRadicals_atom_of_not_noImplicit K hKnI
        set flag := a.aromatic with hflagdef
        set c := (C.atoms[i.val]! : WAtom).charge with hcdef
        set pk := P.kindsAt i with hpkdef
        set B := Loc.bareP e.atomicNumber c flag pk with hB
        set X : WAtom := { (P.atoms[i.val]! : WAtom) with aromatic := false } with hX
        set Y : WAtom := { B with aromatic := false } with hY
        have rz : X.z = Y.z := by change (P.atoms[i.val]! : WAtom).z = _; rw [hPz, hz]; rfl
        have rc : X.charge = Y.charge := by
          change (P.atoms[i.val]! : WAtom).charge = _; rw [hPc]; rfl
        have re : X.explicitHs = Y.explicitHs := by
          change (P.atoms[i.val]! : WAtom).explicitHs = _; rw [hPe, hnone]; rfl
        have rn : X.noImplicit = Y.noImplicit := by
          change (P.atoms[i.val]! : WAtom).noImplicit = _
          rw [hPn]; simp [hnone, hae, hY, hB, Loc.bareP]
        have rr : X.radicals = Y.radicals := by
          change (P.atoms[i.val]! : WAtom).radicals = _; rw [hPr]; rfl
        have rv : X.cachedValence = Y.cachedValence := by
          change (P.atoms[i.val]! : WAtom).cachedValence = _
          rw [hPv, hPev]
          simp only [hY, hB, Loc.bareP, Option.some.injEq]
          apply Loc.ev_congr
          · rw [hCz, hz]
          · rfl
          · rw [hCe, hnone]; rfl
        have ri : X.cachedImplicit = Y.cachedImplicit := by
          change (P.atoms[i.val]! : WAtom).cachedImplicit = _
          rw [hPi, hCimpl]
          simp only [hY, hB, Loc.bareP]
          apply Loc.impl_congr
          · rw [hCz, hz]
          · rfl
          · rw [hCe, hnone]; rfl
          · rw [hCn]; simp [hnone, hae]
        have ra : X.adjustHs = Y.adjustHs := by
          change (P.atoms[i.val]! : WAtom).adjustHs = _; rw [hPadj, hCar]; rfl
        -- perception facts, on the `bareP` record
        have hperc' : (S.kindsAt i).any (· == .aromatic) = true → 2 ≤ (S.kindsAt i).length ∧
            0 ≤ Loc.elec Y (K.kindsAt i) ∧ Loc.cand Y (K.kindsAt i) = true := by
          intro har
          obtain ⟨h1, h2, h3⟩ := hperc har
          rw [hKRa, hKa] at h2 h3
          exact ⟨h1, (Loc.elec_congr rz rc re ri rr rv _) ▸ h2,
            (Loc.cand_congr rz rc re ri rr rv _) ▸ h3⟩
        -- the element may be aromatic
        have hzin : e.atomicNumber ∈ ([5, 6, 7, 8, 15, 16] : List ℕ) := by
          refine organic_aromatic_z e (by simpa using horg) ?_
          rcases not_and_or.1 hq with h | h
          · right
            have := haro (by simpa using h)
            simpa [hae] using this
          · left
            have := elec_nonneg_dv (hperc' (by simpa using h)).2.1
            simpa [hY, hB, Loc.bareP] using this
        -- the charge `cleanUp` may give it
        have hzc : (e.atomicNumber, c) ∈ Loc.bareZC := by
          have hcc := (cleanFine_cleaned m).charge i
          obtain ⟨hFz, hFc⟩ := freezeHs_atom_z_charge m i
          rw [hFz, hFc, ← ha, hch0, hz, ← hcdef] at hcc
          simp only [CleanCharge] at hcc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hzin
          rcases hzin with h | h | h | h | h | h <;> rw [h] at hcc ⊢ <;>
            rcases hcc with h' | h' | ⟨h', h''⟩ | h' | h' | h' <;>
            first
            | (rw [h']; decide)
            | omega
        have hpk3 : pk.length ≤ 3 := by
          rcases not_and_or.1 hq with h | h
          · exact (hcnt (by simpa using h)).2
          · have := elec_nonneg_length (hperc' (by simpa using h)).2.1
            rw [← length_of_mem_kekAll hkek]
            exact this
        have hkk : K.kindsAt i ∈ Loc.kekAll (flag && Loc.ndb B pk (B.cachedValence.getD 0)) pk := by
          have := hkek
          rw [hcandOf] at this
          have e1 : Loc.ev (P.atoms[i.val]! : WAtom) (Loc.bhs pk) flag =
              B.cachedValence.getD 0 := by
            simp only [hB, Loc.bareP, Option.getD_some]
            apply Loc.ev_congr
            · rw [hPz, hz]
            · rw [hPc]
            · rw [hPe, hnone]; rfl
          rw [e1, Loc.ndb_congr (a := (P.atoms[i.val]! : WAtom)) (b := B) rz rc re rn ri rr] at this
          exact this
        have := Loc.bare_restore hzc (Loc.mem_lists 3 pk hpk3)
          (fun hf ↦ ⟨(hcnt hf).1, (hcnt hf).2, hzin⟩) hnf hkk hmarks hperc'
        rw [Loc.restore_congr rz rc re rn ri ra]
        exact this
  · -- the `[nH]`/`[pH]` kekulization rewrites
    obtain ⟨hbar, hbz, hbc, hbe⟩ := hbr
    have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
      rw [Bool.eq_false_iff]
      intro h
      simp only [kindsAt, List.any_map, List.any_eq_true, Function.comp_apply, beq_iff_eq] at h
      obtain ⟨k, -, hk⟩ := h
      exact hKnoar k hk
    rw [hKany] at hKa
    have hfa : a.aromatic = true := by rw [← hPar0]; exact hbar
    have hsome : a.explicitH = some 1 := by
      rw [hPe] at hbe
      cases h : a.explicitH with
      | none => rw [h] at hbe; cases hbe
      | some x => rw [h] at hbe; simp only [Option.getD_some] at hbe; rw [hbe]
    set z := (P.atoms[i.val]! : WAtom).z with hzdef
    set pk := P.kindsAt i with hpkdef
    set kk := K.kindsAt i with hkkdef
    have hz' : z = 7 ∨ z = 15 := hbz
    -- `P`'s record is `branchP`'s
    have hCn1 : (C.atoms[i.val]! : WAtom).noImplicit = true := by rw [hCn, hsome]; rfl
    have hP0 : (P.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
      rw [hPi, hCimpl]; simp [Loc.impl, hCn1]
    have hPev' : Loc.ev (P.atoms[i.val]! : WAtom) (Loc.bhs pk) true =
        (Loc.branchP z pk).cachedValence.getD 0 := by
      simp only [Loc.branchP, Option.getD_some]
      apply Loc.ev_congr
      · rfl
      · exact hbc
      · exact hbe
    have hndb : Loc.ndb (P.atoms[i.val]! : WAtom) pk (Loc.ev (P.atoms[i.val]! : WAtom)
        (Loc.bhs pk) true) = Loc.ndb (Loc.branchP z pk) pk ((Loc.branchP z pk).cachedValence.getD 0)
        := by
      rw [hPev']
      apply Loc.ndb_congr
      · rfl
      · exact hbc
      · exact hbe
      · rw [hPn, hsome]; rfl
      · exact hP0
      · exact hPr
    have hkk : kk ∈ Loc.kekAll (Loc.ndb (Loc.branchP z pk) pk
        ((Loc.branchP z pk).cachedValence.getD 0)) pk := by
      have := hkek
      rw [hcandOf, hfa, Bool.true_and, hndb] at this
      exact this
    -- `K`'s record is `branchK`'s
    have hKh : K.bondHalfSum i = Loc.bhs kk := bondHalfSum_eq_loc K i
    have hKz : (K.atoms[i.val]! : WAtom).z = (Loc.branchK z pk kk).z := by rw [hKa]; rfl
    have hKc : (K.atoms[i.val]! : WAtom).charge = (Loc.branchK z pk kk).charge := by
      rw [hKa]; exact hbc
    have hKe : (K.atoms[i.val]! : WAtom).explicitHs = (Loc.branchK z pk kk).explicitHs := by
      rw [hKa]; rfl
    have hKn : (K.atoms[i.val]! : WAtom).noImplicit = (Loc.branchK z pk kk).noImplicit := by
      rw [hKa]; rfl
    have hKr : (K.atoms[i.val]! : WAtom).radicals = (Loc.branchK z pk kk).radicals := by
      rw [hKa]; exact hPr
    have hKv : (K.atoms[i.val]! : WAtom).cachedValence = (Loc.branchK z pk kk).cachedValence := by
      rw [hKa, hKh]; rfl
    have hKi : (K.atoms[i.val]! : WAtom).cachedImplicit =
        (Loc.branchK z pk kk).cachedImplicit := by
      rw [hKa, hKh]
      simp only [branchRec, Loc.branchK, Loc.branchP]
      apply Loc.impl_congr
      · rfl
      · exact hbc
      · rfl
      · rfl
    have hKadj : (K.atoms[i.val]! : WAtom).adjustHs = (Loc.branchK z pk kk).adjustHs := by
      rw [hKa]
      change (P.atoms[i.val]! : WAtom).adjustHs = true
      rw [hPadj, hCar, hfa]
    have hKnI : (K.atoms[i.val]! : WAtom).noImplicit = false := by rw [hKa]; rfl
    have hKRa : (KR.atoms[i.val]! : WAtom) = K.atoms[i.val]! :=
      assignRadicals_atom_of_not_noImplicit K hKnI
    have hperc' : (S.kindsAt i).any (· == .aromatic) = true → 2 ≤ (S.kindsAt i).length ∧
        0 ≤ Loc.elec (Loc.branchK z pk kk) kk ∧ Loc.cand (Loc.branchK z pk kk) kk = true := by
      intro har
      obtain ⟨h1, h2, h3⟩ := hperc har
      rw [hKRa] at h2 h3
      exact ⟨h1, (Loc.elec_congr hKz hKc hKe hKi hKr hKv _) ▸ h2,
        (Loc.cand_congr hKz hKc hKe hKi hKr hKv _) ▸ h3⟩
    have h3 : pk.length ≤ 3 := (hcnt hfa).2
    have := Loc.branch_restore hz' (Loc.mem_lists 3 pk h3) (hcnt hfa).1 h3 hkk hmarks hperc'
    rw [Loc.restore_congr hKz hKc hKe hKn hKi hKadj]
    exact this

/-! ### Donor types, locally -/

/-- **A donor type other than `none` needs what `Loc.donorOk` asks**: a non-negative electron
count, and two or more electrons, a multiple bond, or (one electron) a multiple bond's worth of
valence or a positive charge. -/
lemma donorOk_of_donorType (w : Work) (rbs : List ℕ) (i : ℕ) (h : w.donorType rbs i ≠ .none) :
    Loc.donorOk w.atoms[i]! (w.kindsAt i) = true := by
  have hel := countAtomElec_eq_loc w i
  have hcv := cachedValence_eq_loc w i
  have hdeg := degree_eq_loc w i
  -- a negative count gives `none`
  have hne : 0 ≤ w.countAtomElec i := by
    by_contra hlt
    push Not at hlt
    apply h
    unfold donorType
    simp [Id.run, hlt]
    rfl
  by_cases hm : (w.kindsAt i).any isMultiple = true
  · unfold Loc.donorOk
    simp [← hel, hne, hm]
  have hnm : ∀ k ∈ w.bondsOf i, isMultiple (w.bonds[k]! : WBond).kind = false := by
    intro k hk
    by_contra hk'
    rw [Bool.not_eq_false] at hk'
    exact hm (List.any_eq_true.2 ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, hk'⟩)
  have hwho : w.exocyclicMultiple? rbs i = none := by
    unfold exocyclicMultiple?
    rw [Option.map_eq_none_iff, List.find?_eq_none]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    simp [hnm k hk]
  have hring' : ¬ ∃ x ∈ w.bondsOf i, x ∈ rbs ∧ isMultiple (w.bonds[x]! : WBond).kind = true := by
    rintro ⟨x, hx, -, hmx⟩
    rw [hnm x hx] at hmx
    cases hmx
  by_cases h2 : 2 ≤ w.countAtomElec i
  · unfold Loc.donorOk
    simp [← hel, hne, h2]
  by_cases h0 : w.countAtomElec i = 0
  · exfalso
    apply h
    unfold donorType
    simp [Id.run, hwho, hring', h0]
    rfl
  have h1 : w.countAtomElec i = 1 := by omega
  by_cases hc : w.cachedValence i ≠ w.degree i + (w.atoms[i]! : WAtom).explicitHs ∨
      (w.atoms[i]! : WAtom).charge = 1
  · unfold Loc.donorOk
    rw [← hel, ← hcv, ← hdeg]
    simp [h1, hc]
  · exfalso
    apply h
    push Not at hc
    unfold donorType
    simp [Id.run, hwho, h1, hc.1, hc.2]
    rfl

/-! ### What perception leaves at an atom, for reuse -/

lemma IsRing.of_sameSkel {w w' : Work} (h : SameSkel w' w) {c : List ℕ} (hc : w.IsRing c) :
    w'.IsRing c := by
  have hadj : w'.Adj = w.Adj := by
    funext u v
    simp only [Adj, h.neighbors]
  exact ⟨hc.nodup, hc.three, hadj ▸ hc.chain, hadj ▸ hc.close⟩

/-- **What perception leaves at an atom of the kekulized copy**: its bonds' kinds are a marking
of the Kekulé ones, it is aromatic exactly when one is marked, and if one is, it lies on a ring
(two bonds at least), passes the candidate test, has a donor type, and at two bonds has every
single or double bond marked. -/
theorem perceived_atom {n : ℕ} {m : Molecule n} {K : Work}
    (hK : (prepare m).kekulize (prepare m).relevantCycles = .ok K) (i : ℕ) :
    let S := K.assignRadicals.setAromaticity (prepare m).relevantCycles
    let KR := K.assignRadicals
    S.kindsAt i ∈ Loc.marks (K.kindsAt i) ∧
      S.isAromaticAtom i = (S.kindsAt i).any (· == .aromatic) ∧
      ((S.kindsAt i).any (· == .aromatic) = true →
        2 ≤ (S.kindsAt i).length ∧ 0 ≤ Loc.elec KR.atoms[i]! (K.kindsAt i) ∧
        Loc.cand KR.atoms[i]! (K.kindsAt i) = true ∧
        Loc.donorOk KR.atoms[i]! (K.kindsAt i) = true ∧
        ((S.kindsAt i).length = 2 →
          ((S.kindsAt i).zip (K.kindsAt i)).all fun sk ↦ sk.1 == .aromatic || !isSD sk.2) ∧
        ∃ rbs len, KR.isAromaticCandidate i (KR.ringDonor rbs len i) = true) := by
  intro S KR
  set P := prepare m with hP
  set R := P.relevantCycles with hR
  have hKP := kekulize_kindsRel hK
  have hna := kekulize_noArom hK
  have hsKP : SameSkel K P := hKP.sameSkel
  have hsKRK : SameSkel KR K := (afterRel_assignRadicals (w := K)).sameSkel
  have hsSKR : SameSkel S KR := (afterRel_setAromaticity KR R).sameSkel
  have hKRk : KR.kindsAt i = K.kindsAt i := by
    simp only [kindsAt, bondsOf, numBonds, KR, assignRadicals_bonds]
  have hkindS : ∀ k < KR.bonds.size, (S.bonds[k]! : WBond).kind =
      if k ∈ KR.aromaticBondList R ∧ isSD (KR.bonds[k]! : WBond).kind then .aromatic
      else (KR.bonds[k]! : WBond).kind := fun k hk ↦ by
    simp only [S, setAromaticity]
    exact kind_foldl_markAromatic KR _ k hk
  have hmarks : S.kindsAt i ∈ Loc.marks (K.kindsAt i) := by
    rw [← hKRk]
    refine Loc.mem_marks _ _ (kindsAt_forall₂ hsSKR (fun s k ↦ Loc.MarkRel k s) i
      fun k hk ↦ ?_).flip
    have hk' : k < KR.bonds.size := lt_of_mem_bondsOf hk
    change Loc.MarkRel (KR.bonds[k]! : WBond).kind (S.bonds[k]! : WBond).kind
    rw [hkindS k hk']
    unfold Loc.MarkRel
    split
    · rename_i h
      right
      refine ⟨rfl, ?_⟩
      simpa [isSD] using h.2
    · left; rfl
  have hKnoar : ∀ k : ℕ, (K.bonds[k]! : WBond).kind ≠ .aromatic := by
    intro k
    by_cases hk : k < K.bonds.size
    · rw [getElem!_pos K.bonds k hk]; exact hna.2 _ (Array.getElem_mem hk)
    · rw [getElem!_neg K.bonds k hk]; decide
  have hKRflag : ∀ j : ℕ, (KR.atoms[j]! : WAtom).aromatic = false := by
    intro j
    have e := congrArg WAtom.aromatic
      (getElem!_eq_of_map_radicals (getElem?_assignRadicals_atoms K) j)
    simp only at e
    rw [e]
    by_cases hj : j < K.atoms.size
    · rw [getElem!_pos K.atoms j hj]; exact hna.1 _ (Array.getElem_mem hj)
    · rw [getElem!_neg K.atoms j hj]; rfl
  have harS : S.isAromaticAtom i = (S.kindsAt i).any (· == .aromatic) := by
    rw [isAromaticAtom_eq_loc]
    cases hf : (S.atoms[i]! : WAtom).aromatic
    · rfl
    · obtain ⟨k, hk, hka⟩ := setAromaticity_flag KR R hKRflag i hf
      symm
      simp only [Bool.true_or, List.any_eq_true, beq_iff_eq]
      exact ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, hka⟩
  refine ⟨hmarks, harS, fun har ↦ ?_⟩
  simp only [List.any_eq_true, beq_iff_eq, kindsAt, List.mem_map] at har
  obtain ⟨_, ⟨k, hk, rfl⟩, hka⟩ := har
  have hkS : k < S.bonds.size := lt_of_mem_bondsOf hk
  have hkKR : k < KR.bonds.size := by simpa [hsSKR.numBonds] using lt_of_mem_bondsOf hk
  have h1 : S.kind? k = some .aromatic := by
    simp [kind?, Array.getElem?_eq_getElem hkS, ← getElem!_pos S.bonds k hkS, hka]
  have h0 : KR.kind? k ≠ some .aromatic := by
    have hb : KR.bonds = K.bonds := assignRadicals_bonds K
    have hkK : k < K.bonds.size := by rwa [← hb]
    simp only [kind?, hb, Array.getElem?_eq_getElem hkK, Option.map_some, ne_eq,
      Option.some.injEq]
    rw [← getElem!_pos K.bonds k hkK]
    exact hKnoar k
  have hmem := mem_aromaticBondList_of_kind? KR R h1 h0
  obtain ⟨_, ring, hring, hsrc, hdst, ⟨r₁, l₁, c₁⟩, ⟨r₂, l₂, c₂⟩⟩ :=
    of_kind?_setAromaticity_donor KR R h1 h0
  have ht := touches_of_mem_bondsOf hk
  rw [WBond.touches, hsSKR.src, hsSKR.dst, getElem!_pos KR.bonds k hkKR] at ht
  simp only [Bool.or_eq_true, beq_iff_eq] at ht
  have hcand : ∃ rbs len, KR.isAromaticCandidate i (KR.ringDonor rbs len i) = true := by
    rcases ht with ht | ht
    · exact ⟨r₁, l₁, ht ▸ c₁⟩
    · exact ⟨r₂, l₂, ht ▸ c₂⟩
  have hir : i ∈ ring := by rcases ht with ht | ht <;> [exact ht ▸ hsrc; exact ht ▸ hdst]
  obtain ⟨rbs, len, hc⟩ := hcand
  have hlS : (S.kindsAt i).length = (KR.bondsOf i).length := by
    simp only [kindsAt, List.length_map, hsSKR.bondsOf]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨rbs, len, hc⟩⟩
  · have hIs : P.IsRing ring := isRing_of_mem_relevantCycles P (by simpa [hR] using hring)
    obtain ⟨k₁, k₂, hne, -, -, hk₁, hk₂⟩ := hIs.two_bonds hir
    have := two_le_length_of_ne hne hk₁ hk₂
    have hl : (S.kindsAt i).length = (P.bondsOf i).length := by
      simp only [kindsAt, List.length_map, hsSKR.bondsOf, hsKRK.bondsOf, hsKP.bondsOf]
    omega
  · rw [← hKRk, ← countAtomElec_eq_loc]
    exact countAtomElec_nonneg_of_cand KR hc
  · rw [← hKRk, ← isAromaticCandidate_eq_loc KR i (isAromaticCandidate_donor_ne hc)]
    exact hc
  · rw [← hKRk]
    apply donorOk_of_donorType KR rbs i
    intro hd
    have hne := isAromaticCandidate_donor_ne hc
    apply hne
    unfold ringDonor
    simp [hd]
  · intro h2
    have hdeg : (KR.bondsOf i).length = 2 := by omega
    have hrings : ∀ r ∈ R.toList, KR.IsRing r := fun r hr ↦
      IsRing.of_sameSkel (hsKRK.trans hsKP)
        (isRing_of_mem_relevantCycles P (by simpa [hR] using hr))
    rw [← hKRk]
    unfold kindsAt
    rw [hsSKR.bondsOf, zip_map_map, List.all_map, List.all_eq_true]
    intro k' hk'
    have hk'lt : k' < KR.bonds.size := lt_of_mem_bondsOf hk'
    have hmem' := mem_aromaticBondList_deg2 KR R hrings hdeg (by rwa [← hsSKR.bondsOf]) hk' hmem
    simp only [Function.comp_apply, hkindS k' hk'lt]
    by_cases hsd : isSD (KR.bonds[k']! : WBond).kind = true
    · simp [hmem', hsd]
    · simp [hsd]

/-! ### Small facts for the witness -/

lemma order_sum_eq_bhs (ks : List BondKind) :
    (ks.map BondKind.order).sum = (Loc.bhs ks : ℚ) / 2 := by
  induction ks with
  | nil => simp [Loc.bhs]
  | cons k ks ih =>
    simp only [List.map_cons, List.sum_cons, ih, Loc.bhs, Nat.cast_add]
    cases k <;> simp [BondKind.order, halfOrder] <;> linarith

lemma bhs_even_of_noArom : ∀ {ks : List BondKind}, ks.any (· == .aromatic) = false →
    Loc.bhs ks % 2 = 0
  | [], _ => rfl
  | k :: ks, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have ih := bhs_even_of_noArom h.2
    simp only [Loc.bhs, List.map_cons, List.sum_cons] at ih ⊢
    cases k <;> simp_all [halfOrder] <;> omega

lemma donorOk_congr {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (hv : a.cachedValence = b.cachedValence) (ks : List BondKind) :
    Loc.donorOk a ks = Loc.donorOk b ks := by
  simp only [Loc.donorOk, Loc.elec_congr hz hc he hi hr hv, Loc.cv_congr he hv, he, hc]

lemma radicalCount_eq_loc (w : Work) (i : ℕ) :
    w.radicalCount i = Loc.radC (w.atoms[i]! : WAtom).z (w.atoms[i]! : WAtom).charge
      (w.bondHalfSum i / 2 + (w.atoms[i]! : WAtom).explicitHs) := rfl

/-- `assignRadicals` gives a bracketed atom its radical count. -/
lemma radicals_assignRadicals (w : Work) {i : ℕ} (hi : i < w.atoms.size)
    (hn : (w.atoms[i]! : WAtom).noImplicit = true) (hz : (w.atoms[i]! : WAtom).z ≠ 0) :
    (w.assignRadicals.atoms[i]! : WAtom).radicals = w.radicalCount i := by
  -- the steps at other atoms leave atom `i`, the bonds and the size alone
  have other : ∀ (l : List ℕ) (x : Work), i ∉ l →
      ((l.foldl radicalStep x).atoms[i]! : WAtom) = x.atoms[i]! ∧
        (l.foldl radicalStep x).bonds = x.bonds ∧
        (l.foldl radicalStep x).atoms.size = x.atoms.size := by
    intro l
    induction l with
    | nil => intro x _; exact ⟨rfl, rfl, rfl⟩
    | cons j l ih =>
      intro x hl
      rw [List.foldl_cons]
      have hj : j ≠ i := fun e ↦ hl (e ▸ List.mem_cons_self)
      obtain ⟨h1, h2, h3⟩ := ih (radicalStep x j) (fun h ↦ hl (List.mem_cons_of_mem _ h))
      refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
      · unfold radicalStep
        dsimp only
        split
        · rfl
        · exact modifyAtom_atom_of_ne x hj _
      · unfold radicalStep
        dsimp only
        split <;> rfl
      · unfold radicalStep
        dsimp only
        split
        · rfl
        · simp
  have hmem : i ∈ List.range w.numAtoms := List.mem_range.2 (by simpa [numAtoms] using hi)
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hmem
  have hnd : (l₁ ++ i :: l₂).Nodup := hl ▸ List.nodup_range
  have h1 : i ∉ l₁ := fun h ↦ (List.nodup_append.1 hnd).2.2 _ h _ List.mem_cons_self rfl
  have h2 : i ∉ l₂ := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  unfold assignRadicals
  rw [hl, List.foldl_append, List.foldl_cons]
  obtain ⟨a1, b1, c1⟩ := other l₁ w h1
  set x := l₁.foldl radicalStep w
  have hstep : ((radicalStep x i).atoms[i]! : WAtom).radicals = w.radicalCount i := by
    unfold radicalStep
    dsimp only
    have hcond : (!(x.atoms[i]! : WAtom).noImplicit || (x.atoms[i]! : WAtom).z == 0) = false := by
      rw [a1]; simp [hn, hz]
    rw [if_neg (by rw [hcond]; decide), modifyAtom_atom_self, if_pos (by rw [c1]; exact hi)]
    simp only [radicalCount_eq_loc, a1]
    simp only [bondHalfSum, bondsOf, numBonds, b1]
  obtain ⟨a2, -⟩ := other l₂ (radicalStep x i) h2
  rw [a2, hstep]

end LeanSMILES.Aromaticity.Work
