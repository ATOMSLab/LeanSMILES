/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeWalk
public import LeanSMILES.Aromaticity.RingFacts
public import LeanSMILES.Aromaticity.PerceiveAgree

/-!
# LeanSMILES.Aromaticity.KekulizeCompose

**Kekulization is correct over the whole molecule** (`Work.kekulize_correct`): when it succeeds,
there is a set `D` of bonds written aromatic such that every bond of `D` is double, every other
bond written aromatic is single, every other bond is as it was; `D` is a matching (no atom on two
of its bonds) of atoms that are aromatic and need a double bond, and every such atom is matched.

`kekulize` handles the fused ring systems one after another (`Work.kekulizeSystem`, correct by
`Work.kekulizeSystem_correct`).  They compose because an aromatic atom with at most three bonds
lies in at most one system (`Work.fusedSystems_spec`): a system only changes bonds at its own
aromatic atoms, and its double bonds join two of its own candidates.  Every aromatic atom lies in
some ring (else `kekulize` fails), hence in some system, so every bond written aromatic between
aromatic atoms ends up single or double.

## Main definitions

* `Work.kekWa`, `Work.kekEv0`: the bonds written aromatic and the explicit valences `kekulize`
  reads before it starts.
* `Work.candOf`: an atom that is aromatic and needs a double bond.
* `Work.SysInv`: what holds after the systems processed so far.
* `Work.CvOk`: what kekulization may leave as an atom's cached valence and written hydrogens.

## Main statements

* `Work.sysInv_step`, `Work.sysInv_foldlM`: `SysInv` survives one more system, and all of them.
* `Work.kekulize_correct`: kekulization places a matching of double bonds covering every
  candidate, makes the other bonds written aromatic single, and keeps the rest.
* `Work.kekulize_cvOk`: what kekulization caches at an atom.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-- The bonds `kekulize` treats as written aromatic. -/
def kekWa (m : Work) (k : ℕ) : Bool :=
  ((List.range m.numBonds).filter (m.bonds[·]!.kind == .aromatic)).contains k

/-- A bond is treated as written aromatic exactly when it is in range and its kind is aromatic. -/
lemma kekWa_iff {m : Work} {k : ℕ} :
    m.kekWa k = true ↔ k < m.bonds.size ∧ (m.bonds[k]! : WBond).kind = .aromatic := by
  simp [kekWa, numBonds]

/-- The explicit valences `kekulize` reads before it starts. -/
def kekEv0 (m : Work) : List ℕ := (List.range m.numAtoms).map m.explicitValence

/-- `needsDoubleBond` reads the bonds only through their ends and the kinds of those not written
aromatic. -/
lemma needsDoubleBond_congr {m w : Work} {wa : ℕ → Bool} {e i : ℕ} (ha : w.atoms = m.atoms)
    (hb : ∀ j, w.bondsOf j = m.bondsOf j)
    (hk : ∀ k, ¬ wa k = true → (w.bonds[k]! : WBond).kind = (m.bonds[k]! : WBond).kind) :
    w.needsDoubleBond wa e i = m.needsDoubleBond wa e i := by
  have hfun : ∀ k, (if wa k = true then 1 else (halfOrder (w.bonds[k]! : WBond).kind + 1) / 2) =
      (if wa k = true then 1 else (halfOrder (m.bonds[k]! : WBond).kind + 1) / 2) := by
    intro k
    split
    · rfl
    · rename_i h; rw [hk k h]
  unfold needsDoubleBond degree
  simp only [ha, hb, hfun]

section Compose

variable (m : Work) (wa : ℕ → Bool) (ev0 : List ℕ)

/-- An atom that is aromatic and needs a double bond, read on `m`. -/
def candOf (x : ℕ) : Bool := (m.atoms[x]! : WAtom).aromatic && m.needsDoubleBond wa ev0[x]! x

open Classical in
/-- After the systems whose atoms `P` collects: bonds of `D` are double, other bonds written
aromatic at an aromatic atom of `P` are single, the rest are as in `m`; `D` is a matching of
candidates of `P` covering them. -/
structure SysInv (P : ℕ → Prop) (out : Work) (D : ℕ → Bool) : Prop where
  /-- The atoms are those of `m`. -/
  atoms : out.atoms = m.atoms
  /-- The bonds join the same atoms as in `m`. -/
  skel : SameSkel m out
  /-- Bonds of `D` are double, other bonds written aromatic at an aromatic atom of `P` single,
  the rest as in `m`. -/
  kinds : ∀ k, (out.bonds[k]! : WBond).kind = if D k = true then .double else
    if wa k = true ∧ ∃ x, P x ∧ (m.atoms[x]! : WAtom).aromatic = true ∧ k ∈ m.bondsOf x
    then .single else (m.bonds[k]! : WBond).kind
  /-- A bond of `D` is in range, written aromatic, and joins candidates of `P`. -/
  dOk : ∀ k, D k = true → k < m.bonds.size ∧ wa k = true ∧
    ∀ x, (m.bonds[k]! : WBond).touches x = true → P x ∧ candOf m wa ev0 x = true
  /-- No atom lies on two bonds of `D`. -/
  matching : ∀ k₁ k₂ x, D k₁ = true → D k₂ = true → (m.bonds[k₁]! : WBond).touches x = true →
    (m.bonds[k₂]! : WBond).touches x = true → k₁ = k₂
  /-- Every candidate of `P` in range lies on a bond of `D`. -/
  cover : ∀ x, P x → candOf m wa ev0 x = true → x < m.atoms.size →
    ∃ k, D k = true ∧ (m.bonds[k]! : WBond).touches x = true

variable {m wa ev0}

/-- Before any system: `m` itself, with no atoms collected and no bonds in `D`. -/
lemma sysInv_start :SysInv m wa ev0 (fun _ ↦ False) m (fun _ ↦ false) where
  atoms := rfl
  skel := SameSkel.refl m
  kinds k := by simp
  dOk k h := by cases h
  matching _ _ _ h := by cases h
  cover _ h := h.elim

/-- The kinds of bonds not written aromatic are those of `m`. -/
lemma SysInv.kind_of_not_wa {P : ℕ → Prop} {out : Work} {D : ℕ → Bool}
    (hi : SysInv m wa ev0 P out D) {k : ℕ} (hk : ¬ wa k = true) :
    (out.bonds[k]! : WBond).kind = (m.bonds[k]! : WBond).kind := by
  rw [hi.kinds k, if_neg, if_neg]
  · exact fun h ↦ hk h.1
  · exact fun h ↦ hk (hi.dOk k h).2.1

/-- **One more system.** -/
lemma sysInv_step (hwf : WF m) (hnd : m.NbrsDistinct) {rings : Array (List ℕ)}
    {P : ℕ → Prop} {out w : Work} {D : ℕ → Bool} (hi : SysInv m wa ev0 P out D) {C : List ℕ}
    (huniq : ∀ x, P x → x ∈ systemAtoms rings C → (m.atoms[x]! : WAtom).aromatic = true →
      (∃ k ∈ m.bondsOf x, wa k = true) → False)
    (hw : kekulizeSystem wa ev0 rings out C = .ok w) :
    ∃ D', SysInv m wa ev0 (fun x ↦ P x ∨ x ∈ systemAtoms rings C) w D' := by
  obtain ⟨hatoms, hskel, DS, hkS, hdS, hmS, hcS⟩ :=
    kekulizeSystem_correct (hi.skel.wf hwf) (hi.skel.nbrsDistinct hnd) hw
  have hbo : ∀ j, out.bondsOf j = m.bondsOf j := fun j ↦ by rw [hi.skel.bondsOf]
  have htch : ∀ k x, (out.bonds[k]! : WBond).touches x = (m.bonds[k]! : WBond).touches x :=
    fun k x ↦ (hi.skel.touches k x).symm
  have hcand : ∀ x, ((out.atoms[x]! : WAtom).aromatic && out.needsDoubleBond wa ev0[x]! x) =
      candOf m wa ev0 x := by
    intro x
    rw [candOf, hi.atoms, needsDoubleBond_congr hi.atoms hbo (fun k hk ↦ hi.kind_of_not_wa hk)]
  have hsz : out.bonds.size = m.bonds.size := hi.skel.numBonds.symm
  have hasz : out.atoms.size = m.atoms.size := by rw [hi.atoms]
  -- a bond of `D` touches no aromatic atom of the new system
  have hDA : ∀ k x, D k = true → (m.bonds[k]! : WBond).touches x = true →
      x ∈ systemAtoms rings C → False := by
    intro k x hk ht hx
    obtain ⟨hp, hc⟩ := (hi.dOk k hk).2.2 x ht
    simp only [candOf, Bool.and_eq_true] at hc
    refine huniq x hp hx hc.1 ⟨k, ?_, (hi.dOk k hk).2.1⟩
    simp only [bondsOf, List.mem_filter, List.mem_range, numBonds]
    exact ⟨(hi.dOk k hk).1, ht⟩
  refine ⟨fun k ↦ D k || DS[k]!, ⟨hatoms.trans hi.atoms, hi.skel.trans hskel, fun k ↦ ?_,
    fun k hk ↦ ?_, fun k₁ k₂ x h₁ h₂ t₁ t₂ ↦ ?_, fun x hx hc hlt ↦ ?_⟩⟩
  · -- kinds
    rw [hkS k]
    by_cases hS : DS[k]! = true
    · simp [hS]
    have hS' : DS[k]! = false := by simpa using hS
    simp only [hS', Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    split
    · rename_i hA
      obtain ⟨x, hx, hxa, hxk, hwk⟩ := hA
      have hx' : x ∈ systemAtoms rings C := hx
      rw [hi.atoms] at hxa
      rw [hbo] at hxk
      have hD : D k = false := by
        by_contra hD
        exact hDA k x (by simpa using hD) (touches_of_mem_bondsOf hxk) hx'
      rw [if_neg (by simp [hD]), if_pos ⟨hwk, x, .inr hx', hxa, hxk⟩]
    · rename_i hA
      rw [hi.kinds k]
      have hc : (wa k = true ∧ ∃ x, P x ∧ (m.atoms[x]! : WAtom).aromatic = true ∧
          k ∈ m.bondsOf x) ↔ (wa k = true ∧ ∃ x, (P x ∨ x ∈ systemAtoms rings C) ∧
          (m.atoms[x]! : WAtom).aromatic = true ∧ k ∈ m.bondsOf x) := by
        constructor
        · rintro ⟨hwk, x, hx, hxa, hxk⟩
          exact ⟨hwk, x, .inl hx, hxa, hxk⟩
        · rintro ⟨hwk, x, hx | hx, hxa, hxk⟩
          · exact ⟨hwk, x, hx, hxa, hxk⟩
          · exact absurd ⟨x, hx, by rw [hi.atoms]; exact hxa, by rw [hbo]; exact hxk, hwk⟩ hA
      by_cases hco : wa k = true ∧ ∃ x, P x ∧ (m.atoms[x]! : WAtom).aromatic = true ∧
          k ∈ m.bondsOf x
      · rw [if_pos hco, if_pos (hc.1 hco)]
      · rw [if_neg hco, if_neg (fun h ↦ hco (hc.2 h))]
  · -- dOk
    rcases Bool.or_eq_true_iff.1 hk with hk | hk
    · obtain ⟨h1, h2, h3⟩ := hi.dOk k hk
      exact ⟨h1, h2, fun x hx ↦ ⟨.inl (h3 x hx).1, (h3 x hx).2⟩⟩
    · obtain ⟨h1, h2, h3⟩ := hdS k hk
      refine ⟨hsz ▸ h1, h2, fun x hx ↦ ?_⟩
      obtain ⟨h4, h5⟩ := h3 x (by rw [htch]; exact hx)
      exact ⟨.inr h4, by rw [← hcand]; exact h5⟩
  · -- matching
    rcases Bool.or_eq_true_iff.1 h₁ with h₁ | h₁ <;> rcases Bool.or_eq_true_iff.1 h₂ with h₂ | h₂
    · exact hi.matching k₁ k₂ x h₁ h₂ t₁ t₂
    · exact (hDA k₁ x h₁ t₁ ((hdS k₂ h₂).2.2 x (by rw [htch]; exact t₂)).1).elim
    · exact (hDA k₂ x h₂ t₂ ((hdS k₁ h₁).2.2 x (by rw [htch]; exact t₁)).1).elim
    · exact hmS k₁ k₂ x h₁ h₂ (by rw [htch]; exact t₁) (by rw [htch]; exact t₂)
  · -- cover
    rcases hx with hx | hx
    · obtain ⟨k, hk, ht⟩ := hi.cover x hx hc hlt
      exact ⟨k, by simp [hk], ht⟩
    · obtain ⟨k, hk, ht⟩ := hcS x hx (by beta_reduce; rw [hcand]; exact hc) (hasz ▸ hlt)
      exact ⟨k, by simp [hk], by rw [← htch]; exact ht⟩

/-- **All the systems**, an aromatic atom with a bond written aromatic having at most three bonds,
so being in at most one. -/
lemma sysInv_foldlM (hwf : WF m) (hnd : m.NbrsDistinct) {rings : Array (List ℕ)}
    (hdeg : ∀ x, (m.atoms[x]! : WAtom).aromatic = true → (∃ k ∈ m.bondsOf x, wa k = true) →
      (m.bondsOf x).length ≤ 3) :
    ∀ (l : List (List ℕ)) (P : ℕ → Prop) (out w : Work) (D : ℕ → Bool),
      l.Pairwise (fun C E ↦ ∀ x, x ∈ systemAtoms rings C → x ∈ systemAtoms rings E →
        3 < (m.bondsOf x).length) →
      (∀ C ∈ l, ∀ x, P x → x ∈ systemAtoms rings C → 3 < (m.bondsOf x).length) →
      SysInv m wa ev0 P out D → l.foldlM (kekulizeSystem wa ev0 rings) out = .ok w →
      ∃ D', SysInv m wa ev0 (fun x ↦ P x ∨ ∃ C ∈ l, x ∈ systemAtoms rings C) w D'
  | [], P, out, w, D, _, _, hi, hw => by
    cases hw
    have : (fun x ↦ P x ∨ ∃ C ∈ ([] : List (List ℕ)), x ∈ systemAtoms rings C) = P := by
      funext x; simp
    rw [this]
    exact ⟨D, hi⟩
  | C :: l, P, out, w, D, hpw, hP, hi, hw => by
    rw [List.foldlM_cons] at hw
    cases hx : kekulizeSystem wa ev0 rings out C with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      obtain ⟨D₁, h₁⟩ := sysInv_step hwf hnd hi
        (fun x hp hxC ha hk ↦ by
          have := hP C List.mem_cons_self x hp hxC; have := hdeg x ha hk; omega)
        hx
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.1 hpw
      obtain ⟨D₂, h₂⟩ := sysInv_foldlM hwf hnd hdeg l _ v w D₁ htail
        (fun E hE x hx hxE ↦ by
          rcases hx with hx | hx
          · exact hP E (List.mem_cons_of_mem _ hE) x hx hxE
          · exact hhead E hE x hx hxE) h₁ hw
      have : (fun x ↦ (P x ∨ x ∈ systemAtoms rings C) ∨ ∃ E ∈ l, x ∈ systemAtoms rings E) =
          (fun x ↦ P x ∨ ∃ E ∈ C :: l, x ∈ systemAtoms rings E) := by
        funext x
        simp only [List.mem_cons, exists_eq_or_imp, eq_iff_iff]
        tauto
      rw [this] at h₂
      exact ⟨D₂, h₂⟩

end Compose

/-- An aromatic atom's flag read with `!`, through `?`. -/
lemma aromatic_getElem! (a : Array WAtom) (i : ℕ) :
    (a[i]! : WAtom).aromatic = ((a[i]?.map (·.aromatic)).getD false) := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, Array.getElem?_eq_getElem h]; rfl
  · rw [getElem!_neg a i h, Array.getElem?_eq_none (by omega)]; rfl

/-- `clearAromatic` succeeds only if every aromatic atom it meets is a ring atom. -/
lemma foldlM_clearAromatic_ring {ra : List ℕ} :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ra) w = .ok w' →
      ∀ i ∈ l, (w.atoms[i]! : WAtom).aromatic = true → i ∈ ra
  | [], _, _, _ => by simp
  | x :: l, w, w', hw => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ra w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      intro i hi ha
      by_cases hix : i = x
      · subst hix
        unfold clearAromatic at hx
        dsimp only at hx
        rw [if_neg (by simp [ha])] at hx
        split at hx
        · cases hx
        · rename_i hc
          simpa using hc
      · have hil : i ∈ l := by
          rcases List.mem_cons.1 hi with h | h
          · exact absurd h hix
          · exact h
        apply foldlM_clearAromatic_ring l v w' hw i hil
        rw [aromatic_getElem!] at ha ⊢
        rw [(clearAromatic_spec hx).2.1 i hix]
        exact ha

/-- `clearAromatic` keeps the bonds. -/
lemma foldlM_clearAromatic_bonds {ra : List ℕ} (l : List ℕ) {w w' : Work}
    (hw : l.foldlM (clearAromatic ra) w = .ok w') : w'.bonds = w.bonds :=
  foldlM_except_of (fun v ↦ v.bonds = w.bonds) _
    (fun _ _ _ hq hx ↦ clearAromatic_m (Q := fun v ↦ v.bonds = w.bonds)
      (fun _ _ _ _ h ↦ h) hq hx) l w w' rfl hw

/-- **Kekulization is correct** on a copy whose rings are cycles, whose aromatic atoms have at
most three bonds, and whose bonds written aromatic start at an aromatic atom: there is a set `D`
of bonds written aromatic, double, the other bonds written aromatic single, the rest unchanged;
`D` is a matching of atoms that are aromatic and need a double bond, covering every such atom. -/
theorem kekulize_correct {m K : Work} {rings : Array (List ℕ)} (hwf : WF m)
    (hnd : m.NbrsDistinct) (hr : ∀ ring ∈ rings, m.IsRing ring)
    (hdeg : ∀ x, (m.atoms[x]! : WAtom).aromatic = true → (∃ k ∈ m.bondsOf x, m.kekWa k = true) →
      (m.bondsOf x).length ≤ 3)
    (hK : m.kekulize rings = .ok K) :
    ∃ D : ℕ → Bool,
      (∀ k, (K.bonds[k]! : WBond).kind = if D k = true then .double else
        if m.kekWa k = true then .single else (m.bonds[k]! : WBond).kind) ∧
      (∀ k, D k = true → k < m.bonds.size ∧ m.kekWa k = true ∧
        ∀ x, (m.bonds[k]! : WBond).touches x = true → candOf m m.kekWa m.kekEv0 x = true) ∧
      (∀ k₁ k₂ x, D k₁ = true → D k₂ = true → (m.bonds[k₁]! : WBond).touches x = true →
        (m.bonds[k₂]! : WBond).touches x = true → k₁ = k₂) ∧
      ∀ x < m.atoms.size, candOf m m.kekWa m.kekEv0 x = true →
        ∃ k, D k = true ∧ (m.bonds[k]! : WBond).touches x = true := by
  unfold kekulize at hK
  dsimp only at hK
  split at hK
  · -- nothing aromatic
    rename_i hnone
    cases hK
    rw [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at hnone
    have hwa : ∀ k, m.kekWa k = false := by
      intro k
      simp only [kekWa, hnone.1, List.contains_nil]
    have harom : ∀ x : ℕ, (m.atoms[x]! : WAtom).aromatic = false := by
      intro x
      rw [aromatic_getElem!]
      cases hx : m.atoms[x]? with
      | none => rfl
      | some a =>
        have := hnone.2
        rw [Array.any_eq_false] at this
        obtain ⟨hlt, e⟩ := Array.getElem?_eq_some_iff.1 hx
        have := this x hlt
        simp only [e] at this
        simpa using this
    refine ⟨fun _ ↦ false, fun k ↦ (by simp [hwa k]), fun k h ↦ (by cases h),
      fun _ _ _ h ↦ (by cases h), fun x _ hc ↦ ?_⟩
    simp [candOf, harom x] at hc
  · simp only [pure, Except.pure, bind, Except.bind] at hK
    split at hK
    · cases hK
    · rename_i out1 h1
      split at hK
      · cases hK
      · rename_i out2 h2
        split at hK
        · cases hK
        · rename_i hleft
          cases hK
          obtain ⟨hcov, hpw⟩ := fusedSystems_spec m hr
          obtain ⟨D, hi⟩ := sysInv_foldlM (wa := m.kekWa) (ev0 := m.kekEv0) hwf hnd hdeg
            (components rings.size (m.kekFusedNbrs rings)) (fun _ ↦ False) m out1
            (fun _ ↦ false) (hpw.imp fun h x h1 h2 ↦ h x h1 h2) (by simp) sysInv_start
            (by exact h1)
          have hb := foldlM_clearAromatic_bonds _ h2
          have hring := foldlM_clearAromatic_ring _ _ _ h2
          rw [hi.atoms] at hring
          -- every aromatic atom is in a system
          have hP : ∀ x, (m.atoms[x]! : WAtom).aromatic = true →
              False ∨ ∃ C ∈ components rings.size (m.kekFusedNbrs rings),
                x ∈ systemAtoms rings C := by
            intro x hx
            have hxs : x < m.atoms.size := by
              by_contra h'
              rw [getElem!_neg m.atoms x h'] at hx
              cases hx
            have hxr := hring x (List.mem_range.2 (by
              rw [numAtoms, hi.atoms]; exact hxs)) hx
            rw [List.mem_eraseDups, List.mem_flatten] at hxr
            obtain ⟨ring, hring', hxring⟩ := hxr
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hring'
            have hj' : j < rings.size := by simpa using hj
            obtain ⟨C, hC, hxC⟩ := hcov j hj' x (by
              rw [getElem!_pos rings j hj']
              simpa using hxring)
            exact .inr ⟨C, hC, hxC⟩
          refine ⟨D, fun k ↦ ?_, fun k hk ↦ ?_, hi.matching, fun x hx hc ↦ ?_⟩
          · rw [hb, hi.kinds k]
            by_cases hD : D k = true
            · simp [hD]
            rw [if_neg hD, if_neg hD]
            by_cases hw : m.kekWa k = true
            · rw [if_pos hw]
              split
              · rfl
              · -- a bond written aromatic not made single would be left aromatic
                rename_i hno
                exfalso
                obtain ⟨hk, hka⟩ := kekWa_iff.1 hw
                have hko : (out1.bonds[k]! : WBond).kind = .aromatic := by
                  rw [hi.kinds k, if_neg hD, if_neg hno, hka]
                apply hleft
                rw [hb, Array.any_eq_true]
                have hk1 : k < out1.bonds.size := by
                  have := hi.skel.numBonds; simp only [numBonds] at this; omega
                exact ⟨k, hk1, by rw [← getElem!_pos out1.bonds k hk1, hko]; rfl⟩
            · rw [if_neg hw, if_neg (fun h ↦ hw h.1)]
          · obtain ⟨h1, h2, h3⟩ := hi.dOk k hk
            exact ⟨h1, h2, fun x hx ↦ (h3 x hx).2⟩
          · have ha : (m.atoms[x]! : WAtom).aromatic = true := by
              simp only [candOf, Bool.and_eq_true] at hc
              exact hc.1
            exact hi.cover x (hP x ha) hc hx

/-! ### What kekulization caches at an atom -/

/-- Atom `i` keeps the cached valence `cv` and written hydrogens `e`, or (the nitrogen and
phosphorus case of `clearAromatic`) has no written hydrogens and the Kekulé bond-order sum as
cached valence. -/
def CvOk (w : Work) (i : ℕ) (cv : Option ℕ) (e : ℕ) : Prop :=
  ((w.atoms[i]! : WAtom).cachedValence = cv ∧ (w.atoms[i]! : WAtom).explicitHs = e) ∨
    ((w.atoms[i]! : WAtom).explicitHs = 0 ∧
      (w.atoms[i]! : WAtom).cachedValence = some (w.bondHalfSum i / 2))

/-- Folding `halfOrder` over the bonds `l` from `s` adds their half-order sum to `s`. -/
lemma foldl_halfOrder (w : Work) (l : List ℕ) (s : ℕ) :
    l.foldl (fun s k ↦ s + halfOrder (w.bonds[k]! : WBond).kind) s =
      s + (l.map fun k ↦ halfOrder (w.bonds[k]! : WBond).kind).sum := by
  induction l generalizing s with
  | nil => simp
  | cons k l ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

/-- `bondHalfSum` depends only on the bonds. -/
lemma bondHalfSum_congr {w w' : Work} (h : w'.bonds = w.bonds) :
    w'.bondHalfSum = w.bondHalfSum := by
  funext i
  simp only [bondHalfSum, bondsOf, numBonds, h]

/-- `CvOk` at atom `i` carries over to a copy with the same bonds and the same record at `i`. -/
lemma CvOk.of_atom {w w' : Work} {i : ℕ} {cv : Option ℕ} {e : ℕ} (hb : w'.bonds = w.bonds)
    (ha : (w'.atoms[i]! : WAtom) = (w.atoms[i]! : WAtom)) (h : CvOk w i cv e) :
    CvOk w' i cv e := by
  unfold CvOk
  rw [ha, bondHalfSum_congr hb]
  exact h

/-- One successful `clearAromatic` step keeps the bonds and keeps `CvOk` at atom `i`. -/
lemma clearAromatic_cvOk {ra : List ℕ} {w w' : Work} {j : ℕ} (hw : clearAromatic ra w j = .ok w')
    (i : ℕ) {cv : Option ℕ} {e : ℕ} (h : CvOk w i cv e) :
    w'.bonds = w.bonds ∧ CvOk w' i cv e := by
  unfold clearAromatic at hw
  dsimp only at hw
  split at hw
  · cases hw; exact ⟨rfl, h⟩
  split at hw
  · cases hw
  split at hw
  · cases hw
    refine ⟨rfl, ?_⟩
    by_cases hji : j = i
    · subst hji
      by_cases hjs : j < w.atoms.size
      · right
        rw [modifyAtom_atom_self, if_pos (by simpa [modifyAtom] using hjs), modifyAtom_atom_self,
          if_pos hjs]
        refine ⟨rfl, ?_⟩
        simp only [Option.some.injEq]
        rw [foldl_halfOrder, Nat.zero_add, bondHalfSum_congr (by rfl)]
        rfl
      · refine CvOk.of_atom (w := w) rfl ?_ h
        rw [modifyAtom_atom_self, if_neg (by simpa [modifyAtom] using hjs), modifyAtom_atom_self,
          if_neg hjs]
    · refine CvOk.of_atom (w := w) rfl ?_ h
      rw [modifyAtom_atom_of_ne _ hji, modifyAtom_atom_of_ne _ hji]
  · cases hw
    refine ⟨rfl, ?_⟩
    by_cases hji : j = i
    · subst hji
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        rw [modifyAtom_atom_self]
        split <;> exact ⟨h1, h2⟩
      · right
        rw [modifyAtom_atom_self, bondHalfSum_congr (w' := w.modifyAtom j _) rfl]
        split <;> exact ⟨h1, h2⟩
    · refine CvOk.of_atom (w := w) rfl ?_ h
      rw [modifyAtom_atom_of_ne _ hji]

/-- A successful run of `clearAromatic` over the atoms `l` keeps `CvOk` at atom `i`. -/
lemma foldlM_clearAromatic_cvOk {ra : List ℕ} (i : ℕ) {cv : Option ℕ} {e : ℕ} :
    ∀ (l : List ℕ) (w w' : Work), l.foldlM (clearAromatic ra) w = .ok w' → CvOk w i cv e →
      CvOk w' i cv e
  | [], w, w', hw, h => by cases hw; exact h
  | x :: l, w, w', hw, h => by
    rw [List.foldlM_cons] at hw
    cases hx : clearAromatic ra w x with
    | error e => rw [hx] at hw; cases hw
    | ok v =>
      rw [hx] at hw
      exact foldlM_clearAromatic_cvOk i l v w' hw (clearAromatic_cvOk hx i h).2

/-- **What kekulization caches at an atom**: the cached valence and written hydrogens it had, or
none written and the Kekulé bond-order sum. -/
theorem kekulize_cvOk {m K : Work} {rings : Array (List ℕ)} (hK : m.kekulize rings = .ok K)
    (i : ℕ) : CvOk K i (m.atoms[i]! : WAtom).cachedValence (m.atoms[i]! : WAtom).explicitHs := by
  unfold kekulize at hK
  dsimp only at hK
  split at hK
  · cases hK; exact .inl ⟨rfl, rfl⟩
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
          refine foldlM_clearAromatic_cvOk i _ _ _ h2 (.inl ?_)
          simp only at q1
          rw [q1]
          exact ⟨rfl, rfl⟩

end LeanSMILES.Aromaticity.Work
