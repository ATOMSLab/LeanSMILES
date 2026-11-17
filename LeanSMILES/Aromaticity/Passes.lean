/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Perceive

/-!
# LeanSMILES.Aromaticity.Passes

What each pass of `Molecule.aromatize` changes in the working copy, and what it leaves alone:
the facts `LeanSMILES.Aromaticity.Invariance` needs.

* `cleanUp` only sets bond kinds to single or double and changes charges, and every change it
  makes charges an atom that was neutral (`Work.cleanUp_eq_self_of_charge`): when the charges come
  out as they went in, it did nothing.
* kekulization returns a working copy with nothing aromatic unchanged (`Work.kekulize_of_noArom`).
* the passes after kekulization keep every charge and every bond's endpoints, and change a bond
  kind only to aromatic.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-- A property kept by every step of a left fold holds of its result. -/
theorem foldl_induction {α β : Type*} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h, _ => h
  | a :: l, b, h, hf =>
    foldl_induction P f l (f b a) (hf b a List.mem_cons_self h)
      fun b' a' ha' hb' ↦ hf b' a' (List.mem_cons_of_mem _ ha') hb'

/-- A relation that is reflexive and transitive, and that every step of a left fold takes its
input to its output in, takes the fold's input to its output. -/
theorem foldl_rel {α β : Type*} (R : β → β → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c) (f : β → α → β) (l : List α) (b : β)
    (hf : ∀ b' a, a ∈ l → R b b' → R b' (f b' a)) : R b (l.foldl f b) :=
  foldl_induction (R b) f l b (hrefl b) fun b' a ha h ↦ htrans _ _ _ h (hf b' a ha h)

namespace Work

variable (w : Work)

/-! ### Reading and writing the working copy -/

/-- The charge of atom `j`, if there is an atom `j`. -/
def charge? (j : ℕ) : Option ℤ := w.atoms[j]?.map (·.charge)

/-- The kind of bond `k`, if there is a bond `k`. -/
def kind? (k : ℕ) : Option BondKind := w.bonds[k]?.map (·.kind)

@[simp] lemma setKind_atoms (k : ℕ) (o : BondKind) : (w.setKind k o).atoms = w.atoms := rfl

@[simp] lemma modifyAtom_bonds (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).bonds = w.bonds := rfl

@[simp] lemma size_setKind_bonds (k : ℕ) (o : BondKind) :
    (w.setKind k o).bonds.size = w.bonds.size := by simp [setKind]

@[simp] lemma size_modifyAtom_atoms (i : ℕ) (f : WAtom → WAtom) :
    (w.modifyAtom i f).atoms.size = w.atoms.size := by simp [modifyAtom]

lemma getElem?_setKind_bonds (k : ℕ) (o : BondKind) (j : ℕ) :
    (w.setKind k o).bonds[j]? =
      if k = j then w.bonds[j]?.map ({ · with kind := o }) else w.bonds[j]? := by
  simp [setKind, Array.getElem?_modify]

lemma getElem?_modifyAtom_atoms (i : ℕ) (f : WAtom → WAtom) (j : ℕ) :
    (w.modifyAtom i f).atoms[j]? = if i = j then w.atoms[j]?.map f else w.atoms[j]? := by
  simp [modifyAtom, Array.getElem?_modify]

@[simp] lemma charge?_setKind (k : ℕ) (o : BondKind) : (w.setKind k o).charge? = w.charge? := rfl

lemma charge?_modifyAtom_charge (i : ℕ) (c : ℤ) (j : ℕ) :
    (w.modifyAtom i ({ · with charge := c })).charge? j =
      if i = j then (w.charge? j).map fun _ ↦ c else w.charge? j := by
  unfold charge?
  rw [getElem?_modifyAtom_atoms]
  split <;> simp [Option.map_map, Function.comp_def]

/-- An atom read with `!` whose element is set is in range: out of range it would read as the
default atom, of atomic number `0`. -/
lemma lt_size_of_z_ne_zero {j : ℕ} (h : w.atoms[j]!.z ≠ 0) : j < w.atoms.size := by
  by_contra hj
  exact h (by simp [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt hj)]; rfl)

/-- In range, `!` reads the atom. -/
lemma charge?_eq_of_lt {j : ℕ} (h : j < w.atoms.size) : w.charge? j = some w.atoms[j]!.charge := by
  simp [charge?, getElem!_def, Array.getElem?_eq_getElem h]

/-! ### `cleanUp` -/

/-- How `cleanUp` may change `o` into `w`: the same atoms but for charges, each charge either
`o`'s or nonzero; the same bonds but for kinds, each kind either `o`'s or single or double. -/
structure CleanRel (o w : Work) : Prop where
  /-- As many atoms. -/
  atoms_size : w.atoms.size = o.atoms.size
  /-- As many bonds. -/
  bonds_size : w.bonds.size = o.bonds.size
  /-- The atoms but for their charges. -/
  atoms : ∀ j : ℕ, w.atoms[j]?.map (fun a : WAtom ↦ { a with charge := 0 }) =
    o.atoms[j]?.map (fun a : WAtom ↦ { a with charge := 0 })
  /-- The bonds but for their kinds. -/
  bonds : ∀ k : ℕ, w.bonds[k]?.map (fun b : WBond ↦ { b with kind := .single }) =
    o.bonds[k]?.map (fun b : WBond ↦ { b with kind := .single })
  /-- Every charge is `o`'s, or nonzero. -/
  charge : ∀ (j : ℕ) (c : ℤ), w.charge? j = some c → c ≠ 0 ∨ o.charge? j = some c
  /-- Every kind is `o`'s, or single, or double. -/
  kind : ∀ (k : ℕ) (t : BondKind), w.kind? k = some t → t = .single ∨ t = .double ∨ o.kind? k = some t

/-- Some atom neutral in `o` is charged in `w`. -/
def Charged (o w : Work) : Prop := ∃ j c, o.charge? j = some 0 ∧ w.charge? j = some c ∧ c ≠ 0

/-- One `cleanUp` rewrite or several: `w` is `o`, or `o` changed as `cleanUp` changes it and with
some neutral atom charged. -/
def CleanStep (o w : Work) : Prop := CleanRel o w ∧ (w = o ∨ Charged o w)

lemma CleanRel.refl (o : Work) : CleanRel o o :=
  ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ _ h ↦ .inr h, fun _ _ h ↦ .inr (.inr h)⟩

lemma CleanRel.trans {o w w' : Work} (h : CleanRel o w) (h' : CleanRel w w') : CleanRel o w' where
  atoms_size := h'.atoms_size.trans h.atoms_size
  bonds_size := h'.bonds_size.trans h.bonds_size
  atoms j := (h'.atoms j).trans (h.atoms j)
  bonds k := (h'.bonds k).trans (h.bonds k)
  charge j c hc := (h'.charge j c hc).elim .inl fun hc' ↦ h.charge j c hc'
  kind k t ht := (h'.kind k t ht).elim .inl fun ht' ↦
    ht'.elim (fun h1 ↦ .inr (.inl h1)) fun ht'' ↦ h.kind k t ht''

lemma charge?_isSome_iff (j : ℕ) : (w.charge? j).isSome ↔ j < w.atoms.size := by
  simp [charge?]

lemma Charged.of_cleanRel {o w w' : Work} (h : Charged o w) (h' : CleanRel w w') :
    Charged o w' := by
  obtain ⟨j, c, ho, hw, hc⟩ := h
  obtain ⟨c', hc'⟩ : ∃ c', w'.charge? j = some c' := Option.isSome_iff_exists.mp <| by
    rw [charge?_isSome_iff, h'.atoms_size, ← charge?_isSome_iff, hw]; rfl
  refine ⟨j, c', ho, hc', ?_⟩
  rcases h'.charge j c' hc' with h1 | h1
  · exact h1
  · rw [hw] at h1; cases h1; exact hc

lemma Charged.of_cleanRel_left {o w w' : Work} (h : CleanRel o w) (h' : Charged w w') :
    Charged o w' := by
  obtain ⟨j, c, hw, hw', hc⟩ := h'
  refine ⟨j, c, ?_, hw', hc⟩
  rcases h.charge j 0 hw with h1 | h1
  · exact absurd rfl h1
  · exact h1

lemma CleanStep.refl (o : Work) : CleanStep o o := ⟨CleanRel.refl o, .inl rfl⟩

lemma CleanStep.trans {o w w' : Work} (h : CleanStep o w) (h' : CleanStep w w') :
    CleanStep o w' := by
  refine ⟨h.1.trans h'.1, ?_⟩
  rcases h'.2 with rfl | h2
  · exact h.2
  · rcases h.2 with rfl | h1
    · exact .inr h2
    · exact .inr (h1.of_cleanRel h'.1)

lemma CleanStep.of_charged {o w : Work} (h : CleanRel o w) (h' : Charged o w) : CleanStep o w :=
  ⟨h, .inr h'⟩

lemma cleanRel_setKind (k : ℕ) (t : BondKind) (ht : t = .single ∨ t = .double) :
    CleanRel w (w.setKind k t) where
  atoms_size := rfl
  bonds_size := by simp
  atoms _ := rfl
  bonds j := by rw [getElem?_setKind_bonds]; split <;> simp [Option.map_map, Function.comp_def]
  charge _ _ h := .inr h
  kind j t' h := by
    simp only [kind?, getElem?_setKind_bonds] at h ⊢
    split at h
    · simp only [Option.map_map, Function.comp_def, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact ht.elim .inl fun h ↦ .inr (.inl h)
    · exact .inr (.inr h)

lemma cleanRel_modifyAtom_charge (i : ℕ) (c : ℤ) (hc : c ≠ 0) :
    CleanRel w (w.modifyAtom i ({ · with charge := c })) where
  atoms_size := by simp
  bonds_size := rfl
  atoms j := by rw [getElem?_modifyAtom_atoms]; split <;> simp [Option.map_map, Function.comp_def]
  bonds _ := rfl
  charge j c' h := by
    rw [charge?_modifyAtom_charge] at h
    split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      exact .inl hc
    · exact .inr h
  kind _ _ h := .inr (.inr h)

lemma charge?_modifyAtom_charge_self {i : ℕ} (hi : i < w.atoms.size) (c : ℤ) :
    (w.modifyAtom i ({ · with charge := c })).charge? i = some c := by
  rw [charge?_modifyAtom_charge, if_pos rfl, charge?_eq_of_lt w hi]; rfl

lemma charge?_modifyAtom_charge_of_ne_zero {i j : ℕ} {c d : ℤ} (h : w.charge? i = some c)
    (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ e, (w.modifyAtom j ({ · with charge := d })).charge? i = some e ∧ e ≠ 0 := by
  rw [charge?_modifyAtom_charge]
  split
  · exact ⟨d, by simp [h], hd⟩
  · exact ⟨c, h, hc⟩

/-- The rewrite of `nitrogensCleanup` and `phosphorusCleanup`: a bond made single or double and two
atoms charged, one of them neutral before. -/
lemma cleanStep_rewrite {k : ℕ} {t : BondKind} (ht : t = .single ∨ t = .double) {i j : ℕ}
    {c d : ℤ} (hc : c ≠ 0) (hd : d ≠ 0) (hi : i < w.atoms.size) (h0 : w.atoms[i]!.charge = 0) :
    CleanStep w (((w.setKind k t).modifyAtom i ({ · with charge := c })).modifyAtom j
      ({ · with charge := d })) := by
  refine .of_charged (((cleanRel_setKind w k t ht).trans
    (cleanRel_modifyAtom_charge _ i c hc)).trans (cleanRel_modifyAtom_charge _ j d hd)) ?_
  obtain ⟨e, he, he0⟩ := charge?_modifyAtom_charge_of_ne_zero (j := j) (d := d) _
    (charge?_modifyAtom_charge_self (w.setKind k t) (by simpa using hi) c) hc hd
  exact ⟨i, e, by rw [charge?_eq_of_lt w hi, h0], he, he0⟩

/-- `nitroStep` is a `cleanUp` rewrite or nothing. -/
lemma cleanStep_nitroStep (p : Work × List ℕ) (i : ℕ) (hi : i < p.1.atoms.size) :
    CleanStep p.1 (nitroStep p i).1 := by
  obtain ⟨w, consider⟩ := p
  unfold nitroStep
  dsimp only
  split
  · exact .refl w
  · rename_i h
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h
    split
    · exact w.cleanStep_rewrite (.inl rfl) one_ne_zero (by decide) hi h.1.2
    · exact .refl w

/-- `azideStep` is a `cleanUp` rewrite or nothing. -/
lemma cleanStep_azideStep (i : ℕ) : CleanStep w (azideStep w i) := by
  unfold azideStep
  dsimp only
  split
  · rename_i k j hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have hj : j < w.atoms.size := w.lt_size_of_z_ne_zero (by rw [hp.1.1]; decide)
    refine .of_charged (((cleanRel_setKind w k _ (.inr rfl)).trans
      (cleanRel_modifyAtom_charge _ i 1 one_ne_zero)).trans
      (cleanRel_modifyAtom_charge _ j (-1) (by decide))) ⟨j, -1, ?_, ?_, by decide⟩
    · rw [charge?_eq_of_lt w hj, hp.1.2]
    · exact charge?_modifyAtom_charge_self _ (by simpa using hj) _
  · exact .refl w

/-- `phosphorusCleanup` is a `cleanUp` rewrite or nothing. -/
lemma cleanStep_phosphorusCleanup {i : ℕ} (hi : i < w.atoms.size) :
    CleanStep w (w.phosphorusCleanup i) := by
  unfold phosphorusCleanup
  dsimp only
  split
  · exact .refl w
  · rename_i h
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h
    split
    · split
      · rename_i k j _ _
        refine .of_charged (((cleanRel_setKind w k _ (.inl rfl)).trans
          (cleanRel_modifyAtom_charge _ j (-1) (by decide))).trans
          (cleanRel_modifyAtom_charge _ i 1 one_ne_zero)) ⟨i, 1, ?_, ?_, one_ne_zero⟩
        · rw [charge?_eq_of_lt w hi, h.1.1]
        · exact charge?_modifyAtom_charge_self _ (by simpa using hi) _
      · exact .refl w
    · exact .refl w

/-- Setting the charge an atom already has changes nothing. -/
lemma modifyAtom_charge_self {i : ℕ} {c : ℤ} (h : w.atoms[i]!.charge = c) :
    w.modifyAtom i ({ · with charge := c }) = w := by
  unfold modifyAtom
  congr 1
  apply Array.ext (by simp)
  intro j hj _
  simp only [Array.getElem_modify]
  split
  · rename_i hij
    subst hij
    have hj' : i < w.atoms.size := by simpa using hj
    simp only [getElem!_def, Array.getElem?_eq_getElem hj'] at h
    subst h
    rfl
  · rfl

/-- `halogenCleanup` is a `cleanUp` rewrite or nothing. -/
lemma cleanStep_halogenCleanup {i : ℕ} (hi : i < w.atoms.size) :
    CleanStep w (w.halogenCleanup i) := by
  unfold halogenCleanup
  dsimp only
  split
  · exact .refl w
  · rename_i h
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not] at h
    split
    · exact .refl w
    · -- the inner loop: rewrites of `=O`, counted
      have key : ∀ p : Work × ℤ, CleanRel w p.1 ∧ (p.2 = 0 ∧ p.1 = w ∨ 0 < p.2) →
          ∀ kj, CleanRel w (halogenStep p kj).1 ∧
            ((halogenStep p kj).2 = 0 ∧ (halogenStep p kj).1 = w ∨ 0 < (halogenStep p kj).2) := by
        rintro ⟨w', fc⟩ ⟨h1, h2⟩ ⟨k, j⟩
        unfold halogenStep
        dsimp only
        split
        · refine ⟨(h1.trans (cleanRel_setKind w' k _ (.inl rfl))).trans
            (cleanRel_modifyAtom_charge _ j (-1) (by decide)), .inr ?_⟩
          rcases h2 with ⟨rfl, -⟩ | h2 <;> dsimp only <;> omega
        · exact ⟨h1, h2⟩
      obtain ⟨h1, h2⟩ := foldl_induction (fun p : Work × ℤ ↦
        CleanRel w p.1 ∧ (p.2 = 0 ∧ p.1 = w ∨ 0 < p.2)) halogenStep (w.neighbors i) (w, 0)
        ⟨.refl w, .inl ⟨rfl, rfl⟩⟩ (fun p kj _ hp ↦ key p hp kj)
      generalize (w.neighbors i).foldl halogenStep (w, 0) = p at h1 h2
      obtain ⟨w', fc⟩ := p
      dsimp only at h1 h2 ⊢
      rcases h2 with ⟨h3, h4⟩ | h2
      · subst h3 h4
        rw [modifyAtom_charge_self _ h.1]
        exact .refl _
      · refine .of_charged (h1.trans (cleanRel_modifyAtom_charge _ i fc (by omega)))
          ⟨i, fc, ?_, ?_, by omega⟩
        · rw [charge?_eq_of_lt w hi, h.1]
        · exact charge?_modifyAtom_charge_self _ (by rw [h1.atoms_size]; exact hi) _

/-- `cleanUpStep` on an atom in range is a `cleanUp` rewrite or nothing. -/
lemma cleanStep_cleanUpStep {i : ℕ} (hi : i < w.atoms.size) : CleanStep w (cleanUpStep w i) := by
  unfold cleanUpStep
  dsimp only
  split
  · exact w.cleanStep_phosphorusCleanup hi
  · split
    · exact w.cleanStep_halogenCleanup hi
    · exact .refl w

/-- `nitrogensCleanup` is a sequence of `cleanUp` rewrites. -/
lemma cleanStep_nitrogensCleanup : CleanStep w w.nitrogensCleanup := by
  unfold nitrogensCleanup
  have h1 := foldl_induction (fun p : Work × List ℕ ↦ CleanStep w p.1) nitroStep
    (List.range w.numAtoms) (w, []) (.refl w) fun p i hi hp ↦ hp.trans
      (cleanStep_nitroStep p i (by
        rw [hp.1.atoms_size]; simpa [numAtoms] using hi))
  generalize (List.range w.numAtoms).foldl nitroStep (w, []) = p at h1
  obtain ⟨w', consider⟩ := p
  exact foldl_induction (CleanStep w) azideStep consider w' h1
    fun w'' i _ h ↦ h.trans (cleanStep_azideStep w'' i)

/-- `cleanUp` is a sequence of rewrites, each of which charges a neutral atom. -/
lemma cleanStep_cleanUp : CleanStep w w.cleanUp := by
  unfold cleanUp
  have h := w.cleanStep_nitrogensCleanup
  exact foldl_induction (CleanStep w) cleanUpStep (List.range w.nitrogensCleanup.numAtoms) _ h
    fun w' i hi h' ↦ h'.trans (cleanStep_cleanUpStep w' (by
      rw [h'.1.atoms_size, ← h.1.atoms_size]; simpa [numAtoms] using hi))

/-- **When `cleanUp` keeps every charge it does nothing**: each of its rewrites charges an atom
that was neutral, and charges, once set, are never set back to zero. -/
theorem cleanUp_eq_self_of_charge (h : ∀ j, w.cleanUp.charge? j = w.charge? j) :
    w.cleanUp = w := by
  rcases w.cleanStep_cleanUp.2 with h' | ⟨j, c, h0, hc, hc0⟩
  · exact h'
  · rw [h j, h0] at hc
    cases hc
    exact absurd rfl hc0

/-- `cleanUp` keeps the atoms but for their charges. -/
lemma cleanRel_cleanUp : CleanRel w w.cleanUp := w.cleanStep_cleanUp.1

end Work

end LeanSMILES.Aromaticity
