/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.CleanFacts
public import LeanSMILES.Aromaticity.KekulizeAtoms

/-!
# LeanSMILES.Aromaticity.PrepareFacts

The working copy `aromatize` kekulizes (`Work.prepare`), atom by atom: each atom's record is the
molecule's atom with RDKit's caches filled and `cleanUp`'s charge (`Work.prepare_atom`), and the
kinds of its bonds are the molecule's, aromatic exactly where the molecule's are
(`Work.kindsAt_prepare`).

## Main definitions

* `Work.cleaned`: the copy `prepare` builds before caching valences.

## Main statements

* `Work.prepare_atom`: an atom of `prepare m` is the cleaned atom with RDKit's caches filled.
* `Work.cleaned_atom`: an atom of the cleaned copy is the molecule's, but for its charge and
  frozen hydrogen count.
* `Work.kindsAt_prepare`: the bonds at an atom of `prepare m` are aromatic exactly where the
  molecule's are.
* `Work.freezeCache_atom`: an atom of a molecule's frozen, cached copy, written out in full.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-! ### Same skeleton -/

/-- Two copies with as many atoms and bonds, whose bonds join the same atoms, have the same
skeleton. -/
lemma sameSkel_of_ends {w w' : Work} (hn : w'.atoms.size = w.atoms.size)
    (hs : w'.bonds.size = w.bonds.size)
    (he : ∀ k : ℕ, w'.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      w.bonds[k]?.map (fun b : WBond ↦ (b.src, b.dst))) : SameSkel w' w :=
  ⟨hn, hs, fun k ↦ (ends_getElem! hs he k).1, fun k ↦ (ends_getElem! hs he k).2⟩

/-- Copies related by `CleanRel` have the same skeleton. -/
lemma CleanRel.sameSkel {o w : Work} (h : CleanRel o w) : SameSkel w o :=
  sameSkel_of_ends h.atoms_size h.bonds_size fun k ↦ ends_of_single (h.bonds k)

/-- Copies related by `KindsRel` have the same skeleton. -/
lemma KindsRel.sameSkel {o w : Work} (h : KindsRel o w) : SameSkel w o :=
  sameSkel_of_ends h.atoms_size h.bonds_size h.ends

/-- Copies related by `AfterRel` have the same skeleton. -/
lemma AfterRel.sameSkel {o w : Work} (h : AfterRel o w) : SameSkel w o :=
  sameSkel_of_ends h.atoms_size h.bonds_size fun k ↦ ends_of_single (h.bonds k)

/-- Two copies with the same skeleton have, at each atom, the kinds of the same bonds. -/
lemma kindsAt_forall₂ {w w' : Work} (h : SameSkel w' w) (R : BondKind → BondKind → Prop) (i : ℕ)
    (hR : ∀ k ∈ w.bondsOf i, R (w'.bonds[k]! : WBond).kind (w.bonds[k]! : WBond).kind) :
    List.Forall₂ R (w'.kindsAt i) (w.kindsAt i) := by
  unfold kindsAt
  rw [h.bondsOf]
  generalize w.bondsOf i = l at hR ⊢
  induction l with
  | nil => exact .nil
  | cons k l ih =>
    exact .cons (hR k List.mem_cons_self) (ih fun k' hk' ↦ hR k' (List.mem_cons_of_mem _ hk'))

/-! ### The molecule's bonds at an atom -/

/-- Filtering a list's indices by `p` of the entry and mapping each kept index to `f` of its
entry is filtering the list by `p` and mapping `f`. -/
lemma range_filter_map {α β : Type*} [Inhabited α] (l : List α) (p : α → Bool) (f : α → β) :
    ((List.range l.length).filter (fun k ↦ p l[k]!)).map (fun k ↦ f l[k]!) =
      (l.filter p).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, List.filter_map]
    have h0 : (a :: l)[0]! = a := rfl
    have hs : ∀ k, (a :: l)[k + 1]! = l[k]! := fun _ ↦ rfl
    simp only [h0, Function.comp_def, hs]
    by_cases hp : p a = true
    · simp only [hp, if_true, List.map_cons, List.map_map, Function.comp_def, hs, ih,
        List.filter_cons_of_pos hp, h0]
    · simp only [hp, Bool.false_eq_true, if_false, List.map_map, Function.comp_def, hs, ih,
        List.filter_cons_of_neg hp]

/-- The kinds of the bonds at atom `i` of a molecule's working copy: those of the molecule's bonds
at `i`, in order. -/
lemma kindsAt_ofMolecule {n : ℕ} (m : Molecule n) (i : Fin n) :
    (ofMolecule m).kindsAt i = (m.bonds.filter (·.touches i)).map (·.kind) := by
  let g : Bond n → WBond := fun b ↦ { src := b.src.val, dst := b.dst.val, kind := b.kind }
  have hb : ∀ k : ℕ, ((ofMolecule m).bonds[k]! : WBond) = ((m.bonds.map g)[k]! : WBond) := by
    intro k
    simp [ofMolecule, getElem!_def, g]
  have ht : ∀ b : Bond n, (g b).touches i.val = b.touches i := by
    intro b
    simp only [g, WBond.touches, Bond.touches]
    rw [Bool.eq_iff_iff]
    simp [Bool.or_eq_true, beq_iff_eq, Fin.val_inj]
  have hn : (ofMolecule m).numBonds = (m.bonds.map g).length := by simp [numBonds, ofMolecule]
  unfold kindsAt bondsOf
  simp only [hb, hn]
  rw [range_filter_map (m.bonds.map g) (·.touches i.val) (·.kind), List.filter_map,
    List.map_map]
  simp only [Function.comp_def, ht]
  rfl

/-! ### `prepare`, atom by atom -/

/-- The copy `prepare` builds before caching: `cleanUp` after freezing the hydrogen counts. -/
def cleaned {n : ℕ} (m : Molecule n) : Work := (ofMolecule m).freezeHs.cleanUp

/-- `prepare m` is the cleaned copy with its valences cached. -/
lemma prepare_eq {n : ℕ} (m : Molecule n) : prepare m = (cleaned m).cacheValences := rfl

/-- The cleaned copy is related to the frozen copy by `CleanFine`. -/
lemma cleanFine_cleaned {n : ℕ} (m : Molecule n) : CleanFine (ofMolecule m).freezeHs (cleaned m) :=
  cleanFine_cleanUp _

/-- The cleaned copy has the skeleton of the molecule's working copy. -/
lemma sameSkel_cleaned {n : ℕ} (m : Molecule n) : SameSkel (cleaned m) (ofMolecule m) :=
  (cleanFine_cleaned m).rel.sameSkel.trans
    ⟨by simp [numAtoms], rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- `prepare m` has the skeleton of the molecule's working copy. -/
lemma sameSkel_prepare {n : ℕ} (m : Molecule n) : SameSkel (prepare m) (ofMolecule m) :=
  (⟨by simp [numAtoms, prepare_eq], rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩ :
    SameSkel (prepare m) (cleaned m)).trans (sameSkel_cleaned m)

/-- The cleaned copy of a molecule with `n` atoms has `n` atoms. -/
lemma size_cleaned {n : ℕ} (m : Molecule n) : (cleaned m).atoms.size = n := by
  rw [(cleanFine_cleaned m).rel.atoms_size]
  simp [ofMolecule]

/-- An atom of the cleaned copy: the molecule's atom, but for its charge and frozen count. -/
lemma cleaned_atom {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((cleaned m).atoms[i.val]! : WAtom) =
      { ((ofMolecule m).atoms[i.val]! : WAtom) with
        charge := ((cleaned m).atoms[i.val]! : WAtom).charge,
        frozenHs := ((cleaned m).atoms[i.val]! : WAtom).frozenHs } := by
  have hc : i.val < (cleaned m).atoms.size := by rw [size_cleaned]; exact i.isLt
  have ho : i.val < (ofMolecule m).atoms.size := by simp [ofMolecule]
  have h := (cleanFine_cleaned m).rel.atoms i.val
  rw [getElem?_freezeHs_atoms, Array.getElem?_eq_getElem hc, Array.getElem?_eq_getElem ho] at h
  rw [getElem!_pos (cleaned m).atoms i.val hc, getElem!_pos (ofMolecule m).atoms i.val ho]
  generalize (cleaned m).atoms[i.val] = x at h ⊢
  generalize (ofMolecule m).atoms[i.val] = y at h ⊢
  cases x; cases y
  simp only [Option.map_some, Option.some.injEq, WAtom.mk.injEq] at h
  simp [h]

/-- An atom of a molecule's working copy: the molecule's element, aromatic flag, charge and
written hydrogens, with `noImplicit` set for bracket atoms and `*`. -/
lemma ofMolecule_atom {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((ofMolecule m).atoms[i.val]! : WAtom) =
      { z := (m.atom i).atomicNumber, aromatic := (m.atom i).aromatic, charge := (m.atom i).charge,
        explicitHs := (m.atom i).explicitH.getD 0,
        noImplicit := (m.atom i).explicitH.isSome || (m.atom i).element.isNone } := by
  simp [ofMolecule]

/-- An atom of `prepare m`: the cleaned atom with its valence, implicit hydrogens and
`adjustHs` mark cached. -/
lemma prepare_atom {n : ℕ} (m : Molecule n) (i : Fin n) :
    ((prepare m).atoms[i.val]! : WAtom) =
      { ((cleaned m).atoms[i.val]! : WAtom) with
        cachedValence := some ((cleaned m).explicitValence i),
        cachedImplicit := (cleaned m).implicitHs i,
        adjustHs := (cleaned m).isAromaticAtom i } := by
  have hc : i.val < (cleaned m).atoms.size := by rw [size_cleaned]; exact i.isLt
  have h := getElem?_cacheValences_atoms (cleaned m) i.val
  rw [prepare_eq]
  rw [Array.getElem?_eq_getElem hc, Option.map_some] at h
  have hp : i.val < (cleaned m).cacheValences.atoms.size := by simpa using hc
  rw [Array.getElem?_eq_getElem hp, Option.some.injEq] at h
  rw [getElem!_pos (cleaned m).cacheValences.atoms i.val hp,
    getElem!_pos (cleaned m).atoms i.val hc, h]

/-- The bonds at an atom of `prepare m` are aromatic exactly where the molecule's are. -/
lemma kindsAt_prepare {n : ℕ} (m : Molecule n) (i : Fin n) :
    List.Forall₂ (fun p o ↦ (p = BondKind.aromatic ↔ o = BondKind.aromatic))
      ((prepare m).kindsAt i) ((m.bonds.filter (·.touches i)).map (·.kind)) := by
  rw [← kindsAt_ofMolecule]
  refine kindsAt_forall₂ (sameSkel_prepare m) _ _ fun k _ ↦ ?_
  rw [prepare_eq, cacheValences_bonds]
  exact (cleanFine_cleaned m).arom k

/-- Freezing the hydrogen counts keeps every element and charge. -/
lemma freezeHs_atom_z_charge {n : ℕ} (m : Molecule n) (i : Fin n) :
    (((ofMolecule m).freezeHs.atoms[i.val]! : WAtom).z = (m.atom i).atomicNumber) ∧
      (((ofMolecule m).freezeHs.atoms[i.val]! : WAtom).charge = (m.atom i).charge) := by
  have hlt : i.val < (ofMolecule m).atoms.size := by simp [ofMolecule]
  have h := getElem?_freezeHs_atoms (ofMolecule m) i.val
  rw [Array.getElem?_eq_getElem hlt, Option.map_some] at h
  have hlt' : i.val < (ofMolecule m).freezeHs.atoms.size := by simp
  rw [Array.getElem?_eq_getElem hlt', Option.some.injEq] at h
  rw [getElem!_pos (ofMolecule m).freezeHs.atoms i.val hlt', h]
  have ho := ofMolecule_atom m i
  rw [getElem!_pos (ofMolecule m).atoms i.val hlt] at ho
  rw [ho]
  exact ⟨rfl, rfl⟩

/-- An atom of a molecule's frozen, cached working copy (no `cleanUp`): the molecule's atom with
RDKit's caches filled. -/
lemma freezeCache_atom {n : ℕ} (x : Molecule n) (i : Fin n) :
    ((ofMolecule x).freezeHs.cacheValences.atoms[i.val]! : WAtom) =
      { z := (x.atom i).atomicNumber, aromatic := (x.atom i).aromatic,
        charge := (x.atom i).charge, explicitHs := (x.atom i).explicitH.getD 0,
        noImplicit := (x.atom i).explicitH.isSome || (x.atom i).element.isNone,
        frozenHs := some ((ofMolecule x).totalHs i),
        cachedValence := some ((ofMolecule x).freezeHs.explicitValence i),
        cachedImplicit := (ofMolecule x).freezeHs.implicitHs i,
        adjustHs := (ofMolecule x).freezeHs.isAromaticAtom i } := by
  have hlt : i.val < (ofMolecule x).atoms.size := by simp [ofMolecule]
  have hlt' : i.val < (ofMolecule x).freezeHs.atoms.size := by simp
  have hlt'' : i.val < (ofMolecule x).freezeHs.cacheValences.atoms.size := by simp
  have h1 := getElem?_cacheValences_atoms (ofMolecule x).freezeHs i.val
  have h2 := getElem?_freezeHs_atoms (ofMolecule x) i.val
  rw [Array.getElem?_eq_getElem hlt'', Array.getElem?_eq_getElem hlt', Option.map_some,
    Option.some.injEq] at h1
  rw [Array.getElem?_eq_getElem hlt', Array.getElem?_eq_getElem hlt, Option.map_some,
    Option.some.injEq] at h2
  rw [getElem!_pos (ofMolecule x).freezeHs.cacheValences.atoms i.val hlt'', h1, h2]
  have ho := ofMolecule_atom x i
  rw [getElem!_pos (ofMolecule x).atoms i.val hlt] at ho
  rw [ho]

/-- An atom of a molecule's frozen working copy. -/
lemma freezeHs_ofMolecule_atom {n : ℕ} (x : Molecule n) (i : Fin n) :
    ((ofMolecule x).freezeHs.atoms[i.val]! : WAtom) =
      { z := (x.atom i).atomicNumber, aromatic := (x.atom i).aromatic,
        charge := (x.atom i).charge, explicitHs := (x.atom i).explicitH.getD 0,
        noImplicit := (x.atom i).explicitH.isSome || (x.atom i).element.isNone,
        frozenHs := some ((ofMolecule x).totalHs i) } := by
  have hlt : i.val < (ofMolecule x).atoms.size := by simp [ofMolecule]
  have hlt' : i.val < (ofMolecule x).freezeHs.atoms.size := by simp
  have h2 := getElem?_freezeHs_atoms (ofMolecule x) i.val
  rw [Array.getElem?_eq_getElem hlt', Array.getElem?_eq_getElem hlt, Option.map_some,
    Option.some.injEq] at h2
  rw [getElem!_pos (ofMolecule x).freezeHs.atoms i.val hlt', h2]
  have ho := ofMolecule_atom x i
  rw [getElem!_pos (ofMolecule x).atoms i.val hlt] at ho
  rw [ho]

end LeanSMILES.Aromaticity.Work
