/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.SMILES.Canonicity
public import Mathlib.Logic.Relation

/-!
# LeanSMILES.SMILES.KekuleClass

One canonical SMILES for all the Kekulé structures of a molecule.

`Molecule.canonicalSmiles_relabel` makes canonical SMILES independent of how the atoms are
numbered, but not of where the double bonds are drawn. The two Kekulé structures of o-xylene,
`CC1=C(C)C=CC=C1` and `CC1=CC=CC=C1C`, are different graphs, and no renumbering turns one into
the other, so they get different strings. This file says which drawings are one molecule and
gives them one string.

## The class

Two drawings are **Kekulé partners** (`Molecule.KekulePartner`) when they have the same atoms,
configurations and skeleton, their bonds differ only between single and double, and every atom
keeps its bond-order sum: the double bonds have moved around closed alternating paths. Two
drawings are **one molecule** when a chain of renumberings and Kekulé moves joins them
(`Relation.EqvGen Molecule.KekuleRedraw`). The definition is graph theory. It uses no model of
aromaticity.

## The canonical form

A bond is **movable** (`Molecule.movable`) when the Kekulé partners disagree about it: double in
some, single in others. Every other bond has the same kind in every partner
(`Molecule.KekulePartner.kind_eq_of_not_movable`). `Molecule.delocalize` writes the movable bonds
aromatic, and the atoms on them, which turns every partner into the same molecule
(`Molecule.KekulePartner.delocalize_eq`). `Molecule.kekuleCanonicalSmiles` is the canonical SMILES
of that molecule. Delocalizing commutes with renumbering (`Molecule.delocalize_relabel`), so
`Molecule.canonicalSmiles_relabel` does the rest:

* `Molecule.kekuleCanonicalSmiles_eq_of_kekulePartner` and `Molecule.kekuleCanonicalSmiles_relabel`
  are the two steps;
* `Molecule.kekuleCanonicalSmiles_eq_of_eqvGen` is the uniqueness theorem: one molecule, one
  string. It has no hypotheses.

This is aromaticity defined by graph theory alone: a bond is aromatic when the Kekulé structures
disagree about it. The output reads like an aromatic SMILES (benzene's movable bonds are its six
ring bonds), and a ring with only one Kekulé structure has nothing movable and stays as drawn.

An earlier draft took the least canonical SMILES over all the partners. The uniqueness proof was
the same, but it canonicalized once per Kekulé structure, and C60 has 12 500 of them. This version
canonicalizes once.

## What it merges

The chemistry spec, `LeanSMILES.Aromaticity.Resonance`, merges two Kekulé partners only when
RDKit's aromaticity model marks every moved bond aromatic, and its theorems need hypotheses about
RDKit's `cleanUp`. This class merges every pair of Kekulé partners:

* all five Kekulé structures of biphenylene, which the chemistry spec splits four to one;
* the three of the benzazete `Cc1cccc2ncc12`, which it splits into two molecules;
* the two bond-shift isomers of 1,2-dimethylcyclooctatetraene, `CC1=CC=CC=CC=C1C` and
  `CC=1C=CC=CC=CC1C`, which are separate compounds when bond shifting is slow. This is the price.
  Both are written with an aromatic eight-membered ring, which RDKit's model would not call
  aromatic.

It does not merge drawings that move a charge rather than a bond: the two forms `cleanUp`
normalizes, `N(=O)=O` and `[N+](=O)[O-]`, have different atoms, so they are not Kekulé partners.
That is a larger class, not defined here.

## Not covered yet

* **Finding the movable bonds fast.** `Molecule.movable` tries all `2 ^ numBonds` placements of
  the double bonds, which is a specification, not an algorithm. `lake exe kekule-bench` finds them
  with one backtracking search per tradable bond and checks the result against `movable` and
  against full enumeration. That the fast search agrees with `movable` is tested, not proved.
* **Lowercase input.** `kekuleCanonicalSmiles` reads the bonds as drawn, so an aromatic SMILES has
  to be kekulized first. Where the kekulizer puts the double bonds depends on the atom order, but
  every answer is a Kekulé partner of every other, so that should not matter. The kekulizer's side
  of this is not proved.
* **Reading the string back.** Aromatic SMILES means each lowercase atom gets one double bond among
  its aromatic bonds. An atom with two double bonds among its movable bonds (possible only for a
  hypervalent atom) breaks that reading: the string is still unique, but read back as SMILES it
  means a different set of structures.
* **The converse.** Only one direction is proved: one molecule, one string. That one string means
  one molecule needs canonical SMILES to tell apart molecules that are not renumberings of each
  other, which the repository does not prove.
-/

@[expose] public section

namespace LeanSMILES

/-- The kind with `double` read as `single`. A Kekulé partner may change a
bond between those two kinds and no other. -/
def BondKind.forgetDouble : BondKind → BondKind
  | .double => .single
  | k => k

/-- Only the aromatic kind forgets to aromatic. -/
@[simp] lemma BondKind.forgetDouble_eq_aromatic {k : BondKind} :
    k.forgetDouble = .aromatic ↔ k = .aromatic := by
  cases k <;> simp [BondKind.forgetDouble]

/-- The bond with `double` read as `single`. The endpoints and the `/` `\` mark are kept. -/
def Bond.forgetDouble {n : ℕ} (b : Bond n) : Bond n := { b with kind := b.kind.forgetDouble }

/-- Reading `double` as `single` commutes with renumbering the atoms. -/
@[simp] lemma Bond.forgetDouble_map {n m : ℕ} (σ : Fin n → Fin m) (hσ : Function.Injective σ)
    (b : Bond n) : (b.map σ hσ).forgetDouble = b.forgetDouble.map σ hσ := rfl

namespace Molecule

variable {n : ℕ}

/-- Replace the kind of bond number `k` by `f k` of its kind. The endpoints are kept, so the
graph stays simple. -/
def setKinds (m : Molecule n) (f : ℕ → BondKind → BondKind) : Molecule n where
  atoms := m.atoms
  bonds := m.bonds.zipIdx.map fun p ↦ { p.1 with kind := f p.2 p.1.kind }
  nodup := by
    have h : (m.bonds.zipIdx.map fun p ↦ { p.1 with kind := f p.2 p.1.kind }).map Bond.edge
        = m.bonds.map Bond.edge := by
      rw [List.map_map, show (Bond.edge ∘ fun p : Bond n × ℕ ↦ { p.1 with kind := f p.2 p.1.kind })
          = Bond.edge ∘ Prod.fst from rfl, ← List.map_map, List.zipIdx_map_fst]
    exact h ▸ m.nodup
  stereo := m.stereo

/-! ### Kekulé partners -/

/-- A Kekulé structure: no atom is written aromatic and no bond is aromatic. -/
def IsKekule (m : Molecule n) : Prop :=
  (∀ i, (m.atom i).aromatic = false) ∧ ∀ b ∈ m.bonds, b.kind ≠ .aromatic

instance (m : Molecule n) : Decidable m.IsKekule :=
  inferInstanceAs (Decidable ((∀ i, (m.atom i).aromatic = false) ∧
    ∀ b ∈ m.bonds, b.kind ≠ .aromatic))

/-- Renumbering keeps a Kekulé structure Kekulé, and only a Kekulé structure renumbers to one. -/
theorem isKekule_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).IsKekule ↔ m.IsKekule := by
  simp only [IsKekule, bonds_relabel, List.forall_mem_map, Bond.kind_map]
  refine and_congr_left' ⟨fun h i ↦ by simpa using h (σ i), fun h i ↦ ?_⟩
  rw [← Equiv.apply_symm_apply σ i, atom_relabel]
  exact h _

/-- What all Kekulé partners of `m` share: the atoms, the bonds with `double` read as `single`,
each atom's bond-order sum, and the configurations. -/
def kekuleData (m : Molecule n) :
    Vector Atom n × List (Bond n) × Vector ℚ n × Vector (Option (Stereo n)) n :=
  (m.atoms, m.bonds.map Bond.forgetDouble, Vector.ofFn m.bondOrderSum, m.stereo)

/-- `m₁` and `m₂` are Kekulé partners: one skeleton with its double bonds moved around closed
alternating paths. The atoms, the configurations and the bond list are the same, position by
position, except that a bond may change between single and double; every atom keeps its
bond-order sum, and so its number of double bonds. -/
def KekulePartner (m₁ m₂ : Molecule n) : Prop := m₁.kekuleData = m₂.kekuleData

instance (m₁ m₂ : Molecule n) : Decidable (m₁.KekulePartner m₂) := by
  unfold KekulePartner
  infer_instance

/-- Being Kekulé partners is an equivalence relation. -/
theorem kekulePartner_equivalence : Equivalence (KekulePartner (n := n)) :=
  ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- A Kekulé partner of a Kekulé structure is a Kekulé structure. -/
theorem KekulePartner.isKekule {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂)
    (hk : m₁.IsKekule) : m₂.IsKekule := by
  simp only [KekulePartner, kekuleData, Prod.mk.injEq] at h
  obtain ⟨ha, hb, -⟩ := h
  refine ⟨fun i ↦ by simpa [atom, ← ha] using hk.1 i, fun b hb₂ hba ↦ ?_⟩
  have hmem : b.forgetDouble ∈ m₁.bonds.map Bond.forgetDouble := by
    rw [hb]
    exact List.mem_map_of_mem hb₂
  obtain ⟨b', hb', he⟩ := List.mem_map.mp hmem
  have hk' : b'.kind.forgetDouble = b.kind.forgetDouble := congrArg Bond.kind he
  rw [hba] at hk'
  exact hk.2 b' hb' (BondKind.forgetDouble_eq_aromatic.mp hk')

/-! ### Renumbering -/

/-- A renumbered molecule with `Equiv.refl` is the molecule. -/
lemma relabel_refl (m : Molecule n) : m.relabel (Equiv.refl _) = m :=
  Molecule.ext (Vector.ext fun _ _ ↦ by simp [relabel]) (List.map_id'' (fun _ ↦ rfl) _)
    (Vector.ext fun _ _ ↦ by
      have h : ∀ o : Option (Stereo n), o.map (Stereo.map (Equiv.refl _)) = o := fun o ↦ by
        cases o <;> simp [Stereo.map_refl]
      simp [relabel, h])

/-- Setting bond kinds commutes with renumbering the atoms. -/
lemma setKinds_relabel (m : Molecule n) (f : ℕ → BondKind → BondKind) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).setKinds f = (m.setKinds f).relabel σ := by
  refine Molecule.ext rfl ?_ rfl
  simp only [setKinds, bonds_relabel, List.zipIdx_map, List.map_map]
  rfl

/-- What Kekulé partners share, for a renumbered molecule: the same data, renumbered. -/
lemma kekuleData_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).kekuleData = (relabelVec σ m.atoms,
      (m.bonds.map Bond.forgetDouble).map (Bond.map σ σ.injective),
      relabelVec σ (Vector.ofFn m.bondOrderSum), relabelStereo σ m.stereo) := by
  simp only [kekuleData, atoms_relabel, bonds_relabel, stereo_relabel, List.map_map,
    Prod.mk.injEq, true_and, and_true]
  refine ⟨rfl, Vector.ext fun i hi ↦ ?_⟩
  have h := bondOrderSum_relabel m σ (σ.symm ⟨i, hi⟩)
  rw [Equiv.apply_symm_apply] at h
  simpa using h

/-- Renumbering two Kekulé partners the same way keeps them partners. -/
theorem KekulePartner.relabel {m₁ m₂ : Molecule n} (σ : Equiv.Perm (Fin n))
    (h : m₁.KekulePartner m₂) : (m₁.relabel σ).KekulePartner (m₂.relabel σ) := by
  have h' : m₁.kekuleData = m₂.kekuleData := h
  simp only [KekulePartner, kekuleData_relabel]
  simp only [kekuleData, Prod.mk.injEq] at h'
  rw [h'.1, h'.2.1, h'.2.2.1, h'.2.2.2]

/-- Two drawings renumbered the same way are Kekulé partners exactly when they were before. -/
theorem kekulePartner_relabel_iff (m₁ m₂ : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m₁.relabel σ).KekulePartner (m₂.relabel σ) ↔ m₁.KekulePartner m₂ := by
  refine ⟨fun h ↦ ?_, KekulePartner.relabel σ⟩
  simpa only [relabel_relabel, Equiv.self_trans_symm, relabel_refl] using h.relabel σ.symm

/-! ### The Kekulé class -/

/-- Every list of `k` booleans. -/
def allBits : ℕ → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBits k).flatMap fun s ↦ [false :: s, true :: s]

/-- `allBits k` holds exactly the lists of length `k`. -/
lemma mem_allBits {s : List Bool} : ∀ {k : ℕ}, s ∈ allBits k ↔ s.length = k
  | 0 => by cases s <;> simp [allBits]
  | k + 1 => by
    cases s with
    | nil => simp [allBits]
    | cons b s => cases b <;> simp [allBits, mem_allBits]

/-- The kind bond number `k` gets from `withDoubles s`, given its kind with `double` read as
`single`: double when that kind is single and `s` holds at `k`. -/
def placeDouble (s : List Bool) (k : ℕ) (b : BondKind) : BondKind :=
  if b = .single ∧ s.getD k false = true then .double else b

/-- The drawing of `m`'s skeleton with double bonds where `s` says: bond `k` is double when it is
single or double in `m` and `s` holds at `k`, and every other bond keeps its kind. Only the kinds
with `double` read as `single` are used, so Kekulé partners give the same drawings. -/
def withDoubles (m : Molecule n) (s : List Bool) : Molecule n :=
  m.setKinds fun k b ↦ placeDouble s k b.forgetDouble

/-- `withDoubles` reads only what Kekulé partners share. -/
lemma withDoubles_congr {m₁ m₂ : Molecule n} (ha : m₁.atoms = m₂.atoms)
    (hb : m₁.bonds.map Bond.forgetDouble = m₂.bonds.map Bond.forgetDouble)
    (hs : m₁.stereo = m₂.stereo) (s : List Bool) : m₁.withDoubles s = m₂.withDoubles s := by
  have key (m : Molecule n) : (m.withDoubles s).bonds =
      (m.bonds.map Bond.forgetDouble).zipIdx.map
        fun p ↦ { p.1 with kind := placeDouble s p.2 p.1.kind } := by
    simp only [withDoubles, setKinds, List.zipIdx_map, List.map_map]
    rfl
  exact Molecule.ext ha (by rw [key, key, hb]) hs

/-- `withDoubles` commutes with renumbering the atoms. -/
lemma withDoubles_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) (s : List Bool) :
    (m.relabel σ).withDoubles s = (m.withDoubles s).relabel σ :=
  setKinds_relabel _ _ _

/-- With the double bonds `m` has, `withDoubles` draws `m`. -/
lemma withDoubles_self (m : Molecule n) : m.withDoubles (m.bonds.map (·.kind == .double)) = m := by
  refine Molecule.ext rfl ?_ rfl
  simp only [withDoubles, setKinds]
  conv_rhs => rw [← List.zipIdx_map_fst 0 m.bonds]
  refine List.map_congr_left fun p hp ↦ ?_
  obtain ⟨b, i⟩ := p
  obtain ⟨hi, hb⟩ := List.mem_zipIdx' hp
  have hs : (m.bonds.map (·.kind == .double)).getD i false = (b.kind == .double) := by
    simp [List.getD_eq_getElem?_getD, hi, hb]
  simp only [placeDouble, hs]
  obtain ⟨src, dst, kind, dir, ne⟩ := b
  cases kind <;> simp [BondKind.forgetDouble]

/-- The Kekulé partners of `m`, found by trying every placement of double bonds on its skeleton.
-/
def kekuleClass (m : Molecule n) : List (Molecule n) :=
  ((allBits m.numBonds).map m.withDoubles).filter fun x ↦ decide (m.KekulePartner x)

/-- Kekulé partners have the same number of bonds. -/
lemma KekulePartner.numBonds_eq {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) :
    m₁.numBonds = m₂.numBonds := by
  have := congrArg (fun d ↦ d.2.1.length) h
  simpa [kekuleData, numBonds] using this

/-- `m` is in its own Kekulé class. -/
theorem self_mem_kekuleClass (m : Molecule n) : m ∈ m.kekuleClass := by
  simp only [kekuleClass, List.mem_filter, List.mem_map, decide_eq_true_eq]
  exact ⟨⟨_, mem_allBits.mpr (by simp [numBonds]), m.withDoubles_self⟩,
    kekulePartner_equivalence.refl m⟩

/-- Kekulé partners have the same Kekulé class. -/
theorem KekulePartner.kekuleClass_eq {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) :
    m₁.kekuleClass = m₂.kekuleClass := by
  have hd : m₁.kekuleData = m₂.kekuleData := h
  have hd' := hd
  simp only [kekuleData, Prod.mk.injEq] at hd'
  have hw : m₁.withDoubles = m₂.withDoubles :=
    funext (withDoubles_congr hd'.1 hd'.2.1 hd'.2.2.2)
  unfold kekuleClass
  rw [h.numBonds_eq, hw]
  exact List.filter_congr fun x _ ↦ by simp [KekulePartner, hd]

/-- The Kekulé class of a renumbered molecule is its Kekulé class, renumbered. -/
theorem kekuleClass_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).kekuleClass = m.kekuleClass.map (·.relabel σ) := by
  have hmap : (allBits (m.relabel σ).numBonds).map (m.relabel σ).withDoubles =
      ((allBits m.numBonds).map m.withDoubles).map (·.relabel σ) := by
    simp [numBonds_relabel, List.map_map, Function.comp_def, withDoubles_relabel]
  rw [kekuleClass, kekuleClass, hmap, List.filter_map]
  congr 1
  exact List.filter_congr fun x _ ↦ by simp [kekulePartner_relabel_iff]

/-! ### Movable bonds

A bond is movable when the Kekulé partners disagree about it: double in one, single in another.
Every other bond has the same kind in every partner. Writing the movable bonds aromatic, and the
atoms on them, gives one molecule for the whole class, and its canonical SMILES is the canonical
form. That costs one canonical SMILES, however many partners there are. -/

/-- The kind of bond `k`, if there is one. -/
def kindAt (m : Molecule n) (k : ℕ) : Option BondKind := m.bonds[k]?.map (·.kind)

/-- Bond `k` of `m` is **movable**: it is double in some Kekulé partner of `m` and single in
another. -/
def movable (m : Molecule n) (k : ℕ) : Bool :=
  m.kekuleClass.any (·.kindAt k == some .double) && m.kekuleClass.any (·.kindAt k == some .single)

/-- Whether atom `i` is on a bond `mask` picks. -/
def onMask (m : Molecule n) (mask : ℕ → Bool) (i : Fin n) : Bool :=
  m.bonds.zipIdx.any fun p ↦ mask p.2 && p.1.touches i

/-- `m` with the bonds `mask` picks written aromatic, and the atoms on them. -/
def delocalizeWith (m : Molecule n) (mask : ℕ → Bool) : Molecule n where
  atoms := Vector.ofFn fun i ↦ { m.atom i with aromatic := (m.atom i).aromatic || m.onMask mask i }
  bonds := (m.setKinds fun k kind ↦ if mask k then .aromatic else kind).bonds
  nodup := (m.setKinds fun k kind ↦ if mask k then .aromatic else kind).nodup
  stereo := m.stereo

/-- `m` with its movable bonds written aromatic: one molecule for the whole Kekulé class. -/
def delocalize (m : Molecule n) : Molecule n := m.delocalizeWith m.movable

/-- A movable bond is witnessed by two members of the class. -/
lemma movable_of_mem {m x y : Molecule n} {k : ℕ} (hx : x ∈ m.kekuleClass)
    (hy : y ∈ m.kekuleClass) (hxk : x.kindAt k = some .double) (hyk : y.kindAt k = some .single) :
    m.movable k = true := by
  simp only [movable, Bool.and_eq_true, List.any_eq_true, beq_iff_eq]
  exact ⟨⟨x, hx, hxk⟩, ⟨y, hy, hyk⟩⟩

/-- Two kinds that agree with `double` read as `single` are equal or are `double` and `single`. -/
lemma BondKind.eq_or_of_forgetDouble_eq {a b : BondKind} (h : a.forgetDouble = b.forgetDouble) :
    a = b ∨ (a = .double ∧ b = .single) ∨ (a = .single ∧ b = .double) := by
  cases a <;> cases b <;> simp_all [BondKind.forgetDouble]

/-- Kekulé partners agree on every bond that is not movable. -/
theorem KekulePartner.kind_eq_of_not_movable {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂)
    {k : ℕ} (h₁ : k < m₁.bonds.length) (h₂ : k < m₂.bonds.length) (hk : m₁.movable k = false) :
    m₁.bonds[k].kind = m₂.bonds[k].kind := by
  have hd : m₁.kekuleData = m₂.kekuleData := h
  have hb := congrArg (fun d ↦ (d.2.1[k]?).map Bond.kind) hd
  simp only [kekuleData, List.getElem?_map, h₁, h₂, List.getElem?_eq_getElem, Option.map_some,
    Bond.forgetDouble, Option.some.injEq] at hb
  have hm₁ : m₁ ∈ m₁.kekuleClass := self_mem_kekuleClass m₁
  have hm₂ : m₂ ∈ m₁.kekuleClass := h.kekuleClass_eq ▸ self_mem_kekuleClass m₂
  have hx : m₁.kindAt k = some m₁.bonds[k].kind := by simp [kindAt, h₁]
  have hy : m₂.kindAt k = some m₂.bonds[k].kind := by simp [kindAt, h₂]
  rcases BondKind.eq_or_of_forgetDouble_eq hb with he | ⟨ha, hb'⟩ | ⟨ha, hb'⟩
  · exact he
  · rw [ha] at hx
    rw [hb'] at hy
    simp [movable_of_mem hm₁ hm₂ hx hy] at hk
  · rw [ha] at hx
    rw [hb'] at hy
    simp [movable_of_mem hm₂ hm₁ hy hx] at hk

/-- Which atoms are on the mask depends only on the endpoints of the bonds. -/
lemma onMask_eq (m : Molecule n) (mask : ℕ → Bool) (i : Fin n) :
    m.onMask mask i = (m.bonds.map Bond.forgetDouble).zipIdx.any fun p ↦ mask p.2 && p.1.touches i
    := by
  rw [onMask, List.zipIdx_map, List.any_map]
  rfl

/-- Two bonds that agree with `double` read as `single`, given kinds by a rule that agrees on
them, are equal. -/
lemma Bond.kind_update_eq {b₁ b₂ : Bond n} (he : b₁.forgetDouble = b₂.forgetDouble)
    (K : BondKind → BondKind) (hK : K b₁.kind = K b₂.kind) :
    { b₁ with kind := K b₁.kind } = { b₂ with kind := K b₂.kind } := by
  obtain ⟨s₁, d₁, k₁, r₁, n₁⟩ := b₁
  obtain ⟨s₂, d₂, k₂, r₂, n₂⟩ := b₂
  simp only [Bond.forgetDouble, Bond.mk.injEq] at he
  obtain ⟨rfl, rfl, -, rfl⟩ := he
  simpa using hK

/-- Two molecules with the same atoms, configurations and skeleton, agreeing on every bond off the
mask, give one molecule when the mask is delocalized. -/
theorem delocalizeWith_congr {m₁ m₂ : Molecule n} (mask : ℕ → Bool) (ha : m₁.atoms = m₂.atoms)
    (hb : m₁.bonds.map Bond.forgetDouble = m₂.bonds.map Bond.forgetDouble)
    (hs : m₁.stereo = m₂.stereo)
    (hk : ∀ k (h₁ : k < m₁.bonds.length) (h₂ : k < m₂.bonds.length), mask k = false →
      m₁.bonds[k].kind = m₂.bonds[k].kind) :
    m₁.delocalizeWith mask = m₂.delocalizeWith mask := by
  have hlen : m₁.bonds.length = m₂.bonds.length := by
    simpa using congrArg List.length hb
  refine Molecule.ext ?_ ?_ hs
  · refine Vector.ext fun i hi ↦ ?_
    simp only [delocalizeWith, Vector.getElem_ofFn, onMask_eq, hb, atom, ha]
  · simp only [delocalizeWith, setKinds]
    refine List.ext_getElem (by simp [hlen]) fun k hk₁ hk₂ ↦ ?_
    simp only [List.getElem_map, List.getElem_zipIdx]
    have h₁ : k < m₁.bonds.length := by simpa using hk₁
    have h₂ : k < m₂.bonds.length := by simpa using hk₂
    have he := congrArg (·[k]?) hb
    simp only [List.getElem?_map, h₁, h₂, List.getElem?_eq_getElem, Option.map_some,
      Option.some.injEq] at he
    have hkk := hk k h₁ h₂
    simp only [Nat.zero_add]
    refine Bond.kind_update_eq he (fun kd ↦ if mask k = true then .aromatic else kd) ?_
    cases hm : mask k
    · simp [hkk hm]
    · simp

/-- Kekulé partners delocalize to one molecule. -/
theorem KekulePartner.delocalize_eq {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) :
    m₁.delocalize = m₂.delocalize := by
  have hd : m₁.kekuleData = m₂.kekuleData := h
  simp only [kekuleData, Prod.mk.injEq] at hd
  have hmov : m₁.movable = m₂.movable := by
    funext k
    simp only [movable, h.kekuleClass_eq]
  rw [delocalize, delocalize, ← hmov]
  exact delocalizeWith_congr _ hd.1 hd.2.1 hd.2.2.2
    fun k h₁ h₂ hk ↦ h.kind_eq_of_not_movable h₁ h₂ hk

/-- Renumbering keeps the kind at each position. -/
@[simp] lemma kindAt_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    (m.relabel σ).kindAt k = m.kindAt k := by
  simp [kindAt, bonds_relabel, List.getElem?_map, Option.map_map, Function.comp_def]

/-- Renumbering keeps the movable bonds. -/
@[simp] lemma movable_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).movable = m.movable := by
  funext k
  simp [movable, kekuleClass_relabel, List.any_map, Function.comp_def]

/-- Renumbering moves the atoms on the mask along. -/
lemma onMask_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) (mask : ℕ → Bool) (i : Fin n) :
    (m.relabel σ).onMask mask (σ i) = m.onMask mask i := by
  simp [onMask, bonds_relabel, List.zipIdx_map, List.any_map, Function.comp_def]

/-- Delocalizing commutes with renumbering. -/
theorem delocalizeWith_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) (mask : ℕ → Bool) :
    (m.relabel σ).delocalizeWith mask = (m.delocalizeWith mask).relabel σ := by
  refine Molecule.ext (Vector.ext fun j hj ↦ ?_) (congrArg Molecule.bonds
    (setKinds_relabel m (fun k kind ↦ if mask k then .aromatic else kind) σ) :) rfl
  have key : ∀ i : Fin n, { (m.relabel σ).atom (σ i) with
      aromatic := ((m.relabel σ).atom (σ i)).aromatic || (m.relabel σ).onMask mask (σ i) } =
      { m.atom i with aromatic := (m.atom i).aromatic || m.onMask mask i } := by
    intro i
    rw [onMask_relabel, atom_relabel]
  have := key (σ.symm ⟨j, hj⟩)
  simp only [Equiv.apply_symm_apply] at this
  simp only [delocalizeWith, atoms_relabel, getElem_relabelVec, Vector.getElem_ofFn]
  exact this.trans (by simp [Fin.getElem_fin])

/-- Delocalizing the movable bonds commutes with renumbering. -/
theorem delocalize_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).delocalize = m.delocalize.relabel σ := by
  rw [delocalize, delocalize, movable_relabel, delocalizeWith_relabel]

/-! ### The canonical form -/

/-- The canonical SMILES of the Kekulé class of `m`: `m` with its movable bonds written aromatic,
canonicalized. -/
def kekuleCanonicalSmiles (m : Molecule n) : String := m.delocalize.canonicalSmiles

/-- Kekulé partners have one Kekulé canonical SMILES. -/
theorem kekuleCanonicalSmiles_eq_of_kekulePartner {m₁ m₂ : Molecule n}
    (h : m₁.KekulePartner m₂) : m₁.kekuleCanonicalSmiles = m₂.kekuleCanonicalSmiles := by
  rw [kekuleCanonicalSmiles, kekuleCanonicalSmiles, h.delocalize_eq]

/-- The Kekulé canonical SMILES does not depend on how the atoms are numbered. -/
theorem kekuleCanonicalSmiles_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).kekuleCanonicalSmiles = m.kekuleCanonicalSmiles := by
  rw [kekuleCanonicalSmiles, kekuleCanonicalSmiles, delocalize_relabel, canonicalSmiles_relabel]

/-- One step between two drawings of one molecule: renumber the atoms, or move double bonds
around closed alternating paths. -/
inductive KekuleRedraw : Molecule n → Molecule n → Prop
  /-- Renumber the atoms. -/
  | relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) : KekuleRedraw m (m.relabel σ)
  /-- Move double bonds to a Kekulé partner. -/
  | partner {m₁ m₂ : Molecule n} : m₁.KekulePartner m₂ → KekuleRedraw m₁ m₂

/-- **Uniqueness.** Two drawings joined by any chain of renumberings and Kekulé moves, in any
order and either direction, have one Kekulé canonical SMILES. -/
theorem kekuleCanonicalSmiles_eq_of_eqvGen {m₁ m₂ : Molecule n}
    (h : Relation.EqvGen KekuleRedraw m₁ m₂) :
    m₁.kekuleCanonicalSmiles = m₂.kekuleCanonicalSmiles := by
  induction h with
  | rel x y hxy =>
    cases hxy with
    | relabel σ => exact (kekuleCanonicalSmiles_relabel x σ).symm
    | partner hp => exact kekuleCanonicalSmiles_eq_of_kekulePartner hp
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Molecule

end LeanSMILES
