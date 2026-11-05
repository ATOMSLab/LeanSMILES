/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Perceive
public import LeanSMILES.SMILES.Canonicity

/-!
# LeanSMILES.Aromaticity.Resonance

When two resonance structures are one molecule, and what `Molecule.aromatize`
must do for canonical SMILES to give them one string.

`Molecule.canonicalSmiles_relabel` makes canonical SMILES independent of how
the atoms are numbered. It says nothing about bond orders. The Kekulé
structures of o-xylene, `CC1=C(C)C=CC=C1` and `CC1=CC=CC=C1C`, are different
graphs, and no renumbering turns one into the other, so they get different
strings. Whether two such drawings are one molecule is a chemical question:

* **Kekulé partners** (`Molecule.KekulePartner`) have the same atoms and the
  same skeleton, and their single and double bonds differ while every atom
  keeps its bond-order sum: the double bonds have moved around closed
  alternating paths. This is graph theory, and it relates too much. The two
  bond-shift isomers of 1,2-dimethylcyclooctatetraene are Kekulé partners and
  different compounds.
* **Resonance structures** (`Molecule.ResonanceStructure`) are Kekulé partners
  that differ only on bonds the aromaticity model marks aromatic: the π
  electrons that moved are delocalized, so both drawings describe one
  molecule. The model is RDKit's default, ported in `Molecule.aromatize`.

## The specification

Three properties of `aromatize`, stated here as `Prop`s and not yet proved.
`lake exe resonance-test` checks them on the data.

1. `AromaticBondsKekuleInvariant`: Kekulé partners get the same aromatic bonds.
2. `AromatizeMergesExactlyResonance`: Kekulé partners aromatize to one molecule
   exactly when they differ only on aromatic bonds.
3. `AromatizeRelabelKekule`: on Kekulé input, aromatizing commutes with
   relabeling.

`AromatizeRelabel` is property 3 for every input, lowercase included. It is
false: `Cc1ccccccc1C` does not say which bond-shift isomer it means, and the
kekulizer's choice depends on the atom order. RDKit behaves the same way.

## What the data say

On 2399 Kekulé structures (Delaney, the aromaticity, isotope and hydrogen
cases, EGFR and hand-picked cases), 1379 have more than one Kekulé partner and
properties 1–3 hold on every one, over 25720 pairs. Before aromatization the
partners of 1047 molecules have more than one canonical SMILES; after it, none
from the datasets do.

Three hand-picked cases keep partners apart, and these are where the model,
not the graph, decides what is one molecule:

* dimethylcyclooctatetraene, two bond-shift isomers: the right answer;
* the benzazete `Cc1cccc2ncc12`, where the four-membered ring is not aromatic;
* biphenylene, whose Kekulé structure with double bonds in the four-membered
  ring stays apart from the other four (`c1ccc=2c(c1)=c1ccccc21`). Chemically
  that is the same molecule drawn another way, so here RDKit's model is
  stricter than the chemistry.

## The bridge

Properties 2 and 3 are what the canonicity theorem needs. Two Kekulé structures
related by any chain of renumberings and resonance moves (`Molecule.Redraw`)
have the same canonical SMILES after aromatization
(`Molecule.aromaticCanonicalSmiles_eq_of_eqvGen`).
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

/-! ### Kekulé partners -/

/-- A Kekulé structure: no atom is written aromatic and no bond is aromatic. -/
def IsKekule (m : Molecule n) : Prop :=
  (∀ i, (m.atom i).aromatic = false) ∧ ∀ b ∈ m.bonds, b.kind ≠ .aromatic

instance (m : Molecule n) : Decidable m.IsKekule := by
  unfold IsKekule
  infer_instance

/-- Renumbering keeps a Kekulé structure Kekulé, and only a Kekulé structure renumbers to one. -/
theorem isKekule_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).IsKekule ↔ m.IsKekule := by
  simp only [IsKekule, bonds_relabel, List.forall_mem_map, Bond.kind_map]
  refine and_congr_left' ⟨fun h i ↦ by simpa using h (σ i), fun h i ↦ ?_⟩
  rw [← Equiv.apply_symm_apply σ i, atom_relabel]
  exact h _

/-- What all Kekulé partners of `m` share: the atoms, the bonds with `double` read as `single`,
and each atom's bond-order sum. -/
def kekuleData (m : Molecule n) : Vector Atom n × List (Bond n) × Vector ℚ n :=
  (m.atoms, m.bonds.map Bond.forgetDouble, Vector.ofFn m.bondOrderSum)

/-- `m₁` and `m₂` are Kekulé partners: one skeleton with its double bonds moved around closed
alternating paths. The atoms and the bond list are the same, position by position, except that a
bond may change between single and double; every atom keeps its bond-order sum, and so its
number of double bonds. -/
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

/-! ### The hypervalent atoms `cleanUp` rewrites

`aromatize` starts with RDKit's `cleanUp`, which rewrites a few hypervalent atoms into
charge-separated form, and which ones it rewrites can depend on where the double bonds sit. In
`O=P1=CC=CC=B1` the phosphorus has its second double bond to carbon, so `cleanUp` makes it
`[P+]-[O-]` and the ring comes out aromatic; in its Kekulé partner `O=P1C=CC=CB=1` the second
double bond goes to boron, `cleanUp` leaves it alone, and the ring does not. Moving double bonds
next to such an atom is excluded below. -/

/-- An atom RDKit's `cleanUp` may rewrite: a neutral N or P of valence 5, or a neutral Cl, Br or I
of valence 3, 5 or 7. The valence is the bond-order sum plus the hydrogens written in brackets. -/
def CleanUpTarget (m : Molecule n) (i : Fin n) : Prop :=
  (m.atom i).charge = 0 ∧
    (((m.atom i).atomicNumber = 7 ∨ (m.atom i).atomicNumber = 15) ∧
        m.bondOrderSum i + ((m.atom i).explicitH.getD 0 : ℚ) = 5 ∨
      ((m.atom i).atomicNumber = 17 ∨ (m.atom i).atomicNumber = 35 ∨
          (m.atom i).atomicNumber = 53) ∧
        (m.bondOrderSum i + ((m.atom i).explicitH.getD 0 : ℚ) = 3 ∨
          m.bondOrderSum i + ((m.atom i).explicitH.getD 0 : ℚ) = 5 ∨
          m.bondOrderSum i + ((m.atom i).explicitH.getD 0 : ℚ) = 7))

instance (m : Molecule n) (i : Fin n) : Decidable (m.CleanUpTarget i) := by
  unfold CleanUpTarget
  infer_instance

/-- No bond on which `m₁` and `m₂` differ touches an atom `cleanUp` may rewrite. The bond lists are
compared position by position, as for Kekulé partners. -/
def MovesAvoidCleanUp (m₁ m₂ : Molecule n) : Prop :=
  ∀ p ∈ m₁.bonds.zip m₂.bonds, p.1.kind ≠ p.2.kind →
    ¬ m₁.CleanUpTarget p.1.src ∧ ¬ m₁.CleanUpTarget p.1.dst

instance (m₁ m₂ : Molecule n) : Decidable (m₁.MovesAvoidCleanUp m₂) := by
  unfold MovesAvoidCleanUp
  infer_instance

/-! ### Resonance structures -/

/-- Which bonds are aromatic, in bond-list order. -/
def aromaticBonds (m : Molecule n) : List Bool := m.bonds.map (·.kind == .aromatic)

/-- Every bond at which `m₁` and `m₂` differ in kind is marked in `mask`. The bond lists are
compared position by position, as for Kekulé partners. -/
def differOnlyOn (m₁ m₂ : Molecule n) (mask : List Bool) : Bool :=
  ((m₁.bonds.zip m₂.bonds).zip mask).all fun ((b₁, b₂), a) ↦ b₁.kind == b₂.kind || a

/-- `m₂` is a resonance structure of `m₁` in the aromaticity model of `aromatize`: a Kekulé
partner that differs from `m₁` only on bonds that `m₁.aromatize` marks aromatic, and not next to
an atom `cleanUp` rewrites. -/
def ResonanceStructure (m₁ m₂ : Molecule n) : Prop :=
  m₁.KekulePartner m₂ ∧ (∃ a, m₁.aromatize = .ok a ∧ m₁.differOnlyOn m₂ a.aromaticBonds = true) ∧
    m₁.MovesAvoidCleanUp m₂

/-- The canonical SMILES of the aromatized molecule; `none` when aromatization fails. -/
def aromaticCanonicalSmiles (m : Molecule n) : Option String :=
  (m.aromatize.map canonicalSmiles).toOption

end Molecule

namespace Aromaticity

/-! ### The specification -/

/-- **Property 1.** The bonds the model makes aromatic do not depend on which Kekulé structure is
drawn, as long as the double bonds do not move next to an atom `cleanUp` rewrites
(`Molecule.MovesAvoidCleanUp`). Without that it is false: `O=P1=CC=CC=B1` comes out aromatic and
its partner `O=P1C=CC=CB=1` does not. -/
def AromaticBondsKekuleInvariant : Prop :=
  ∀ ⦃n : ℕ⦄ (m₁ m₂ : Molecule n), m₁.IsKekule → m₁.KekulePartner m₂ → m₁.MovesAvoidCleanUp m₂ →
    (m₁.aromatize.map Molecule.aromaticBonds).toOption =
      (m₂.aromatize.map Molecule.aromaticBonds).toOption

/-- **Property 2.** Kekulé partners aromatize to one molecule exactly when they differ only on
bonds the model makes aromatic. Aromatization merges resonance structures and nothing else. Like
property 1 it needs the double bonds to stay away from the atoms `cleanUp` rewrites; the same pair
`O=P1=CC=CC=B1`, `O=P1C=CC=CB=1` differs only on aromatic bonds of the first and aromatizes to two
molecules. -/
def AromatizeMergesExactlyResonance : Prop :=
  ∀ ⦃n : ℕ⦄ (m₁ m₂ a : Molecule n), m₁.IsKekule → m₁.KekulePartner m₂ →
    m₁.MovesAvoidCleanUp m₂ → m₁.aromatize = .ok a →
    (m₂.aromatize = .ok a ↔ m₁.differOnlyOn m₂ a.aromaticBonds = true)

/-- **Property 3.** On Kekulé input, aromatizing commutes with renumbering the atoms. -/
def AromatizeRelabelKekule : Prop :=
  ∀ ⦃n : ℕ⦄ (m : Molecule n) (σ : Equiv.Perm (Fin n)), m.IsKekule →
    (m.relabel σ).aromatize = m.aromatize.map (·.relabel σ)

/-- Property 3 for every input, lowercase included. **False**: when a ring written lowercase does
not come out aromatic, as in `Cc1ccccccc1C`, the input does not say where the double bonds go,
and the kekulizer's answer depends on the atom order (as RDKit's does). -/
def AromatizeRelabel : Prop :=
  ∀ ⦃n : ℕ⦄ (m : Molecule n) (σ : Equiv.Perm (Fin n)),
    (m.relabel σ).aromatize = m.aromatize.map (·.relabel σ)

end Aromaticity

namespace Molecule

open Aromaticity

variable {n : ℕ}

/-! ### The bridge -/

/-- Given property 2, resonance structures have one aromatic canonical SMILES. -/
theorem aromaticCanonicalSmiles_eq_of_resonanceStructure (h : AromatizeMergesExactlyResonance)
    {m₁ m₂ : Molecule n} (hk : m₁.IsKekule) (hr : m₁.ResonanceStructure m₂) :
    m₂.aromaticCanonicalSmiles = m₁.aromaticCanonicalSmiles := by
  obtain ⟨hp, ⟨a, ha, hd⟩, hc⟩ := hr
  simp only [aromaticCanonicalSmiles, ha, (h m₁ m₂ a hk hp hc ha).mpr hd]

/-- Given property 3, the aromatic canonical SMILES of a Kekulé structure does not depend on how
its atoms are numbered. -/
theorem aromaticCanonicalSmiles_relabel (h : AromatizeRelabelKekule) (m : Molecule n)
    (σ : Equiv.Perm (Fin n)) (hk : m.IsKekule) :
    (m.relabel σ).aromaticCanonicalSmiles = m.aromaticCanonicalSmiles := by
  simp only [aromaticCanonicalSmiles, h m σ hk]
  rcases m.aromatize with e | a
  · rfl
  · exact congrArg some (a.canonicalSmiles_relabel σ)

/-- One step between two drawings of one molecule: renumber the atoms, or move double bonds
around aromatic rings. -/
inductive Redraw : Molecule n → Molecule n → Prop
  /-- Renumber the atoms. -/
  | relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) : Redraw m (m.relabel σ)
  /-- Move double bonds around aromatic rings. -/
  | resonance {m₁ m₂ : Molecule n} : m₁.ResonanceStructure m₂ → Redraw m₁ m₂

/-- A redrawing step keeps a Kekulé structure Kekulé, in both directions. -/
lemma Redraw.isKekule_iff {m₁ m₂ : Molecule n} (h : Redraw m₁ m₂) :
    m₁.IsKekule ↔ m₂.IsKekule := by
  cases h with
  | relabel σ => exact (isKekule_relabel _ σ).symm
  | resonance hr => exact ⟨hr.1.isKekule, (kekulePartner_equivalence.symm hr.1).isKekule⟩

/-- **The bridge.** Given properties 2 and 3, any two Kekulé structures related by renumbering
and resonance moves, in any order and either direction, have one aromatic canonical SMILES. -/
theorem aromaticCanonicalSmiles_eq_of_eqvGen (h₂ : AromatizeMergesExactlyResonance)
    (h₃ : AromatizeRelabelKekule) {m₁ m₂ : Molecule n} (hk : m₁.IsKekule)
    (h : Relation.EqvGen Redraw m₁ m₂) :
    m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles := by
  suffices H : (m₁.IsKekule ↔ m₂.IsKekule) ∧
      (m₁.IsKekule → m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles) from H.2 hk
  clear hk
  induction h with
  | rel x y hxy =>
    refine ⟨hxy.isKekule_iff, fun hx ↦ ?_⟩
    cases hxy with
    | relabel σ => exact (aromaticCanonicalSmiles_relabel h₃ x σ hx).symm
    | resonance hr => exact (aromaticCanonicalSmiles_eq_of_resonanceStructure h₂ hx hr).symm
  | refl x => exact ⟨Iff.rfl, fun _ ↦ rfl⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy ↦ (ih.2 (ih.1.mpr hy)).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
    exact ⟨ih₁.1.trans ih₂.1, fun hx ↦ (ih₁.2 hx).trans (ih₂.2 (ih₁.1.mp hx))⟩

end Molecule

end LeanSMILES
