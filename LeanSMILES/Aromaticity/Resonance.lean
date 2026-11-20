/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Perceive
public import LeanSMILES.SMILES.KekuleClass

/-!
# LeanSMILES.Aromaticity.Resonance

When two resonance structures are one molecule, and what `Molecule.aromatize`
must do for canonical SMILES to give them one string.

## Main definitions

* `Molecule.CleanUpTarget`: an atom RDKit's `cleanUp` may rewrite.
* `Molecule.MovesAvoidCleanUp`, `Molecule.CleanUpTargetsApart`, `Molecule.RingsCoverCycles`: the
  hypotheses the three properties need.
* `Molecule.ResonanceStructure`: a Kekulé partner differing only on bonds the model makes aromatic.
* `Aromaticity.AromaticBondsKekuleInvariant`, `Aromaticity.AromatizeMergesExactlyResonance`,
  `Aromaticity.AromatizeRelabelKekule`: properties 1, 2 and 3 of `aromatize`, as `Prop`s.
* `Molecule.Redraw`: one step between two drawings, a renumbering or a resonance move.

## Main statements

* `Molecule.aromaticCanonicalSmiles_eq_of_resonanceStructure`: given property 2, resonance
  structures have one aromatic canonical SMILES.
* `Molecule.aromaticCanonicalSmiles_relabel`: given property 3, it does not depend on the
  numbering.
* `Molecule.aromaticCanonicalSmiles_eq_of_eqvGen`: given properties 2 and 3, any chain of
  redrawings keeps the aromatic canonical SMILES.

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
  different compounds. Kekulé partners are defined in
  `LeanSMILES.SMILES.KekuleClass`, whose canonical form merges every pair of
  them with no model of aromaticity, and which is meant to replace this file.
* **Resonance structures** (`Molecule.ResonanceStructure`) are Kekulé partners
  that differ only on bonds the aromaticity model marks aromatic: the π
  electrons that moved are delocalized, so both drawings describe one
  molecule. The model is RDKit's default, ported in `Molecule.aromatize`.

## The specification

Three properties of `aromatize`, stated here as `Prop`s:

1. `AromaticBondsKekuleInvariant`: Kekulé partners get the same aromatic bonds
   (with a second hypothesis, below).
2. `AromatizeMergesExactlyResonance`: Kekulé partners aromatize to one molecule
   exactly when they differ only on aromatic bonds.
3. `AromatizeRelabelKekule`: on Kekulé input, aromatizing commutes with
   relabeling.

As first stated, for every molecule, none of the three holds. Each needs one
hypothesis about RDKit's `cleanUp`, the first step of `aromatize`, which
rewrites a few hypervalent atoms into charge-separated form (a neutral N or P
of valence 5, a neutral Cl, Br or I of valence 3, 5 or 7;
`Molecule.CleanUpTarget`):

* Properties 1 and 2 need the moved double bonds to stay away from those atoms
  (`Molecule.MovesAvoidCleanUp`). In `O=P1=CC=CC=B1` the phosphorus has its
  second double bond to carbon, so `cleanUp` makes it `[P+]-[O-]` and the ring
  comes out aromatic; in the partner `O=P1C=CC=CB=1` that bond goes to boron,
  `cleanUp` leaves the phosphorus alone, and the ring does not.
* Property 3 needs those atoms apart: no two bonded or with a common neighbour
  (`Molecule.CleanUpTargetsApart`). `cleanUp` visits the atoms in order, and in
  `CN(C)#N(C)C` whichever nitrogen comes first becomes `[N+]`.

These are chemically exotic inputs, and `ResonanceStructure` includes the
first hypothesis. `lake exe resonance-test` checks all three properties on the
data, with and without the hypotheses, and checks that the counterexamples
still fail without them.

**Status.** Properties 1 and 2, with their hypothesis, are theorems:
`Aromaticity.aromaticBondsKekuleInvariant` and
`Aromaticity.aromatizeMergesExactlyResonance`
(`LeanSMILES.Aromaticity.ResonanceProofs`, on the lockstep simulation of
`LeanSMILES.Aromaticity.KekuleSim`). Property 3 is not proved, only checked on
the data. A proof needs `Work.relevantCycles` to give the same rings, in some
order and drawn from some atom, after renumbering. Its breadth-first search is
a `while` loop, which Lean cannot unfold. It also needs `setAromaticity` not to
depend on the order of the rings, and `cleanUp` not to depend on the order of
the atoms.

Property 1 has a second hypothesis, `Molecule.RingsCoverCycles`, about the
molecule and not about the pair: every bond on a cycle is a bond of one of the
rings perception looks at (`Work.relevantCycles`). Donor typing asks of each
double bond whether it is a ring bond, and a moved bond must get the same
answer in both partners. A moved bond lies on a cycle
(`Work.RelD.onCycle_of_D`), so with this hypothesis it is a ring bond. The
relevant cycles span the cycle space, so the hypothesis should hold of every
molecule, but `relevantCycles` searches with a `while` loop, which Lean cannot
unfold, and nothing is proved about what it returns. `resonance-test` finds no
molecule that fails it. Property 2 does not need it: there the moved bonds come
out aromatic, and a bond the model makes aromatic is a bond of one of the rings
(`Work.mem_flatMap_ringBonds_of_mem_aromaticBondList`).

`LeanSMILES.Aromaticity.Invariance` states the same merging from the other
side. Its `KekuleVariant` moves double bonds only where the output is aromatic,
and its hypothesis is on the output (`ChargesKept`: `cleanUp` rewrote nothing),
where this file's is on the input (`MovesAvoidCleanUp`: `cleanUp` may rewrite,
away from the moved bonds). Neither contains the other. Both proofs go through
`Work.Swapped` (`LeanSMILES.Aromaticity.Congruence`): two working copies that
differ only in where the double bonds sit are perceived alike.

`AromatizeRelabel` is property 3 for every input, lowercase included. It is
false even with the hypothesis: `Cc1ccccccc1C` does not say which bond-shift
isomer it means, and the kekulizer's choice depends on the atom order. RDKit
behaves the same way.

## What the data say

On 2399 Kekulé structures (Delaney, the aromaticity, isotope and hydrogen
cases, EGFR and hand-picked cases), 1379 have more than one Kekulé partner and
properties 1–3 hold on every one, over 25720 pairs, with or without their
hypotheses: the hypotheses leave out none of these pairs and molecules. Before
aromatization the partners of 1047 molecules have more than one canonical
SMILES; after it, none from the datasets do.

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
(`Molecule.aromaticCanonicalSmiles_eq_of_eqvGen`, which takes both as
hypotheses). With property 2 proved, chains of resonance moves alone need no
hypothesis (`Molecule.aromaticCanonicalSmiles_eq_of_eqvGen_resonance`), and
the full bridge needs only property 3
(`Molecule.aromaticCanonicalSmiles_eq_of_eqvGen'`).
-/

@[expose] public section

namespace LeanSMILES

namespace Molecule

variable {n : ℕ}

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

/-- The bonds of the rings aromaticity perception looks at, by their place in the bond list: the
bonds of `Work.relevantCycles`. Ring perception reads only which atoms the bonds join, so Kekulé
partners have the same ones. -/
def ringBondNumbers (m : Molecule n) : List ℕ :=
  (Aromaticity.Work.ofMolecule m).relevantCycles.toList.flatMap
    (Aromaticity.Work.ofMolecule m).ringBonds

/-- Ring perception misses no ring bond of `m`: every bond on a cycle (`Work.onCycle`: its two
atoms are still joined without it) is a bond of one of the rings perception looks at.

This should hold of every molecule, since the relevant cycles span the cycle space. It is a fact
about `Work.relevantCycles` that is not proved, so property 1 takes it as a hypothesis. It reads
only which atoms the bonds join, so Kekulé partners have it together. -/
def RingsCoverCycles (m : Molecule n) : Prop :=
  ∀ k < m.bonds.length, (Aromaticity.Work.ofMolecule m).onCycle k = true → k ∈ m.ringBondNumbers

instance (m : Molecule n) : Decidable m.RingsCoverCycles := by
  unfold RingsCoverCycles
  infer_instance

/-- No two atoms `cleanUp` may rewrite are bonded or have a common neighbour. Then its rewrites do
not touch each other, and the order it visits the atoms in does not matter. -/
def CleanUpTargetsApart (m : Molecule n) : Prop :=
  ∀ i j, i ≠ j → m.CleanUpTarget i → m.CleanUpTarget j →
    ¬ m.graph.Adj i j ∧ ∀ k, ¬ (m.graph.Adj i k ∧ m.graph.Adj j k)

instance (m : Molecule n) : Decidable m.CleanUpTargetsApart := by
  unfold CleanUpTargetsApart
  infer_instance

/-- Atom `σ i` of the relabeled molecule is one `cleanUp` may rewrite exactly when atom `i` of `m`
is. -/
lemma cleanUpTarget_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (m.relabel σ).CleanUpTarget (σ i) ↔ m.CleanUpTarget i := by
  simp only [CleanUpTarget, atom_relabel, bondOrderSum_relabel]

/-- Renumbering keeps the atoms `cleanUp` rewrites apart, and only renumbers ones that are. -/
theorem cleanUpTargetsApart_relabel (m : Molecule n) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).CleanUpTargetsApart ↔ m.CleanUpTargetsApart := by
  constructor
  · intro h i j hij hi hj
    have := h (σ i) (σ j) (σ.injective.ne hij) ((cleanUpTarget_relabel m σ i).mpr hi)
      ((cleanUpTarget_relabel m σ j).mpr hj)
    refine ⟨fun hadj ↦ this.1 ((m.relabel_adj_iff σ i j).mpr hadj), fun k hk ↦ this.2 (σ k)
      ⟨(m.relabel_adj_iff σ i k).mpr hk.1, (m.relabel_adj_iff σ j k).mpr hk.2⟩⟩
  · intro h i j hij hi hj
    obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    have := h i j (fun e ↦ hij (by rw [e])) ((cleanUpTarget_relabel m σ i).mp hi)
      ((cleanUpTarget_relabel m σ j).mp hj)
    refine ⟨fun hadj ↦ this.1 ((m.relabel_adj_iff σ i j).mp hadj), fun k hk ↦ ?_⟩
    obtain ⟨k, rfl⟩ := σ.surjective k
    exact this.2 k ⟨(m.relabel_adj_iff σ i k).mp hk.1, (m.relabel_adj_iff σ j k).mp hk.2⟩

/-- Kekulé partners have one molecular graph. -/
lemma KekulePartner.graph_eq {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) :
    m₁.graph = m₂.graph := by
  simp only [KekulePartner, kekuleData, Prod.mk.injEq] at h
  have he : m₁.edges = m₂.edges := by
    have := congrArg (List.map Bond.edge) h.2.1
    simpa [edges, List.map_map, Function.comp_def, Bond.forgetDouble, Bond.edge] using this
  ext i j
  simp only [graph, he]

/-- Kekulé partners have the same atoms `cleanUp` may rewrite. -/
lemma KekulePartner.cleanUpTarget_iff {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) (i : Fin n) :
    m₁.CleanUpTarget i ↔ m₂.CleanUpTarget i := by
  simp only [KekulePartner, kekuleData, Prod.mk.injEq] at h
  have ha : m₁.atom i = m₂.atom i := by simp [atom, h.1]
  have hs : m₁.bondOrderSum i = m₂.bondOrderSum i := by simpa using congrArg (·[i]) h.2.2.1
  simp only [CleanUpTarget, ha, hs]

/-- Of two Kekulé partners, one has the atoms `cleanUp` rewrites apart exactly when the other
does. -/
lemma KekulePartner.cleanUpTargetsApart_iff {m₁ m₂ : Molecule n} (h : m₁.KekulePartner m₂) :
    m₁.CleanUpTargetsApart ↔ m₂.CleanUpTargetsApart := by
  simp only [CleanUpTargetsApart, h.graph_eq, h.cleanUpTarget_iff]

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
its partner `O=P1C=CC=CB=1` does not.

`Molecule.RingsCoverCycles` is not about the two drawings. It says ring perception misses no ring
bond of the skeleton, which is not proved of `Work.relevantCycles`; no molecule is known to fail
it. -/
def AromaticBondsKekuleInvariant : Prop :=
  ∀ ⦃n : ℕ⦄ (m₁ m₂ : Molecule n), m₁.IsKekule → m₁.KekulePartner m₂ → m₁.MovesAvoidCleanUp m₂ →
    m₁.RingsCoverCycles →
    m₁.aromatize.map Molecule.aromaticBonds = m₂.aromatize.map Molecule.aromaticBonds

/-- **Property 2.** Kekulé partners aromatize to one molecule exactly when they differ only on
bonds the model makes aromatic. Aromatization merges resonance structures and nothing else. Like
property 1 it needs the double bonds to stay away from the atoms `cleanUp` rewrites; the same pair
`O=P1=CC=CC=B1`, `O=P1C=CC=CB=1` differs only on aromatic bonds of the first and aromatizes to two
molecules. -/
def AromatizeMergesExactlyResonance : Prop :=
  ∀ ⦃n : ℕ⦄ (m₁ m₂ a : Molecule n), m₁.IsKekule → m₁.KekulePartner m₂ →
    m₁.MovesAvoidCleanUp m₂ → m₁.aromatize = .ok a →
    (m₂.aromatize = .ok a ↔ m₁.differOnlyOn m₂ a.aromaticBonds = true)

/-- **Property 3.** On Kekulé input, aromatizing commutes with renumbering the atoms, as long as
the atoms `cleanUp` rewrites are apart (`Molecule.CleanUpTargetsApart`). Without that it is false:
`cleanUp` visits the atoms in order, and in `CN(C)#N(C)C` both nitrogens are neutral and
5-valent, so whichever comes first becomes `[N+]` and the other `[N-]`. RDKit behaves the same
way. -/
def AromatizeRelabelKekule : Prop :=
  ∀ ⦃n : ℕ⦄ (m : Molecule n) (σ : Equiv.Perm (Fin n)), m.IsKekule → m.CleanUpTargetsApart →
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
    (σ : Equiv.Perm (Fin n)) (hk : m.IsKekule) (ha : m.CleanUpTargetsApart) :
    (m.relabel σ).aromaticCanonicalSmiles = m.aromaticCanonicalSmiles := by
  simp only [aromaticCanonicalSmiles, h m σ hk ha]
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

/-- A redrawing step keeps the atoms `cleanUp` rewrites apart, in both directions. -/
lemma Redraw.cleanUpTargetsApart_iff {m₁ m₂ : Molecule n} (h : Redraw m₁ m₂) :
    m₁.CleanUpTargetsApart ↔ m₂.CleanUpTargetsApart := by
  cases h with
  | relabel σ => exact (cleanUpTargetsApart_relabel _ σ).symm
  | resonance hr => exact hr.1.cleanUpTargetsApart_iff

/-- **The bridge.** Given properties 2 and 3, any two Kekulé structures related by renumbering
and resonance moves, in any order and either direction, have one aromatic canonical SMILES, as long
as the atoms `cleanUp` rewrites are apart. -/
theorem aromaticCanonicalSmiles_eq_of_eqvGen (h₂ : AromatizeMergesExactlyResonance)
    (h₃ : AromatizeRelabelKekule) {m₁ m₂ : Molecule n} (hk : m₁.IsKekule)
    (ha : m₁.CleanUpTargetsApart) (h : Relation.EqvGen Redraw m₁ m₂) :
    m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles := by
  suffices H : (m₁.IsKekule ∧ m₁.CleanUpTargetsApart ↔ m₂.IsKekule ∧ m₂.CleanUpTargetsApart) ∧
      (m₁.IsKekule ∧ m₁.CleanUpTargetsApart →
        m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles) from H.2 ⟨hk, ha⟩
  clear hk ha
  induction h with
  | rel x y hxy =>
    refine ⟨and_congr hxy.isKekule_iff hxy.cleanUpTargetsApart_iff, fun hx ↦ ?_⟩
    cases hxy with
    | relabel σ => exact (aromaticCanonicalSmiles_relabel h₃ x σ hx.1 hx.2).symm
    | resonance hr => exact (aromaticCanonicalSmiles_eq_of_resonanceStructure h₂ hx.1 hr).symm
  | refl x => exact ⟨Iff.rfl, fun _ ↦ rfl⟩
  | symm x y _ ih => exact ⟨ih.1.symm, fun hy ↦ (ih.2 (ih.1.mpr hy)).symm⟩
  | trans x y z _ _ ih₁ ih₂ =>
    exact ⟨ih₁.1.trans ih₂.1, fun hx ↦ (ih₁.2 hx).trans (ih₂.2 (ih₁.1.mp hx))⟩

end Molecule

end LeanSMILES
