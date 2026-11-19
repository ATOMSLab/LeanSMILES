/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Congruence
public import LeanSMILES.Aromaticity.KekuleSim
public import LeanSMILES.Aromaticity.KekulizeFacts
public import LeanSMILES.Aromaticity.KekulizeCompose
public import LeanSMILES.Aromaticity.HsRestoreK
public import LeanSMILES.Aromaticity.DonorFacts
public import LeanSMILES.Aromaticity.PerceiveAgree
public import LeanSMILES.Aromaticity.PerceiveFacts
public import LeanSMILES.SMILES.Canonicity
public import LeanSMILES.SMILES.KekuleClass

/-!
# LeanSMILES.Aromaticity.Invariance

What `Molecule.aromatize` does not depend on: the numbering of the atoms, the
listing of the bonds, and which Kekulé structure of an aromatic system was
written.  With `canonicalSmiles_relabel` and `canonicalSmiles_eq_of_sameBonds`
this gives the statement a user wants: every Kekulé structure of a molecule,
with its atoms in any order and its bonds listed any way, aromatizes to one
canonical SMILES (`canonicalSmiles_aromatize_eq`).

**Status: partly proved.**  The definitions are complete and decidable, and
each statement was tested as written (below) before it was fixed.  Proved, with
only the standard axioms: `sameSkeleton_aromatize`, `stereo_aromatize`,
`IsKekule.exists_aromatize`, `IsKekule.aromaticKept`, `kind_aromatize`,
`aromatize_of_kekuleVariant_of_chargesKept` (two Kekulé structures of one
aromatic system aromatize to the same molecule; the facts it rests on are in
`Aromaticity/Passes.lean`, `Aromaticity/Congruence.lean` and
`Aromaticity/PerceiveFacts.lean`), `kekuleWitness_spec` (the Kekulé
structure the pipeline computes is one of the output; from
`Aromaticity/KekulizeFacts.lean`), and `kekuleWitness_aromatize` with
`exists_kekule_aromatize` (the witness aromatizes back to the output: the two
working copies cache the same hydrogen totals, `kekuleWitness_totals`, write
the same hydrogens or swap written for implied, `kekuleWitness_swap`, are read
alike by perception, `kekuleWitness_cand_donor`, and get their hydrogens back
in `adjustHs`, `Work.hsRestored_kekulize` and `kekuleWitness_hsRestored`; the
per-atom arithmetic is decided in `Aromaticity/HsDecide.lean`,
`Aromaticity/DonorDecide.lean` and `Aromaticity/DonorFacts.lean`).  Every
corollary is proved from the statements it names, so it is as proved as they
are.  Still `sorry`: `aromatize_relabel` and `aromatize_of_sameBonds` (both
need the ring set `Work.relevantCycles` to be canonical up to order and to
where each ring's atom list starts, and the relabeling one also needs
kekulization's walk to give every candidate atom exactly one double bond),
`aromatize_aromatize` and `aromatize_of_isKekuleSpellingOf`.
Kekulization itself is proved correct (`Work.kekulize_correct`, with the ring facts of
`Aromaticity/RingFacts.lean`).

The Kekulé statement is **false without `ChargesKept`**, so it is stated only
with it (`aromatize_of_kekuleVariant_of_chargesKept`):
`O=P1[SiH]=CC=CC=1` aromatizes to `[O-][p+]1[siH]cccc1` (`cleanUp`'s phosphorus
rule fires: P has `=O` and `=C`), while its Kekulé variant `O=P1=[SiH]C=CC=C1`
(the ring bonds flipped, every bond-order sum kept) has P's ring double bond on
silicon, so the rule does not fire and it aromatizes to itself.  RDKit 2025.09
agrees.  The headline `canonicalSmiles_aromatize_eq` assumes `ChargesKept`
anyway.

`LeanSMILES.Aromaticity.Resonance` states the Kekulé-structure result from the
input's side (no moved bond at an atom `cleanUp` may rewrite, instead of
`ChargesKept`), with its converse, and `LeanSMILES.SMILES.KekuleClass` gives a
canonical form for Kekulé structures that needs no model of aromaticity and no
hypothesis.  `IsKekule` is defined there.

## The hypotheses, and why each is there

`aromatize` is a port of RDKit's sanitization, and three of its steps look at
the molecule in an order.  Each of the four target statements is false without
a hypothesis that switches the offending step off.

* **`ChargesKept m a`** — the output has the input's formal charges, which
  holds exactly when RDKit's `cleanUp` rewrote nothing (every rewrite charges
  an atom).  `cleanUp` picks "the first" oxygen of a nitro group in *bond*
  order, so relisting the bonds of `c1ccccc1N(=O)=O` moves the charge to the
  other oxygen: the two outputs are isomorphic but not equal.  Its second pass
  handles a pair of five-valent nitrogens joined by a triple bond in *atom*
  order, so renumbering `CN(C)#N(C)CC` charges the other nitrogen: there the
  outputs are different molecules with different canonical strings.
* **`AromaticKept m a`** — every bond written aromatic comes out aromatic.
  Kekulization places the double bonds of a lowercase ring by a walk in atom
  order.  When the ring is then perceived aromatic the choice is invisible;
  when it is not, the output keeps the walk's double bonds, and renumbering
  changes them: `Cc1cc2cccc2c1` (a pentalene), `c1ccc1`, `c1ccccccc1`,
  `c1ccc2cccccc2cc1` and `Cc1cccc2ncc12` all aromatize to a different molecule
  after renumbering, the last one to a different canonical string.
* **`m.IsKekule`** — nothing written aromatic.  Then kekulization is the
  identity, `aromatize` cannot fail, and `AromaticKept` holds trivially.
* **`KekuleVariant a m m'`** — `m'` is `m` with the double bonds moved, but
  only on bonds that `a = aromatize m` has aromatic, and with every atom
  keeping its bond-order sum.  "Differ by flipping an alternating cycle" is not
  enough: `CC1=C(C)C=CC=CC=C1` and `CC1=CC=CC=CC=C1C` (1,2-dimethylcycloocta-
  tetraene) differ that way and aromatize differently, as they should, since
  nothing in them is aromatic.  In a ring that stays non-aromatic the output
  keeps the input's double bonds (`kind_aromatize`), so two inputs that
  differ there have different outputs.

Success is not claimed to be invariant.  Kekulization gives up after 100
backtracks of a walk that depends on the numbering, so a lowercase input might
in principle aromatize under one numbering and fail under another; no such
input was found (success agreed in all 101 080 renumberings tested), but the
statements about lowercase input (`aromatize_relabel`, `aromatize_aromatize`)
assume both runs succeed rather than assert it.

## Lowercase input

A lowercase molecule is related to its Kekulé structures through the output.
The output is a fixed point (`aromatize_aromatize`), and it is the image of a
Kekulé structure of itself (`exists_kekule_aromatize`, provided RDKit reads the
valences of both alike, `Molecule.SameValences`, which fails only at exotic
aromatic atoms like the `[s-]` of `c1cc2cc[s-]2cc1`, and every atom without
brackets could be written so, `Molecule.BareWritable`), both provided `cleanUp`
rewrites nothing on the second run: `O=p1ccccc1` aromatizes to
`O=P1=CC=CC=C1`, which `cleanUp` then rewrites to `[O-][p+]1ccccc1`, in RDKit
too, because the first run's `cleanUp` came before kekulization made the
`P=C`.  Both need the output's bare atoms to read back with their hydrogens,
which is why bracket normal form keeps iodine at a bond-order sum of 2 or 4
bracketed (`readsDifferentlyInRDKit`): written bare, `CC=[I]` would come back
as `CC=I`, which RDKit reads as `CC=[IH]`.  The Kekulé structure is its own atoms with the
aromatic flags cleared and each aromatic bond single or double.  Every other
Kekulé structure with the same bond-order sums then has the same image
(`aromatize_of_kekuleVariant_of_chargesKept`).

## What was tested

Each statement was checked as written — the hypotheses decided by the
instances below, the conclusions as equalities of molecules — by
`lake exe invariance-test` (`LeanSMILES/Tests/AromatizeInvariance.lean`) on
20 216 SMILES: every Kekulé structure and the lowercase form of 1 147 aromatic
molecules in random atom orders (13 701 strings); 2 719 lowercase rewrites of
stereo-rich molecules; the 2 992 strings of `datasets/*-oracle.csv`; and the
813 hard cases of `datasets/aromatize-invariance.smi` (lowercase rings that
stay non-aromatic, fused systems with one aromatic and one non-aromatic ring,
charged rings, exocyclic double bonds, annulenes, cyclophanes, large
polycyclic aromatics, the inputs `cleanUp` rewrites, hypervalent iodine and nitrogen; in
lowercase and Kekulé form and in random atom orders).  Per string: five renumberings (a rotation,
the reversal, three pseudo-random permutations), five relistings (reversed,
every bond turned round, three pseudo-random orders), and up to 64 Kekulé
variants over the aromatic bonds, enumerated exhaustively.  Only the hard
cases are in the repository; the test takes other files as arguments.

| statement | checks | failures |
|---|---|---|
| `sameSkeleton_aromatize`, `stereo_aromatize` | 20 216 | 0 |
| `IsKekule.exists_aromatize`, `IsKekule.aromaticKept` | 16 248 | 0 |
| `kind_aromatize` | 16 228 | 0 |
| `aromatize_relabel` | 100 290 | 0 |
| `IsKekule.aromatize_relabel` | 81 140 | 0 |
| `aromatize_of_sameBonds` | 100 690 | 0 |
| Kekulé statement, no `ChargesKept` (no input was a counterexample) | 77 310 | 0 |
| `aromatize_aromatize` | 20 216 | 0 |
| `exists_kekule_aromatize` (the witness below) | 20 216 | 0 |
| `canonicalSmiles_aromatize_eq` | 37 950 | 0 |

The witness tested for `exists_kekule_aromatize` is the Kekulé structure the
pipeline itself computes: the output's atoms with the aromatic flags cleared,
and each aromatic bond given the kind `Work.kekulize` gave it on the way.

Without the hypotheses, on the same inputs: relabeling fails to commute in 24
of 101 080 checks (the lowercase non-aromatic rings and the `N#N` pairs
above), and relisting changes the output in 189 of 101 080 (nitro groups
written `N(=O)=O`).  The canonical string survived relisting in all 101 080
checks with no hypothesis at all — for a nitro group the two outputs differ by
swapping two equivalent oxygens — but that is not stated here: proving it
needs that symmetry, not just this file's hypotheses.  RDKit 2025.09 shares
the first failure: it gives `Cc1cccc2ncc12` two canonical SMILES, by atom
order.
-/

@[expose] public section

namespace LeanSMILES

namespace Molecule

variable {n : ℕ}

/-! ### The relations -/

/-- Bond for bond, the same two atoms in the same orientation with the same `/` `\` mark: the
bond lists differ at most in the kinds. -/
def SameSkeleton (m m' : Molecule n) : Prop :=
  List.Forall₂ (fun b b' ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir) m.bonds m'.bonds

instance (m m' : Molecule n) : Decidable (m.SameSkeleton m') :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

/-- The formal charges of `m` are those of `a`.  For `a` the output of `aromatize m`, this says
that RDKit's `cleanUp` rewrote nothing: each of its rewrites (nitro `N(=O)=O`, azide-like `N#N`,
`P(=O)=C`, perhalogenates) gives a neutral atom a charge. -/
def ChargesKept (m a : Molecule n) : Prop := ∀ i, (a.atom i).charge = (m.atom i).charge

instance (m a : Molecule n) : Decidable (m.ChargesKept a) :=
  inferInstanceAs (Decidable (∀ i, (a.atom i).charge = (m.atom i).charge))

/-- Every atom of `m` is within the valences its element allows, as RDKit's sanitization checks
them after `cleanUp` (`Work.firstBadValence`; "Explicit valence for atom # 1 C, 5, is greater
than permitted" for `CC(C)(C)(C)(C)C`).  `aromatize` does not check this; RDKit rejects the
molecule when it fails. -/
def ValenceOk (m : Molecule n) : Prop :=
  (Aromaticity.Work.ofMolecule m).freezeHs.cleanUp.firstBadValence = none

instance (m : Molecule n) : Decidable m.ValenceOk :=
  inferInstanceAs (Decidable (_ = none))

/-- Aromatic bonds as they are written: every atom written lowercase has at least two bonds
written aromatic and at most three bonds, and every bond written aromatic joins two lowercase
atoms.  RDKit rounds the valence of an aromatic atom as if its bonds were aromatic; where this
fails the rounded valence is not the one any Kekulé structure gives the atom: a lowercase atom with
fewer than two aromatic bonds (`N[se]=CC`; `c1cC2C(=O)NC(=O)C2cc1`, whose ring passes through
uppercase carbons; `C[se]1(C)CC1`), one with four bonds (`c2\3c4c56`), or an uppercase atom with
an aromatic bond (`C:c1ccccc1`).  Of the 12 027 dataset molecules, 3 fail this, all malformed in
the second way. -/
def AromaticWritten (m : Molecule n) : Prop :=
  (∀ i, (m.atom i).aromatic = true →
    2 ≤ (m.bonds.filter fun b ↦ b.touches i && b.kind == .aromatic).length ∧
      (m.bonds.filter (·.touches i)).length ≤ 3) ∧
  ∀ b ∈ m.bonds, b.kind = .aromatic →
    (m.atom b.src).aromatic = true ∧ (m.atom b.dst).aromatic = true

instance (m : Molecule n) : Decidable m.AromaticWritten := by
  unfold AromaticWritten
  infer_instance

/-- Every atom written without brackets could be: an atom whose hydrogens are not in brackets
(`explicitH = none`) has no charge, isotope, chirality or class, and is `*` or an element of the
organic subset (`Atom.canBeBare`), one that may be written lowercase if it is aromatic (`b`, `c`,
`n`, `o`, `p`, `s`).  Every parsed molecule is so: SMILES has no other way to write an atom
without brackets.  A `Molecule` built directly need not be, and RDKit's hydrogen bookkeeping goes
wrong on some atoms it allows, such as a bare lowercase `Cl⁺` with three aromatic bonds, which
kekulization leaves with single bonds and `adjustHs` cannot give its hydrogen back. -/
def BareWritable (m : Molecule n) : Prop :=
  ∀ i, (m.atom i).explicitH = none → (m.atom i).canBeBare = true ∧
    ((m.atom i).aromatic = true → (m.atom i).element.all Element.aromaticAllowed = true)

instance (m : Molecule n) : Decidable m.BareWritable := by
  unfold BareWritable
  infer_instance

/-- RDKit's explicit valence of atom `i` less its written hydrogens (the bond part of the
valence), as it reads `m` before kekulization: rounded the RDKit way at an aromatic atom. -/
def bondValence (m : Molecule n) (i : Fin n) : ℤ :=
  ((Aromaticity.Work.prepare m).cachedValence i.val : ℤ) -
    ((Aromaticity.Work.prepare m).atoms[i.val]! : Aromaticity.WAtom).explicitHs

/-- `k` gives every atom the bond part of the valence `m` gives it.  For a Kekulé structure `k` of
an aromatic `m`, this asks RDKit's rounding of each aromatic atom's valence to land on the Kekulé
one.  It does at every atom of the 12 027 dataset molecules, but not at some exotic aromatic atoms:
`c1cc2cc[s-]2cc1` (rounded to 5, Kekulé 4), `c1c[pH2-](C)cc1`, `O=c1cc[as+2]cc1`. -/
def SameValences (m k : Molecule n) : Prop := ∀ i, k.bondValence i = m.bondValence i

instance (m k : Molecule n) : Decidable (m.SameValences k) := by
  unfold SameValences
  infer_instance

/-- Every bond of `m` written aromatic is aromatic in `a`, bond for bond.  For `a` the output of
`aromatize m`, this says that every lowercase ring of the input was perceived aromatic, so the
double bonds kekulization placed in it do not show. -/
def AromaticKept (m a : Molecule n) : Prop :=
  List.Forall₂ (fun b b' ↦ b.kind = .aromatic → b'.kind = .aromatic) m.bonds a.bonds

instance (m a : Molecule n) : Decidable (m.AromaticKept a) :=
  inferInstanceAs (Decidable (List.Forall₂ _ _ _))

/-- The pairs of atoms joined by an aromatic bond. -/
def aromaticEdges (a : Molecule n) : List (Sym2 (Fin n)) :=
  (a.bonds.filter (·.kind == .aromatic)).map Bond.edge

/-- `m'` is another Kekulé structure of `m` over the bonds `a` has aromatic: the same atoms and
configurations; bond for bond the same atoms, orientation and mark; on a bond that is aromatic
in `a`, both kinds single or double; on every other bond, the same kind; and every atom keeps
its bond-order sum, so it keeps its number of double bonds. -/
structure KekuleVariant (a m m' : Molecule n) : Prop where
  /-- The same atoms. -/
  atoms : m'.atoms = m.atoms
  /-- The same configurations. -/
  stereo : m'.stereo = m.stereo
  /-- Bond for bond: the same skeleton, and kinds that differ only where `a` is aromatic, between
  single and double. -/
  bonds : List.Forall₂ (fun b b' ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
    if b.edge ∈ a.aromaticEdges then
      (b.kind = .single ∨ b.kind = .double) ∧ (b'.kind = .single ∨ b'.kind = .double)
    else b'.kind = b.kind) m.bonds m'.bonds
  /-- Every atom keeps its bond-order sum. -/
  valence : ∀ i, m'.bondOrderSum i = m.bondOrderSum i

instance (a m m' : Molecule n) : Decidable (KekuleVariant a m m') :=
  decidable_of_iff (m'.atoms = m.atoms ∧ m'.stereo = m.stereo ∧
    List.Forall₂ (fun b b' ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
      if b.edge ∈ a.aromaticEdges then
        (b.kind = .single ∨ b.kind = .double) ∧ (b'.kind = .single ∨ b'.kind = .double)
      else b'.kind = b.kind) m.bonds m'.bonds ∧
    ∀ i, m'.bondOrderSum i = m.bondOrderSum i)
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun h ↦ ⟨h.atoms, h.stereo, h.bonds, h.valence⟩⟩

/-- `k` is a Kekulé structure of the aromatized molecule `a`: `a`'s atoms with the aromatic
flags cleared, `a`'s configurations, and `a`'s bonds with each aromatic one made single or
double and every other one left alone. -/
structure IsKekuleStructureOf (k a : Molecule n) : Prop where
  /-- The atoms of `a`, no longer flagged aromatic. -/
  atoms : ∀ i, k.atom i = { a.atom i with aromatic := false }
  /-- The same configurations. -/
  stereo : k.stereo = a.stereo
  /-- Bond for bond: the same skeleton; an aromatic bond of `a` is single or double in `k`, any
  other bond has the same kind. -/
  bonds : List.Forall₂ (fun b b' ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
    if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
    k.bonds a.bonds

instance (k a : Molecule n) : Decidable (k.IsKekuleStructureOf a) :=
  decidable_of_iff ((∀ i, k.atom i = { a.atom i with aromatic := false }) ∧ k.stereo = a.stereo ∧
    List.Forall₂ (fun b b' : Bond n ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
      if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
      k.bonds a.bonds)
    ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun h ↦ ⟨h.atoms, h.stereo, h.bonds⟩⟩

/-! ### What `aromatize` keeps -/

open Aromaticity in
/-- The working copy of a Kekulé structure has nothing aromatic, all the way to kekulization. -/
lemma IsKekule.noArom_prepare {m : Molecule n} (hk : m.IsKekule) : (Work.prepare m).NoArom :=
  Work.noArom_cacheValences ((Work.cleanRel_cleanUp _).noArom
    (Work.noArom_freezeHs (Work.noArom_ofMolecule m hk.1 hk.2)))

open Aromaticity in
/-- A Kekulé structure is kekulized to itself. -/
lemma IsKekule.kekulize_prepare {m : Molecule n} (hk : m.IsKekule) :
    (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok (Work.prepare m) :=
  Work.kekulize_of_noArom hk.noArom_prepare _

open Aromaticity in
/-- The output's charges are those `cleanUp` left. -/
lemma charge?_finish_prepare (m : Molecule n) (k : Work) (hk : Work.AfterRel (Work.prepare m) k)
    (rings : Array (List ℕ)) (i : Fin n) :
    some ((m.aromatizeOutput (k.finish rings)).atom i).charge =
      (Work.ofMolecule m).freezeHs.cleanUp.charge? i := by
  have h1 := (hk.trans (k.afterRel_finish rings))
  have hsize : i.val < (k.finish rings).atoms.size := by
    rw [h1.atoms_size]
    simp [Work.prepare, (Work.cleanRel_cleanUp _).atoms_size]
  rw [charge_aromatizeOutput, ← Work.charge?_eq_of_lt _ hsize, h1.charge]
  simp [Work.prepare]

open Aromaticity in
/-- **When the charges are kept, `cleanUp` did nothing.** -/
lemma ChargesKept.cleanUp_eq {m a : Molecule n} (k : Work) (hk : Work.AfterRel (Work.prepare m) k)
    (rings : Array (List ℕ)) (ha : m.aromatizeOutput (k.finish rings) = a) (hc : m.ChargesKept a) :
    (Work.ofMolecule m).freezeHs.cleanUp = (Work.ofMolecule m).freezeHs := by
  apply Work.cleanUp_eq_self_of_charge
  intro j
  by_cases hj : j < n
  · have h1 := charge?_finish_prepare m k hk rings ⟨j, hj⟩
    rw [ha, hc ⟨j, hj⟩] at h1
    rw [← h1, Work.charge?_freezeHs, Work.charge?_ofMolecule m ⟨j, hj⟩]
  · have h2 : ¬ j < (Work.ofMolecule m).freezeHs.cleanUp.atoms.size := by
      simpa [(Work.cleanRel_cleanUp _).atoms_size] using hj
    have h3 : ¬ j < (Work.ofMolecule m).freezeHs.atoms.size := by simpa using hj
    rw [← Work.charge?_isSome_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at h2 h3
    rw [h2, h3]

open Aromaticity in
/-- **When the charges are kept, `cleanUp` did nothing**: the working copy kekulized is the input's,
with its hydrogens frozen and valences cached. -/
lemma ChargesKept.prepare_eq {m a : Molecule n} (k : Work) (hk : Work.AfterRel (Work.prepare m) k)
    (rings : Array (List ℕ)) (ha : m.aromatizeOutput (k.finish rings) = a) (hc : m.ChargesKept a) :
    Work.prepare m = (Work.ofMolecule m).freezeHs.cacheValences := by
  simp only [Work.prepare, hc.cleanUp_eq k hk rings ha]

/-- `aromatize` changes bond kinds and nothing else about the bond list: its order, and every
bond's two atoms, orientation and `/` `\` mark, are the input's. -/
theorem sameSkeleton_aromatize {m a : Molecule n} (h : m.aromatize = .ok a) :
    m.SameSkeleton a := by
  obtain ⟨k, -, rfl⟩ := aromatize_eq_ok.mp h
  exact Aromaticity.forall₂_map_zipIdx _ _ m.bonds 0 fun _ _ _ ↦ ⟨rfl, rfl, rfl⟩

/-- `aromatize` keeps the configurations. -/
theorem stereo_aromatize {m a : Molecule n} (h : m.aromatize = .ok a) : a.stereo = m.stereo := by
  obtain ⟨k, -, rfl⟩ := aromatize_eq_ok.mp h
  rfl

/-- A Kekulé structure always aromatizes: the only step that can fail is kekulization, which has
nothing to do. -/
theorem IsKekule.exists_aromatize {m : Molecule n} (hk : m.IsKekule) :
    ∃ a, m.aromatize = .ok a := by
  exact ⟨_, aromatize_eq_ok.mpr ⟨_, hk.kekulize_prepare, rfl⟩⟩

/-- A Kekulé structure keeps every aromatic bond written in it: there is none. -/
theorem IsKekule.aromaticKept {m a : Molecule n} (hk : m.IsKekule) (h : m.aromatize = .ok a) :
    m.AromaticKept a := by
  obtain ⟨k, -, rfl⟩ := aromatize_eq_ok.mp h
  refine Aromaticity.forall₂_map_zipIdx _ _ m.bonds 0 fun b k hb hb' ↦ ?_
  exact absurd hb' (hk.2 b (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hb)))

/-- **Rings that stay non-aromatic keep their double bonds.**  For a Kekulé input whose charges
are kept, each bond of the output is either aromatic or has the kind it was written with. -/
theorem kind_aromatize {m a : Molecule n} (hk : m.IsKekule) (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) :
    List.Forall₂ (fun b b' ↦ b'.kind = .aromatic ∨ b'.kind = b.kind) m.bonds a.bonds := by
  obtain ⟨k, hkek, rfl⟩ := aromatize_eq_ok.mp h
  rw [hk.kekulize_prepare] at hkek
  cases hkek
  have hp := hc.prepare_eq _ (.refl _) _ rfl
  have hr :=
    (Aromaticity.Work.prepare m).afterRel_finish (Aromaticity.Work.prepare m).relevantCycles
  refine Aromaticity.forall₂_map_zipIdx _ _ m.bonds 0 fun b k hb ↦ ?_
  have hb := List.mk_mem_zipIdx_iff_getElem?.mp hb
  have hkind : (Aromaticity.Work.prepare m).kind? k = some b.kind := by
    rw [hp]
    simp [Aromaticity.Work.kind?, Aromaticity.Work.getElem?_ofMolecule_bonds, hb]
  change (((Aromaticity.Work.prepare m).finish _).kind? k).getD b.kind = .aromatic ∨
    (((Aromaticity.Work.prepare m).finish _).kind? k).getD b.kind = b.kind
  rcases hr.kind k with h1 | h1 <;> rw [h1]
  · exact .inr (by rw [hkind]; rfl)
  · exact .inl rfl

/-- Relabeling a Kekulé structure gives a Kekulé structure. -/
lemma IsKekule.relabel {m : Molecule n} (hk : m.IsKekule) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).IsKekule := by
  refine ⟨fun i ↦ ?_, fun b hb ↦ ?_⟩
  · obtain ⟨j, rfl⟩ := σ.surjective i
    rw [atom_relabel]
    exact hk.1 j
  · rw [bonds_relabel, List.mem_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact hk.2 b₀ hb₀

/-- Relabeling both molecules keeps `ChargesKept`. -/
lemma ChargesKept.relabel {m a : Molecule n} (hc : m.ChargesKept a) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).ChargesKept (a.relabel σ) := fun i ↦ by
  obtain ⟨j, rfl⟩ := σ.surjective i
  rw [atom_relabel, atom_relabel, hc j]

/-- An element of the right list of a `Forall₂` is related to one of the left list. -/
lemma _root_.List.Forall₂.exists_mem_left {α β : Type*} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hr _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

/-- Another Kekulé structure of a Kekulé structure is one. -/
lemma KekuleVariant.isKekule {a m m' : Molecule n} (hv : KekuleVariant a m m') (hk : m.IsKekule) :
    m'.IsKekule := by
  refine ⟨fun i ↦ ?_, fun b' hb' ↦ ?_⟩
  · simpa [atom, hv.atoms] using hk.1 i
  · obtain ⟨b, hb, -, -, -, h⟩ := hv.bonds.exists_mem_left hb'
    split at h
    · rcases h.2 with h | h <;> rw [h] <;> decide
    · rw [h]
      exact hk.2 b hb

/-- Another Kekulé structure keeps the charges kept. -/
lemma KekuleVariant.chargesKept {a m m' : Molecule n} (hv : KekuleVariant a m m')
    (hc : m.ChargesKept a) : m'.ChargesKept a := fun i ↦ by
  rw [hc i]
  simp [atom, hv.atoms]

/-! ### 1. The numbering of the atoms -/

/-- **`aromatize` commutes with relabeling.**  If `m` aromatizes to `a` keeping its charges and
every bond written aromatic, and the relabeled molecule aromatizes at all, it aromatizes to `a`
relabeled.  Both hypotheses are needed (module docstring): without `ChargesKept`,
`CN(C)#N(C)CC`; without `AromaticKept`, `Cc1cc2cccc2c1`. -/
theorem aromatize_relabel {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (σ : Equiv.Perm (Fin n))
    (h' : (m.relabel σ).aromatize = .ok a') : a' = a.relabel σ := by
  sorry

/-- For a Kekulé structure nothing has to be assumed about the relabeled run: it aromatizes, to
the relabeled output.  From `aromatize_relabel`, `IsKekule.exists_aromatize` and
`IsKekule.aromaticKept`. -/
theorem IsKekule.aromatize_relabel {m a : Molecule n} (hk : m.IsKekule)
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (σ : Equiv.Perm (Fin n)) :
    (m.relabel σ).aromatize = .ok (a.relabel σ) := by
  obtain ⟨a', h'⟩ := (hk.relabel σ).exists_aromatize
  rw [h', Molecule.aromatize_relabel h hc (hk.aromaticKept h) σ h']

/-! ### 2. The listing of the bonds -/

/-- **`aromatize` does not depend on how the bonds are listed.**  If `m` aromatizes to `a`
keeping its charges, a molecule with the same atoms, configurations and bonds — in any order,
each in either orientation — aromatizes too, to the same atoms and configurations and the same
bonds.  The output's bond list follows the input's, so the outputs are equal only up to
`SameBonds`.  `ChargesKept` is needed: relisting `c1ccccc1N(=O)=O` moves the charge that
`cleanUp` gives "the first" oxygen. -/
theorem aromatize_of_sameBonds {m m' a : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hat : m'.atoms = m.atoms) (hst : m'.stereo = m.stereo)
    (hb : m'.SameBonds m) :
    ∃ a', m'.aromatize = .ok a' ∧ a'.atoms = a.atoms ∧ a'.stereo = a.stereo ∧
      a'.SameBonds a := by
  sorry

/-! ### 3. The Kekulé structure -/

/-- Two lists related element for element: at each position both have nothing, or both have an
element, related. -/
lemma _root_.List.Forall₂.getElem? {α β : Type*} {R : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ R l₁ l₂) (k : ℕ) :
    (l₁[k]? = none ∧ l₂[k]? = none) ∨ ∃ x y, l₁[k]? = some x ∧ l₂[k]? = some y ∧ R x y := by
  induction h generalizing k with
  | nil => simp
  | cons hr _ ih =>
    cases k with
    | zero => exact .inr ⟨_, _, rfl, rfl, hr⟩
    | succ k => simpa using ih k

/-- The bonds of `withKinds`, position by position. -/
lemma getElem?_withKinds (m : Molecule n) (w : Aromaticity.Work) (k : ℕ) :
    (Aromaticity.withKinds m w)[k]? =
      m.bonds[k]?.map fun b ↦ { b with kind := (w.bonds[k]?.map (·.kind)).getD b.kind } := by
  simp only [Aromaticity.withKinds, List.getElem?_map, List.getElem?_zipIdx]
  cases m.bonds[k]? <;> simp

/-- A bond of `m` joins atoms an aromatic bond of the output `a` joins exactly when its own
output is aromatic: the outputs' bonds are `m`'s in order, and no two join the same atoms. -/
lemma edge_mem_aromaticEdges_iff {m a : Molecule n} (hs : m.SameSkeleton a) {k : ℕ} {b : Bond n}
    (hb : m.bonds[k]? = some b) :
    b.edge ∈ a.aromaticEdges ↔ ∃ b', a.bonds[k]? = some b' ∧ b'.kind = .aromatic := by
  have hk : k < m.bonds.length := (List.getElem?_eq_some_iff.mp hb).1
  have hlen := hs.length_eq
  have hka : k < a.bonds.length := hlen ▸ hk
  have hedge : (a.bonds[k]).edge = b.edge := by
    rcases hs.getElem? k with ⟨h1, -⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [hb] at h1; cases h1
    · rw [hb] at hx
      cases hx
      rw [List.getElem?_eq_getElem hka] at hy
      cases hy
      simp [Bond.edge, hxy.1, hxy.2.1]
  constructor
  · intro he
    simp only [aromaticEdges, List.mem_map, List.mem_filter, beq_iff_eq] at he
    obtain ⟨b', ⟨hb', hk'⟩, he'⟩ := he
    obtain ⟨k', hk'l, rfl⟩ := List.getElem_of_mem hb'
    have : k' = k := by
      have hnd := a.nodup
      have e : (a.bonds.map Bond.edge)[k']'(by simpa using hk'l) =
          (a.bonds.map Bond.edge)[k]'(by simpa using hka) := by
        simp [he', hedge]
      exact (List.Nodup.getElem_inj_iff hnd).mp e
    subst this
    exact ⟨_, List.getElem?_eq_getElem hka, hk'⟩
  · rintro ⟨b', hb', hk'⟩
    rw [List.getElem?_eq_getElem hka] at hb'
    cases hb'
    simp only [aromaticEdges, List.mem_map, List.mem_filter, beq_iff_eq]
    exact ⟨_, ⟨List.getElem_mem hka, hk'⟩, hedge⟩

/-- The output of the finished working copy does not see the kinds of the input's bonds: inputs
with the same atoms, configurations and skeleton give the same output. -/
lemma aromatizeOutput_eq_of_forall₂ {m m' : Molecule n} (W : Aromaticity.Work)
    (hat : m'.atoms = m.atoms) (hst : m'.stereo = m.stereo)
    (hb : List.Forall₂ (fun b b' ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir)
      m.bonds m'.bonds) (hW : W.bonds.size = m.bonds.length) :
    m'.aromatizeOutput W = m.aromatizeOutput W := by
  have hk : Aromaticity.withKinds m' W = Aromaticity.withKinds m W := by
    apply List.ext_getElem?
    intro k
    rw [getElem?_withKinds, getElem?_withKinds]
    rcases hb.getElem? k with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [h1, h2]
    · rw [hx, hy]
      have hkl : k < W.bonds.size := hW ▸ (List.getElem?_eq_some_iff.mp hx).1
      simp only [Option.map_some, Array.getElem?_eq_getElem hkl, Option.getD_some,
        Option.some.injEq]
      obtain ⟨s, d, kd, dir, ne⟩ := x
      obtain ⟨s', d', kd', dir', ne'⟩ := y
      simp only at hxy
      obtain ⟨rfl, rfl, rfl⟩ := hxy
      rfl
  simp only [aromatizeOutput, outAtom_congr hat, hk, hst]

/-- **Every Kekulé structure of an aromatic system aromatizes to the same molecule**, when the
charges are kept: if the Kekulé structure `m` aromatizes to `a`, so does every `m'` that differs
from `m` only on bonds aromatic in `a`, with each atom keeping its bond-order sum.  `ChargesKept`
is the hypothesis the headline `canonicalSmiles_aromatize_eq` has anyway; without it the
statement is false (`O=P1[SiH]=CC=CC=1`, module docstring). -/
theorem aromatize_of_kekuleVariant_of_chargesKept {m m' a : Molecule n} (hk : m.IsKekule)
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (hv : KekuleVariant a m m') :
    m'.aromatize = .ok a := by
  open Aromaticity in
  obtain ⟨k, hkek, ha⟩ := aromatize_eq_ok.mp h
  rw [hk.kekulize_prepare] at hkek
  cases hkek
  set F0 := (Work.ofMolecule m).freezeHs with hF0
  set R := (Work.prepare m).relevantCycles with hR
  have hcl : F0.cleanUp = F0 := hc.cleanUp_eq _ (.refl _) _ ha
  have hP : Work.prepare m = F0.cacheValences := by simp only [Work.prepare, ← hF0, hcl]
  have hskel := sameSkeleton_aromatize h
  -- the bonds that are aromatic in `a`
  let Fs : ℕ → Bool := fun k ↦ (a.bonds[k]?.map (·.kind == .aromatic)).getD false
  have hFs : ∀ k, Fs k = true ↔ ∃ b', a.bonds[k]? = some b' ∧ b'.kind = .aromatic := by
    intro k
    simp only [Fs]
    cases a.bonds[k]? <;> simp
  -- in the run on `m` they are made aromatic by `setAromaticity`
  have hA : ∀ k, Fs k = true →
      ((Work.prepare m).assignRadicals.setAromaticity R).kind? k = some .aromatic := by
    intro k hk'
    obtain ⟨b', hb', hk''⟩ := (hFs k).mp hk'
    rw [← ha, aromatizeOutput_bonds, getElem?_withKinds] at hb'
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hb'
    simp only at hk''
    have hbk : b.kind ≠ .aromatic := hk.2 b (List.mem_of_getElem? hb)
    have e : ((Work.prepare m).finish R).kind? k = some .aromatic := by
      unfold Work.kind?
      cases hw : ((Work.prepare m).finish R).bonds[k]? with
      | none => rw [hw] at hk''; exact absurd hk'' hbk
      | some x => rw [hw] at hk''; simpa using hk''
    simpa [Work.finish, Work.kind?, Work.finalizeHs_bonds] using e
  have h0 : ∀ k, (Work.prepare m).assignRadicals.kind? k ≠ some .aromatic := by
    intro k e
    rw [Work.kind?, Work.assignRadicals_bonds, Option.map_eq_some_iff] at e
    obtain ⟨x, hx, hxk⟩ := e
    exact hk.noArom_prepare.2 x (Array.mem_of_getElem? hx) hxk
  have hsrc := fun k (hk' : Fs k = true) ↦
    Work.of_kind?_setAromaticity _ R (hA k hk') (h0 k)
  -- the swap
  have hsw : Work.Swapped Fs (Work.ofMolecule m) (Work.ofMolecule m') := by
    -- bond `k` of `m` is in `Fs` exactly when its atoms are joined by an aromatic bond of `a`
    have hFx : ∀ k x, m.bonds[k]? = some x → (Fs k = true ↔ x.edge ∈ a.aromaticEdges) :=
      fun k x hx ↦ (hFs k).trans (edge_mem_aromaticEdges_iff hskel hx).symm
    refine ⟨?_, ?_, fun k ↦ ?_, fun k hk' ↦ ?_, fun k hk' ↦ ?_, fun i ↦ ?_⟩
    · simp only [Work.ofMolecule, Molecule.atom, hv.atoms]
    · simp [Work.ofMolecule, hv.bonds.length_eq]
    · rw [Work.getElem?_ofMolecule_bonds, Work.getElem?_ofMolecule_bonds]
      rcases hv.bonds.getElem? k with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hxy⟩
      · rw [h1, h2]
      · rw [hx, hy]
        simp [hxy.1, hxy.2.1]
    · rw [Work.kind?_ofMolecule, Work.kind?_ofMolecule]
      rcases hv.bonds.getElem? k with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hxy⟩
      · rw [h1, h2]
      · rw [hx, hy]
        have hne : x.edge ∉ a.aromaticEdges := fun he ↦ by
          rw [← hFx k x hx] at he; rw [he] at hk'; cases hk'
        obtain ⟨-, -, -, hif⟩ := hxy
        rw [if_neg hne] at hif
        simp [hif]
    · rw [Work.kind?_ofMolecule, Work.kind?_ofMolecule]
      rcases hv.bonds.getElem? k with ⟨h1, -⟩ | ⟨x, y, hx, hy, hxy⟩
      · obtain ⟨b', hb', -⟩ := (hFs k).mp hk'
        have : k < a.bonds.length := (List.getElem?_eq_some_iff.mp hb').1
        rw [← hskel.length_eq] at this
        rw [List.getElem?_eq_none_iff] at h1
        omega
      · rw [hx, hy]
        obtain ⟨-, -, -, hif⟩ := hxy
        rw [if_pos ((hFx k x hx).mp hk')] at hif
        exact ⟨⟨x.kind, rfl, hif.1⟩, ⟨y.kind, rfl, hif.2⟩⟩
    · by_cases hi : i < n
      · have e1 := Work.bondHalfSum_ofMolecule m ⟨i, hi⟩
        have e2 := Work.bondHalfSum_ofMolecule m' ⟨i, hi⟩
        rw [hv.valence ⟨i, hi⟩, ← e1] at e2
        exact_mod_cast e2
      · rw [Work.bondHalfSum_ofMolecule_of_le m (Nat.le_of_not_lt hi),
          Work.bondHalfSum_ofMolecule_of_le m' (Nat.le_of_not_lt hi)]
  -- `cleanUp` does nothing on `m'` either
  have hcl' : (Work.ofMolecule m').freezeHs.cleanUp = (Work.ofMolecule m').freezeHs := by
    refine Work.cleanUp_eq_of_quiet _ (hsw.freezeHs.quiet (Work.quiet_of_cleanUp_eq _ hcl) ?_)
    intro k hk' i hki hv
    obtain ⟨bd, hbd, -, ⟨d₁, hd₁⟩, d₂, hd₂⟩ := hsrc k hk'
    rw [Work.assignRadicals_bonds, hP, Work.cacheValences_bonds] at hbd
    have ht : F0.bonds[k]!.touches i = true := by
      simp only [Work.bondsOf, List.mem_filter] at hki
      exact hki.2
    replace ht : bd.touches i = true := by simpa [getElem!_def, hbd] using ht
    rw [hP] at hd₁ hd₂
    by_cases hi : i < F0.atoms.size
    · simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with rfl | rfl
      · exact Work.not_hypervalent_of_isAromaticCandidate F0 hi hd₁ hv
      · exact Work.not_hypervalent_of_isAromaticCandidate F0 hi hd₂ hv
    · have hz : F0.atoms[i]!.z = 0 := by
        simp [getElem!_def, Array.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl
      obtain ⟨-, ⟨hz', -⟩ | ⟨hz', -⟩⟩ := hv <;> rw [hz] at hz' <;> omega
  have hP' : Work.prepare m' = (Work.ofMolecule m').freezeHs.cacheValences := by
    simp only [Work.prepare, hcl']
  have hsw2 : Work.Swapped Fs (Work.prepare m) (Work.prepare m') := by
    rw [hP, hP']; exact hsw.freezeHs.cacheValences
  have hF : ∀ k, Fs k = true → k ∈ R.toList.flatMap (Work.prepare m).ringBonds := by
    intro k hk'
    obtain ⟨-, -, hmem, -⟩ := hsrc k hk'
    rwa [Work.ringBonds_of_bonds_eq (Work.assignRadicals_bonds _)] at hmem
  rw [aromatize_eq_ok]
  refine ⟨Work.prepare m', (hv.isKekule hk).kekulize_prepare, ?_⟩
  rw [hsw2.relevantCycles_eq, ← hR, hsw2.finish_eq R hF hA, ← ha]
  refine aromatizeOutput_eq_of_forall₂ _ hv.atoms hv.stereo
    (hv.bonds.imp fun _ _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩) ?_
  rw [Work.finish, Work.finalizeHs_bonds, (Work.afterRel_setAromaticity _ R).bonds_size,
    Work.assignRadicals_bonds, hP]
  simp [hF0, Work.ofMolecule]

/-- **`aromatize` is idempotent** when the second run's `cleanUp` rewrites nothing: an output
that aromatizes again, keeping its charges, aromatizes to itself.  This is the lowercase form of
a molecule as an input: a fixed point.  `ChargesKept` is needed: `O=p1ccccc1` aromatizes to
`O=P1=CC=CC=C1` (its ring is not aromatic, so it keeps the double bonds kekulization placed), and
that, now with `P(=O)=C`, to `[O-][p+]1ccccc1`.  RDKit 2026.09 does the same: `cleanUp` runs
before kekulization, so it does not see what kekulization makes.  `ValenceOk` is needed too:
`CC1=C[N](C)C=C1.Cl[I]Cl`, whose `[N]` RDKit rejects as four-valent, aromatizes to an output
whose iodine gains a hydrogen the second time. -/
theorem aromatize_aromatize {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (h' : a.aromatize = .ok a') (hc' : a.ChargesKept a') (hv : a.ValenceOk) : a' = a := by
  sorry

/-- The kind the witness gives bond `k` of kind `t` in the output: its kind in `K` if `t` is
aromatic, `t` otherwise. -/
def witnessKind (K : Aromaticity.Work) (k : ℕ) (t : BondKind) : BondKind :=
  if t = .aromatic then (K.bonds[k]?.map (·.kind)).getD t else t

/-- The Kekulé structure of an output `a` that a kekulized working copy `K` gives: `a`'s atoms
with the aromatic flags cleared, and each aromatic bond of `a` with the kind it has in `K`. -/
def kekuleWitness (a : Molecule n) (K : Aromaticity.Work) : Molecule n :=
  ({ a with atoms := a.atoms.map fun x ↦ { x with aromatic := false } } : Molecule n).setKinds
    (witnessKind K)

open Aromaticity in
/-- A bond that comes out of `aromatize` aromatic was single or double after kekulization. -/
lemma kind_kekulize_of_aromatic {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) {j : ℕ}
    {b : Bond n} (hb : a.bonds[j]? = some b) (harom : b.kind = .aromatic) :
    ∃ bk, K.bonds[j]? = some bk ∧ (bk.kind = .single ∨ bk.kind = .double) := by
  rw [← ha, aromatizeOutput_bonds, getElem?_withKinds] at hb
  obtain ⟨mb, hmb, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hj : j < m.bonds.length := (List.getElem?_eq_some_iff.mp hmb).1
  have hKs : K.bonds.size = m.bonds.length := by
    rw [(Work.kekulize_kindsRel hK).bonds_size]
    simp [Work.prepare, (Work.cleanRel_cleanUp _).bonds_size, Work.ofMolecule]
  have hjK : j < K.bonds.size := hKs ▸ hj
  have hjA : j < K.assignRadicals.bonds.size := by rwa [Work.assignRadicals_bonds]
  have hF : ((K.finish (Work.prepare m).relevantCycles).bonds[j]! : WBond).kind =
      if j ∈ K.assignRadicals.aromaticBondList (Work.prepare m).relevantCycles ∧
        Work.isSD (K.assignRadicals.bonds[j]! : WBond).kind then .aromatic
      else (K.assignRadicals.bonds[j]! : WBond).kind := by
    rw [Work.finish, Work.finalizeHs_bonds]
    exact Work.kind_foldl_markAromatic _ _ _ hjA
  have hFs : j < (K.finish (Work.prepare m).relevantCycles).bonds.size := by
    rw [Work.finish, Work.finalizeHs_bonds, (Work.afterRel_setAromaticity _ _).bonds_size]
    exact hjA
  simp only [Array.getElem?_eq_getElem hFs, Option.map_some, Option.getD_some] at harom
  rw [← getElem!_pos _ j hFs, hF, Work.assignRadicals_bonds] at harom
  refine ⟨K.bonds[j], Array.getElem?_eq_getElem hjK, ?_⟩
  rw [getElem!_pos _ j hjK] at harom
  split at harom
  · rename_i hsd
    simpa [Work.isSD] using hsd.2
  · exact absurd harom ((Work.kekulize_noArom hK).2 _ (Array.getElem_mem hjK))

open Aromaticity in
/-- The witness is a Kekulé structure, and a Kekulé structure of the output. -/
theorem kekuleWitness_spec {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) :
    (kekuleWitness a K).IsKekule ∧ (kekuleWitness a K).IsKekuleStructureOf a := by
  have hbonds : List.Forall₂ (fun b b' : Bond n ↦ b.src = b'.src ∧ b.dst = b'.dst ∧
      b.dir = b'.dir ∧
      if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
      (kekuleWitness a K).bonds a.bonds := by
    refine (Aromaticity.forall₂_map_zipIdx (fun (b' b : Bond n) ↦ b.src = b'.src ∧ b.dst = b'.dst ∧
      b.dir = b'.dir ∧
      if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
      _ a.bonds 0 fun b j hb ↦ ?_).flip
    refine ⟨rfl, rfl, rfl, ?_⟩
    split
    · rename_i harom
      obtain ⟨bk, hbk, hsd⟩ := kind_kekulize_of_aromatic hK ha
        (List.mk_mem_zipIdx_iff_getElem?.mp hb) harom
      simpa [witnessKind, harom, hbk] using hsd
    · rename_i harom
      simp [witnessKind, harom]
  refine ⟨⟨fun i ↦ ?_, fun b hb ↦ ?_⟩, ⟨fun i ↦ ?_, rfl, hbonds⟩⟩
  · simp [kekuleWitness, setKinds, atom]
  · obtain ⟨b', -, -, -, -, h⟩ := hbonds.flip.exists_mem_left hb
    split at h
    · rcases h with h | h <;> rw [h] <;> decide
    · rw [h]
      intro hb'
      exact absurd hb' ‹_›
  · simp [kekuleWitness, setKinds, atom]

open Aromaticity in
/-- The kekulized working copy has as many bonds as `m`. -/
lemma size_kekulized {m : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K) :
    K.bonds.size = m.bonds.length := by
  rw [(Work.kekulize_kindsRel hK).bonds_size]
  simp [Work.prepare, (Work.cleanRel_cleanUp _).bonds_size, Work.ofMolecule]

open Aromaticity in
/-- The kekulized working copy joins the atoms `m`'s bonds join. -/
lemma ends_kekulized {m : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K) (j : ℕ) :
    K.bonds[j]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      m.bonds[j]?.map (fun b ↦ (b.src.val, b.dst.val)) := by
  rw [(Work.kekulize_kindsRel hK).ends j, Work.prepare, Work.cacheValences_bonds,
    Work.ends_of_single ((Work.cleanRel_cleanUp _).bonds j), Work.freezeHs_bonds,
    Work.getElem?_ofMolecule_bonds, Option.map_map]
  rfl

/-- The witness's bonds, position by position: the output's, each aromatic one with its kind in
`K`. -/
lemma getElem?_kekuleWitness_bonds (a : Molecule n) (K : Aromaticity.Work) (j : ℕ) :
    (kekuleWitness a K).bonds[j]? =
      a.bonds[j]?.map fun b ↦ { b with kind := witnessKind K j b.kind } := by
  simp only [kekuleWitness, setKinds, List.getElem?_map, List.getElem?_zipIdx]
  cases a.bonds[j]? <;> simp

open Aromaticity in
/-- **The witness's working copy has the kekulized copy's bonds**, kinds included: a bond the
output has aromatic takes its kind in `K`, and any other kept its kind in `K` through perception. -/
lemma bonds_ofMolecule_kekuleWitness {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) :
    (Work.ofMolecule (kekuleWitness a K)).bonds = K.bonds := by
  apply Array.ext_getElem?
  intro j
  have hAR := K.afterRel_finish (Work.prepare m).relevantCycles
  rw [Work.getElem?_ofMolecule_bonds, getElem?_kekuleWitness_bonds, ← ha, aromatizeOutput_bonds,
    getElem?_withKinds]
  have he := ends_kekulized hK j
  cases hmb : m.bonds[j]? with
  | none =>
    rw [hmb, Option.map_none, Option.map_eq_none_iff] at he
    simp [he]
  | some mb =>
    rw [hmb] at he
    obtain ⟨bk, hbk, hbke⟩ := Option.map_eq_some_iff.mp he
    have hjK : j < K.bonds.size := (Array.getElem?_eq_some_iff.mp hbk).1
    have hFs : j < (K.finish (Work.prepare m).relevantCycles).bonds.size := hAR.bonds_size ▸ hjK
    have hnoA := (Work.kekulize_noArom hK).2 bk (Array.mem_of_getElem? hbk)
    have hFk := hAR.kind j
    simp only [Work.kind?, Array.getElem?_eq_getElem hFs, hbk, Option.map_some,
      Option.some.injEq] at hFk
    simp only [Option.map_some, Array.getElem?_eq_getElem hFs, Option.getD_some, hbk,
      Option.some.injEq]
    obtain ⟨bs, bd, bkk⟩ := bk
    simp only [Prod.mk.injEq] at hbke
    obtain ⟨rfl, rfl⟩ := hbke
    rcases hFk with h | h
    · rw [h]
      simp only at hnoA
      simp [witnessKind, hnoA]
    · rw [h]
      simp [witnessKind, hbk]

/-- Bracket normalization keeps the aromatic flag. -/
@[simp] lemma aromatic_normalizeBracket (x : Atom) (s : ℚ) :
    (normalizeBracket x s).aromatic = x.aromatic := by
  dsimp only [normalizeBracket]; split <;> (try split) <;> rfl

/-- Splitting an atom's hydrogens as `aromatizeOutput` does, at the atom's own count, changes
nothing. -/
lemma resplitH (x : Atom) :
    ({ x with
        explicitH := x.explicitH.map fun e ↦ min e x.totalH
        implicitH := x.totalH - (x.explicitH.map fun e ↦ min e x.totalH).getD 0 } : Atom) = x := by
  cases x with
  | mk el ar iso ch eh ih chi cl =>
    cases eh <;> simp [Atom.totalH]

open Aromaticity in
/-- An atom of the output: the output atom of the final working copy, bracket-normalized. -/
lemma atom_aromatizeOutput (m : Molecule n) (w : Work) (i : Fin n) :
    (m.aromatizeOutput w).atom i =
      normalizeBracket (m.outAtom w i) ((m.aromatizeOutput w).bondOrderSum i) := by
  unfold aromatizeOutput
  rw [atom_normalizeBrackets, bondOrderSum_normalizeBrackets]
  simp [atom]

open Aromaticity in
/-- An output atom carries the working copy's hydrogen count. -/
lemma totalH_outAtom (m : Molecule n) (w : Work) (i : Fin n) :
    (m.outAtom w i).totalH =
      w.atoms[i.val]!.frozenHs.getD (w.atoms[i.val]!.explicitHs + w.implicitHs i) := by
  simp only [outAtom, Atom.totalH]
  cases (m.atom i).explicitH <;> simp

open Aromaticity in
/-- Two final working copies that `aromatizeOutput` reads alike, on `n` atoms: the same bonds,
and on each atom the same aromaticity, charge and hydrogen count. -/
structure OutAgree (n : ℕ) (W W' : Work) : Prop where
  /-- The same bonds. -/
  bonds : W'.bonds = W.bonds
  /-- The same aromatic atoms. -/
  aromatic : ∀ i : Fin n, W'.isAromaticAtom i = W.isAromaticAtom i
  /-- The same charges. -/
  charge : ∀ i : Fin n, W'.atoms[i.val]!.charge = W.atoms[i.val]!.charge
  /-- The same hydrogen counts. -/
  hs : ∀ i : Fin n,
    W'.atoms[i.val]!.frozenHs.getD (W'.atoms[i.val]!.explicitHs + W'.implicitHs i) =
      W.atoms[i.val]!.frozenHs.getD (W.atoms[i.val]!.explicitHs + W.implicitHs i)

open Aromaticity in
/-- **Two final working copies agree on what the output reads** if, before perception, they are
read alike by it (`Work.PerceiveAgree`) with the same bonds and aromatic flags, and at every atom
of each the `adjustHs` step gives back the cached hydrogen total (`Work.HsRestored`). -/
theorem outAgree_finish {w w' : Work} {rings : Array (List ℕ)} (hn : w.atoms.size = n)
    (hp : Work.PerceiveAgree rings w.assignRadicals w'.assignRadicals)
    (hm : Work.SameMarks w.assignRadicals w'.assignRadicals)
    (hr : ∀ i < n, Work.HsRestored (w.assignRadicals.setAromaticity rings) i)
    (hr' : ∀ i < n, Work.HsRestored (w'.assignRadicals.setAromaticity rings) i) :
    OutAgree n (w.finish rings) (w'.finish rings) := by
  have hs := hp.setAromaticity hm
  have hnA : w.assignRadicals.atoms.size = n := by
    rw [(Work.afterRel_assignRadicals (w := w)).atoms_size, hn]
  have hnA' : w'.assignRadicals.atoms.size = n := by rw [hp.size, hnA]
  have hnS : (w.assignRadicals.setAromaticity rings).atoms.size = n := by
    rw [(Work.afterRel_setAromaticity _ _).atoms_size, hnA]
  have hnS' : (w'.assignRadicals.setAromaticity rings).atoms.size = n := by
    rw [(Work.afterRel_setAromaticity _ _).atoms_size, hnA']
  refine ⟨?_, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · simp only [Work.finish, Work.finalizeHs_bonds]
    exact hs.bonds
  · simp only [Work.finish, Work.isAromaticAtom_finalizeHs]
    exact congrFun hs.isAromaticAtom_eq i
  · have hF : (w.finish rings).atoms.size = n := by
      rw [(w.afterRel_finish rings).atoms_size, hn]
    have hF' : (w'.finish rings).atoms.size = n := by
      rw [(w'.afterRel_finish rings).atoms_size,
        ← (Work.afterRel_assignRadicals (w := w')).atoms_size, hnA']
    have e : some ((w'.finish rings).atoms[i.val]! : WAtom).charge =
        some ((w.finish rings).atoms[i.val]! : WAtom).charge := by
      rw [← Work.charge?_eq_of_lt _ (hF' ▸ i.isLt), ← Work.charge?_eq_of_lt _ (hF ▸ i.isLt),
        congrFun (w'.afterRel_finish rings).charge, congrFun (w.afterRel_finish rings).charge,
        ← congrFun (Work.afterRel_assignRadicals (w := w')).charge,
        ← congrFun (Work.afterRel_assignRadicals (w := w)).charge,
        Work.charge?_eq_of_lt _ (hnA' ▸ i.isLt), Work.charge?_eq_of_lt _ (hnA ▸ i.isLt),
        hp.charge]
    exact Option.some_injective _ e
  · simp only [Work.finish]
    rw [Work.frozenHs_finalizeHs_of_restored _ (hnS' ▸ i.isLt) (hr' i i.isLt),
      Work.frozenHs_finalizeHs_of_restored _ (hnS ▸ i.isLt) (hr i i.isLt), Option.getD_some,
      Option.getD_some, Work.cachedTotalHs_setAromaticity, Work.cachedTotalHs_setAromaticity,
      hp.total]

open Aromaticity in
/-- **A working copy read like the first run's final one gives the output back from the
witness**: the witness's atoms are the output's, which bracket normalization leaves alone. -/
theorem aromatizeOutput_kekuleWitness_of_agree {m a : Molecule n} {K W' : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hW : OutAgree n (K.finish (Work.prepare m).relevantCycles) W') :
    (kekuleWitness a K).aromatizeOutput W' = a := by
  subst ha
  set F := K.finish (Work.prepare m).relevantCycles with hF
  have hFs : F.bonds.size = m.bonds.length := by
    rw [hF, Work.finish, Work.finalizeHs_bonds, (Work.afterRel_setAromaticity _ _).bonds_size,
      Work.assignRadicals_bonds, size_kekulized hK]
  have hbonds : withKinds (kekuleWitness (m.aromatizeOutput F) K) W' = withKinds m F := by
    apply List.ext_getElem?
    intro j
    rw [getElem?_withKinds, getElem?_withKinds, getElem?_kekuleWitness_bonds,
      aromatizeOutput_bonds, getElem?_withKinds, hW.bonds]
    cases hmb : m.bonds[j]? with
    | none => simp
    | some mb =>
      have hj : j < F.bonds.size := hFs ▸ (List.getElem?_eq_some_iff.mp hmb).1
      simp [Array.getElem?_eq_getElem hj]
  have hk := (kekuleWitness_spec hK rfl).2
  refine Molecule.ext (Vector.ext fun j hj ↦ ?_) (by simp [hbonds])
    (by simp [kekuleWitness, setKinds])
  change ((kekuleWitness _ K).aromatizeOutput W').atom ⟨j, hj⟩ =
    (m.aromatizeOutput F).atom ⟨j, hj⟩
  set i : Fin n := ⟨j, hj⟩
  have hsum : ((kekuleWitness (m.aromatizeOutput F) K).aromatizeOutput W').bondOrderSum i =
      (m.aromatizeOutput F).bondOrderSum i := by
    simp only [bondOrderSum, bondsAt, aromatizeOutput_bonds, hbonds]
  rw [atom_aromatizeOutput, hsum]
  set N := (m.aromatizeOutput F).atom i with hN
  have hNa : N.aromatic = F.isAromaticAtom i := by
    rw [hN, atom_aromatizeOutput, aromatic_normalizeBracket]; rfl
  have hNc : N.charge = F.atoms[i.val]!.charge := by
    rw [hN, atom_aromatizeOutput, charge_normalizeBracket]; rfl
  have hNh : N.totalH =
      F.atoms[i.val]!.frozenHs.getD (F.atoms[i.val]!.explicitHs + F.implicitHs i) := by
    rw [hN, atom_aromatizeOutput, totalH_normalizeBracket, totalH_outAtom]
  have hout : (kekuleWitness (m.aromatizeOutput F) K).outAtom W' i = N := by
    have hka : ((m.aromatizeOutput F).kekuleWitness K).atom i = { N with aromatic := false } :=
      hk.atoms i
    rw [← resplitH N]
    simp only [outAtom, hka, hW.aromatic i, hW.charge i, hW.hs i, hNa, hNc, hNh]
  rw [hout, hN, atom_aromatizeOutput, normalizeBracket_normalizeBracket]

open Aromaticity in
/-- The working copy `aromatize` starts from has an atom for each atom of `m`. -/
lemma size_prepare_atoms (m : Molecule n) : (Work.prepare m).atoms.size = n := by
  simp [Work.prepare, (Work.cleanRel_cleanUp _).atoms_size, Work.ofMolecule]

open Aromaticity in
/-- The elements of a molecule's working copy. -/
lemma z?_ofMolecule (x : Molecule n) (j : ℕ) :
    (Work.ofMolecule x).atoms[j]?.map (·.z) =
      if h : j < n then some (x.atom ⟨j, h⟩).atomicNumber else none := by
  by_cases h : j < n <;> simp [Work.ofMolecule, h, atom]

open Aromaticity in
/-- The working copy `aromatize` kekulizes has the molecule's elements. -/
lemma z?_prepare (x : Molecule n) (j : ℕ) :
    (Work.prepare x).atoms[j]?.map (·.z) = (Work.ofMolecule x).atoms[j]?.map (·.z) := by
  have hc := congrArg (Option.map fun a : WAtom ↦ a.z)
    ((Work.cleanRel_cleanUp (Work.ofMolecule x).freezeHs).atoms j)
  simp only [Option.map_map, Function.comp_def] at hc
  simp only [Work.prepare, Work.getElem?_cacheValences_atoms, Option.map_map, Function.comp_def,
    hc, Work.getElem?_freezeHs_atoms]

open Aromaticity in
/-- The witness's atoms have `m`'s elements. -/
lemma atomicNumber_kekuleWitness {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) (i : Fin n) :
    ((kekuleWitness a K).atom i).atomicNumber = (m.atom i).atomicNumber := by
  rw [(kekuleWitness_spec hK ha).2.atoms i]
  subst ha
  simp [Atom.atomicNumber, atom_aromatizeOutput, outAtom]

open Aromaticity in
/-- The witness's atoms have the kekulized copy's charges. -/
lemma charge_kekuleWitness {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) (i : Fin n) :
    ((kekuleWitness a K).atom i).charge = (K.atoms[i.val]! : WAtom).charge := by
  rw [(kekuleWitness_spec hK ha).2.atoms i]
  subst ha
  rw [charge_aromatizeOutput]
  exact Work.getElem!_eq_of_map (fun x : WAtom ↦ x.charge)
    (by simpa only [Work.charge?] using congrFun (K.afterRel_finish _).charge i.val)

open Aromaticity in
/-- **The routine part of the starting relation**: after radicals, the two copies have the same
bonds (none aromatic), as many atoms, the same elements, charges and aromatic flags. -/
theorem kekuleWitness_start_basic {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) :
    let P' := (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences
    P'.assignRadicals.bonds = K.assignRadicals.bonds ∧
      P'.assignRadicals.atoms.size = K.assignRadicals.atoms.size ∧
      (∀ i : ℕ, (P'.assignRadicals.atoms[i]! : WAtom).z = (K.assignRadicals.atoms[i]! : WAtom).z) ∧
      (∀ i : ℕ, (P'.assignRadicals.atoms[i]! : WAtom).charge =
        (K.assignRadicals.atoms[i]! : WAtom).charge) ∧
      Work.SameMarks K.assignRadicals P'.assignRadicals ∧
      ∀ b ∈ K.assignRadicals.bonds, b.kind ≠ .aromatic := by
  intro P'
  have hKR := Work.kekulize_kindsRel hK
  have hnK : K.atoms.size = n := by rw [hKR.atoms_size, size_prepare_atoms]
  have hnP : P'.atoms.size = n := by simp [P', Work.ofMolecule]
  have hb : P'.assignRadicals.bonds = K.assignRadicals.bonds := by
    rw [Work.assignRadicals_bonds, Work.assignRadicals_bonds, Work.cacheValences_bonds,
      Work.freezeHs_bonds, bonds_ofMolecule_kekuleWitness hK ha]
  have hs : P'.assignRadicals.atoms.size = K.assignRadicals.atoms.size := by
    rw [(Work.afterRel_assignRadicals (w := P')).atoms_size,
      (Work.afterRel_assignRadicals (w := K)).atoms_size, hnP, hnK]
  -- elements, as options
  have hz : ∀ j : ℕ, P'.assignRadicals.atoms[j]?.map (·.z) =
      K.assignRadicals.atoms[j]?.map (·.z) := by
    intro j
    rw [Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl),
      Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl), hKR.z j, z?_prepare]
    simp only [P', Work.getElem?_cacheValences_atoms, Work.getElem?_freezeHs_atoms,
      Option.map_map, Function.comp_def]
    have e1 := z?_ofMolecule (kekuleWitness a K) j
    have e2 := z?_ofMolecule m j
    rw [e1, e2]
    split
    · rename_i h
      rw [atomicNumber_kekuleWitness hK ha ⟨j, h⟩]
    · rfl
  -- charges, as options
  have hc : ∀ j : ℕ, P'.assignRadicals.charge? j = K.assignRadicals.charge? j := by
    intro j
    rw [congrFun (Work.afterRel_assignRadicals (w := P')).charge,
      congrFun (Work.afterRel_assignRadicals (w := K)).charge]
    simp only [P', Work.charge?_cacheValences, Work.charge?_freezeHs]
    by_cases h : j < n
    · rw [Work.charge?_ofMolecule (kekuleWitness a K) ⟨j, h⟩, charge_kekuleWitness hK ha ⟨j, h⟩,
        Work.charge?_eq_of_lt _ (hnK ▸ h)]
    · have h1 : (Work.ofMolecule (kekuleWitness a K)).atoms.size ≤ j := by
        simp [Work.ofMolecule]
        omega
      have h2 : K.atoms.size ≤ j := by omega
      simp only [Work.charge?, Array.getElem?_eq_none h1, Array.getElem?_eq_none h2,
        Option.map_none]
  -- aromatic flags: none on either side
  have hfK : ∀ j : ℕ, K.assignRadicals.atoms[j]?.map (·.aromatic) =
      K.atoms[j]?.map fun _ ↦ false := by
    intro j
    rw [Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl)]
    cases hj : K.atoms[j]? with
    | none => rfl
    | some x =>
      simp only [Option.map_some, Option.some.injEq]
      exact (Work.kekulize_noArom hK).1 x (Array.mem_of_getElem? hj)
  have hfP : ∀ j : ℕ, P'.assignRadicals.atoms[j]?.map (·.aromatic) =
      P'.atoms[j]?.map fun _ ↦ false := by
    intro j
    rw [Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl)]
    simp only [P', Work.getElem?_cacheValences_atoms, Work.getElem?_freezeHs_atoms,
      Option.map_map, Function.comp_def]
    by_cases h : j < n
    · have := (kekuleWitness_spec hK ha).1.1 ⟨j, h⟩
      simpa [Work.ofMolecule, h, atom] using this
    · simp [Work.ofMolecule, h]
  refine ⟨hb, hs, fun i ↦ Work.getElem!_eq_of_map (fun x : WAtom ↦ x.z) (hz i),
    fun i ↦ Work.getElem!_eq_of_map (fun x : WAtom ↦ x.charge)
      (by simpa only [Work.charge?] using hc i),
    ⟨hb, fun j ↦ ?_⟩, fun b hb' ↦ ?_⟩
  · rw [hfP j, hfK j]
    by_cases h : j < n
    · rw [Array.getElem?_eq_getElem (hnP ▸ h), Array.getElem?_eq_getElem (hnK ▸ h)]
      rfl
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  · rw [Work.assignRadicals_bonds] at hb'
    exact (Work.kekulize_noArom hK).2 b hb'

open Aromaticity in
/-- `assignRadicals` keeps every cached valence. -/
lemma Work.cachedValence_assignRadicals (w : Work) (i : ℕ) :
    w.assignRadicals.cachedValence i = w.cachedValence i := by
  have h1 : (w.assignRadicals.atoms[i]! : WAtom).cachedValence =
      (w.atoms[i]! : WAtom).cachedValence :=
    Work.getElem!_eq_of_map (fun x : WAtom ↦ x.cachedValence)
      (Work.getElem?_assignRadicals_map w _ (fun _ ↦ rfl) i)
  have h2 : (w.assignRadicals.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs :=
    Work.getElem!_eq_of_map (fun x : WAtom ↦ x.explicitHs)
      (Work.getElem?_assignRadicals_map w _ (fun _ ↦ rfl) i)
  simp only [Work.cachedValence, Work.kekuleValence, h1, h2,
    Work.bondHalfSum_congr (Work.assignRadicals_bonds w)]

open Aromaticity in
lemma Work.explicitHs_assignRadicals (w : Work) (i : ℕ) :
    (w.assignRadicals.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs :=
  Work.getElem!_eq_of_map (fun x : WAtom ↦ x.explicitHs)
    (Work.getElem?_assignRadicals_map w _ (fun _ ↦ rfl) i)

open Aromaticity in
/-- `cacheValences` caches every atom's explicit valence. -/
lemma Work.cachedValence_cacheValences_atom (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    (w.cacheValences.atoms[i]! : WAtom).cachedValence = some (w.explicitValence i) := by
  rw [getElem!_pos _ i (by simpa [Work.cacheValences, Work.numAtoms] using hi)]
  simp [Work.cacheValences, Work.numAtoms]

open Aromaticity in
/-- **The kekulized copy's cached valence, less its written hydrogens, is its Kekulé bond-order
sum**, when RDKit gives the witness the input's valences (`Molecule.SameValences`): at an atom
kekulization leaves alone, the cached valence is the input's, which is the witness's, whose bonds
are the kekulized ones; at the nitrogen and phosphorus `clearAromatic` rewrites, kekulization
caches the Kekulé sum itself. -/
theorem kekuleWitness_kekule {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs)
    (i : ℕ) :
    (K.assignRadicals.cachedValence i : ℤ) - (K.assignRadicals.atoms[i]! : WAtom).explicitHs =
      ((K.assignRadicals.bondHalfSum i / 2 : ℕ) : ℤ) := by
  rw [Work.cachedValence_assignRadicals, Work.explicitHs_assignRadicals,
    Work.bondHalfSum_congr (Work.assignRadicals_bonds K)]
  have hnK : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  by_cases hi : i < n
  · rcases Work.kekulize_cvOk hK i with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- as `prepare` cached it: the witness's bond part
      have hP : ((Work.prepare m).atoms[i]! : WAtom).cachedValence =
          some ((Work.ofMolecule m).freezeHs.cleanUp.explicitValence i) := by
        unfold Work.prepare
        apply Work.cachedValence_cacheValences_atom
        rw [(Work.cleanRel_cleanUp _).atoms_size]
        simpa [Work.ofMolecule, Work.freezeHs, Work.numAtoms] using hi
      have hKc : K.cachedValence i = (Work.prepare m).cachedValence i := by
        simp only [Work.cachedValence, h1, hP, Option.getD_some]
      rw [hKc, h2, ← hsv i hi]
      obtain ⟨hk, -⟩ := kekuleWitness_spec hK ha
      have hna := Work.noArom_freezeHs (Work.noArom_ofMolecule (kekuleWitness a K) hk.1 hk.2)
      have := Work.cachedValence_sub_of_noArom hna i
      rw [Work.cachedValence_assignRadicals, Work.explicitHs_assignRadicals] at this
      rw [this, Work.bondHalfSum_congr (w := K) (w' := _) ?_]
      · rw [Work.assignRadicals_bonds, Work.cacheValences_bonds, Work.freezeHs_bonds,
          bonds_ofMolecule_kekuleWitness hK ha]
    · -- kekulization cached the Kekulé sum
      simp only [Work.cachedValence, h2, Option.getD_some, h1, CharP.cast_eq_zero, sub_zero]
  · -- beyond the atoms: nothing cached, nothing written
    have hd : (K.atoms[i]! : WAtom) = default := getElem!_neg K.atoms i (by omega)
    have hcv : (default : WAtom).cachedValence = none := rfl
    have he : (default : WAtom).explicitHs = 0 := rfl
    simp only [Work.cachedValence, Work.kekuleValence, hd, hcv, he, Option.getD_none, add_zero,
      Nat.cast_zero, sub_zero]

open Aromaticity in
/-- The output's working copy has the final working copy's bonds. -/
lemma bonds_ofMolecule_output {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) :
    (Work.ofMolecule a).bonds = (K.finish (Work.prepare m).relevantCycles).bonds := by
  apply Array.ext_getElem?
  intro j
  have hAR := K.afterRel_finish (Work.prepare m).relevantCycles
  rw [Work.getElem?_ofMolecule_bonds, ← ha, aromatizeOutput_bonds, getElem?_withKinds]
  have he := ends_kekulized hK j
  have hFe := Work.ends_of_single (hAR.bonds j)
  cases hmb : m.bonds[j]? with
  | none =>
    rw [hmb, Option.map_none, Option.map_eq_none_iff] at he
    rw [he, Option.map_none, Option.map_eq_none_iff] at hFe
    simp [hFe]
  | some mb =>
    rw [hmb] at he
    obtain ⟨bk, hbk, hbke⟩ := Option.map_eq_some_iff.mp he
    rw [hbk, Option.map_some] at hFe
    obtain ⟨bf, hbf, hbfe⟩ := Option.map_eq_some_iff.mp hFe
    simp only [Option.map_some, hbf, Option.getD_some, Option.some.injEq]
    obtain ⟨fs, fd, fk⟩ := bf
    simp only [Prod.mk.injEq] at hbke hbfe
    simp [hbfe.1, hbfe.2, hbke.1, hbke.2]

open Aromaticity in
/-- The bonds of the output at atom `i` have the kinds perception left. -/
lemma kindsAt_aromatizeOutput {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a) (i : Fin n) :
    (a.bonds.filter (·.touches i)).map (·.kind) =
      (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt i := by
  rw [← Work.kindsAt_ofMolecule]
  simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, bonds_ofMolecule_output hK ha,
    Work.finish, Work.finalizeHs_bonds]

set_option maxHeartbeats 4000000 in -- one long case analysis over the records of both copies
open Aromaticity in
/-- **The witness's copy and the kekulized copy cache the same hydrogen totals.** -/
theorem kekuleWitness_totals {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs)
    (i : ℕ) :
    (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.cachedTotalHs i =
      K.assignRadicals.cachedTotalHs i := by
  rw [Work.cachedTotalHs_assignRadicals, Work.cachedTotalHs_assignRadicals]
  have hnK : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  by_cases hi : i < n
  swap
  · have h1 : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! : WAtom) =
        default := getElem!_neg _ i (by simp [Work.ofMolecule]; omega)
    have h2 : (K.atoms[i]! : WAtom) = default := getElem!_neg _ i (by omega)
    simp only [Work.cachedTotalHs, h1, h2]
  set i' : Fin n := ⟨i, hi⟩ with hi'
  -- the witness's side: written hydrogens, and RDKit's count on the Kekulé bonds
  set A := a.atom i' with hA
  have hkA : (kekuleWitness a K).atom i' = { A with aromatic := false } :=
    (kekuleWitness_spec hK ha).2.atoms i'
  have hW : (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedTotalHs i =
      A.explicitH.getD 0 + Loc.impl
        { z := A.atomicNumber, aromatic := false, charge := A.charge,
          explicitHs := A.explicitH.getD 0, noImplicit := A.explicitH.isSome || A.element.isNone }
        (Loc.bhs (K.kindsAt i)) false := by
    have hb : (Work.ofMolecule (kekuleWitness a K)).freezeHs.bonds = K.bonds := by
      rw [Work.freezeHs_bonds, bonds_ofMolecule_kekuleWitness hK ha]
    have hka : (Work.ofMolecule (kekuleWitness a K)).freezeHs.kindsAt i = K.kindsAt i := by
      simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hb]
    have hfa := Work.freezeHs_ofMolecule_atom (kekuleWitness a K) i'
    rw [hkA] at hfa
    have hnoar : (K.kindsAt i).any (· == .aromatic) = false := by
      rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hlt := Work.lt_of_mem_bondsOf hk
      rw [getElem!_pos K.bonds k hlt]
      simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
    have har : (Work.ofMolecule (kekuleWitness a K)).freezeHs.isAromaticAtom i = false := by
      rw [Work.isAromaticAtom_eq_loc, hka, hnoar]
      change (((Work.ofMolecule (kekuleWitness a K)).freezeHs.atoms[i'.val]! : WAtom).aromatic ||
        false) = false
      rw [hfa]
      rfl
    unfold Work.cachedTotalHs
    have hc := Work.freezeCache_atom (kekuleWitness a K) i'
    rw [hkA] at hc
    change (((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).explicitHs + _) = _
    rw [hc]
    dsimp only
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hka, har]
    congr 1
    apply Loc.impl_congr <;> (rw [hfa]; try rfl)
  rw [hW]
  set P := Work.prepare m with hP
  set R := P.relevantCycles with hR
  set KR := K.assignRadicals with hKR
  set S := KR.setAromaticity R with hS
  set F := K.finish R with hF
  obtain ⟨hmarks, harS, hperc⟩ := Work.perceived_atom hK i
  have hkek := Work.kindsAt_kekulize_mem hw.1 hw.2 hK i'
  have hnS : i < S.atoms.size := by
    rw [(Work.afterRel_setAromaticity KR R).atoms_size,
      (Work.afterRel_assignRadicals (w := K)).atoms_size, hnK]; exact hi
  set T := K.cachedTotalHs i with hT
  have hFT : (F.atoms[i]! : WAtom).frozenHs = some T := by
    have hr := Work.hsRestored_kekulize hw.1 hw.2 hbw hK i'
    rw [hF, Work.finish, Work.frozenHs_finalizeHs_of_restored _ hnS hr,
      Work.cachedTotalHs_setAromaticity, Work.cachedTotalHs_assignRadicals]
  -- the output atom, before bracket normalization
  set O := m.outAtom F i' with hOdef
  have hAO : A = normalizeBracket O (a.bondOrderSum i') := by
    have := atom_aromatizeOutput m F i'
    rw [ha] at this
    exact this
  have hOtot : O.totalH = T := by
    rw [hOdef, totalH_outAtom]
    change ((F.atoms[i]! : WAtom).frozenHs.getD _) = T
    rw [hFT]; rfl
  have hOH : O.explicitH = (m.atom i').explicitH.map (min · T) := by
    simp only [hOdef, Molecule.outAtom]
    change Option.map (fun x ↦ min x ((F.atoms[i]! : WAtom).frozenHs.getD _)) _ = _
    rw [hFT]; rfl
  have hOel : O.element = (m.atom i').element := by simp [hOdef, Molecule.outAtom]
  have hOz : O.atomicNumber = (m.atom i').atomicNumber := by
    simp [Atom.atomicNumber, hOel]
  have hOc : O.charge = (K.atoms[i]! : WAtom).charge := by
    change (F.atoms[i]! : WAtom).charge = _
    exact Work.getElem!_eq_of_map (fun x : WAtom ↦ x.charge)
      (by simpa only [Work.charge?] using congrFun (K.afterRel_finish R).charge i)
  have hOar : O.aromatic = (S.kindsAt i).any (· == .aromatic) := by
    simp only [hOdef, Molecule.outAtom]
    rw [hF, Work.finish, Work.isAromaticAtom_finalizeHs]
    exact harS
  have hsum : a.bondOrderSum i' = ((S.kindsAt i).map BondKind.order).sum := by
    simp only [Molecule.bondOrderSum, Molecule.bondsAt]
    rw [show (fun x : Bond n ↦ x.kind.order) = BondKind.order ∘ Bond.kind from rfl,
      ← List.map_map, kindsAt_aromatizeOutput hK ha i']
  -- `P`'s record at `i`
  set C := Work.cleaned m with hC
  have hPa : (P.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs,
        cachedValence := some (C.explicitValence i), cachedImplicit := C.implicitHs i,
        adjustHs := C.isAromaticAtom i } := by
    rw [hP, Work.prepare_atom, hC]
    conv_lhs => rw [Work.cleaned_atom, Work.ofMolecule_atom]
  have hCa : (C.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs } := by
    conv_lhs => rw [hC, Work.cleaned_atom, Work.ofMolecule_atom]
  have hCk : C.kindsAt i = P.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hP, Work.prepare_eq,
      Work.cacheValences_bonds, hC]
  have hPc : (P.atoms[i'.val]! : WAtom).charge = (C.atoms[i'.val]! : WAtom).charge := by rw [hPa]
  -- the case split: how the output writes atom `i`, and how kekulization left it
  -- an aromatic bond at `i` makes `i` lowercase
  have hflag : (P.kindsAt i).any (· == .aromatic) = true → (m.atom i').aromatic = true := by
    intro h
    have hf := Work.kindsAt_prepare m i'
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨y, hy, hxy⟩ := Work.forall₂_exists_right hf _ hx
    have hy' : y = .aromatic := hxy.1 rfl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hbm, hbt⟩ := List.mem_filter.1 hb
    obtain ⟨h1, h2⟩ := hw.2 b hbm hy'
    simp only [Bond.touches, Bool.or_eq_true, beq_iff_eq] at hbt
    rcases hbt with e | e
    · rw [← e]; exact h1
    · rw [← e]; exact h2
  have hCar : C.isAromaticAtom i = (m.atom i').aromatic := by
    rw [Work.isAromaticAtom_eq_loc, hCk]
    have : (C.atoms[i]! : WAtom).aromatic = (m.atom i').aromatic := by
      change (C.atoms[i'.val]! : WAtom).aromatic = _; rw [hCa]
    rw [this]
    cases hfa : (m.atom i').aromatic
    · cases hany : (P.kindsAt i).any (· == .aromatic)
      · rfl
      · rw [hflag hany] at hfa; cases hfa
    · rfl
  have hCimpl : C.implicitHs i = Loc.impl (C.atoms[i'.val]! : WAtom) (Loc.bhs (P.kindsAt i))
      (m.atom i').aromatic := by
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hCk, hCar]
  -- **a bare atom of `m`**: RDKit's count on the Kekulé bonds is the one cached before
  have hMN : (m.atom i').explicitH = none → ∀ e, (m.atom i').element = some e →
      Loc.impl
          { z := (m.atom i').atomicNumber, aromatic := false,
            charge := (C.atoms[i'.val]! : WAtom).charge, explicitHs := 0, noImplicit := false }
          (Loc.bhs (K.kindsAt i)) false = C.implicitHs i := by
    intro hnone e hae
    obtain ⟨hcb, haro⟩ := hbw i' hnone
    have hcb' := hcb
    simp only [Atom.canBeBare, hnone, hae, Option.isNone_none, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq] at hcb'
    obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
    have hz : (m.atom i').atomicNumber = e.atomicNumber := by simp [Atom.atomicNumber, hae]
    have hCz : (C.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hCa]
    have hCe : (C.atoms[i'.val]! : WAtom).explicitHs = 0 := by rw [hCa]; simp [hnone]
    have hCn : (C.atoms[i'.val]! : WAtom).noImplicit = false := by rw [hCa]; simp [hnone, hae]
    rw [hCimpl]
    set c := (C.atoms[i'.val]! : WAtom).charge with hcdef
    set pk := P.kindsAt i with hpkdef
    by_cases hfa : (m.atom i').aromatic = true
    · -- written lowercase: the decided check
      have hzin : e.atomicNumber ∈ ([5, 6, 7, 8, 15, 16] : List ℕ) :=
        Work.organic_aromatic_z e (by simpa using horg) (.inr (by simpa [hae] using haro hfa))
      have hzc : (e.atomicNumber, c) ∈ Loc.bareZC := by
        have hcc := (Work.cleanFine_cleaned m).charge i'
        obtain ⟨hFz, hFc⟩ := Work.freezeHs_atom_z_charge m i'
        rw [hFz, hFc, hch0, hz, ← hC, ← hcdef] at hcc
        simp only [CleanCharge] at hcc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzin
        rcases hzin with h | h | h | h | h | h <;> rw [h] at hcc ⊢ <;>
          rcases hcc with h' | h' | ⟨h', h''⟩ | h' | h' | h' <;>
          first
          | (rw [h']; decide)
          | omega
      obtain ⟨c1, c2⟩ := Work.kindsAt_prepare_counts m i'
      obtain ⟨h1, h2⟩ := hw.1 i' hfa
      have hpk3 : pk.length ≤ 3 := c1 ▸ h2
      have hnar : 2 ≤ (pk.filter (· == .aromatic)).length := c2 ▸ h1
      -- `candOf` is `bareP`'s need
      have hPev : Loc.ev (P.atoms[i'.val]! : WAtom) (Loc.bhs pk) true =
          (Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0 := by
        simp only [Loc.bareP, Option.getD_some]
        apply Loc.ev_congr
        · rw [hPa, hz]
        · rw [hPa]
        · rw [hPa, hnone]; rfl
      have hPar : P.isAromaticAtom i = true := by
        rw [Work.isAromaticAtom_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this]; rfl
      have hcand : Work.candOf P P.kekWa P.kekEv0 i =
          Loc.ndb (Loc.bareP e.atomicNumber c true pk) pk
            ((Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0) := by
        have hPlt : i < P.atoms.size := by
          rw [hP, Work.prepare_eq, Work.size_cacheValences_atoms, Work.size_cleaned]; exact hi
        unfold Work.candOf
        rw [Work.kekWa_eq, Work.needsDoubleBond_eq_loc, Work.kekEv0_getElem! P hPlt,
          Work.explicitValence_eq_loc, hPar, Work.bondHalfSum_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this, Bool.true_and]
        change Loc.ndb (P.atoms[i'.val]! : WAtom) pk (Loc.ev (P.atoms[i'.val]! : WAtom) _ true) = _
        rw [hPev]
        apply Loc.ndb_congr
        · rw [hPa, hz]; rfl
        · rw [hPa]; rfl
        · rw [hPa, hnone]; rfl
        · rw [hPa]; simp [hnone, hae, Loc.bareP]
        · rw [hPa, hCimpl, hfa]
          simp only [Loc.bareP]
          apply Loc.impl_congr
          · rw [hCz, hz]
          · rfl
          · exact hCe
          · exact hCn
        · rw [hPa]; rfl
      have hkk := hkek
      rw [hcand] at hkk
      have hb := Loc.bareKek_ok
      rw [List.all_eq_true] at hb
      have := hb _ hzc
      rw [List.all_eq_true] at this
      have hc := this pk (Loc.mem_lists 3 pk hpk3)
      unfold Loc.bareKekCheck at hc
      have hs1 : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length) ||
          !([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber) = false := by
        have hzin' : ([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber = true :=
          List.contains_iff_mem.2 hzin
        rw [hzin']
        simp only [Bool.not_true, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not,
          not_lt]
        omega
      rw [if_neg (by rw [hs1]; decide), List.all_eq_true] at hc
      have := hc _ hkk
      rw [beq_iff_eq] at this
      rw [hfa]
      calc Loc.impl _ (Loc.bhs (K.kindsAt i)) false
          = Loc.impl { Loc.bareP e.atomicNumber c true pk with aromatic := false }
              (Loc.bhs (K.kindsAt i)) false := by
            apply Loc.impl_congr
            · simp [Loc.bareP, hz]
            · rfl
            · rfl
            · rfl
        _ = (Loc.bareP e.atomicNumber c true pk).cachedImplicit := this
        _ = _ := by
            simp only [Loc.bareP]
            apply Loc.impl_congr
            · rw [hCz, hz]
            · rfl
            · exact hCe.symm
            · exact hCn.symm
    · -- not lowercase: no aromatic bond, kekulization changed nothing here
      rw [Bool.not_eq_true] at hfa
      have hpk : pk.any (· == .aromatic) = false := by
        cases h : pk.any (· == .aromatic)
        · rfl
        · rw [hflag h] at hfa; cases hfa
      rw [Work.kekAll_eq_of_noArom hkek hpk, hfa]
      apply Loc.impl_congr
      · exact hCz.symm
      · rfl
      · exact hCe.symm
      · exact hCn.symm
  have hCn : (C.atoms[i'.val]! : WAtom).noImplicit =
      ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) := by rw [hCa]
  have hC0 : ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) = true →
      C.implicitHs i = 0 := by
    intro h
    rw [hCimpl]
    simp [Loc.impl, hCn, h]
  rcases Work.kekulize_atom hK i with hKa | ⟨hbr, hKa⟩
  · -- kekulization only cleared the flag
    have hKi : (K.atoms[i]! : WAtom) = { (P.atoms[i'.val]! : WAtom) with aromatic := false } := hKa
    have hT' : T = (m.atom i').explicitH.getD 0 + C.implicitHs i := by
      rw [hT, Work.cachedTotalHs, hKi]
      change (P.atoms[i'.val]! : WAtom).explicitHs + (P.atoms[i'.val]! : WAtom).cachedImplicit = _
      rw [hPa]
    have hKc : (K.atoms[i]! : WAtom).charge = (C.atoms[i'.val]! : WAtom).charge := by
      rw [hKi]; exact hPc
    rw [hAO]
    unfold normalizeBracket
    dsimp only
    split_ifs with hcb hbare
    · -- written bare
      set b : Atom := { O with explicitH := none, implicitH := 0 } with hbdef
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hbare
      obtain ⟨hsm, hrd⟩ := hbare
      rw [hOtot] at hsm
      simp only [Option.getD_none, Nat.zero_add, Option.isSome_none, Bool.false_or]
      have hz' : ({ b with implicitH := O.totalH } : Atom).atomicNumber =
          (m.atom i').atomicNumber := hOz
      have hel' : ({ b with implicitH := O.totalH } : Atom).element = (m.atom i').element := hOel
      have hc' : ({ b with implicitH := O.totalH } : Atom).charge =
          (C.atoms[i'.val]! : WAtom).charge := by rw [← hKc]; exact hOc
      rw [hz', hel', hc']
      cases hme : (m.atom i').element with
      | none =>
        -- `*`: OpenSMILES gives it no hydrogen, so it has none
        have hb0 : Molecule.implicitHydrogens b (a.bondOrderSum i') = 0 := by
          unfold Molecule.implicitHydrogens
          rw [show b.element = none from hOel.trans hme]
        simp [Loc.impl, ← hsm, hb0]
      | some e =>
        simp only [Option.isNone_some]
        cases hmh : (m.atom i').explicitH with
        | none =>
          rw [hT', hmh]
          simp only [Option.getD_none, Nat.zero_add]
          exact hMN hmh e hme
        | some eh =>
          -- bracketed in `m`, bare in the output: OpenSMILES's count is RDKit's
          have hTe : T = eh := by rw [hT', hmh, hC0 (by simp [hmh])]; rfl
          have hcb' := hcb
          simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb'
          obtain ⟨⟨⟨⟨⟨-, -⟩, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
          have hbel : b.element = some e := hOel.trans hme
          rw [hbel] at horg
          have horg' : e ∈ Loc.organic := Loc.mem_organic e horg
          have hc0 : (C.atoms[i'.val]! : WAtom).charge = 0 := by
            rw [← hKc, ← hOc]; exact hch0
          have hz : (m.atom i').atomicNumber = e.atomicNumber := by
            simp [Atom.atomicNumber, hme]
          rw [hc0, hz, ← hsm]
          -- `b` reads like the bare element
          set aromS := (S.kindsAt i).any (· == .aromatic) with haromS
          have hbar : b.aromatic = aromS := hOar
          have hsm' : Molecule.implicitHydrogens b (a.bondOrderSum i') =
              Molecule.implicitHydrogens { element := some e, aromatic := aromS }
                (((S.kindsAt i).map BondKind.order).sum) := by
            rw [hsum]
            exact Loc.implicitHydrogens_congr (a := b)
              (b := ({ element := some e, aromatic := aromS } : Atom)) hbel hbar rfl _
          have hrd' : Molecule.readsDifferentlyInRDKit
              ({ element := some e, aromatic := aromS } : Atom)
              (((S.kindsAt i).map BondKind.order).sum) = false := by
            rw [← Loc.readsDifferently_congr (a := b)
              (b := ({ element := some e, aromatic := aromS } : Atom)) hbel hbar, ← hsum]
            exact hrd
          rw [hsm']
          have hKk : (K.kindsAt i).any (· == .aromatic) = false := by
            rw [List.any_eq_false]
            intro x hx
            obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
            have hlt := Work.lt_of_mem_bondsOf hk
            rw [getElem!_pos K.bonds k hlt]
            simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
          set kk := K.kindsAt i with hkkdef
          set h := Loc.bhs kk with hhdef
          have hzbd := Loc.organic_z horg'
          cases haS : aromS with
          | false =>
            -- not aromatic: the kinds are the Kekulé ones, and only the bond-order sum counts
            have hsk : S.kindsAt i = kk := Work.marks_eq_of_noArom hmarks (haS ▸ haromS ▸ rfl)
            have hq : ((S.kindsAt i).map BondKind.order).sum = (h : ℚ) / 2 := by
              rw [hsk, Work.order_sum_eq_bhs]
            rw [hq]
            rw [haS] at hrd'
            rw [hq] at hrd'
            have heven := Work.bhs_even_of_noArom hKk
            obtain ⟨t, ht⟩ : ∃ t, h = 2 * t := ⟨h / 2, by omega⟩
            by_cases ht9 : t < 9
            · have hb := Loc.bareNonArom_ok
              rw [List.all_eq_true] at hb
              have := hb e horg'
              rw [List.all_eq_true] at this
              have hc := this t (List.mem_range.2 ht9)
              unfold Loc.bareNonAromCheck at hc
              rw [← ht] at hc
              simp only [hrd', Bool.false_or, beq_iff_eq] at hc
              exact hc
            · have h13 : 13 < h := by omega
              rw [Loc.impl_large (by rfl) hzbd (by rfl) h13, Loc.implicitHydrogens_large e]
              have : (6 : ℚ) < 9 := by norm_num
              have h9 : (9 : ℚ) ≤ (h : ℚ) / 2 := by
                rw [le_div_iff₀ (by norm_num)]
                exact_mod_cast (by omega : 18 ≤ h)
              linarith
          | true =>
            -- aromatic: the decided check, with what perception tells
            obtain ⟨hl2, hel, hcd, hdo, hd2, -⟩ := hperc (haS ▸ haromS ▸ rfl)
            have hkk3 : kk ∈ Loc.nonArom 3 := Loc.mem_nonArom 3 kk hKk (by
              have := Work.elec_nonneg_length hel; omega)
            have hb := Loc.bareArom_ok
            rw [List.all_eq_true] at hb
            have := hb e horg'
            rw [List.all_eq_true] at this
            have hc := this kk hkk3
            unfold Loc.bareAromCheck at hc
            rw [List.all_eq_true] at hc
            have hc' := hc _ hmarks
            dsimp only at hc'
            -- the count the output writes is the bracket count
            have hTv : Molecule.implicitHydrogens ({ element := some e, aromatic := true } : Atom)
                (((S.kindsAt i).map BondKind.order).sum) = eh := by
              have := hsm'
              rw [haS] at this
              rw [← this, hsm, hTe]
            -- the radical-marked kekulized record at `i`
            have hiK : i < K.atoms.size := by rw [hnK]; exact hi
            have hKn : (K.atoms[i]! : WAtom).noImplicit = true := by
              rw [hKi]; change (P.atoms[i'.val]! : WAtom).noImplicit = true; rw [hPa]; simp [hmh]
            have hKz : (K.atoms[i]! : WAtom).z = e.atomicNumber := by
              rw [hKi]; change (P.atoms[i'.val]! : WAtom).z = _; rw [hPa, hz]
            have hKc0 : (K.atoms[i]! : WAtom).charge = 0 := by rw [hKc, hc0]
            have hKe : (K.atoms[i]! : WAtom).explicitHs = eh := by
              rw [hKi]; change (P.atoms[i'.val]! : WAtom).explicitHs = _; rw [hPa, hmh]; rfl
            have hKci : (K.atoms[i]! : WAtom).cachedImplicit = 0 := by
              rw [hKi]; change (P.atoms[i'.val]! : WAtom).cachedImplicit = _; rw [hPa]
              exact hC0 (by simp [hmh])
            have hKcv : (K.atoms[i]! : WAtom).cachedValence = some (C.explicitValence i) := by
              rw [hKi]; change (P.atoms[i'.val]! : WAtom).cachedValence = _; rw [hPa]
            have eqKR := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms K) i
            have fz : (KR.atoms[i]! : WAtom).z = e.atomicNumber := by
              have := congrArg WAtom.z eqKR; simp only at this; rw [this, hKz]
            have fc : (KR.atoms[i]! : WAtom).charge = 0 := by
              have := congrArg WAtom.charge eqKR; simp only at this; rw [this, hKc0]
            have fe : (KR.atoms[i]! : WAtom).explicitHs = eh := by
              have := congrArg WAtom.explicitHs eqKR; simp only at this; rw [this, hKe]
            have fci : (KR.atoms[i]! : WAtom).cachedImplicit = 0 := by
              have := congrArg WAtom.cachedImplicit eqKR; simp only at this; rw [this, hKci]
            have fcv0 : (KR.atoms[i]! : WAtom).cachedValence = some (C.explicitValence i) := by
              have := congrArg WAtom.cachedValence eqKR; simp only at this; rw [this, hKcv]
            have hKh : K.bondHalfSum i = h := by rw [Work.bondHalfSum_eq_loc]
            -- the cached valence is the Kekulé one
            have hev : C.explicitValence i = h / 2 + eh := by
              have hk := kekuleWitness_kekule hK ha hsv i
              rw [← hKR] at hk
              have hbh : KR.bondHalfSum i = h := by
                rw [← hKh]; simp only [Work.bondHalfSum, Work.bondsOf, Work.numBonds, hKR,
                  Work.assignRadicals_bonds]
              simp only [Work.cachedValence, fcv0, Option.getD_some, fe, hbh] at hk
              omega
            have fcv : (KR.atoms[i]! : WAtom).cachedValence = some (h / 2 + eh) := by
              rw [fcv0, hev]
            have fr : (KR.atoms[i]! : WAtom).radicals = Loc.radC e.atomicNumber 0 (h / 2 + eh) := by
              have hz0 : (K.atoms[i]! : WAtom).z ≠ 0 := by rw [hKz]; exact Loc.organic_z_pos horg'
              rw [Work.radicals_assignRadicals K hiK hKn hz0,
                Work.radicalCount_eq_loc, hKz, hKc0, hKe, hKh]
            rw [hTv] at hc' ⊢
            -- every other way out of the check is closed
            simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_true,
              beq_iff_eq] at hc'
            have hany : ((K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt
                i).any (· == .aromatic) = true := haS ▸ haromS ▸ rfl
            have hrd'' : Molecule.readsDifferentlyInRDKit
                ({ element := some e, aromatic := true } : Atom)
                ((((K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt
                  i).map BondKind.order).sum) = false := by
              have := hrd'; rw [haS] at this; exact this
            rcases hc' with ((((((h1 | h1) | h1) | h1) | h1) | h1) | h1) | h1
            · rw [hany] at h1; cases h1
            · exact absurd h1 (not_lt.2 hl2)
            · exfalso
              have := hd2 h1.1
              rw [List.all_eq_true] at this
              obtain ⟨⟨s', k'⟩, hp, hpv⟩ := List.any_eq_true.1 h1.2
              have h2 := this _ hp
              revert hpv h2
              cases s' <;> cases k' <;> decide
            · rw [hrd''] at h1; cases h1
            · exact absurd (lt_of_eq_of_lt (Loc.elec_congr (b := (KR.atoms[i]! : WAtom)) fz.symm
                fc.symm fe.symm fci.symm fr.symm fcv.symm _).symm h1) (not_lt.2 hel)
            · exfalso
              have g1 := fz.symm
              have g2 := fc.symm
              have g3 := fe.symm
              have g4 := fci.symm
              have g5 := fr.symm
              have g6 := fcv.symm
              rw [Loc.cand_congr (b := (KR.atoms[i]! : WAtom)) ?_ ?_ ?_ ?_ ?_ ?_, hcd] at h1
              all_goals first | cases h1 | assumption
            · exfalso
              have g1 := fz.symm
              have g2 := fc.symm
              have g3 := fe.symm
              have g4 := fci.symm
              have g5 := fr.symm
              have g6 := fcv.symm
              rw [Work.donorOk_congr (b := (KR.atoms[i]! : WAtom)) ?_ ?_ ?_ ?_ ?_ ?_, hdo] at h1
              all_goals first | cases h1 | assumption
            · exact h1
    · -- written in brackets with its hydrogens
      simp [Loc.impl, hOtot]
    · -- kept as it was
      rw [hOH, hOz, hOel, hOc, hKc]
      cases hmh : (m.atom i').explicitH with
      | some e =>
        have hTe : T = e := by rw [hT', hmh, hC0 (by simp [hmh])]; rfl
        simp [Loc.impl, hTe]
      | none =>
        cases hme : (m.atom i').element with
        | none =>
          have hT0 : T = 0 := by rw [hT', hmh, hC0 (by simp [hme])]; rfl
          simp [Loc.impl, hT0]
        | some e =>
          rw [hT', hmh]
          simp only [Option.map_none, Option.getD_none, Option.isSome_none, Option.isNone_some,
            Bool.or_false, Nat.zero_add]
          exact hMN hmh e hme
  · -- the `[nH]`/`[pH]` kekulization rewrites
    obtain ⟨hbar, hbz, hbc, hbe⟩ := hbr
    have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
      rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hlt := Work.lt_of_mem_bondsOf hk
      rw [getElem!_pos K.bonds k hlt]
      simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
    rw [hKany] at hKa
    have hKi : (K.atoms[i]! : WAtom) =
        Work.branchRec (P.atoms[i'.val]! : WAtom) (K.bondHalfSum i) false := hKa
    have hfa : (m.atom i').aromatic = true := by
      have : (P.atoms[i'.val]! : WAtom).aromatic = (m.atom i').aromatic := by rw [hPa]
      rw [← this]; exact hbar
    have hsome : (m.atom i').explicitH = some 1 := by
      have : (P.atoms[i'.val]! : WAtom).explicitHs = (m.atom i').explicitH.getD 0 := by rw [hPa]
      rw [this] at hbe
      cases h : (m.atom i').explicitH with
      | none => rw [h] at hbe; cases hbe
      | some x => rw [h] at hbe; rw [show x = 1 from hbe]
    set z := (P.atoms[i'.val]! : WAtom).z with hzdef
    set pk := P.kindsAt i with hpkdef
    set kk := K.kindsAt i with hkkdef
    have hPz : (P.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hPa]
    have hPn : (P.atoms[i'.val]! : WAtom).noImplicit = true := by rw [hPa]; simp [hsome]
    have hP0 : (P.atoms[i'.val]! : WAtom).cachedImplicit = 0 := by
      rw [hPa]; exact hC0 (by simp [hsome])
    have hPr : (P.atoms[i'.val]! : WAtom).radicals = 0 := by rw [hPa]
    -- the total: RDKit's count on the Kekulé bonds
    have hTb : T = Loc.impl
        { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false }
        (Loc.bhs kk) false := by
      rw [hT, Work.cachedTotalHs, hKi, Work.bondHalfSum_eq_loc]
      simp only [Work.branchRec, Nat.zero_add]
      apply Loc.impl_congr <;> first | rfl | exact hbc
    -- at most one
    have hT1 : T ≤ 1 := by
      obtain ⟨c1, c2⟩ := Work.kindsAt_prepare_counts m i'
      obtain ⟨h1, h2⟩ := hw.1 i' hfa
      have hpk3 : pk.length ≤ 3 := c1 ▸ h2
      have hnar : 2 ≤ (pk.filter (· == .aromatic)).length := c2 ▸ h1
      have hPlt : i < P.atoms.size := by
        rw [hP, Work.prepare_eq, Work.size_cacheValences_atoms, Work.size_cleaned]; exact hi
      have hPar : P.isAromaticAtom i = true := by
        rw [Work.isAromaticAtom_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := hbar
        rw [this]; rfl
      have hcand : Work.candOf P P.kekWa P.kekEv0 i =
          Loc.ndb (Loc.branchP z pk) pk ((Loc.branchP z pk).cachedValence.getD 0) := by
        unfold Work.candOf
        rw [Work.kekWa_eq, Work.needsDoubleBond_eq_loc, Work.kekEv0_getElem! P hPlt,
          Work.explicitValence_eq_loc, hPar, Work.bondHalfSum_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := hbar
        rw [this, Bool.true_and]
        change Loc.ndb (P.atoms[i'.val]! : WAtom) pk (Loc.ev (P.atoms[i'.val]! : WAtom) _ true) = _
        have hev : Loc.ev (P.atoms[i'.val]! : WAtom) (Loc.bhs pk) true =
            (Loc.branchP z pk).cachedValence.getD 0 := by
          simp only [Loc.branchP, Option.getD_some]
          apply Loc.ev_congr <;> first | rfl | exact hbc | exact hbe
        rw [hev]
        apply Loc.ndb_congr <;>
          first | rfl | exact hbc | exact hbe | simp [Loc.branchP, hPn, hP0, hPr]
      have hkk := hkek
      rw [hcand] at hkk
      have hb := Loc.branchH_ok
      rw [List.all_eq_true] at hb
      have hzl : z ∈ ([7, 15] : List ℕ) := by rcases hbz with h | h <;> rw [h] <;> decide
      have := hb z hzl
      rw [List.all_eq_true] at this
      have hc := this pk (Loc.mem_lists 3 pk hpk3)
      unfold Loc.branchHCheck at hc
      have hs : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length)) =
          false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
      rw [if_neg (by rw [hs]; decide), List.all_eq_true] at hc
      have h := hc _ hkk
      rw [decide_eq_true_eq] at h
      rw [hTb]
      refine le_trans (le_of_eq ?_) h
      simp only [Loc.branchK, Loc.branchP]
      apply Loc.impl_congr <;> rfl
    rw [hAO]
    unfold normalizeBracket
    dsimp only
    split_ifs with hcb hbare
    · -- written bare: RDKit reads the same atom
      have hOc' : O.charge = 0 := by rw [hOc, hKi]; exact hbc
      rw [hTb]
      simp only [Option.getD_none, Nat.zero_add, Option.isSome_none, Bool.false_or]
      apply Loc.impl_congr
      · change O.atomicNumber = _
        rw [hOz, ← hPz]
      · exact hOc'
      · rfl
      · change (false || O.element.isNone) = false
        rw [hOel]
        cases h : (m.atom i').element
        · simp only [Atom.atomicNumber, h, Option.map_none, Option.getD_none] at hPz
          rcases hbz with e | e <;> rw [← hzdef, e] at hPz <;> cases hPz
        · rfl
    · simp [Loc.impl, hOtot]
    · rw [hOH, hsome]
      simp only [Option.map_some, Option.getD_some, Option.isSome_some, Bool.true_or]
      have : Loc.impl
          { z := O.atomicNumber, aromatic := false, charge := O.charge, explicitHs := min 1 T,
            noImplicit := true } (Loc.bhs (K.kindsAt i)) false = 0 := by
        simp [Loc.impl]
      rw [this]
      omega

set_option maxHeartbeats 4000000 in -- the record facts of the totals proof, for any atom
open Aromaticity in
/-- **What kekulization leaves at an atom of `m`**: no radicals, `m`'s element and the charge
`cleanUp` left; either `m`'s written hydrogens and the counts cached before kekulization (for a
bare atom, RDKit's count on the Kekulé bonds), or, at an aromatic `[nH]`/`[pH]`, a bare record
with RDKit's count on the Kekulé bonds and their bond-order sum as its valence. -/
theorem kekulize_record {m : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (hw : m.AromaticWritten) (hbw : m.BareWritable) {i : ℕ} (hi : i < n) :
    (K.atoms[i]! : WAtom).radicals = 0 ∧
      (K.atoms[i]! : WAtom).z = (m.atom ⟨i, hi⟩).atomicNumber ∧
      (K.atoms[i]! : WAtom).charge = ((Work.cleaned m).atoms[i]! : WAtom).charge ∧
      (((K.atoms[i]! : WAtom).explicitHs = (m.atom ⟨i, hi⟩).explicitH.getD 0 ∧
          (K.atoms[i]! : WAtom).noImplicit =
            ((m.atom ⟨i, hi⟩).explicitH.isSome || (m.atom ⟨i, hi⟩).element.isNone) ∧
          (K.atoms[i]! : WAtom).cachedImplicit = (Work.cleaned m).implicitHs i ∧
          (K.atoms[i]! : WAtom).cachedValence = some ((Work.cleaned m).explicitValence i) ∧
          (((m.atom ⟨i, hi⟩).explicitH.isSome || (m.atom ⟨i, hi⟩).element.isNone) = true →
            (Work.cleaned m).implicitHs i = 0) ∧
          ((m.atom ⟨i, hi⟩).explicitH = none → ∀ e, (m.atom ⟨i, hi⟩).element = some e →
            (Work.cleaned m).implicitHs i = Loc.rdCount (m.atom ⟨i, hi⟩).atomicNumber
              ((Work.cleaned m).atoms[i]! : WAtom).charge (Loc.bhs (K.kindsAt i)))) ∨
        ((m.atom ⟨i, hi⟩).explicitH = some 1 ∧ (K.atoms[i]! : WAtom).charge = 0 ∧
          (K.atoms[i]! : WAtom).explicitHs = 0 ∧ (K.atoms[i]! : WAtom).noImplicit = false ∧
          (K.atoms[i]! : WAtom).cachedImplicit =
            Loc.rdCount (K.atoms[i]! : WAtom).z 0 (Loc.bhs (K.kindsAt i)) ∧
          (K.atoms[i]! : WAtom).cachedValence = some (K.bondHalfSum i / 2) ∧
          ((K.atoms[i]! : WAtom).z = 7 ∨ (K.atoms[i]! : WAtom).z = 15))) := by
  set i' : Fin n := ⟨i, hi⟩ with hi'
  set P := Work.prepare m with hP
  set R := P.relevantCycles with hR
  have hkek := Work.kindsAt_kekulize_mem hw.1 hw.2 hK i'
  set T := K.cachedTotalHs i with hT
  set C := Work.cleaned m with hC
  have hPa : (P.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs,
        cachedValence := some (C.explicitValence i), cachedImplicit := C.implicitHs i,
        adjustHs := C.isAromaticAtom i } := by
    rw [hP, Work.prepare_atom, hC]
    conv_lhs => rw [Work.cleaned_atom, Work.ofMolecule_atom]
  have hCa : (C.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs } := by
    conv_lhs => rw [hC, Work.cleaned_atom, Work.ofMolecule_atom]
  have hCk : C.kindsAt i = P.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hP, Work.prepare_eq,
      Work.cacheValences_bonds, hC]
  have hPc : (P.atoms[i'.val]! : WAtom).charge = (C.atoms[i'.val]! : WAtom).charge := by rw [hPa]
  -- the case split: how the output writes atom `i`, and how kekulization left it
  -- an aromatic bond at `i` makes `i` lowercase
  have hflag : (P.kindsAt i).any (· == .aromatic) = true → (m.atom i').aromatic = true := by
    intro h
    have hf := Work.kindsAt_prepare m i'
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨y, hy, hxy⟩ := Work.forall₂_exists_right hf _ hx
    have hy' : y = .aromatic := hxy.1 rfl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hbm, hbt⟩ := List.mem_filter.1 hb
    obtain ⟨h1, h2⟩ := hw.2 b hbm hy'
    simp only [Bond.touches, Bool.or_eq_true, beq_iff_eq] at hbt
    rcases hbt with e | e
    · rw [← e]; exact h1
    · rw [← e]; exact h2
  have hCar : C.isAromaticAtom i = (m.atom i').aromatic := by
    rw [Work.isAromaticAtom_eq_loc, hCk]
    have : (C.atoms[i]! : WAtom).aromatic = (m.atom i').aromatic := by
      change (C.atoms[i'.val]! : WAtom).aromatic = _; rw [hCa]
    rw [this]
    cases hfa : (m.atom i').aromatic
    · cases hany : (P.kindsAt i).any (· == .aromatic)
      · rfl
      · rw [hflag hany] at hfa; cases hfa
    · rfl
  have hCimpl : C.implicitHs i = Loc.impl (C.atoms[i'.val]! : WAtom) (Loc.bhs (P.kindsAt i))
      (m.atom i').aromatic := by
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hCk, hCar]
  -- **a bare atom of `m`**: RDKit's count on the Kekulé bonds is the one cached before
  have hMN : (m.atom i').explicitH = none → ∀ e, (m.atom i').element = some e →
      Loc.impl
          { z := (m.atom i').atomicNumber, aromatic := false,
            charge := (C.atoms[i'.val]! : WAtom).charge, explicitHs := 0, noImplicit := false }
          (Loc.bhs (K.kindsAt i)) false = C.implicitHs i := by
    intro hnone e hae
    obtain ⟨hcb, haro⟩ := hbw i' hnone
    have hcb' := hcb
    simp only [Atom.canBeBare, hnone, hae, Option.isNone_none, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq] at hcb'
    obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
    have hz : (m.atom i').atomicNumber = e.atomicNumber := by simp [Atom.atomicNumber, hae]
    have hCz : (C.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hCa]
    have hCe : (C.atoms[i'.val]! : WAtom).explicitHs = 0 := by rw [hCa]; simp [hnone]
    have hCn : (C.atoms[i'.val]! : WAtom).noImplicit = false := by rw [hCa]; simp [hnone, hae]
    rw [hCimpl]
    set c := (C.atoms[i'.val]! : WAtom).charge with hcdef
    set pk := P.kindsAt i with hpkdef
    by_cases hfa : (m.atom i').aromatic = true
    · -- written lowercase: the decided check
      have hzin : e.atomicNumber ∈ ([5, 6, 7, 8, 15, 16] : List ℕ) :=
        Work.organic_aromatic_z e (by simpa using horg) (.inr (by simpa [hae] using haro hfa))
      have hzc : (e.atomicNumber, c) ∈ Loc.bareZC := by
        have hcc := (Work.cleanFine_cleaned m).charge i'
        obtain ⟨hFz, hFc⟩ := Work.freezeHs_atom_z_charge m i'
        rw [hFz, hFc, hch0, hz, ← hC, ← hcdef] at hcc
        simp only [CleanCharge] at hcc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzin
        rcases hzin with h | h | h | h | h | h <;> rw [h] at hcc ⊢ <;>
          rcases hcc with h' | h' | ⟨h', h''⟩ | h' | h' | h' <;>
          first
          | (rw [h']; decide)
          | omega
      obtain ⟨c1, c2⟩ := Work.kindsAt_prepare_counts m i'
      obtain ⟨h1, h2⟩ := hw.1 i' hfa
      have hpk3 : pk.length ≤ 3 := c1 ▸ h2
      have hnar : 2 ≤ (pk.filter (· == .aromatic)).length := c2 ▸ h1
      -- `candOf` is `bareP`'s need
      have hPev : Loc.ev (P.atoms[i'.val]! : WAtom) (Loc.bhs pk) true =
          (Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0 := by
        simp only [Loc.bareP, Option.getD_some]
        apply Loc.ev_congr
        · rw [hPa, hz]
        · rw [hPa]
        · rw [hPa, hnone]; rfl
      have hPar : P.isAromaticAtom i = true := by
        rw [Work.isAromaticAtom_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this]; rfl
      have hcand : Work.candOf P P.kekWa P.kekEv0 i =
          Loc.ndb (Loc.bareP e.atomicNumber c true pk) pk
            ((Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0) := by
        have hPlt : i < P.atoms.size := by
          rw [hP, Work.prepare_eq, Work.size_cacheValences_atoms, Work.size_cleaned]; exact hi
        unfold Work.candOf
        rw [Work.kekWa_eq, Work.needsDoubleBond_eq_loc, Work.kekEv0_getElem! P hPlt,
          Work.explicitValence_eq_loc, hPar, Work.bondHalfSum_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this, Bool.true_and]
        change Loc.ndb (P.atoms[i'.val]! : WAtom) pk (Loc.ev (P.atoms[i'.val]! : WAtom) _ true) = _
        rw [hPev]
        apply Loc.ndb_congr
        · rw [hPa, hz]; rfl
        · rw [hPa]; rfl
        · rw [hPa, hnone]; rfl
        · rw [hPa]; simp [hnone, hae, Loc.bareP]
        · rw [hPa, hCimpl, hfa]
          simp only [Loc.bareP]
          apply Loc.impl_congr
          · rw [hCz, hz]
          · rfl
          · exact hCe
          · exact hCn
        · rw [hPa]; rfl
      have hkk := hkek
      rw [hcand] at hkk
      have hb := Loc.bareKek_ok
      rw [List.all_eq_true] at hb
      have := hb _ hzc
      rw [List.all_eq_true] at this
      have hc := this pk (Loc.mem_lists 3 pk hpk3)
      unfold Loc.bareKekCheck at hc
      have hs1 : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length) ||
          !([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber) = false := by
        have hzin' : ([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber = true :=
          List.contains_iff_mem.2 hzin
        rw [hzin']
        simp only [Bool.not_true, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not,
          not_lt]
        omega
      rw [if_neg (by rw [hs1]; decide), List.all_eq_true] at hc
      have := hc _ hkk
      rw [beq_iff_eq] at this
      rw [hfa]
      calc Loc.impl _ (Loc.bhs (K.kindsAt i)) false
          = Loc.impl { Loc.bareP e.atomicNumber c true pk with aromatic := false }
              (Loc.bhs (K.kindsAt i)) false := by
            apply Loc.impl_congr
            · simp [Loc.bareP, hz]
            · rfl
            · rfl
            · rfl
        _ = (Loc.bareP e.atomicNumber c true pk).cachedImplicit := this
        _ = _ := by
            simp only [Loc.bareP]
            apply Loc.impl_congr
            · rw [hCz, hz]
            · rfl
            · exact hCe.symm
            · exact hCn.symm
    · -- not lowercase: no aromatic bond, kekulization changed nothing here
      rw [Bool.not_eq_true] at hfa
      have hpk : pk.any (· == .aromatic) = false := by
        cases h : pk.any (· == .aromatic)
        · rfl
        · rw [hflag h] at hfa; cases hfa
      rw [Work.kekAll_eq_of_noArom hkek hpk, hfa]
      apply Loc.impl_congr
      · exact hCz.symm
      · rfl
      · exact hCe.symm
      · exact hCn.symm
  have hCn : (C.atoms[i'.val]! : WAtom).noImplicit =
      ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) := by rw [hCa]
  have hC0 : ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) = true →
      C.implicitHs i = 0 := by
    intro h
    rw [hCimpl]
    simp [Loc.impl, hCn, h]
  rcases Work.kekulize_atom hK i with hKa | ⟨hbr, hKa⟩
  · have hKi : (K.atoms[i]! : WAtom) = { (P.atoms[i'.val]! : WAtom) with aromatic := false } := hKa
    have f : ∀ {α : Type} (g : WAtom → α), (∀ x : WAtom, g { x with aromatic := false } = g x) →
        g (K.atoms[i]! : WAtom) = g (P.atoms[i'.val]! : WAtom) := fun g hg ↦ by rw [hKi, hg]
    refine ⟨by rw [f WAtom.radicals (fun _ ↦ rfl), hPa], by rw [f WAtom.z (fun _ ↦ rfl), hPa],
      by rw [f WAtom.charge (fun _ ↦ rfl), hPa],
      .inl ⟨by rw [f WAtom.explicitHs (fun _ ↦ rfl), hPa],
      by rw [f WAtom.noImplicit (fun _ ↦ rfl), hPa],
      by rw [f WAtom.cachedImplicit (fun _ ↦ rfl), hPa],
      by rw [f WAtom.cachedValence (fun _ ↦ rfl), hPa], hC0, fun hn e he ↦ (hMN hn e he).symm⟩⟩
  · -- the `[nH]`/`[pH]` kekulization rewrites
    obtain ⟨hbar, hbz, hbc, hbe⟩ := hbr
    have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
      rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hlt := Work.lt_of_mem_bondsOf hk
      rw [getElem!_pos K.bonds k hlt]
      simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
    rw [hKany] at hKa
    have hKi : (K.atoms[i]! : WAtom) =
        Work.branchRec (P.atoms[i'.val]! : WAtom) (K.bondHalfSum i) false := hKa
    have hfa : (m.atom i').aromatic = true := by
      have : (P.atoms[i'.val]! : WAtom).aromatic = (m.atom i').aromatic := by rw [hPa]
      rw [← this]; exact hbar
    have hsome : (m.atom i').explicitH = some 1 := by
      have : (P.atoms[i'.val]! : WAtom).explicitHs = (m.atom i').explicitH.getD 0 := by rw [hPa]
      rw [this] at hbe
      cases h : (m.atom i').explicitH with
      | none => rw [h] at hbe; cases hbe
      | some x => rw [h] at hbe; rw [show x = 1 from hbe]
    set z := (P.atoms[i'.val]! : WAtom).z with hzdef
    set pk := P.kindsAt i with hpkdef
    set kk := K.kindsAt i with hkkdef
    have hPz : (P.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hPa]
    have hPn : (P.atoms[i'.val]! : WAtom).noImplicit = true := by rw [hPa]; simp [hsome]
    have hP0 : (P.atoms[i'.val]! : WAtom).cachedImplicit = 0 := by
      rw [hPa]; exact hC0 (by simp [hsome])
    have hPr : (P.atoms[i'.val]! : WAtom).radicals = 0 := by rw [hPa]
    -- the total: RDKit's count on the Kekulé bonds
    have hTb : T = Loc.impl
        { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false }
        (Loc.bhs kk) false := by
      rw [hT, Work.cachedTotalHs, hKi, Work.bondHalfSum_eq_loc]
      simp only [Work.branchRec, Nat.zero_add]
      apply Loc.impl_congr <;> first | rfl | exact hbc
    refine ⟨by rw [hKi]; exact hPr, by rw [hKi]; exact hPz, by rw [hKi, ← hPc]; rfl,
      .inr ⟨hsome, by rw [hKi]; exact hbc, by rw [hKi]; rfl, by rw [hKi]; rfl, ?_, by rw [hKi]; rfl,
      by rw [hKi]; exact hbz⟩⟩
    have : T = (K.atoms[i]! : WAtom).cachedImplicit := by
      rw [hT, Work.cachedTotalHs, hKi]; simp [Work.branchRec]
    rw [← this, hTb, hKi]
    rfl

set_option maxHeartbeats 4000000 in -- the totals proof's case analysis, on the written hydrogens
open Aromaticity in
/-- **How the two copies write an atom's hydrogens.**  Before radicals, the witness's copy and the
kekulized copy write the same hydrogens at an atom, bracketed or not, or they swap: hydrogens
implied in the kekulized copy and written in the witness's, at RDKit's count on the Kekulé bonds
(at a charge `cleanUp` may leave on a bare atom), or written in the kekulized copy and implied in
the witness's, at OpenSMILES's count on the bonds perception leaves.  Neither copy has radicals
yet. -/
theorem kekuleWitness_swap {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable) {i : ℕ} (hi : i < n) :
    let P' := (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences
    let S := K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles
    let T := K.cachedTotalHs i
    (K.atoms[i]! : WAtom).radicals = 0 ∧ (P'.atoms[i]! : WAtom).radicals = 0 ∧
      (((P'.atoms[i]! : WAtom).explicitHs = (K.atoms[i]! : WAtom).explicitHs ∧
          (P'.atoms[i]! : WAtom).noImplicit = (K.atoms[i]! : WAtom).noImplicit) ∨
        ∃ e ∈ Loc.organic, (K.atoms[i]! : WAtom).z = e.atomicNumber ∧
          (((K.atoms[i]! : WAtom).explicitHs = 0 ∧ (K.atoms[i]! : WAtom).noImplicit = false ∧
              (P'.atoms[i]! : WAtom).explicitHs = T ∧ (P'.atoms[i]! : WAtom).noImplicit = true ∧
              ((K.atoms[i]! : WAtom).charge = 0 ∨
                CleanCharge e.atomicNumber (K.atoms[i]! : WAtom).charge) ∧
              T = Loc.rdCount e.atomicNumber (K.atoms[i]! : WAtom).charge
                (Loc.bhs (K.kindsAt i))) ∨
            ((K.atoms[i]! : WAtom).explicitHs = T ∧ (K.atoms[i]! : WAtom).noImplicit = true ∧
              (P'.atoms[i]! : WAtom).explicitHs = 0 ∧ (P'.atoms[i]! : WAtom).noImplicit = false ∧
              (K.atoms[i]! : WAtom).charge = 0 ∧
              Molecule.readsDifferentlyInRDKit
                ({ element := some e, aromatic := (S.kindsAt i).any (· == .aromatic) } : Atom)
                (((S.kindsAt i).map BondKind.order).sum) = false ∧
              T = Loc.smCount e (S.kindsAt i)))) := by
  dsimp only
  have hnK : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  set i' : Fin n := ⟨i, hi⟩ with hi'
  -- the witness's side: written hydrogens, and RDKit's count on the Kekulé bonds
  set A := a.atom i' with hA
  have hkA : (kekuleWitness a K).atom i' = { A with aromatic := false } :=
    (kekuleWitness_spec hK ha).2.atoms i'
  set P := Work.prepare m with hP
  set R := P.relevantCycles with hR
  set KR := K.assignRadicals with hKR
  set S := KR.setAromaticity R with hS
  set F := K.finish R with hF
  obtain ⟨hmarks, harS, hperc⟩ := Work.perceived_atom hK i
  have hkek := Work.kindsAt_kekulize_mem hw.1 hw.2 hK i'
  have hnS : i < S.atoms.size := by
    rw [(Work.afterRel_setAromaticity KR R).atoms_size,
      (Work.afterRel_assignRadicals (w := K)).atoms_size, hnK]; exact hi
  set T := K.cachedTotalHs i with hT
  have hFT : (F.atoms[i]! : WAtom).frozenHs = some T := by
    have hr := Work.hsRestored_kekulize hw.1 hw.2 hbw hK i'
    rw [hF, Work.finish, Work.frozenHs_finalizeHs_of_restored _ hnS hr,
      Work.cachedTotalHs_setAromaticity, Work.cachedTotalHs_assignRadicals]
  -- the output atom, before bracket normalization
  set O := m.outAtom F i' with hOdef
  have hAO : A = normalizeBracket O (a.bondOrderSum i') := by
    have := atom_aromatizeOutput m F i'
    rw [ha] at this
    exact this
  have hOtot : O.totalH = T := by
    rw [hOdef, totalH_outAtom]
    change ((F.atoms[i]! : WAtom).frozenHs.getD _) = T
    rw [hFT]; rfl
  have hOH : O.explicitH = (m.atom i').explicitH.map (min · T) := by
    simp only [hOdef, Molecule.outAtom]
    change Option.map (fun x ↦ min x ((F.atoms[i]! : WAtom).frozenHs.getD _)) _ = _
    rw [hFT]; rfl
  have hOel : O.element = (m.atom i').element := by simp [hOdef, Molecule.outAtom]
  have hOz : O.atomicNumber = (m.atom i').atomicNumber := by
    simp [Atom.atomicNumber, hOel]
  have hOc : O.charge = (K.atoms[i]! : WAtom).charge := by
    change (F.atoms[i]! : WAtom).charge = _
    exact Work.getElem!_eq_of_map (fun x : WAtom ↦ x.charge)
      (by simpa only [Work.charge?] using congrFun (K.afterRel_finish R).charge i)
  have hOar : O.aromatic = (S.kindsAt i).any (· == .aromatic) := by
    simp only [hOdef, Molecule.outAtom]
    rw [hF, Work.finish, Work.isAromaticAtom_finalizeHs]
    exact harS
  have hsum : a.bondOrderSum i' = ((S.kindsAt i).map BondKind.order).sum := by
    simp only [Molecule.bondOrderSum, Molecule.bondsAt]
    rw [show (fun x : Bond n ↦ x.kind.order) = BondKind.order ∘ Bond.kind from rfl,
      ← List.map_map, kindsAt_aromatizeOutput hK ha i']
  -- `P`'s record at `i`
  set C := Work.cleaned m with hC
  have hPa : (P.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs,
        cachedValence := some (C.explicitValence i), cachedImplicit := C.implicitHs i,
        adjustHs := C.isAromaticAtom i } := by
    rw [hP, Work.prepare_atom, hC]
    conv_lhs => rw [Work.cleaned_atom, Work.ofMolecule_atom]
  have hCa : (C.atoms[i'.val]! : WAtom) =
      { z := (m.atom i').atomicNumber, aromatic := (m.atom i').aromatic,
        charge := (C.atoms[i'.val]! : WAtom).charge,
        explicitHs := (m.atom i').explicitH.getD 0,
        noImplicit := (m.atom i').explicitH.isSome || (m.atom i').element.isNone,
        frozenHs := (C.atoms[i'.val]! : WAtom).frozenHs } := by
    conv_lhs => rw [hC, Work.cleaned_atom, Work.ofMolecule_atom]
  have hCk : C.kindsAt i = P.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hP, Work.prepare_eq,
      Work.cacheValences_bonds, hC]
  have hPc : (P.atoms[i'.val]! : WAtom).charge = (C.atoms[i'.val]! : WAtom).charge := by rw [hPa]
  -- the case split: how the output writes atom `i`, and how kekulization left it
  -- an aromatic bond at `i` makes `i` lowercase
  have hflag : (P.kindsAt i).any (· == .aromatic) = true → (m.atom i').aromatic = true := by
    intro h
    have hf := Work.kindsAt_prepare m i'
    simp only [List.any_eq_true, beq_iff_eq] at h
    obtain ⟨x, hx, rfl⟩ := h
    obtain ⟨y, hy, hxy⟩ := Work.forall₂_exists_right hf _ hx
    have hy' : y = .aromatic := hxy.1 rfl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hbm, hbt⟩ := List.mem_filter.1 hb
    obtain ⟨h1, h2⟩ := hw.2 b hbm hy'
    simp only [Bond.touches, Bool.or_eq_true, beq_iff_eq] at hbt
    rcases hbt with e | e
    · rw [← e]; exact h1
    · rw [← e]; exact h2
  have hCar : C.isAromaticAtom i = (m.atom i').aromatic := by
    rw [Work.isAromaticAtom_eq_loc, hCk]
    have : (C.atoms[i]! : WAtom).aromatic = (m.atom i').aromatic := by
      change (C.atoms[i'.val]! : WAtom).aromatic = _; rw [hCa]
    rw [this]
    cases hfa : (m.atom i').aromatic
    · cases hany : (P.kindsAt i).any (· == .aromatic)
      · rfl
      · rw [hflag hany] at hfa; cases hfa
    · rfl
  have hCimpl : C.implicitHs i = Loc.impl (C.atoms[i'.val]! : WAtom) (Loc.bhs (P.kindsAt i))
      (m.atom i').aromatic := by
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hCk, hCar]
  -- **a bare atom of `m`**: RDKit's count on the Kekulé bonds is the one cached before
  have hMN : (m.atom i').explicitH = none → ∀ e, (m.atom i').element = some e →
      Loc.impl
          { z := (m.atom i').atomicNumber, aromatic := false,
            charge := (C.atoms[i'.val]! : WAtom).charge, explicitHs := 0, noImplicit := false }
          (Loc.bhs (K.kindsAt i)) false = C.implicitHs i := by
    intro hnone e hae
    obtain ⟨hcb, haro⟩ := hbw i' hnone
    have hcb' := hcb
    simp only [Atom.canBeBare, hnone, hae, Option.isNone_none, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq] at hcb'
    obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
    have hz : (m.atom i').atomicNumber = e.atomicNumber := by simp [Atom.atomicNumber, hae]
    have hCz : (C.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hCa]
    have hCe : (C.atoms[i'.val]! : WAtom).explicitHs = 0 := by rw [hCa]; simp [hnone]
    have hCn : (C.atoms[i'.val]! : WAtom).noImplicit = false := by rw [hCa]; simp [hnone, hae]
    rw [hCimpl]
    set c := (C.atoms[i'.val]! : WAtom).charge with hcdef
    set pk := P.kindsAt i with hpkdef
    by_cases hfa : (m.atom i').aromatic = true
    · -- written lowercase: the decided check
      have hzin : e.atomicNumber ∈ ([5, 6, 7, 8, 15, 16] : List ℕ) :=
        Work.organic_aromatic_z e (by simpa using horg) (.inr (by simpa [hae] using haro hfa))
      have hzc : (e.atomicNumber, c) ∈ Loc.bareZC := by
        have hcc := (Work.cleanFine_cleaned m).charge i'
        obtain ⟨hFz, hFc⟩ := Work.freezeHs_atom_z_charge m i'
        rw [hFz, hFc, hch0, hz, ← hC, ← hcdef] at hcc
        simp only [CleanCharge] at hcc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzin
        rcases hzin with h | h | h | h | h | h <;> rw [h] at hcc ⊢ <;>
          rcases hcc with h' | h' | ⟨h', h''⟩ | h' | h' | h' <;>
          first
          | (rw [h']; decide)
          | omega
      obtain ⟨c1, c2⟩ := Work.kindsAt_prepare_counts m i'
      obtain ⟨h1, h2⟩ := hw.1 i' hfa
      have hpk3 : pk.length ≤ 3 := c1 ▸ h2
      have hnar : 2 ≤ (pk.filter (· == .aromatic)).length := c2 ▸ h1
      -- `candOf` is `bareP`'s need
      have hPev : Loc.ev (P.atoms[i'.val]! : WAtom) (Loc.bhs pk) true =
          (Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0 := by
        simp only [Loc.bareP, Option.getD_some]
        apply Loc.ev_congr
        · rw [hPa, hz]
        · rw [hPa]
        · rw [hPa, hnone]; rfl
      have hPar : P.isAromaticAtom i = true := by
        rw [Work.isAromaticAtom_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this]; rfl
      have hcand : Work.candOf P P.kekWa P.kekEv0 i =
          Loc.ndb (Loc.bareP e.atomicNumber c true pk) pk
            ((Loc.bareP e.atomicNumber c true pk).cachedValence.getD 0) := by
        have hPlt : i < P.atoms.size := by
          rw [hP, Work.prepare_eq, Work.size_cacheValences_atoms, Work.size_cleaned]; exact hi
        unfold Work.candOf
        rw [Work.kekWa_eq, Work.needsDoubleBond_eq_loc, Work.kekEv0_getElem! P hPlt,
          Work.explicitValence_eq_loc, hPar, Work.bondHalfSum_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := by
          change (P.atoms[i'.val]! : WAtom).aromatic = _; rw [hPa]; exact hfa
        rw [this, Bool.true_and]
        change Loc.ndb (P.atoms[i'.val]! : WAtom) pk (Loc.ev (P.atoms[i'.val]! : WAtom) _ true) = _
        rw [hPev]
        apply Loc.ndb_congr
        · rw [hPa, hz]; rfl
        · rw [hPa]; rfl
        · rw [hPa, hnone]; rfl
        · rw [hPa]; simp [hnone, hae, Loc.bareP]
        · rw [hPa, hCimpl, hfa]
          simp only [Loc.bareP]
          apply Loc.impl_congr
          · rw [hCz, hz]
          · rfl
          · exact hCe
          · exact hCn
        · rw [hPa]; rfl
      have hkk := hkek
      rw [hcand] at hkk
      have hb := Loc.bareKek_ok
      rw [List.all_eq_true] at hb
      have := hb _ hzc
      rw [List.all_eq_true] at this
      have hc := this pk (Loc.mem_lists 3 pk hpk3)
      unfold Loc.bareKekCheck at hc
      have hs1 : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length) ||
          !([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber) = false := by
        have hzin' : ([5, 6, 7, 8, 15, 16] : List ℕ).contains e.atomicNumber = true :=
          List.contains_iff_mem.2 hzin
        rw [hzin']
        simp only [Bool.not_true, Bool.or_false, Bool.or_eq_false_iff, decide_eq_false_iff_not,
          not_lt]
        omega
      rw [if_neg (by rw [hs1]; decide), List.all_eq_true] at hc
      have := hc _ hkk
      rw [beq_iff_eq] at this
      rw [hfa]
      calc Loc.impl _ (Loc.bhs (K.kindsAt i)) false
          = Loc.impl { Loc.bareP e.atomicNumber c true pk with aromatic := false }
              (Loc.bhs (K.kindsAt i)) false := by
            apply Loc.impl_congr
            · simp [Loc.bareP, hz]
            · rfl
            · rfl
            · rfl
        _ = (Loc.bareP e.atomicNumber c true pk).cachedImplicit := this
        _ = _ := by
            simp only [Loc.bareP]
            apply Loc.impl_congr
            · rw [hCz, hz]
            · rfl
            · exact hCe.symm
            · exact hCn.symm
    · -- not lowercase: no aromatic bond, kekulization changed nothing here
      rw [Bool.not_eq_true] at hfa
      have hpk : pk.any (· == .aromatic) = false := by
        cases h : pk.any (· == .aromatic)
        · rfl
        · rw [hflag h] at hfa; cases hfa
      rw [Work.kekAll_eq_of_noArom hkek hpk, hfa]
      apply Loc.impl_congr
      · exact hCz.symm
      · rfl
      · exact hCe.symm
      · exact hCn.symm
  have hCn : (C.atoms[i'.val]! : WAtom).noImplicit =
      ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) := by rw [hCa]
  have hC0 : ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) = true →
      C.implicitHs i = 0 := by
    intro h
    rw [hCimpl]
    simp [Loc.impl, hCn, h]
  -- the witness's record at `i`
  have hPw := Work.freezeCache_atom (kekuleWitness a K) i'
  rw [hkA] at hPw
  have hP'e : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).explicitHs = A.explicitH.getD 0 := by
    change ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).explicitHs = _
    rw [hPw]
  have hP'n : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).noImplicit = (A.explicitH.isSome || A.element.isNone) := by
    change ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).noImplicit = _
    rw [hPw]
  have hP'r : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).radicals = 0 := by
    change ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).radicals = _
    rw [hPw]
  rcases Work.kekulize_atom hK i with hKa | ⟨hbr, hKa⟩
  · -- kekulization only cleared the flag
    have hKi : (K.atoms[i]! : WAtom) = { (P.atoms[i'.val]! : WAtom) with aromatic := false } := hKa
    have hT' : T = (m.atom i').explicitH.getD 0 + C.implicitHs i := by
      rw [hT, Work.cachedTotalHs, hKi]
      change (P.atoms[i'.val]! : WAtom).explicitHs + (P.atoms[i'.val]! : WAtom).cachedImplicit = _
      rw [hPa]
    have hKc : (K.atoms[i]! : WAtom).charge = (C.atoms[i'.val]! : WAtom).charge := by
      rw [hKi]; exact hPc
    have hKe : (K.atoms[i]! : WAtom).explicitHs = (m.atom i').explicitH.getD 0 := by
      rw [hKi]; change (P.atoms[i'.val]! : WAtom).explicitHs = _; rw [hPa]
    have hKn : (K.atoms[i]! : WAtom).noImplicit =
        ((m.atom i').explicitH.isSome || (m.atom i').element.isNone) := by
      rw [hKi]; change (P.atoms[i'.val]! : WAtom).noImplicit = _; rw [hPa]
    have hKz : (K.atoms[i]! : WAtom).z = (m.atom i').atomicNumber := by
      rw [hKi]; change (P.atoms[i'.val]! : WAtom).z = _; rw [hPa]
    have hKr : (K.atoms[i]! : WAtom).radicals = 0 := by
      rw [hKi]; change (P.atoms[i'.val]! : WAtom).radicals = _; rw [hPa]
    refine ⟨hKr, hP'r, ?_⟩
    rw [hP'e, hP'n, hKe, hKn, hKz, hKc, hAO]
    unfold normalizeBracket
    dsimp only
    split_ifs with hcb hbare
    · -- written bare
      dsimp only
      set b : Atom := { O with explicitH := none, implicitH := 0 } with hbdef
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hbare
      obtain ⟨hsm, hrd⟩ := hbare
      rw [hOtot] at hsm
      simp only [Option.getD_none, Option.isSome_none, Bool.false_or, hOel]
      cases hme : (m.atom i').element with
      | none =>
        -- `*`: OpenSMILES gives it no hydrogen, so it has none
        have hb0 : Molecule.implicitHydrogens b (a.bondOrderSum i') = 0 := by
          unfold Molecule.implicitHydrogens
          rw [show b.element = none from hOel.trans hme]
        left
        refine ⟨by omega, by simp⟩
      | some e =>
        cases hmh : (m.atom i').explicitH with
        | none => left; simp
        | some eh =>
          -- bracketed in `m`, bare in the output: the OpenSMILES swap
          have hTe : T = eh := by rw [hT', hmh, hC0 (by simp [hmh])]; rfl
          have hcb' := hcb
          simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb'
          obtain ⟨⟨⟨⟨⟨-, -⟩, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
          have hbel : b.element = some e := hOel.trans hme
          rw [hbel] at horg
          have horg' : e ∈ Loc.organic := Loc.mem_organic e horg
          have hc0 : (C.atoms[i'.val]! : WAtom).charge = 0 := by
            rw [← hKc, ← hOc]; exact hch0
          have hz : (m.atom i').atomicNumber = e.atomicNumber := by
            simp [Atom.atomicNumber, hme]
          have hbar : b.aromatic = (S.kindsAt i).any (· == .aromatic) := hOar
          have hsm' : Molecule.implicitHydrogens b (a.bondOrderSum i') =
              Loc.smCount e (S.kindsAt i) := by
            rw [hsum]
            exact Loc.implicitHydrogens_congr (a := b)
              (b := ({ element := some e, aromatic := (S.kindsAt i).any (· == .aromatic) } : Atom))
              hbel hbar rfl _
          have hrd' : Molecule.readsDifferentlyInRDKit
              ({ element := some e, aromatic := (S.kindsAt i).any (· == .aromatic) } : Atom)
              (((S.kindsAt i).map BondKind.order).sum) = false := by
            rw [← Loc.readsDifferently_congr (a := b)
              (b := ({ element := some e, aromatic := (S.kindsAt i).any (· == .aromatic) } : Atom))
              hbel hbar, ← hsum]
            exact hrd
          right
          exact ⟨e, horg', hz, .inr ⟨by simp [hTe], by simp, by simp, by simp, hc0, hrd',
            hsm.symm.trans hsm'⟩⟩
    · -- written in brackets with its hydrogens
      dsimp only
      simp only [Option.getD_some, Option.isSome_some, Bool.true_or, hOtot]
      cases hmh : (m.atom i').explicitH with
      | some eh =>
        have hTe : T = eh := by rw [hT', hmh, hC0 (by simp [hmh])]; rfl
        left; simp [hTe]
      | none =>
        cases hme : (m.atom i').element with
        | none =>
          have hT0 : T = 0 := by rw [hT', hmh, hC0 (by simp [hme])]; rfl
          left; simp [hT0]
        | some e =>
          -- bare in `m`, bracketed in the output: the RDKit swap
          right
          obtain ⟨hcbm, -⟩ := hbw i' hmh
          have hcb' := hcbm
          simp only [Atom.canBeBare, hmh, hme, Option.isNone_none, Bool.true_and,
            Bool.and_eq_true, beq_iff_eq] at hcb'
          obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
          have horg' : e ∈ Loc.organic := Loc.mem_organic e (by simpa using horg)
          have hz : (m.atom i').atomicNumber = e.atomicNumber := by
            simp [Atom.atomicNumber, hme]
          have hcc := (Work.cleanFine_cleaned m).charge i'
          obtain ⟨hFz, hFc⟩ := Work.freezeHs_atom_z_charge m i'
          rw [hFz, hFc, hch0, hz, ← hC] at hcc
          refine ⟨e, horg', hz, .inl ⟨by simp, by simp, by simp, by simp, hcc, ?_⟩⟩
          rw [hT', hmh, Option.getD_none, Nat.zero_add, ← hMN hmh e hme, Loc.rdCount, hz]
    · -- kept as it was
      rw [hOH, hOel]
      cases hmh : (m.atom i').explicitH with
      | some eh =>
        have hTe : T = eh := by rw [hT', hmh, hC0 (by simp [hmh])]; rfl
        left; simp [hTe]
      | none => left; simp
  · -- the `[nH]`/`[pH]` kekulization rewrites
    obtain ⟨hbar, hbz, hbc, hbe⟩ := hbr
    have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
      rw [List.any_eq_false]
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      have hlt := Work.lt_of_mem_bondsOf hk
      rw [getElem!_pos K.bonds k hlt]
      simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
    rw [hKany] at hKa
    have hKi : (K.atoms[i]! : WAtom) =
        Work.branchRec (P.atoms[i'.val]! : WAtom) (K.bondHalfSum i) false := hKa
    have hfa : (m.atom i').aromatic = true := by
      have : (P.atoms[i'.val]! : WAtom).aromatic = (m.atom i').aromatic := by rw [hPa]
      rw [← this]; exact hbar
    have hsome : (m.atom i').explicitH = some 1 := by
      have : (P.atoms[i'.val]! : WAtom).explicitHs = (m.atom i').explicitH.getD 0 := by rw [hPa]
      rw [this] at hbe
      cases h : (m.atom i').explicitH with
      | none => rw [h] at hbe; cases hbe
      | some x => rw [h] at hbe; rw [show x = 1 from hbe]
    set z := (P.atoms[i'.val]! : WAtom).z with hzdef
    set pk := P.kindsAt i with hpkdef
    set kk := K.kindsAt i with hkkdef
    have hPz : (P.atoms[i'.val]! : WAtom).z = (m.atom i').atomicNumber := by rw [hPa]
    have hPn : (P.atoms[i'.val]! : WAtom).noImplicit = true := by rw [hPa]; simp [hsome]
    have hP0 : (P.atoms[i'.val]! : WAtom).cachedImplicit = 0 := by
      rw [hPa]; exact hC0 (by simp [hsome])
    have hPr : (P.atoms[i'.val]! : WAtom).radicals = 0 := by rw [hPa]
    -- the total: RDKit's count on the Kekulé bonds
    have hTb : T = Loc.impl
        { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false }
        (Loc.bhs kk) false := by
      rw [hT, Work.cachedTotalHs, hKi, Work.bondHalfSum_eq_loc]
      simp only [Work.branchRec, Nat.zero_add]
      apply Loc.impl_congr <;> first | rfl | exact hbc
    -- at most one
    have hT1 : T ≤ 1 := by
      obtain ⟨c1, c2⟩ := Work.kindsAt_prepare_counts m i'
      obtain ⟨h1, h2⟩ := hw.1 i' hfa
      have hpk3 : pk.length ≤ 3 := c1 ▸ h2
      have hnar : 2 ≤ (pk.filter (· == .aromatic)).length := c2 ▸ h1
      have hPlt : i < P.atoms.size := by
        rw [hP, Work.prepare_eq, Work.size_cacheValences_atoms, Work.size_cleaned]; exact hi
      have hPar : P.isAromaticAtom i = true := by
        rw [Work.isAromaticAtom_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := hbar
        rw [this]; rfl
      have hcand : Work.candOf P P.kekWa P.kekEv0 i =
          Loc.ndb (Loc.branchP z pk) pk ((Loc.branchP z pk).cachedValence.getD 0) := by
        unfold Work.candOf
        rw [Work.kekWa_eq, Work.needsDoubleBond_eq_loc, Work.kekEv0_getElem! P hPlt,
          Work.explicitValence_eq_loc, hPar, Work.bondHalfSum_eq_loc]
        have : (P.atoms[i]! : WAtom).aromatic = true := hbar
        rw [this, Bool.true_and]
        change Loc.ndb (P.atoms[i'.val]! : WAtom) pk (Loc.ev (P.atoms[i'.val]! : WAtom) _ true) = _
        have hev : Loc.ev (P.atoms[i'.val]! : WAtom) (Loc.bhs pk) true =
            (Loc.branchP z pk).cachedValence.getD 0 := by
          simp only [Loc.branchP, Option.getD_some]
          apply Loc.ev_congr <;> first | rfl | exact hbc | exact hbe
        rw [hev]
        apply Loc.ndb_congr <;>
          first | rfl | exact hbc | exact hbe | simp [Loc.branchP, hPn, hP0, hPr]
      have hkk := hkek
      rw [hcand] at hkk
      have hb := Loc.branchH_ok
      rw [List.all_eq_true] at hb
      have hzl : z ∈ ([7, 15] : List ℕ) := by rcases hbz with h | h <;> rw [h] <;> decide
      have := hb z hzl
      rw [List.all_eq_true] at this
      have hc := this pk (Loc.mem_lists 3 pk hpk3)
      unfold Loc.branchHCheck at hc
      have hs : (decide ((pk.filter (· == .aromatic)).length < 2) || decide (3 < pk.length)) =
          false := by
        simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt]; omega
      rw [if_neg (by rw [hs]; decide), List.all_eq_true] at hc
      have h := hc _ hkk
      rw [decide_eq_true_eq] at h
      rw [hTb]
      refine le_trans (le_of_eq ?_) h
      simp only [Loc.branchK, Loc.branchP]
      apply Loc.impl_congr <;> rfl
    have hKr : (K.atoms[i]! : WAtom).radicals = 0 := by
      rw [hKi]; exact hPr
    refine ⟨hKr, hP'r, ?_⟩
    have hKe : (K.atoms[i]! : WAtom).explicitHs = 0 := by rw [hKi]; rfl
    have hKn : (K.atoms[i]! : WAtom).noImplicit = false := by rw [hKi]; rfl
    have hKz : (K.atoms[i]! : WAtom).z = z := by rw [hKi]; rfl
    have hKc : (K.atoms[i]! : WAtom).charge = 0 := by rw [hKi]; exact hbc
    have hme : (m.atom i').element.isNone = false := by
      cases h : (m.atom i').element
      · simp only [Atom.atomicNumber, h, Option.map_none, Option.getD_none] at hPz
        rcases hbz with e | e <;> rw [← hzdef, e] at hPz <;> cases hPz
      · rfl
    obtain ⟨e, he, hez⟩ : ∃ e ∈ Loc.organic, z = e.atomicNumber := by
      rcases hbz with h | h
      · exact ⟨.N, by decide, h⟩
      · exact ⟨.P, by decide, h⟩
    rw [hP'e, hP'n, hKe, hKn, hKz, hKc, hAO]
    unfold normalizeBracket
    dsimp only
    split_ifs with hcb hbare
    · -- written bare: RDKit reads the same atom
      dsimp only
      left
      simp [hOel, hme]
    · -- in brackets: the RDKit swap
      dsimp only
      right
      refine ⟨e, he, hez, .inl ⟨rfl, rfl, by simp [hOtot], by simp, .inl rfl, ?_⟩⟩
      rw [hTb, hez]; rfl
    · -- kept: `[nH]` with its hydrogen, at most one
      rw [hOH, hsome]
      right
      have hm1 : min 1 T = T := by omega
      refine ⟨e, he, hez, .inl ⟨rfl, rfl, by simp [hm1], by simp, .inl rfl, ?_⟩⟩
      rw [hTb, hez]; rfl

open Aromaticity in
/-- **Perception reads an atom of a ring alike in the two copies**, after radicals, in every
environment: from `kekuleWitness_swap` and the decided check (`Loc.swap_ok`). -/
theorem kekuleWitness_readAlike {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs)
    {ring : List ℕ} (hring : ring ∈ (Work.prepare m).relevantCycles.toList) {i : ℕ}
    (hir : i ∈ ring) (rbs : List ℕ) (big : Bool) :
    Loc.readAlike (K.assignRadicals.atoms[i]! : WAtom)
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.atoms[i]! :
        WAtom)
      (K.assignRadicals.kindsAt i) (K.assignRadicals.whoS rbs i) (K.assignRadicals.pullsB rbs i)
      (K.assignRadicals.ringMultB rbs i) big = true := by
  obtain ⟨hb, -, hzz, hcc, -, -⟩ := kekuleWitness_start_basic hK ha
  have htot := kekuleWitness_totals hK ha hw hbw hsv i
  have hkek := kekuleWitness_kekule hK ha hsv i
  obtain ⟨hmarks, -, hperc⟩ := Work.perceived_atom hK i
  have hk := (kekuleWitness_spec hK ha).1
  have hna' := Work.noArom_freezeHs (Work.noArom_ofMolecule (kekuleWitness a K) hk.1 hk.2)
  have hbp := Work.cachedValence_sub_of_noArom hna' i
  have hnK : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  have hnP : (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms.size = n := by
    simp [Work.ofMolecule]
  by_cases hi : i < n
  swap
  · rw [getElem!_neg _ i (by rw [Work.size_atoms_assignRadicals]; omega),
      getElem!_neg _ i (by rw [Work.size_atoms_assignRadicals]; omega)]
    exact Loc.readAlike_self _ _ _ _ _ _
  obtain ⟨hKr, hPr, hcls⟩ := kekuleWitness_swap hK ha hw hbw hi
  have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hlt := Work.lt_of_mem_bondsOf hk
    rw [getElem!_pos K.bonds k hlt]
    simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
  have hlenP : 2 ≤ ((Work.prepare m).bondsOf i).length := by
    have hIs := Work.isRing_of_mem_relevantCycles (Work.prepare m) (by simpa using hring)
    obtain ⟨k₁, k₂, hne, -, -, hk₁, hk₂⟩ := hIs.two_bonds hir
    exact Work.two_le_length_of_ne hne hk₁ hk₂
  have hsKP : Work.SameSkel K (Work.prepare m) := (Work.kekulize_kindsRel hK).sameSkel
  set P' := (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences with hP'
  set KR := K.assignRadicals with hKR
  set PR := P'.assignRadicals with hPR
  set x := (KR.atoms[i]! : WAtom) with hx
  set y := (PR.atoms[i]! : WAtom) with hy
  have hKk : K.kindsAt i = KR.kindsAt i := by
    simp only [hKR, Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds]
  have hPk : PR.kindsAt i = KR.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hb]
  set kk := KR.kindsAt i with hkk
  have hP'k : P'.kindsAt i = kk := by
    rw [← hPk]
    simp only [hPR, Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds]
  have hlen : 2 ≤ kk.length := by
    rw [← hKk]
    simp only [Work.kindsAt, List.length_map, hsKP.bondsOf]
    exact hlenP
  -- the fields `assignRadicals` keeps
  have eqK := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms K) i
  have eqP := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms P') i
  rw [← hKR, ← hx] at eqK
  rw [← hPR, ← hy] at eqP
  have hxz : x.z = (K.atoms[i]! : WAtom).z := by
    have := congrArg WAtom.z eqK; simpa using this
  have hxc : x.charge = (K.atoms[i]! : WAtom).charge := by
    have := congrArg WAtom.charge eqK; simpa using this
  have hxe : x.explicitHs = (K.atoms[i]! : WAtom).explicitHs := by
    have := congrArg WAtom.explicitHs eqK; simpa using this
  have hxn : x.noImplicit = (K.atoms[i]! : WAtom).noImplicit := by
    have := congrArg WAtom.noImplicit eqK; simpa using this
  have hxi : x.cachedImplicit = (K.atoms[i]! : WAtom).cachedImplicit := by
    have := congrArg WAtom.cachedImplicit eqK; simpa using this
  have hyz : y.z = (P'.atoms[i]! : WAtom).z := by
    have := congrArg WAtom.z eqP; simpa using this
  have hyc : y.charge = (P'.atoms[i]! : WAtom).charge := by
    have := congrArg WAtom.charge eqP; simpa using this
  have hye : y.explicitHs = (P'.atoms[i]! : WAtom).explicitHs := by
    have := congrArg WAtom.explicitHs eqP; simpa using this
  have hyn : y.noImplicit = (P'.atoms[i]! : WAtom).noImplicit := by
    have := congrArg WAtom.noImplicit eqP; simpa using this
  -- both records are canonical
  have hcx : Loc.Canonish x kk := by
    constructor
    · rw [Work.cachedValence_eq_loc, Work.bondHalfSum_eq_loc, ← hx, ← hkk] at hkek
      omega
    · have hr := Work.radicals_assignRadicals_eq K (i := i) (by omega)
      rw [← hKR, ← hx, hKr, Work.bondHalfSum_eq_loc, hKk, ← hxz, ← hxc, ← hxe, ← hxn] at hr
      exact hr
  have hcy : Loc.Canonish y kk := by
    constructor
    · rw [Work.cachedValence_eq_loc, Work.bondHalfSum_eq_loc, hPk, ← hy] at hbp
      omega
    · have hr := Work.radicals_assignRadicals_eq P' (i := i) (by omega)
      rw [← hPR, ← hy, hPr, Work.bondHalfSum_eq_loc, hP'k, ← hyz, ← hyc, ← hye, ← hyn] at hr
      exact hr
  -- the same element, charge and hydrogen total
  have hzyx : y.z = x.z := hzz i
  have hcyx : y.charge = x.charge := hcc i
  have htyx : y.explicitHs + y.cachedImplicit = x.explicitHs + x.cachedImplicit := htot
  have hxT : x.explicitHs + x.cachedImplicit = K.cachedTotalHs i := by
    rw [hxe, hxi]; rfl
  -- no donor at more than three bonds, or at an element taking one bond
  by_cases hdeg : 3 < kk.length
  · exact Loc.readAlike_of_deg hdeg _ _ _ _
  by_cases hdv : defaultValence x.z ≤ 1
  · exact Loc.readAlike_of_dv hdv hzyx _ _ _ _
  have hkk3 : kk ∈ Loc.nonArom 3 := Loc.mem_nonArom 3 kk (hKk ▸ hKany) (by omega)
  have henv := Work.env_mem KR rbs i big
  rw [← hkk] at henv
  rw [Loc.readAlike_canonOf hcx hcy]
  unfold Loc.canonOf
  rw [hzyx, hcyx, htyx, hxT]
  rcases hcls with ⟨he, hn⟩ | ⟨e, he, hez, hrd | hsm⟩
  · -- the same hydrogens written
    rw [hye, hyn, he, hn, ← hxe, ← hxn]
    exact Loc.readAlike_self _ _ _ _ _ _
  · -- the RDKit swap
    obtain ⟨hKe0, hKn0, hPe, hPn, hch, hTr⟩ := hrd
    have hxz' : x.z = e.atomicNumber := hxz.trans hez
    have hc : x.charge = -1 ∨ x.charge = 0 ∨ x.charge = 1 := by
      rw [hxc]
      rcases hch with h | h | ⟨h, -⟩ | h | h | h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inl h
      all_goals exact absurd (by rw [hxz', h]; decide) hdv
    rw [hKk, ← hxc] at hTr
    rw [hye, hyn, hPe, hPn, hxe, hxn, hKe0, hKn0, hTr, hxz']
    exact Loc.readAlike_rd he hkk3 hlen hc henv
  · -- the OpenSMILES swap
    obtain ⟨hKeT, hKn1, hPe0, hPn0, hc0, hrd, hTs⟩ := hsm
    have hxz' : x.z = e.atomicNumber := hxz.trans hez
    have hxc0 : x.charge = 0 := hxc.trans hc0
    have hex : ((K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt i).any
        (· == .aromatic) = true → ∃ w' p' r' g', (w', p', r', g') ∈ Loc.envs kk ∧
        Loc.candD (Loc.canon e.atomicNumber 0
            (Loc.smCount e ((K.assignRadicals.setAromaticity
              (Work.prepare m).relevantCycles).kindsAt i)) (Loc.bhs kk)
            (Loc.smCount e ((K.assignRadicals.setAromaticity
              (Work.prepare m).relevantCycles).kindsAt i)) true) kk
          (Loc.ringDonorL (Loc.canon e.atomicNumber 0
            (Loc.smCount e ((K.assignRadicals.setAromaticity
              (Work.prepare m).relevantCycles).kindsAt i)) (Loc.bhs kk)
            (Loc.smCount e ((K.assignRadicals.setAromaticity
              (Work.prepare m).relevantCycles).kindsAt i)) true) kk w' p' r' g') = true := by
      intro har
      obtain ⟨rbs', len', hc'⟩ := (hperc har).2.2.2.2.2
      rw [Work.ringDonor_eq_loc, Work.isAromaticCandidate_eq_candD, ← hx, ← hkk,
        (Loc.canon_read hcx).2, (Loc.canon_read hcx).1] at hc'
      unfold Loc.canonOf at hc'
      rw [hxT, hxe, hxn, hKeT, hKn1, hxc0, hTs, hxz'] at hc'
      exact ⟨_, _, _, _, by rw [hkk]; exact Work.env_mem KR rbs' i _, hc'⟩
    have hd2 := fun har ↦ (hperc har).2.2.2.2.1
    rw [hKk] at hd2 hmarks
    rw [hye, hyn, hPe0, hPn0, hxe, hxn, hKeT, hKn1, hxc0, hTs, hxz']
    exact Loc.readAlike_sm he hkk3 hlen hmarks hrd hd2 hex henv

open Aromaticity in
/-- **The candidate and donor parts of the starting relation**: at every atom of a ring, the two
copies give the same verdict of the candidate test and, at a candidate, the same donor type.  From
`kekuleWitness_readAlike`. -/
theorem kekuleWitness_cand_donor {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs) :
    let P' := (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences
    let R := (Work.prepare m).relevantCycles
    let rbs := (R.toList.flatMap K.assignRadicals.ringBonds).eraseDups
    (∀ ring ∈ R.toList, ∀ i ∈ ring, ∀ len : ℕ,
        P'.assignRadicals.isAromaticCandidate i (P'.assignRadicals.ringDonor rbs len i) =
          K.assignRadicals.isAromaticCandidate i (K.assignRadicals.ringDonor rbs len i)) ∧
      ∀ ring ∈ R.toList, ∀ i ∈ ring, ∀ len : ℕ,
        K.assignRadicals.isAromaticCandidate i (K.assignRadicals.ringDonor rbs len i) = true →
          P'.assignRadicals.ringDonor rbs len i = K.assignRadicals.ringDonor rbs len i := by
  intro P' R rbs
  obtain ⟨hb, -, hz, -, -, -⟩ := kekuleWitness_start_basic hK ha
  replace hb : P'.assignRadicals.bonds = K.assignRadicals.bonds := hb
  replace hz : ∀ i : ℕ, (P'.assignRadicals.atoms[i]! : WAtom).z =
      (K.assignRadicals.atoms[i]! : WAtom).z := hz
  have hk : ∀ i, P'.assignRadicals.kindsAt i = K.assignRadicals.kindsAt i := fun i ↦ by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hb]
  have beq : ∀ d d' : Donor, (d == d') = true → d = d' := by
    intro d d' h
    cases d <;> cases d' <;> first | rfl | exact absurd h (by decide)
  -- both sides, locally
  have loc : ∀ i len, P'.assignRadicals.ringDonor rbs len i =
        Loc.ringDonorL (P'.assignRadicals.atoms[i]! : WAtom) (K.assignRadicals.kindsAt i)
          (K.assignRadicals.whoS rbs i) (K.assignRadicals.pullsB rbs i)
          (K.assignRadicals.ringMultB rbs i) (decide (9 ≤ len)) ∧
      ∀ d, P'.assignRadicals.isAromaticCandidate i d =
        Loc.candD (P'.assignRadicals.atoms[i]! : WAtom) (K.assignRadicals.kindsAt i) d := by
    intro i len
    refine ⟨?_, fun d ↦ ?_⟩
    · rw [Work.ringDonor_eq_loc, hk, Work.whoS_congr hb, Work.pullsB_congr hb hz,
        Work.ringMultB_congr hb]
    · rw [Work.isAromaticCandidate_eq_candD, hk]
  refine ⟨fun ring hring i hir len ↦ ?_, fun ring hring i hir len hc ↦ ?_⟩
  · have h := kekuleWitness_readAlike hK ha hw hbw hsv hring hir rbs (decide (9 ≤ len))
    rw [(loc i len).2, (loc i len).1, Work.isAromaticCandidate_eq_candD, Work.ringDonor_eq_loc]
    unfold Loc.readAlike at h
    rw [Bool.and_eq_true] at h
    exact (beq_iff_eq.1 h.1).symm
  · have h := kekuleWitness_readAlike hK ha hw hbw hsv hring hir rbs (decide (9 ≤ len))
    rw [Work.isAromaticCandidate_eq_candD, Work.ringDonor_eq_loc] at hc
    rw [(loc i len).1, Work.ringDonor_eq_loc]
    unfold Loc.readAlike at h
    rw [Bool.and_eq_true, hc, Bool.not_true, Bool.false_or] at h
    exact (beq _ _ h.2).symm

open Aromaticity in
/-- **On the witness's copy, the `adjustHs` step gives back the cached hydrogen total** at every
atom, once perception marks the two copies alike.  Where perception leaves the atom unmarked, the
witness's cached count is RDKit's on the same bonds.  Where it marks it, by `kekuleWitness_swap`:
the kekulized copy's step when the two write the same hydrogens, nothing to do in brackets, and
`Loc.restoreArom_ok` for an atom the witness writes bare by OpenSMILES's count. -/
theorem kekuleWitness_hsRestored {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs)
    (hs : Work.SameMarks (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles)
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.setAromaticity
        (Work.prepare m).relevantCycles))
    {i : ℕ} (hi : i < n) :
    Work.HsRestored
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.setAromaticity
        (Work.prepare m).relevantCycles) i := by
  obtain ⟨hKr, -, hcls⟩ := kekuleWitness_swap hK ha hw hbw hi
  obtain ⟨-, -, hzz, hcc, -, -⟩ := kekuleWitness_start_basic hK ha
  obtain ⟨hmarks, harS, hperc⟩ := Work.perceived_atom hK i
  have hrK := Work.hsRestored_kekulize hw.1 hw.2 hbw hK ⟨i, hi⟩
  have htot := kekuleWitness_totals hK ha hw hbw hsv i
  rw [Work.cachedTotalHs_assignRadicals, Work.cachedTotalHs_assignRadicals] at htot
  have hkek := kekuleWitness_kekule hK ha hsv i
  have hnK : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  have hnP : (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms.size = n := by
    simp [Work.ofMolecule]
  have hKany : (K.kindsAt i).any (· == .aromatic) = false := by
    rw [List.any_eq_false]
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have hlt := Work.lt_of_mem_bondsOf hk
    rw [getElem!_pos K.bonds k hlt]
    simpa using (Work.kekulize_noArom hK).2 _ (Array.getElem_mem hlt)
  -- the witness's record at `i`: not adjusted, its implicit hydrogens RDKit's on the Kekulé bonds
  set i' : Fin n := ⟨i, hi⟩ with hi'
  have hkA : (kekuleWitness a K).atom i' = { a.atom i' with aromatic := false } :=
    (kekuleWitness_spec hK ha).2.atoms i'
  have hbF : (Work.ofMolecule (kekuleWitness a K)).freezeHs.bonds = K.bonds := by
    rw [Work.freezeHs_bonds, bonds_ofMolecule_kekuleWitness hK ha]
  have hka : (Work.ofMolecule (kekuleWitness a K)).freezeHs.kindsAt i = K.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hbF]
  have hfa := Work.freezeHs_ofMolecule_atom (kekuleWitness a K) i'
  rw [hkA] at hfa
  have harF : (Work.ofMolecule (kekuleWitness a K)).freezeHs.isAromaticAtom i = false := by
    rw [Work.isAromaticAtom_eq_loc, hka, hKany]
    change (((Work.ofMolecule (kekuleWitness a K)).freezeHs.atoms[i'.val]! : WAtom).aromatic ||
      false) = false
    rw [hfa]
    rfl
  have hc := Work.freezeCache_atom (kekuleWitness a K) i'
  rw [hkA] at hc
  have hadjP : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).adjustHs = false := by
    change ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).adjustHs = false
    rw [hc]
    exact harF
  have hciP : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).cachedImplicit = Loc.impl
        ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! : WAtom)
        (Loc.bhs (K.kindsAt i)) false := by
    change ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! :
      WAtom).cachedImplicit = Loc.impl
        ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i'.val]! : WAtom)
        (Loc.bhs (K.kindsAt i)) false
    rw [hc]
    dsimp only
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hka, harF]
    apply Loc.impl_congr <;> (rw [hfa]; try rfl)
  -- the fields `assignRadicals` keeps
  have eqK := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms K) i
  have eqP := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms
    (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences) i
  have tK : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f (K.assignRadicals.atoms[i]! : WAtom) = f (K.atoms[i]! : WAtom) := by
    intro α f h2
    rw [← h2, eqK, h2]
  have tP : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.atoms[i]! :
        WAtom) =
        f ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! : WAtom) := by
    intro α f h2
    rw [← h2, eqP, h2]
  have hzPK : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).z = (K.atoms[i]! : WAtom).z := by
    rw [← tP WAtom.z (fun _ ↦ rfl), ← tK WAtom.z (fun _ ↦ rfl)]; exact hzz i
  have hcPK : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
      WAtom).charge = (K.atoms[i]! : WAtom).charge := by
    rw [← tP WAtom.charge (fun _ ↦ rfl), ← tK WAtom.charge (fun _ ↦ rfl)]; exact hcc i
  -- the steps on the two copies, locally
  have hnS : i < (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).atoms.size := by
    rw [(Work.afterRel_setAromaticity _ _).atoms_size,
      (Work.afterRel_assignRadicals (w := K)).atoms_size, hnK]; exact hi
  have hnS' : i < ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals
      |>.setAromaticity (Work.prepare m).relevantCycles).atoms.size := by
    rw [(Work.afterRel_setAromaticity _ _).atoms_size,
      (Work.afterRel_assignRadicals (w := _)).atoms_size, hnP]; exact hi
  rw [Work.hsRestored_iff_loc _ hnS] at hrK
  rw [Work.hsRestored_iff_loc _ hnS']
  have hk' : ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals
      |>.setAromaticity (Work.prepare m).relevantCycles).kindsAt i =
      (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hs.bonds]
  rw [hk', congrFun hs.isAromaticAtom_eq i, harS]
  rw [harS] at hrK
  have eqS := Work.setAromaticity_atom K.assignRadicals (Work.prepare m).relevantCycles i
  have eqS' := Work.setAromaticity_atom
    (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals
    (Work.prepare m).relevantCycles i
  have trK : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with aromatic := false } = f x) →
      (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f ((K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).atoms[i]! : WAtom) =
        f (K.atoms[i]! : WAtom) := by
    intro α f h1 h2
    rw [← h1, eqS, h1, tK f h2]
  have trP : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with aromatic := false } = f x) →
      (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f (((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.setAromaticity
        (Work.prepare m).relevantCycles).atoms[i]! : WAtom) =
        f ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! : WAtom) := by
    intro α f h1 h2
    rw [← h1, eqS', h1, tP f h2]
  rw [Loc.restore_congr (b := (K.atoms[i]! : WAtom))
    (trK WAtom.z (fun _ ↦ rfl) (fun _ ↦ rfl)) (trK WAtom.charge (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trK WAtom.explicitHs (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trK WAtom.noImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trK WAtom.cachedImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trK WAtom.adjustHs (fun _ ↦ rfl) (fun _ ↦ rfl))] at hrK
  rw [Loc.restore_congr
    (b := ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! : WAtom))
    (trP WAtom.z (fun _ ↦ rfl) (fun _ ↦ rfl)) (trP WAtom.charge (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trP WAtom.explicitHs (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trP WAtom.noImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trP WAtom.cachedImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (trP WAtom.adjustHs (fun _ ↦ rfl) (fun _ ↦ rfl))]
  simp only [Work.cachedTotalHs] at htot
  cases har : ((K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles).kindsAt i).any
    (· == .aromatic)
  · -- not marked: the kinds are the Kekulé ones, and the witness cached RDKit's count on them
    rw [Work.marks_eq_of_noArom hmarks har]
    exact Loc.restore_of_cached hadjP hciP
  rw [har] at hrK
  rcases hcls with ⟨he, hn⟩ | ⟨e, he, hez, hrd | hsm⟩
  · -- the same hydrogens written: the kekulized copy's step
    rw [Loc.restore_congr_true hzPK hcPK he hn (by omega)]
    exact hrK
  · -- in brackets in the witness's copy, nothing to adjust
    obtain ⟨-, -, hPe, hPn, -, -⟩ := hrd
    simp only [Work.cachedTotalHs] at hPe
    exact Loc.restore_of_noImplicit hPn (by omega) _ _
  · -- written bare by OpenSMILES's count: the decided check
    obtain ⟨hKeT, hKn1, hPe0, hPn0, hc0, hrd, hTs⟩ := hsm
    obtain ⟨hl2, hel, hcd, hdo, hd2, -⟩ := hperc har
    -- the kekulized record, canonical
    have hKk : K.assignRadicals.kindsAt i = K.kindsAt i := by
      simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds]
    have hcx : Loc.Canonish (K.assignRadicals.atoms[i]! : WAtom) (K.kindsAt i) := by
      constructor
      · rw [Work.cachedValence_eq_loc, Work.bondHalfSum_eq_loc, hKk] at hkek
        omega
      · rw [Work.radicals_assignRadicals_eq K (by omega), hKr, Work.bondHalfSum_eq_loc,
          tK WAtom.z (fun _ ↦ rfl), tK WAtom.charge (fun _ ↦ rfl),
          tK WAtom.explicitHs (fun _ ↦ rfl), tK WAtom.noImplicit (fun _ ↦ rfl)]
    have hcan : Loc.canonOf (K.assignRadicals.atoms[i]! : WAtom) (K.kindsAt i) =
        Loc.canon e.atomicNumber 0
          (Loc.smCount e ((K.assignRadicals.setAromaticity
            (Work.prepare m).relevantCycles).kindsAt i))
          (Loc.bhs (K.kindsAt i))
          (Loc.smCount e ((K.assignRadicals.setAromaticity
            (Work.prepare m).relevantCycles).kindsAt i))
          true := by
      unfold Loc.canonOf
      rw [tK WAtom.z (fun _ ↦ rfl), tK WAtom.charge (fun _ ↦ rfl),
        tK WAtom.explicitHs (fun _ ↦ rfl), tK WAtom.noImplicit (fun _ ↦ rfl),
        tK WAtom.cachedImplicit (fun _ ↦ rfl), hez, hc0, hKn1, ← Work.cachedTotalHs, hKeT, hTs]
    obtain ⟨g1, g2, g3⟩ := Loc.canon_gates hcx
    rw [g1, hcan] at hel
    rw [g2, hcan] at hcd
    rw [g3, hcan] at hdo
    have hkk3 : K.kindsAt i ∈ Loc.nonArom 3 := Loc.mem_nonArom 3 _ hKany (by
      have := Work.elec_nonneg_length (by rwa [g1, hcan]); omega)
    exact Loc.restore_sm he hkk3 hmarks har hl2 hd2 hrd hel hcd hdo (hzPK.trans hez)
      (hcPK.trans hc0) hPe0 hPn0 (by simp only [Work.cachedTotalHs] at hTs; omega) hadjP

open Aromaticity in
/-- **The starting relation**: after radicals, the kekulized copy of the first run and the
witness's copy are read alike by perception (`Work.PerceiveAgree`), with the same bonds and
flags, and at every atom of each the `adjustHs` step gives back the cached hydrogen total
(`Work.HsRestored`).  From `kekuleWitness_start_basic`, `kekuleWitness_cand_donor` and, once
perception reads the two copies alike, `kekuleWitness_hsRestored`. -/
theorem kekuleWitness_start {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs) :
    Work.PerceiveAgree (Work.prepare m).relevantCycles K.assignRadicals
        (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals ∧
      Work.SameMarks K.assignRadicals
        (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals ∧
      (∀ i < n, Work.HsRestored
        (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles) i) ∧
      ∀ i < n, Work.HsRestored
        ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.setAromaticity
          (Work.prepare m).relevantCycles) i := by
  obtain ⟨hb, hs, hz, hc, hm, hna⟩ := kekuleWitness_start_basic hK ha
  obtain ⟨hcand, hdon⟩ := kekuleWitness_cand_donor hK ha hw hbw hsv
  have htot := kekuleWitness_totals hK ha hw hbw hsv
  have hr : ∀ i < n, Work.HsRestored
      (K.assignRadicals.setAromaticity (Work.prepare m).relevantCycles) i :=
    fun i hi ↦ Work.hsRestored_kekulize hw.1 hw.2 hbw hK ⟨i, hi⟩
  have hkek := kekuleWitness_kekule hK ha hsv
  -- the witness's copy has nothing aromatic, so its bond part is its Kekulé sum, and the bonds
  -- are the kekulized copy's
  have hk := (kekuleWitness_spec hK ha).1
  have hna' := Work.noArom_freezeHs (Work.noArom_ofMolecule (kekuleWitness a K) hk.1 hk.2)
  have hbp : ∀ i : ℕ,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.cachedValence i
          : ℤ) -
        ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals.atoms[i]! :
          WAtom).explicitHs =
      (K.assignRadicals.cachedValence i : ℤ) - (K.assignRadicals.atoms[i]! : WAtom).explicitHs := by
    intro i
    rw [Work.cachedValence_sub_of_noArom hna' i, hkek i]
    simp only [Work.bondHalfSum, Work.bondsOf, Work.numBonds, hb]
  have hp : Work.PerceiveAgree (Work.prepare m).relevantCycles K.assignRadicals
      (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.assignRadicals :=
    ⟨hb, hs, hz, hc, htot, hbp, hkek, hna, hcand, hdon⟩
  exact ⟨hp, hm, hr, fun i hi ↦ kekuleWitness_hsRestored hK ha hw hbw hsv (hp.setAromaticity hm) hi⟩

open Aromaticity in
/-- **The core**: perception and the final hydrogen counts see the same on the witness's working
copy as on the kekulized one.  From the starting relation (`kekuleWitness_start`) through
perception and `finalizeHs` (`outAgree_finish`). -/
theorem finish_kekuleWitness_agree {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs) :
    OutAgree n (K.finish (Work.prepare m).relevantCycles)
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.finish
        (Work.prepare m).relevantCycles) := by
  obtain ⟨hp, hm, hr, hr'⟩ := kekuleWitness_start hK ha hw hbw hsv
  have hn : K.atoms.size = n := by
    rw [(Work.kekulize_kindsRel hK).atoms_size, size_prepare_atoms]
  exact outAgree_finish hn hp hm hr hr'

open Aromaticity in
/-- The witness gives the output back from its working copy: from
`finish_kekuleWitness_agree` and `aromatizeOutput_kekuleWitness_of_agree`. -/
theorem aromatizeOutput_kekuleWitness {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : ∀ i < n,
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.cachedValence i : ℤ) -
          ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.atoms[i]! :
            WAtom).explicitHs =
        ((Work.prepare m).cachedValence i : ℤ) - ((Work.prepare m).atoms[i]! : WAtom).explicitHs) :
    (kekuleWitness a K).aromatizeOutput
      ((Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences.finish
        (Work.prepare m).relevantCycles) = a :=
  aromatizeOutput_kekuleWitness_of_agree hK ha (finish_kekuleWitness_agree hK ha hw hbw hsv)

open Aromaticity in
/-- **The witness aromatizes back to the output**, unless `cleanUp` rewrites it.  From
`aromatizeOutput_kekuleWitness`: the witness is Kekulé, so kekulization does nothing; with its
charges kept, `cleanUp` did nothing; and its ring set is the first run's, since the bonds join the
same atoms. -/
theorem kekuleWitness_aromatize {m a a' : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (h' : (kekuleWitness a K).aromatize = .ok a') (hc' : (kekuleWitness a K).ChargesKept a')
    (hw : m.AromaticWritten) (hbw : m.BareWritable)
    (hsv : m.SameValences (kekuleWitness a K)) : a' = a := by
  obtain ⟨hkk, -⟩ := kekuleWitness_spec hK ha
  obtain ⟨K', hK', ha'⟩ := aromatize_eq_ok.mp h'
  rw [hkk.kekulize_prepare] at hK'
  cases hK'
  have hcl := hc'.cleanUp_eq _ (.refl _) _ ha'
  have hP' : Work.prepare (kekuleWitness a K) =
      (Work.ofMolecule (kekuleWitness a K)).freezeHs.cacheValences := by
    simp only [Work.prepare, hcl]
  have hb : (Work.prepare (kekuleWitness a K)).bonds = K.bonds := by
    rw [hP', Work.cacheValences_bonds, Work.freezeHs_bonds, bonds_ofMolecule_kekuleWitness hK ha]
  have hKP := Work.kekulize_kindsRel hK
  have hR : (Work.prepare (kekuleWitness a K)).relevantCycles =
      (Work.prepare m).relevantCycles := by
    rw [Work.relevantCycles_eq_of_ends (w := K) ?_ (by rw [hb]) (fun j ↦ by rw [hb]),
      Work.relevantCycles_eq_of_ends hKP.atoms_size hKP.bonds_size hKP.ends]
    rw [hKP.atoms_size, size_prepare_atoms, size_prepare_atoms]
  rw [hR, hP'] at ha'
  rw [← ha']
  refine aromatizeOutput_kekuleWitness hK ha hw hbw fun i hi ↦ ?_
  have := hsv ⟨i, hi⟩
  simp only [bondValence, hP'] at this
  exact this

/-- **Every output is the image of a Kekulé structure of itself**, unless `cleanUp` rewrites
that structure.  A witness is the structure the pipeline computes on the way: the output's atoms
with the aromatic flags cleared, and each aromatic bond with the kind `Work.kekulize` gave it
(`kekuleWitness`); if it aromatizes keeping its charges, and RDKit reads its valences as it
reads `m`'s (`m.SameValences k`), it aromatizes to `a`.  Both provisos are needed: for
`O=p1ccccc1` the witness is `O=P1=CC=CC=C1`, which `cleanUp` rewrites (`aromatize_aromatize`);
for `Oc#1ccccc1` the kekulizer gives the carbon next to the triple bond a single ring bond, so the
witness `OC#1C=CC=CC1` has a five-valent carbon (RDKit would reject it, and its valences are not
`m`'s), and aromatizes to itself.  The witness's valences being allowed (`ValenceOk`) need not be
assumed: it follows from `m.SameValences k`.  `m.AromaticWritten` excludes aromatic atoms RDKit's
valence rounding misreads (`N[se]=CC`, `C:c1ccccc1`), and `m.BareWritable` atoms no SMILES can
write without brackets (every parsed molecule is `BareWritable`). -/
theorem exists_kekule_aromatize {m a : Molecule n} (h : m.aromatize = .ok a)
    (hw : m.AromaticWritten) (hbw : m.BareWritable) :
    ∃ k : Molecule n, k.IsKekule ∧ k.IsKekuleStructureOf a ∧
      ∀ a', k.aromatize = .ok a' → k.ChargesKept a' → m.SameValences k → a' = a := by
  obtain ⟨K, hK, ha⟩ := aromatize_eq_ok.mp h
  obtain ⟨hk, hs⟩ := kekuleWitness_spec hK ha
  exact ⟨_, hk, hs, fun _ h' hc' hsv ↦ kekuleWitness_aromatize hK ha h' hc' hw hbw hsv⟩

/-! ### 4. The canonical string -/

/-- Renumbering the atoms does not change the canonical SMILES of the aromatized molecule.
From `aromatize_relabel` and `canonicalSmiles_relabel`. -/
theorem canonicalSmiles_aromatize_relabel {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (σ : Equiv.Perm (Fin n))
    (h' : (m.relabel σ).aromatize = .ok a') : a'.canonicalSmiles = a.canonicalSmiles := by
  rw [aromatize_relabel h hc hk σ h', canonicalSmiles_relabel]

/-- Relisting the bonds does not change the canonical SMILES of the aromatized molecule.  From
`aromatize_of_sameBonds` and `canonicalSmiles_eq_of_sameBonds`. -/
theorem canonicalSmiles_aromatize_of_sameBonds {m m' a : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hat : m'.atoms = m.atoms) (hst : m'.stereo = m.stereo)
    (hb : m'.SameBonds m) :
    ∃ a', m'.aromatize = .ok a' ∧ a'.canonicalSmiles = a.canonicalSmiles := by
  obtain ⟨a', h', ha, hs, hb'⟩ := aromatize_of_sameBonds h hc hat hst hb
  exact ⟨a', h', canonicalSmiles_eq_of_sameBonds ha hs hb'⟩

/-- Aromatizing an output again, keeping its charges, does not change its canonical SMILES.
From `aromatize_aromatize`. -/
theorem canonicalSmiles_aromatize_aromatize {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (h' : a.aromatize = .ok a') (hc' : a.ChargesKept a') (hv : a.ValenceOk) :
    a'.canonicalSmiles = a.canonicalSmiles := by
  rw [aromatize_aromatize h h' hc' hv]

/-- **One molecule, one aromatic canonical SMILES.**  Let the Kekulé structure `m` aromatize to
`a`, keeping its charges.  Take any other Kekulé structure `m₁` of it over the aromatic bonds,
renumber its atoms by any `σ`, and list the renumbered bonds in any order and orientation: the
result `m₂` aromatizes, and to the canonical SMILES of `a`.  From
`aromatize_of_kekuleVariant_of_chargesKept`, `IsKekule.aromatize_relabel`,
`aromatize_of_sameBonds` and
`canonicalSmiles_eq_of_sameBonds_relabel`. -/
theorem canonicalSmiles_aromatize_eq {m m₁ m₂ a : Molecule n} (hk : m.IsKekule)
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (hv : KekuleVariant a m m₁)
    (σ : Equiv.Perm (Fin n)) (hat : m₂.atoms = (m₁.relabel σ).atoms)
    (hst : m₂.stereo = (m₁.relabel σ).stereo) (hb : m₂.SameBonds (m₁.relabel σ)) :
    ∃ a₂, m₂.aromatize = .ok a₂ ∧ a₂.canonicalSmiles = a.canonicalSmiles := by
  have h₁ := aromatize_of_kekuleVariant_of_chargesKept hk h hc hv
  have h₂ := (hv.isKekule hk).aromatize_relabel h₁ (hv.chargesKept hc) σ
  obtain ⟨a₂, h₂', ha, hs, hb'⟩ :=
    aromatize_of_sameBonds h₂ ((hv.chargesKept hc).relabel σ) hat hst hb
  exact ⟨a₂, h₂', canonicalSmiles_eq_of_sameBonds_relabel σ ha hs hb'⟩

/-! ### 5. A lowercase molecule and a Kekulé spelling of it

Sections 1 to 4 relate two Kekulé structures with the same atom records, and
a lowercase molecule to a Kekulé structure of its own *output*.  They do not
relate two *inputs* as a user writes them: `c1cc[nH]c1` and `C1=CNC=C1`.
These differ in more than the bonds.  The nitrogen is a bracket atom with one
written hydrogen in the first and a bare atom with one implied hydrogen in the
second, and the carbons are flagged aromatic in the first only.

The formulation chosen is a direct relation between the two inputs,
`k.IsKekuleSpellingOf m`: the same atoms up to the aromatic flag and up to how
their hydrogens are recorded, the same bond list up to the kinds, each bond
written aromatic in `m` single or double in `k`, and — this is what makes `k`
a Kekulé structure rather than any placement of double bonds — every atom
with the same hydrogens and the same valence in both, *as `aromatize` counts
them* (`sanitizedH`, `sanitizedValence`): RDKit counts an aromatic atom's
bonds as a Kekulé structure would, so its valence in the lowercase molecule is
the bond-order sum a Kekulé structure must give it.

The other route, a lemma that `aromatize` does not depend on how an atom's
hydrogens are recorded, is false: RDKit's `cleanUp` reads the *explicit*
valence, which counts a bracket atom's hydrogens and not a bare atom's, so it
rewrites `O=[IH]=O` (to `[O-][IH+2][O-]`) and leaves `O=I=O` alone, though the
two have the same hydrogens and valences.

What forces each hypothesis of `aromatize_of_isKekuleSpellingOf`:

* `valence`: `Cn1cccc1` against `CN1(=CC=CC=1)`, a five-valent nitrogen with
  two ring double bonds.  Same atoms, same hydrogens, every aromatic bond
  single or double, every atom at an allowed valence; not aromatic.
* `hydrogens`: `c1ccccc1` against `C1=CC=CCC1`.  Same valences, with two
  hydrogens where benzene has one.
* `AromaticKept`: `Cc1cccc2ncc12`, whose five-ring does not come out
  aromatic, against `CC1=CC=CC2=NC=C12`, the Kekulé spelling with that ring's
  double bonds the other way round from where kekulization put them.
* `ChargesKept` for `m`, and for `k` with its own output: `O=I=O` and
  `O=[IH]=O` are Kekulé spellings of each other, and `cleanUp` rewrites only
  the second, whichever of the two is `m`.

The conclusion is an equality of molecules because the relation fixes the
bond list.  Two strings a user writes list their bonds differently, which is
what the corollary `canonicalSmiles_aromatize_of_isKekuleSpellingOf` absorbs.

Tested as written by `lake exe invariance-test`.  From each input, three
spellings are built on the Kekulé structure the pipeline computes for it —
atoms as in the input (`[nH]` becomes `[NH]`), in bracket normal form (`N`, as
a user writes it), and with every hydrogen in brackets — with up to eight
Kekulé variants of each.  The matched pairs are a lowercase and a Kekulé
string of one molecule written by RDKit in the same atom order, each parsed on
its own and the second read onto the bond list of the first: the 229 pairs of
`datasets/aromatize-pairs.tsv` (17 with `[nH]`, 32 with stereo marks) and
1 062 more from the 1 147 molecules above, of which 1 003 keep the atom order.

| statement | checks | failures |
|---|---|---|
| `aromatize_of_isKekuleSpellingOf`, built spellings | 29 109 | 0 |
| `aromatize_of_isKekuleSpellingOf`, matched pairs | 1 231 | 0 |
| `canonicalSmiles_aromatize_of_isKekuleSpellingOf`, built spellings | 9 156 | 0 |
| `canonicalSmiles_aromatize_of_isKekuleSpellingOf`, matched pairs | 1 231 | 0 |

The built spellings are from the 813 hard cases, the 2 992 oracle strings and
a one-in-four sample (3 425) of the 13 701 Kekulé and lowercase strings.
Every one of the 30 459 spellings built satisfied `IsKekuleSpellingOf` as
written; without `ChargesKept` and `AromaticKept`, 24 of them aromatize to
something else.  In all 1 291 matched pairs the two strings got one canonical
SMILES; the 60 that are not spellings as written list their atoms in
different orders, or (one tetrazole) put a hydrogen on another nitrogen.
-/

/-- The hydrogens `aromatize` counts on atom `i` of the input: those written in its brackets, or
for a bare atom those RDKit's valence rule gives it on the bonds as written.  (The `implicitH`
recorded on the atom is not consulted.) -/
def sanitizedH (m : Molecule n) (i : Fin n) : ℕ := (Aromaticity.Work.ofMolecule m).totalHs i

/-- The valence `aromatize` counts on atom `i` of the input: its bond orders, an aromatic atom's
snapped to what a Kekulé structure gives it (RDKit's explicit valence), plus all its
hydrogens. -/
def sanitizedValence (m : Molecule n) (i : Fin n) : ℕ :=
  (Aromaticity.Work.ofMolecule m).explicitValence i + (Aromaticity.Work.ofMolecule m).implicitHs i

/-- `k` is a Kekulé spelling of `m`: nothing in `k` is written aromatic; the configurations are
the same; bond for bond the same atoms, orientation and mark, a bond written aromatic in `m`
single or double in `k` and any other bond of the same kind; atom for atom the same record up
to the aromatic flag and the hydrogens; and each atom with the hydrogens and the valence in `k`
that it has in `m`, as `aromatize` counts them. -/
structure IsKekuleSpellingOf (k m : Molecule n) : Prop where
  /-- Nothing in `k` is written aromatic. -/
  kekule : k.IsKekule
  /-- The same configurations. -/
  stereo : k.stereo = m.stereo
  /-- Bond for bond: the same skeleton; a bond written aromatic in `m` is single or double in
  `k`, any other bond has the same kind. -/
  bonds : List.Forall₂ (fun b b' : Bond n ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
    if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
    k.bonds m.bonds
  /-- Atom for atom the same record, the aromatic flag and the hydrogens aside. -/
  atoms : ∀ i, ({ k.atom i with aromatic := false, explicitH := none, implicitH := 0 } : Atom) =
    { m.atom i with aromatic := false, explicitH := none, implicitH := 0 }
  /-- Every atom has the hydrogens it has in `m`. -/
  hydrogens : ∀ i, k.sanitizedH i = m.sanitizedH i
  /-- Every atom has the valence it has in `m`. -/
  valence : ∀ i, k.sanitizedValence i = m.sanitizedValence i

instance (k m : Molecule n) : Decidable (k.IsKekuleSpellingOf m) :=
  decidable_of_iff (k.IsKekule ∧ k.stereo = m.stereo ∧
    List.Forall₂ (fun b b' : Bond n ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir ∧
      if b'.kind = .aromatic then b.kind = .single ∨ b.kind = .double else b.kind = b'.kind)
      k.bonds m.bonds ∧
    (∀ i, ({ k.atom i with aromatic := false, explicitH := none, implicitH := 0 } : Atom) =
      { m.atom i with aromatic := false, explicitH := none, implicitH := 0 }) ∧
    (∀ i, k.sanitizedH i = m.sanitizedH i) ∧ ∀ i, k.sanitizedValence i = m.sanitizedValence i)
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ ↦ ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
      fun h ↦ ⟨h.kekule, h.stereo, h.bonds, h.atoms, h.hydrogens, h.valence⟩⟩

set_option maxHeartbeats 1000000 in -- many rewrites through the records of one atom
open Aromaticity in
/-- **Every atom of a Kekulé input gets its hydrogens back in `adjustHs`**, when `cleanUp` does
nothing and every atom written bare could be: where perception leaves it unmarked, its cached
count is RDKit's on the same bonds; a bracketed atom has nothing to adjust; a bare atom perception
marks is the decided `Loc.bareRestore_ok`. -/
theorem IsKekule.hsRestored {x : Molecule n} (hx : x.IsKekule) (hbx : x.BareWritable)
    (hq : (Work.ofMolecule x).freezeHs.cleanUp = (Work.ofMolecule x).freezeHs) {i : ℕ}
    (hi : i < n) :
    Work.HsRestored ((Work.prepare x).assignRadicals.setAromaticity
      (Work.prepare x).relevantCycles) i := by
  have hP : Work.prepare x = (Work.ofMolecule x).freezeHs.cacheValences := by
    simp only [Work.prepare, hq]
  have hna := hx.noArom_prepare
  have hrings : ∀ r ∈ (Work.prepare x).relevantCycles.toList, (Work.prepare x).IsRing r :=
    fun r hr ↦ Work.isRing_of_mem_relevantCycles _ (by simpa using hr)
  obtain ⟨hmarks, harS, hperc⟩ := Work.perceived_atom_of_noArom hna hrings i
  have hnP : (Work.prepare x).atoms.size = n := size_prepare_atoms x
  set i' : Fin n := ⟨i, hi⟩ with hi'
  -- the record at `i`
  have hc := Work.freezeCache_atom x i'
  have hfa := Work.freezeHs_ofMolecule_atom x i'
  have hka : (Work.ofMolecule x).freezeHs.kindsAt i = (Work.prepare x).kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hP, Work.cacheValences_bonds]
  have hKany : ((Work.prepare x).kindsAt i).any (· == .aromatic) = false := by
    rw [List.any_eq_false]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    have hlt := Work.lt_of_mem_bondsOf hk
    rw [getElem!_pos _ k hlt]
    simpa using hna.2 _ (Array.getElem_mem hlt)
  have harx : (x.atom i').aromatic = false := hx.1 i'
  have harF : (Work.ofMolecule x).freezeHs.isAromaticAtom i = false := by
    rw [Work.isAromaticAtom_eq_loc, hka, hKany]
    change (((Work.ofMolecule x).freezeHs.atoms[i'.val]! : WAtom).aromatic || false) = false
    rw [hfa]
    simpa using harx
  have hPi : ((Work.prepare x).atoms[i]! : WAtom) =
      ((Work.ofMolecule x).freezeHs.cacheValences.atoms[i'.val]! : WAtom) := by rw [hP]
  have hadj : ((Work.prepare x).atoms[i]! : WAtom).adjustHs = false := by
    rw [hPi, hc]; exact harF
  have hci : ((Work.prepare x).atoms[i]! : WAtom).cachedImplicit =
      Loc.impl ((Work.prepare x).atoms[i]! : WAtom) (Loc.bhs ((Work.prepare x).kindsAt i))
        false := by
    rw [hPi, hc]
    dsimp only
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hka, harF]
    apply Loc.impl_congr <;> (rw [hfa]; try rfl)
  have hez : ((Work.prepare x).atoms[i]! : WAtom).explicitHs = (x.atom i').explicitH.getD 0 := by
    rw [hPi, hc]
  have hnz : ((Work.prepare x).atoms[i]! : WAtom).noImplicit =
      ((x.atom i').explicitH.isSome || (x.atom i').element.isNone) := by
    rw [hPi, hc]
  have hzz : ((Work.prepare x).atoms[i]! : WAtom).z = (x.atom i').atomicNumber := by
    rw [hPi, hc]
  have hcz : ((Work.prepare x).atoms[i]! : WAtom).charge = (x.atom i').charge := by
    rw [hPi, hc]
  have hrz : ((Work.prepare x).atoms[i]! : WAtom).radicals = 0 := by
    rw [hPi, hc]
  -- the step, locally
  have hnS : i < ((Work.prepare x).assignRadicals.setAromaticity
      (Work.prepare x).relevantCycles).atoms.size := by
    rw [(Work.afterRel_setAromaticity _ _).atoms_size,
      (Work.afterRel_assignRadicals (w := _)).atoms_size, hnP]; exact hi
  rw [Work.hsRestored_iff_loc _ hnS, harS]
  have eqS := Work.setAromaticity_atom (Work.prepare x).assignRadicals
    (Work.prepare x).relevantCycles i
  have eqK := Work.getElem!_eq_of_map_radicals
    (Work.getElem?_assignRadicals_atoms (Work.prepare x)) i
  have tK : ∀ {α : Type} (f : WAtom → α), (∀ y : WAtom, f { y with radicals := 0 } = f y) →
      f ((Work.prepare x).assignRadicals.atoms[i]! : WAtom) =
        f ((Work.prepare x).atoms[i]! : WAtom) := by
    intro α f h2
    rw [← h2, eqK, h2]
  have tr : ∀ {α : Type} (f : WAtom → α), (∀ y : WAtom, f { y with aromatic := false } = f y) →
      (∀ y : WAtom, f { y with radicals := 0 } = f y) →
      f (((Work.prepare x).assignRadicals.setAromaticity
        (Work.prepare x).relevantCycles).atoms[i]! : WAtom) =
        f ((Work.prepare x).atoms[i]! : WAtom) := by
    intro α f h1 h2
    rw [← h1, eqS, h1, tK f h2]
  rw [Loc.restore_congr (b := ((Work.prepare x).atoms[i]! : WAtom))
    (tr WAtom.z (fun _ ↦ rfl) (fun _ ↦ rfl)) (tr WAtom.charge (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.explicitHs (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.noImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.cachedImplicit (fun _ ↦ rfl) (fun _ ↦ rfl))
    (tr WAtom.adjustHs (fun _ ↦ rfl) (fun _ ↦ rfl))]
  cases har : (((Work.prepare x).assignRadicals.setAromaticity
      (Work.prepare x).relevantCycles).kindsAt i).any (· == .aromatic)
  · rw [Work.marks_eq_of_noArom hmarks har]
    exact Loc.restore_of_cached hadj hci
  -- marked aromatic
  by_cases hnI : ((Work.prepare x).atoms[i]! : WAtom).noImplicit = true
  · exact Loc.restore_of_noImplicit hnI (by rw [hci]; exact Loc.impl_of_noImplicit hnI _ _) _ _
  rw [hnz, Bool.not_eq_true, Bool.or_eq_false_iff] at hnI
  obtain ⟨hnone, hel⟩ := hnI
  rw [Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at hnone
  obtain ⟨e, he⟩ : ∃ e, (x.atom i').element = some e := by
    cases h : (x.atom i').element with
    | none => rw [h] at hel; cases hel
    | some e => exact ⟨e, rfl⟩
  obtain ⟨hcb, -⟩ := hbx i' hnone
  have hcb' := hcb
  simp only [Atom.canBeBare, hnone, he, Option.isNone_none, Bool.true_and,
    Bool.and_eq_true, beq_iff_eq] at hcb'
  obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
  have horg' : e ∈ Loc.organic := Loc.mem_organic e (by simpa using horg)
  have hz : ((Work.prepare x).atoms[i]! : WAtom).z = e.atomicNumber := by
    rw [hzz]; simp [Atom.atomicNumber, he]
  have hc0 : ((Work.prepare x).atoms[i]! : WAtom).charge = 0 := by rw [hcz]; exact hch0
  have he0 : ((Work.prepare x).atoms[i]! : WAtom).explicitHs = 0 := by rw [hez, hnone]; rfl
  have hn0 : ((Work.prepare x).atoms[i]! : WAtom).noImplicit = false := by
    rw [hnz, hnone, he]; rfl
  have hciT : ((Work.prepare x).atoms[i]! : WAtom).cachedImplicit =
      Loc.rdCount e.atomicNumber 0 (Loc.bhs ((Work.prepare x).kindsAt i)) := by
    rw [hci]
    apply Loc.impl_congr <;> assumption
  obtain ⟨hl2, hel', hcd, hdo, hd2, -⟩ := hperc har
  -- the radical-marked record is canonical
  have hKk : (Work.prepare x).assignRadicals.kindsAt i = (Work.prepare x).kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds]
  have hcx : Loc.Canonish ((Work.prepare x).assignRadicals.atoms[i]! : WAtom)
      ((Work.prepare x).kindsAt i) := by
    constructor
    · have hk := Work.cachedValence_sub_of_noArom
        (Work.noArom_freezeHs (Work.noArom_ofMolecule x hx.1 hx.2)) i
      rw [← hP, Work.cachedValence_eq_loc, Work.bondHalfSum_eq_loc, hKk] at hk
      omega
    · rw [Work.radicals_assignRadicals_eq _ (by omega), hrz, Work.bondHalfSum_eq_loc,
        tK WAtom.z (fun _ ↦ rfl), tK WAtom.charge (fun _ ↦ rfl),
        tK WAtom.explicitHs (fun _ ↦ rfl), tK WAtom.noImplicit (fun _ ↦ rfl)]
  have hcan : Loc.canonOf ((Work.prepare x).assignRadicals.atoms[i]! : WAtom)
      ((Work.prepare x).kindsAt i) =
      Loc.canon e.atomicNumber 0
        (Loc.rdCount e.atomicNumber 0 (Loc.bhs ((Work.prepare x).kindsAt i)))
        (Loc.bhs ((Work.prepare x).kindsAt i)) 0 false := by
    unfold Loc.canonOf
    rw [tK WAtom.z (fun _ ↦ rfl), tK WAtom.charge (fun _ ↦ rfl),
      tK WAtom.explicitHs (fun _ ↦ rfl), tK WAtom.noImplicit (fun _ ↦ rfl),
      tK WAtom.cachedImplicit (fun _ ↦ rfl), hz, hc0, he0, hn0, hciT, Nat.zero_add]
  obtain ⟨g1, g2, g3⟩ := Loc.canon_gates hcx
  rw [g1, hcan] at hel'
  rw [g2, hcan] at hcd
  rw [g3, hcan] at hdo
  have hkk3 : (Work.prepare x).kindsAt i ∈ Loc.nonArom 3 := Loc.mem_nonArom 3 _ hKany (by
    have := Work.elec_nonneg_length (by rwa [g1, hcan]); omega)
  exact Loc.restore_bare horg' hkk3 hmarks har hl2 hd2 hel' hcd hdo hz hc0 he0 hn0 hciT hadj

open Aromaticity in
/-- **The record `aromatize` caches at an atom of a Kekulé input**, when `cleanUp` does nothing:
the atom's element, charge and written hydrogens, no radicals, and implicit hydrogens RDKit's on
its bonds, for a total of the input's hydrogen count. -/
theorem IsKekule.prepare_record {x : Molecule n} (hx : x.IsKekule)
    (hq : (Work.ofMolecule x).freezeHs.cleanUp = (Work.ofMolecule x).freezeHs) (i : Fin n) :
    ((Work.prepare x).atoms[i.val]! : WAtom).z = (x.atom i).atomicNumber ∧
      ((Work.prepare x).atoms[i.val]! : WAtom).charge = (x.atom i).charge ∧
      ((Work.prepare x).atoms[i.val]! : WAtom).explicitHs = (x.atom i).explicitH.getD 0 ∧
      ((Work.prepare x).atoms[i.val]! : WAtom).noImplicit =
        ((x.atom i).explicitH.isSome || (x.atom i).element.isNone) ∧
      ((Work.prepare x).atoms[i.val]! : WAtom).radicals = 0 ∧
      ((Work.prepare x).atoms[i.val]! : WAtom).cachedImplicit =
        Loc.impl ((Work.prepare x).atoms[i.val]! : WAtom)
          (Loc.bhs ((Work.prepare x).kindsAt i.val)) false ∧
      (Work.prepare x).cachedTotalHs i.val = x.sanitizedH i := by
  have hP : Work.prepare x = (Work.ofMolecule x).freezeHs.cacheValences := by
    simp only [Work.prepare, hq]
  have hna := hx.noArom_prepare
  have hc := Work.freezeCache_atom x i
  have hfa := Work.freezeHs_ofMolecule_atom x i
  have hoa := Work.ofMolecule_atom x i
  have hka : (Work.ofMolecule x).freezeHs.kindsAt i.val = (Work.prepare x).kindsAt i.val := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hP, Work.cacheValences_bonds]
  have hko : (Work.ofMolecule x).kindsAt i.val = (Work.prepare x).kindsAt i.val := by
    rw [← hka]
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.freezeHs_bonds]
  have hKany : ((Work.prepare x).kindsAt i.val).any (· == .aromatic) = false := by
    rw [List.any_eq_false]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    have hlt := Work.lt_of_mem_bondsOf hk
    rw [getElem!_pos _ k hlt]
    simpa using hna.2 _ (Array.getElem_mem hlt)
  have harx : (x.atom i).aromatic = false := hx.1 i
  have harF : (Work.ofMolecule x).freezeHs.isAromaticAtom i.val = false := by
    rw [Work.isAromaticAtom_eq_loc, hka, hKany, hfa]
    simpa using harx
  have harO : (Work.ofMolecule x).isAromaticAtom i.val = false := by
    rw [Work.isAromaticAtom_eq_loc, hko, hKany, hoa]
    simpa using harx
  have hPi : ((Work.prepare x).atoms[i.val]! : WAtom) =
      ((Work.ofMolecule x).freezeHs.cacheValences.atoms[i.val]! : WAtom) := by rw [hP]
  have hci : ((Work.prepare x).atoms[i.val]! : WAtom).cachedImplicit =
      Loc.impl ((Work.prepare x).atoms[i.val]! : WAtom) (Loc.bhs ((Work.prepare x).kindsAt i.val))
        false := by
    rw [hPi, hc]
    dsimp only
    rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hka, harF]
    apply Loc.impl_congr <;> (rw [hfa]; try rfl)
  refine ⟨by rw [hPi, hc], by rw [hPi, hc], by rw [hPi, hc], by rw [hPi, hc], by rw [hPi, hc],
    hci, ?_⟩
  unfold Work.cachedTotalHs sanitizedH Work.totalHs
  rw [hci, hoa]
  simp only [Option.getD_none]
  rw [Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc, hko, harO, hoa, hPi, hc]
  exact congrArg _ (Loc.impl_congr rfl rfl rfl rfl _ _)

/-- Bracket normalization of an atom that can be written bare reads only what is not a hydrogen
field, and the total. -/
lemma normalizeBracket_congr_bare {O O' : Atom} (s : ℚ)
    (hb : ({ O with explicitH := none, implicitH := 0 } : Atom) =
      { O' with explicitH := none, implicitH := 0 })
    (ht : O.totalH = O'.totalH)
    (hcb : ({ O with explicitH := none, implicitH := 0 } : Atom).canBeBare = true) :
    normalizeBracket O s = normalizeBracket O' s := by
  have hcb' : ({ O' with explicitH := none, implicitH := 0 } : Atom).canBeBare = true := hb ▸ hcb
  unfold normalizeBracket
  rw [if_pos hcb, if_pos hcb', hb, ht]

/-- Two atoms equal but for their hydrogen fields are equal once those, the flag and the charge
are set alike. -/
lemma atom_eq_of_eraseH {a b : Atom}
    (h : ({ a with explicitH := none, implicitH := 0 } : Atom) =
      { b with explicitH := none, implicitH := 0 }) (ar : Bool) (c : ℤ) (e : Option ℕ) (k : ℕ) :
    ({ a with aromatic := ar, charge := c, explicitH := e, implicitH := k } : Atom) =
      { b with aromatic := ar, charge := c, explicitH := e, implicitH := k } := by
  cases a; cases b
  simp only [Atom.mk.injEq] at h ⊢
  simp_all

open Aromaticity in
/-- **Two inputs that differ only in how hydrogens are written give the same output** from final
working copies that agree (`OutAgree`), when every atom they write differently is written bare in
one of them, and could be. -/
lemma aromatizeOutput_hydrogenSpelling {x y : Molecule n} {Fx Fy : Work} (hO : OutAgree n Fx Fy)
    (hb : y.bonds = x.bonds) (hst : y.stereo = x.stereo)
    (hat : ∀ i, ({ y.atom i with explicitH := none, implicitH := 0 } : Atom) =
      { x.atom i with explicitH := none, implicitH := 0 })
    (hE : ∀ i, (y.atom i).explicitH = (x.atom i).explicitH ∨ (y.atom i).explicitH = none ∨
      (x.atom i).explicitH = none)
    (hbx : x.BareWritable) (hby : y.BareWritable)
    (hcx : ∀ i : Fin n, (Fx.atoms[i.val]! : WAtom).charge = (x.atom i).charge) :
    y.aromatizeOutput Fy = x.aromatizeOutput Fx := by
  have hbonds : withKinds y Fy = withKinds x Fx := by
    apply List.ext_getElem?
    intro j
    rw [getElem?_withKinds, getElem?_withKinds, hb, hO.bonds]
  refine Molecule.ext (Vector.ext fun j hj ↦ ?_) (by simp [hbonds]) (by simp [hst])
  change (y.aromatizeOutput Fy).atom ⟨j, hj⟩ = (x.aromatizeOutput Fx).atom ⟨j, hj⟩
  set i : Fin n := ⟨j, hj⟩
  have hsum : (y.aromatizeOutput Fy).bondOrderSum i = (x.aromatizeOutput Fx).bondOrderSum i := by
    simp only [bondOrderSum, bondsAt, aromatizeOutput_bonds, hbonds]
  rw [atom_aromatizeOutput, atom_aromatizeOutput, hsum]
  have hbase := atom_eq_of_eraseH (hat i)
  have hcy : (Fy.atoms[i.val]! : WAtom).charge = (y.atom i).charge := by
    rw [hO.charge i, hcx i]
    have := congrArg Atom.charge (hat i)
    simpa using this.symm
  have hbeq : ({ y.outAtom Fy i with explicitH := none, implicitH := 0 } : Atom) =
      { x.outAtom Fx i with explicitH := none, implicitH := 0 } := by
    simp only [Molecule.outAtom, hO.aromatic i, hO.charge i]
    exact hbase _ _ _ _
  rcases hE i with he | hn | hn
  · have : y.outAtom Fy i = x.outAtom Fx i := by
      simp only [Molecule.outAtom, hO.aromatic i, hO.charge i, hO.hs i, he]
      exact hbase _ _ _ _
    rw [this]
  · refine normalizeBracket_congr_bare _ hbeq (by rw [totalH_outAtom, totalH_outAtom, hO.hs i]) ?_
    have hcb := (hby i hn).1
    simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb ⊢
    simp only [Molecule.outAtom, hcy]
    exact ⟨⟨⟨⟨⟨rfl, hcb.1.1.1.1.2⟩, hcb.1.1.1.2⟩, hcb.1.1.2⟩, hcb.1.2⟩, hcb.2⟩
  · refine normalizeBracket_congr_bare _ hbeq (by rw [totalH_outAtom, totalH_outAtom, hO.hs i]) ?_
    rw [hbeq]
    have hcb := (hbx i hn).1
    simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb ⊢
    simp only [Molecule.outAtom, hcx]
    exact ⟨⟨⟨⟨⟨rfl, hcb.1.1.1.1.2⟩, hcb.1.1.1.2⟩, hcb.1.1.2⟩, hcb.1.2⟩, hcb.2⟩

set_option maxHeartbeats 2000000 in -- the two runs, field by field
open Aromaticity in
/-- **Two Kekulé inputs that differ only in how hydrogens are written aromatize alike**: the same
bonds and configurations, atoms equal but for their hydrogen fields, the same hydrogen counts,
every atom written bare writable so, and both runs keeping their charges.  Each atom's records in
the two runs are equal or swap written for implied hydrogens at RDKit's count
(`Work.readAlike_of_swap`), both copies get their hydrogens back (`IsKekule.hsRestored`), and
bracket normalization writes the outputs alike (`aromatizeOutput_hydrogenSpelling`). -/
theorem aromatize_of_hydrogenSpelling {x y ax ay : Molecule n} (hx : x.IsKekule)
    (hy : y.IsKekule) (hb : y.bonds = x.bonds) (hst : y.stereo = x.stereo)
    (hat : ∀ i, ({ y.atom i with explicitH := none, implicitH := 0 } : Atom) =
      { x.atom i with explicitH := none, implicitH := 0 })
    (hH : ∀ i, y.sanitizedH i = x.sanitizedH i) (hbx : x.BareWritable) (hby : y.BareWritable)
    (h : x.aromatize = .ok ax) (hc : x.ChargesKept ax)
    (h' : y.aromatize = .ok ay) (hc' : y.ChargesKept ay) : ay = ax := by
  obtain ⟨Kx, hKx, hax⟩ := aromatize_eq_ok.mp h
  rw [hx.kekulize_prepare] at hKx
  cases hKx
  obtain ⟨Ky, hKy, hay⟩ := aromatize_eq_ok.mp h'
  rw [hy.kekulize_prepare] at hKy
  cases hKy
  have hqx := hc.cleanUp_eq _ (.refl _) _ hax
  have hqy := hc'.cleanUp_eq _ (.refl _) _ hay
  have hPx : Work.prepare x = (Work.ofMolecule x).freezeHs.cacheValences := by
    simp only [Work.prepare, hqx]
  have hPy : Work.prepare y = (Work.ofMolecule y).freezeHs.cacheValences := by
    simp only [Work.prepare, hqy]
  have hbP : (Work.prepare y).bonds = (Work.prepare x).bonds := by
    rw [hPx, hPy, Work.cacheValences_bonds, Work.cacheValences_bonds, Work.freezeHs_bonds,
      Work.freezeHs_bonds]
    simp [Work.ofMolecule, hb]
  have hnx := size_prepare_atoms x
  have hny := size_prepare_atoms y
  have hR : (Work.prepare y).relevantCycles = (Work.prepare x).relevantCycles :=
    Work.relevantCycles_eq_of_ends (by rw [hnx, hny]) (by rw [hbP]) (fun k ↦ by rw [hbP])
  rw [hR] at hay
  have hrY : ∀ i < n, Work.HsRestored ((Work.prepare y).assignRadicals.setAromaticity
      (Work.prepare y).relevantCycles) i := fun i hi ↦ hy.hsRestored hby hqy hi
  rw [hR] at hrY
  set R := (Work.prepare x).relevantCycles with hRdef
  set Px := Work.prepare x with hPxdef
  set Py := Work.prepare y with hPydef
  -- atom by atom
  have hel : ∀ i, (y.atom i).element = (x.atom i).element := fun i ↦ by
    have := congrArg Atom.element (hat i); simpa using this
  have hch : ∀ i, (y.atom i).charge = (x.atom i).charge := fun i ↦ by
    have := congrArg Atom.charge (hat i); simpa using this
  have hkP : ∀ j, Py.kindsAt j = Px.kindsAt j := fun j ↦ by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hbP]
  have hzz : ∀ j, (Py.atoms[j]! : WAtom).z = (Px.atoms[j]! : WAtom).z := fun j ↦ by
    by_cases hj : j < n
    · rw [(hy.prepare_record hqy ⟨j, hj⟩).1, (hx.prepare_record hqx ⟨j, hj⟩).1]
      simp [Atom.atomicNumber, hel ⟨j, hj⟩]
    · rw [getElem!_neg _ j (by omega), getElem!_neg _ j (by omega)]
  have hcc : ∀ j, (Py.atoms[j]! : WAtom).charge = (Px.atoms[j]! : WAtom).charge := fun j ↦ by
    by_cases hj : j < n
    · rw [(hy.prepare_record hqy ⟨j, hj⟩).2.1, (hx.prepare_record hqx ⟨j, hj⟩).2.1, hch]
    · rw [getElem!_neg _ j (by omega), getElem!_neg _ j (by omega)]
  have htot : ∀ j, Py.cachedTotalHs j = Px.cachedTotalHs j := fun j ↦ by
    by_cases hj : j < n
    · rw [(hy.prepare_record hqy ⟨j, hj⟩).2.2.2.2.2.2, (hx.prepare_record hqx ⟨j, hj⟩).2.2.2.2.2.2,
        hH]
    · simp only [Work.cachedTotalHs]
      rw [getElem!_neg _ j (by omega), getElem!_neg _ j (by omega)]
  have hr0 : ∀ j, (Px.atoms[j]! : WAtom).radicals = 0 := fun j ↦ by
    by_cases hj : j < n
    · exact (hx.prepare_record hqx ⟨j, hj⟩).2.2.2.2.1
    · rw [getElem!_neg _ j (by omega)]; rfl
  have hr0' : ∀ j, (Py.atoms[j]! : WAtom).radicals = 0 := fun j ↦ by
    by_cases hj : j < n
    · exact (hy.prepare_record hqy ⟨j, hj⟩).2.2.2.2.1
    · rw [getElem!_neg _ j (by omega)]; rfl
  -- written alike, or swapped at RDKit's count
  have hcls : ∀ i : Fin n,
      ((Py.atoms[i.val]! : WAtom).explicitHs = (Px.atoms[i.val]! : WAtom).explicitHs ∧
        (Py.atoms[i.val]! : WAtom).noImplicit = (Px.atoms[i.val]! : WAtom).noImplicit) ∨
      ∃ e ∈ Loc.organic, (Px.atoms[i.val]! : WAtom).z = e.atomicNumber ∧
        (Px.atoms[i.val]! : WAtom).charge = 0 ∧
        Px.cachedTotalHs i.val = Loc.rdCount e.atomicNumber 0 (Loc.bhs (Px.kindsAt i.val)) ∧
        (((Px.atoms[i.val]! : WAtom).explicitHs = 0 ∧
            (Px.atoms[i.val]! : WAtom).noImplicit = false ∧
            (Py.atoms[i.val]! : WAtom).explicitHs = Px.cachedTotalHs i.val ∧
            (Py.atoms[i.val]! : WAtom).noImplicit = true) ∨
          ((Py.atoms[i.val]! : WAtom).explicitHs = 0 ∧
            (Py.atoms[i.val]! : WAtom).noImplicit = false ∧
            (Px.atoms[i.val]! : WAtom).explicitHs = Px.cachedTotalHs i.val ∧
            (Px.atoms[i.val]! : WAtom).noImplicit = true)) := by
    intro i
    obtain ⟨xz, xc, xe, xn, -, xci, -⟩ := hx.prepare_record hqx i
    obtain ⟨-, yc, ye, yn, -, yci, -⟩ := hy.prepare_record hqy i
    have hT := htot i.val
    have hTx : Px.cachedTotalHs i.val = (Px.atoms[i.val]! : WAtom).explicitHs +
        (Px.atoms[i.val]! : WAtom).cachedImplicit := rfl
    have hTy : Py.cachedTotalHs i.val = (Py.atoms[i.val]! : WAtom).explicitHs +
        (Py.atoms[i.val]! : WAtom).cachedImplicit := rfl
    rw [hkP] at yci
    cases hxe : (x.atom i).explicitH with
    | some a =>
      have hxn : (Px.atoms[i.val]! : WAtom).noImplicit = true := by rw [xn, hxe]; rfl
      have hxci : (Px.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
        rw [xci]; exact Loc.impl_of_noImplicit hxn _ _
      cases hye : (y.atom i).explicitH with
      | some b =>
        have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hye]; rfl
        have hyci : (Py.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
          rw [yci]; exact Loc.impl_of_noImplicit hyn _ _
        left
        refine ⟨?_, by rw [hxn, hyn]⟩
        omega
      | none =>
        cases hme : (y.atom i).element with
        | none =>
          have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hye, hme]; rfl
          have hyci : (Py.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
            rw [yci]; exact Loc.impl_of_noImplicit hyn _ _
          left
          refine ⟨?_, by rw [hxn, hyn]⟩
          rw [ye, hye]
          simp only [Option.getD_none]
          rw [ye, hye] at hTy
          simp only [Option.getD_none] at hTy
          omega
        | some e =>
          right
          obtain ⟨hcb, -⟩ := hby i hye
          have hcb' := hcb
          simp only [Atom.canBeBare, hye, hme, Option.isNone_none, Bool.true_and,
            Bool.and_eq_true, beq_iff_eq] at hcb'
          obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
          have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = false := by rw [yn, hye, hme]; rfl
          have hye0 : (Py.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [ye, hye]; rfl
          have hz : (Px.atoms[i.val]! : WAtom).z = e.atomicNumber := by
            rw [xz]; simp [Atom.atomicNumber, ← hel i, hme]
          have hc0 : (Px.atoms[i.val]! : WAtom).charge = 0 := by rw [xc, ← hch]; exact hch0
          refine ⟨e, Loc.mem_organic e (by simpa using horg), hz, hc0, ?_, .inr ⟨hye0, hyn, ?_,
            hxn⟩⟩
          · rw [← hT, hTy, hye0, Nat.zero_add, yci]
            apply Loc.impl_congr
            · rw [hzz, hz]
            · rw [hcc, hc0]
            · exact hye0
            · exact hyn
          · rw [hxci] at hTx
            omega
    | none =>
      cases hme : (x.atom i).element with
      | none =>
        have hxn : (Px.atoms[i.val]! : WAtom).noImplicit = true := by rw [xn, hxe, hme]; rfl
        have hxci : (Px.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
          rw [xci]; exact Loc.impl_of_noImplicit hxn _ _
        have hxe0 : (Px.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [xe, hxe]; rfl
        have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = true := by
          rw [yn, hel, hme]; simp
        have hyci : (Py.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
          rw [yci]; exact Loc.impl_of_noImplicit hyn _ _
        left
        refine ⟨?_, by rw [hxn, hyn]⟩
        omega
      | some e =>
        obtain ⟨hcb, -⟩ := hbx i hxe
        have hcb' := hcb
        simp only [Atom.canBeBare, hxe, hme, Option.isNone_none, Bool.true_and,
          Bool.and_eq_true, beq_iff_eq] at hcb'
        obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
        have hxn : (Px.atoms[i.val]! : WAtom).noImplicit = false := by rw [xn, hxe, hme]; rfl
        have hxe0 : (Px.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [xe, hxe]; rfl
        have hz : (Px.atoms[i.val]! : WAtom).z = e.atomicNumber := by
          rw [xz]; simp [Atom.atomicNumber, hme]
        have hc0 : (Px.atoms[i.val]! : WAtom).charge = 0 := by rw [xc]; exact hch0
        have hTr : Px.cachedTotalHs i.val =
            Loc.rdCount e.atomicNumber 0 (Loc.bhs (Px.kindsAt i.val)) := by
          rw [hTx, hxe0, Nat.zero_add, xci]
          apply Loc.impl_congr <;> assumption
        cases hye : (y.atom i).explicitH with
        | none =>
          left
          refine ⟨by rw [ye, xe, hye, hxe], by rw [yn, xn, hye, hxe, hel]⟩
        | some b =>
          right
          have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hye]; rfl
          have hyci : (Py.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
            rw [yci]; exact Loc.impl_of_noImplicit hyn _ _
          refine ⟨e, Loc.mem_organic e (by simpa using horg), hz, hc0, hTr,
            .inl ⟨hxe0, hxn, ?_, hyn⟩⟩
          omega
  -- perception reads the two copies alike
  have hnaF := Work.noArom_freezeHs (Work.noArom_ofMolecule x hx.1 hx.2)
  have hnaF' := Work.noArom_freezeHs (Work.noArom_ofMolecule y hy.1 hy.2)
  have hkek : ∀ j, (Px.assignRadicals.cachedValence j : ℤ) -
      (Px.assignRadicals.atoms[j]! : WAtom).explicitHs = ((Px.bondHalfSum j / 2 : ℕ) : ℤ) :=
    fun j ↦ by
      have hk := Work.cachedValence_sub_of_noArom hnaF j
      rw [← hPx, Work.bondHalfSum_congr (Work.assignRadicals_bonds _)] at hk
      exact hk
  have hkek' : ∀ j, (Py.assignRadicals.cachedValence j : ℤ) -
      (Py.assignRadicals.atoms[j]! : WAtom).explicitHs = ((Py.bondHalfSum j / 2 : ℕ) : ℤ) :=
    fun j ↦ by
      have hk := Work.cachedValence_sub_of_noArom hnaF' j
      rw [← hPy, Work.bondHalfSum_congr (Work.assignRadicals_bonds _)] at hk
      exact hk
  have hbh : ∀ j, Py.bondHalfSum j = Px.bondHalfSum j := fun j ↦ by
    rw [Work.bondHalfSum_congr hbP]
  have hbR : Py.assignRadicals.bonds = Px.assignRadicals.bonds := by
    rw [Work.assignRadicals_bonds, Work.assignRadicals_bonds, hbP]
  have hzR : ∀ j, (Py.assignRadicals.atoms[j]! : WAtom).z =
      (Px.assignRadicals.atoms[j]! : WAtom).z := fun j ↦ by
    have e1 := congrArg WAtom.z
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Px) j)
    have e2 := congrArg WAtom.z
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Py) j)
    simp only at e1 e2
    rw [e1, e2, hzz]
  have hcR : ∀ j, (Py.assignRadicals.atoms[j]! : WAtom).charge =
      (Px.assignRadicals.atoms[j]! : WAtom).charge := fun j ↦ by
    have e1 := congrArg WAtom.charge
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Px) j)
    have e2 := congrArg WAtom.charge
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Py) j)
    simp only at e1 e2
    rw [e1, e2, hcc]
  have hRA : ∀ ring ∈ R.toList, ∀ i ∈ ring, ∀ (rbs : List ℕ) (big : Bool),
      Loc.readAlike (Px.assignRadicals.atoms[i]! : WAtom) (Py.assignRadicals.atoms[i]! : WAtom)
        (Px.assignRadicals.kindsAt i) (Px.assignRadicals.whoS rbs i)
        (Px.assignRadicals.pullsB rbs i) (Px.assignRadicals.ringMultB rbs i) big = true := by
    intro ring hring i hir rbs big
    by_cases hi : i < n
    · have hlen : 2 ≤ (Px.kindsAt i).length := by
        have hIs := Work.isRing_of_mem_relevantCycles Px (by simpa using hring)
        obtain ⟨k₁, k₂, hne, -, -, hk₁, hk₂⟩ := hIs.two_bonds hir
        simp only [Work.kindsAt, List.length_map]
        exact Work.two_le_length_of_ne hne hk₁ hk₂
      have hnoar : (Px.kindsAt i).any (· == .aromatic) = false := by
        rw [List.any_eq_false]
        intro y' hy'
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy'
        have hlt := Work.lt_of_mem_bondsOf hk
        rw [getElem!_pos _ k hlt]
        simpa using hx.noArom_prepare.2 _ (Array.getElem_mem hlt)
      exact Work.readAlike_of_swap hbP (by omega) (by omega) hlen hnoar (hzz i) (hcc i) (htot i)
        (hkek i) (hkek' i) (hr0 i) (hr0' i) (hcls ⟨i, hi⟩) rbs big
    · rw [getElem!_neg _ i (by rw [Work.size_atoms_assignRadicals]; omega),
        getElem!_neg _ i (by rw [Work.size_atoms_assignRadicals]; omega)]
      exact Loc.readAlike_self _ _ _ _ _ _
  have beq : ∀ d d' : Donor, (d == d') = true → d = d' := by
    intro d d' h
    cases d <;> cases d' <;> first | rfl | exact absurd h (by decide)
  have loc : ∀ rbs i len, Py.assignRadicals.ringDonor rbs len i =
        Loc.ringDonorL (Py.assignRadicals.atoms[i]! : WAtom) (Px.assignRadicals.kindsAt i)
          (Px.assignRadicals.whoS rbs i) (Px.assignRadicals.pullsB rbs i)
          (Px.assignRadicals.ringMultB rbs i) (decide (9 ≤ len)) ∧
      ∀ d, Py.assignRadicals.isAromaticCandidate i d =
        Loc.candD (Py.assignRadicals.atoms[i]! : WAtom) (Px.assignRadicals.kindsAt i) d := by
    intro rbs i len
    have hk : Py.assignRadicals.kindsAt i = Px.assignRadicals.kindsAt i := by
      simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hbR]
    refine ⟨?_, fun d ↦ ?_⟩
    · rw [Work.ringDonor_eq_loc, hk, Work.whoS_congr hbR, Work.pullsB_congr hbR hzR,
        Work.ringMultB_congr hbR]
    · rw [Work.isAromaticCandidate_eq_candD, hk]
  set rbs0 := (R.toList.flatMap Px.assignRadicals.ringBonds).eraseDups with hrbs0
  have hp : Work.PerceiveAgree R Px.assignRadicals Py.assignRadicals := by
    refine ⟨hbR, by rw [Work.size_atoms_assignRadicals, Work.size_atoms_assignRadicals, hnx, hny],
      hzR, hcR, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_, fun ring hring i hir len ↦ ?_,
      fun ring hring i hir len hcd ↦ ?_⟩
    · rw [Work.cachedTotalHs_assignRadicals, Work.cachedTotalHs_assignRadicals, htot]
    · rw [hkek, hkek', hbh]
    · rw [Work.bondHalfSum_congr (Work.assignRadicals_bonds _)]; exact hkek j
    · rw [Work.assignRadicals_bonds]
      exact hx.noArom_prepare.2
    · have h := hRA ring hring i hir
        rbs0 (decide (9 ≤ len))
      rw [(loc rbs0 i len).2, (loc rbs0 i len).1, Work.isAromaticCandidate_eq_candD,
        Work.ringDonor_eq_loc]
      unfold Loc.readAlike at h
      rw [Bool.and_eq_true] at h
      exact (beq_iff_eq.1 h.1).symm
    · have h := hRA ring hring i hir
        rbs0 (decide (9 ≤ len))
      rw [Work.isAromaticCandidate_eq_candD, Work.ringDonor_eq_loc] at hcd
      rw [(loc rbs0 i len).1, Work.ringDonor_eq_loc]
      unfold Loc.readAlike at h
      rw [Bool.and_eq_true, hcd, Bool.not_true, Bool.false_or] at h
      exact (beq _ _ h.2).symm
  have hm : Work.SameMarks Px.assignRadicals Py.assignRadicals := by
    refine ⟨hbR, fun j ↦ ?_⟩
    rw [Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl),
      Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl)]
    by_cases hj : j < n
    · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      rw [hy.noArom_prepare.1 _ (Array.getElem_mem _), hx.noArom_prepare.1 _ (Array.getElem_mem _)]
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  have hO := outAgree_finish hnx hp hm (fun i hi ↦ hx.hsRestored hbx hqx hi) hrY
  -- the outputs
  subst hax hay
  refine aromatizeOutput_hydrogenSpelling hO hb hst hat ?_ hbx hby ?_
  · intro i
    cases hxe : (x.atom i).explicitH with
    | none => exact .inr (.inr rfl)
    | some a =>
      cases hye : (y.atom i).explicitH with
      | none => exact .inr (.inl rfl)
      | some b =>
        left
        obtain ⟨-, -, xe, xn, -, xci, xT⟩ := hx.prepare_record hqx i
        obtain ⟨-, -, ye, yn, -, yci, yT⟩ := hy.prepare_record hqy i
        have hxn : (Px.atoms[i.val]! : WAtom).noImplicit = true := by rw [xn, hxe]; rfl
        have hyn : (Py.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hye]; rfl
        have h1 : Px.cachedTotalHs i.val = a := by
          change (Px.atoms[i.val]! : WAtom).explicitHs + (Px.atoms[i.val]! : WAtom).cachedImplicit
            = a
          rw [xci, Loc.impl_of_noImplicit hxn, xe, hxe]; rfl
        have h2 : Py.cachedTotalHs i.val = b := by
          change (Py.atoms[i.val]! : WAtom).explicitHs + (Py.atoms[i.val]! : WAtom).cachedImplicit
            = b
          rw [yci, Loc.impl_of_noImplicit hyn, ye, hye]; rfl
        rw [← h1, ← h2, htot]
  · intro i
    have := hc i
    rw [atom_aromatizeOutput, charge_normalizeBracket] at this
    simpa [Molecule.outAtom] using this

open Aromaticity in
/-- **When the charges are kept, `cleanUp` did nothing**, from the kekulized copy: kekulization
keeps the atoms and their charges. -/
lemma ChargesKept.cleanUp_eq_of_kekulize {m a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hc : m.ChargesKept a) :
    (Work.ofMolecule m).freezeHs.cleanUp = (Work.ofMolecule m).freezeHs := by
  have hKR := Work.kekulize_kindsRel hK
  have hF := K.afterRel_finish (Work.prepare m).relevantCycles
  apply Work.cleanUp_eq_self_of_charge
  intro j
  by_cases hj : j < n
  · have hsize : j < (K.finish (Work.prepare m).relevantCycles).atoms.size := by
      rw [hF.atoms_size, hKR.atoms_size]
      simp [Work.prepare, (Work.cleanRel_cleanUp _).atoms_size, hj]
    have h1 : some ((m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles)).atom
        ⟨j, hj⟩).charge = (Work.ofMolecule m).freezeHs.cleanUp.charge? j := by
      rw [charge_aromatizeOutput, ← Work.charge?_eq_of_lt _ hsize, hF.charge, hKR.charge]
      simp [Work.prepare]
    rw [ha, hc ⟨j, hj⟩] at h1
    rw [← h1, Work.charge?_freezeHs, Work.charge?_ofMolecule m ⟨j, hj⟩]
  · have h2 : ¬ j < (Work.ofMolecule m).freezeHs.cleanUp.atoms.size := by
      simpa [(Work.cleanRel_cleanUp _).atoms_size] using hj
    have h3 : ¬ j < (Work.ofMolecule m).freezeHs.atoms.size := by simpa using hj
    rw [← Work.charge?_isSome_iff, Bool.not_eq_true, Option.isSome_eq_false_iff,
      Option.isNone_iff_eq_none] at h2 h3
    rw [h2, h3]

open Aromaticity in
/-- **The kekulized copy with a spelling's bonds is a bond swap of it** (`Work.Swapped`) over the
bonds `m` writes aromatic, when the two give every atom the same bond-order sum. -/
lemma swapped_spelling {m k a : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hc : m.ChargesKept a) (hw : m.AromaticWritten) (hs : k.IsKekuleSpellingOf m)
    (hqk : (Work.ofMolecule k).freezeHs.cleanUp = (Work.ofMolecule k).freezeHs)
    (hsum : ∀ i, (Work.prepare k).bondHalfSum i = K.bondHalfSum i) :
    Work.Swapped (fun j ↦ (m.bonds[j]?.map (·.kind == .aromatic)).getD false) K
      { K with bonds := (Work.prepare k).bonds } := by
  have hqm := hc.cleanUp_eq_of_kekulize hK ha
  have hPm : Work.prepare m = (Work.ofMolecule m).freezeHs.cacheValences := by
    simp only [Work.prepare, hqm]
  have hPk : Work.prepare k = (Work.ofMolecule k).freezeHs.cacheValences := by
    simp only [Work.prepare, hqk]
  have hbPm : (Work.prepare m).bonds = (Work.ofMolecule m).bonds := by
    rw [hPm, Work.cacheValences_bonds, Work.freezeHs_bonds]
  have hbPk : (Work.prepare k).bonds = (Work.ofMolecule k).bonds := by
    rw [hPk, Work.cacheValences_bonds, Work.freezeHs_bonds]
  have hKR := Work.kekulize_kindsRel hK
  have hlen : k.bonds.length = m.bonds.length := hs.bonds.length_eq
  have endsK : ∀ j, K.bonds[j]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      m.bonds[j]?.map (fun b : Bond n ↦ (b.src.val, b.dst.val)) := fun j ↦ by
    have := congrArg (Option.map fun b : WBond ↦ (b.src, b.dst)) (hKR.bonds j)
    simp only [Option.map_map, Function.comp_def] at this
    rw [this, hbPm, Work.getElem?_ofMolecule_bonds, Option.map_map]
    rfl
  have endsk : ∀ j, (Work.prepare k).bonds[j]?.map (fun b : WBond ↦ (b.src, b.dst)) =
      m.bonds[j]?.map (fun b : Bond n ↦ (b.src.val, b.dst.val)) := fun j ↦ by
    rw [hbPk, Work.getElem?_ofMolecule_bonds, Option.map_map]
    rcases hs.bonds.getElem? j with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [h1, h2]; rfl
    · rw [hx, hy]
      simp [hxy.1, hxy.2.1]
  obtain ⟨D, hkind, -, -, -⟩ := Work.kekulize_prepare_correct hw.1 hw.2 hK
  refine ⟨rfl, ?_, fun j ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, fun i ↦ ?_⟩
  · change (Work.prepare k).bonds.size = K.bonds.size
    rw [size_kekulized hK, hbPk]
    simp [Work.ofMolecule, hlen]
  · change (Work.prepare k).bonds[j]?.map _ = _
    rw [endsk, endsK]
  · change (Work.prepare k).kind? j = K.kind? j
    have hnot : (Work.prepare m).kind? j ≠ some .aromatic := by
      rw [Work.kind?, hbPm, Work.getElem?_ofMolecule_bonds, Option.map_map]
      intro e
      cases hmj : m.bonds[j]? with
      | none => rw [hmj] at e; cases e
      | some b =>
        rw [hmj] at e hj
        simp only [Option.map_some, Option.getD_some, beq_eq_false_iff_ne, ne_eq] at hj
        simp only [Option.map_some, Function.comp_apply, Option.some.injEq] at e
        exact hj e
    rw [Work.kekulize_kind_of_not_aromatic hK hnot, Work.kind?, Work.kind?, hbPk, hbPm,
      Work.getElem?_ofMolecule_bonds, Work.getElem?_ofMolecule_bonds, Option.map_map,
      Option.map_map]
    rcases hs.bonds.getElem? j with ⟨h1, h2⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [h1, h2]
    · rw [hx, hy]
      rw [hy] at hj
      simp only [Option.map_some, Option.getD_some, beq_eq_false_iff_ne, ne_eq] at hj
      obtain ⟨-, -, -, hif⟩ := hxy
      rw [if_neg hj] at hif
      simp [hif]
  · cases hmj : m.bonds[j]? with
    | none => rw [hmj] at hj; cases hj
    | some b =>
      rw [hmj] at hj
      simp only [Option.map_some, Option.getD_some, beq_iff_eq] at hj
      have hjl : j < m.bonds.length := (List.getElem?_eq_some_iff.mp hmj).1
      have hjK : j < K.bonds.size := by rw [size_kekulized hK]; exact hjl
      have hjP : j < (Work.prepare m).bonds.size := by
        rw [hbPm]; simpa [Work.ofMolecule] using hjl
      have hwa : (Work.prepare m).kekWa j = true := by
        rw [Work.kekWa_iff]
        refine ⟨hjP, ?_⟩
        rw [getElem!_pos _ j hjP]
        have e := Work.getElem?_ofMolecule_bonds m j
        rw [← hbPm, hmj, Array.getElem?_eq_getElem hjP] at e
        simp only [Option.map_some, Option.some.injEq] at e
        rw [e, hj]
      refine ⟨⟨(K.bonds[j]! : WBond).kind, ?_, ?_⟩, ?_⟩
      · rw [Work.kind?, Array.getElem?_eq_getElem hjK, ← getElem!_pos K.bonds j hjK]; rfl
      · rw [hkind j, hwa]
        split
        · exact .inr rfl
        · exact .inl rfl
      · rcases hs.bonds.getElem? j with ⟨-, h2⟩ | ⟨x, y, hx, hy, hxy⟩
        · rw [h2] at hmj; cases hmj
        · rw [hmj] at hy
          cases hy
          obtain ⟨-, -, -, hif⟩ := hxy
          rw [if_pos hj] at hif
          refine ⟨x.kind, ?_, hif⟩
          change (Work.prepare k).kind? j = _
          rw [Work.kind?, hbPk, Work.getElem?_ofMolecule_bonds, hx]
          rfl
  · change Work.bondHalfSum { K with bonds := (Work.prepare k).bonds } i = _
    rw [← hsum i]
    rfl

/-- Two atoms equal but for the aromatic flag and the hydrogen fields are equal once those and the
charge are set alike. -/
lemma atom_eq_of_eraseAH {a b : Atom}
    (h : ({ a with aromatic := false, explicitH := none, implicitH := 0 } : Atom) =
      { b with aromatic := false, explicitH := none, implicitH := 0 }) (ar : Bool) (c : ℤ)
    (e : Option ℕ) (k : ℕ) :
    ({ a with aromatic := ar, charge := c, explicitH := e, implicitH := k } : Atom) =
      { b with aromatic := ar, charge := c, explicitH := e, implicitH := k } := by
  cases a; cases b
  simp only [Atom.mk.injEq] at h ⊢
  simp_all

open Aromaticity in
/-- **Two inputs spelled differently give the same output** from final working copies that agree
(`OutAgree`): the same skeleton (the bond kinds and aromatic flags are the working copy's), atoms
equal but for the aromatic flag and the hydrogen fields, and every atom whose hydrogens the two
write differently written bare in one of them, and writable so. -/
lemma aromatizeOutput_respell {x y : Molecule n} {Fx Fy : Work} (hO : OutAgree n Fx Fy)
    (hFs : Fx.bonds.size = x.bonds.length)
    (hb : List.Forall₂ (fun b b' : Bond n ↦ b.src = b'.src ∧ b.dst = b'.dst ∧ b.dir = b'.dir)
      y.bonds x.bonds)
    (hst : y.stereo = x.stereo)
    (hat : ∀ i, ({ y.atom i with aromatic := false, explicitH := none, implicitH := 0 } : Atom) =
      { x.atom i with aromatic := false, explicitH := none, implicitH := 0 })
    (hE : ∀ i, (y.atom i).explicitH = (x.atom i).explicitH ∨ (y.atom i).explicitH = none ∨
      (x.atom i).explicitH = none)
    (hbx : x.BareWritable) (hby : y.BareWritable)
    (hcx : ∀ i : Fin n, (Fx.atoms[i.val]! : WAtom).charge = (x.atom i).charge) :
    y.aromatizeOutput Fy = x.aromatizeOutput Fx := by
  have hbonds : withKinds y Fy = withKinds x Fx := by
    apply List.ext_getElem?
    intro j
    rw [getElem?_withKinds, getElem?_withKinds, hO.bonds]
    rcases hb.getElem? j with ⟨h1, h2⟩ | ⟨u, v, hu, hv, huv⟩
    · rw [h1, h2]
    · rw [hu, hv]
      have hjl : j < Fx.bonds.size := hFs ▸ (List.getElem?_eq_some_iff.mp hv).1
      simp only [Option.map_some, Array.getElem?_eq_getElem hjl, Option.getD_some,
        Option.some.injEq]
      obtain ⟨s, d, kd, dir, ne⟩ := u
      obtain ⟨s', d', kd', dir', ne'⟩ := v
      simp only at huv
      obtain ⟨rfl, rfl, rfl⟩ := huv
      rfl
  refine Molecule.ext (Vector.ext fun j hj ↦ ?_) (by simp [hbonds]) (by simp [hst])
  change (y.aromatizeOutput Fy).atom ⟨j, hj⟩ = (x.aromatizeOutput Fx).atom ⟨j, hj⟩
  set i : Fin n := ⟨j, hj⟩
  have hsum : (y.aromatizeOutput Fy).bondOrderSum i = (x.aromatizeOutput Fx).bondOrderSum i := by
    simp only [bondOrderSum, bondsAt, aromatizeOutput_bonds, hbonds]
  rw [atom_aromatizeOutput, atom_aromatizeOutput, hsum]
  have hbase := atom_eq_of_eraseAH (hat i)
  have hcy : (Fy.atoms[i.val]! : WAtom).charge = (y.atom i).charge := by
    rw [hO.charge i, hcx i]
    have := congrArg Atom.charge (hat i)
    simpa using this.symm
  have hbeq : ({ y.outAtom Fy i with explicitH := none, implicitH := 0 } : Atom) =
      { x.outAtom Fx i with explicitH := none, implicitH := 0 } := by
    simp only [Molecule.outAtom, hO.aromatic i, hO.charge i]
    exact hbase _ _ _ _
  rcases hE i with he | hn | hn
  · have : y.outAtom Fy i = x.outAtom Fx i := by
      simp only [Molecule.outAtom, hO.aromatic i, hO.charge i, hO.hs i, he]
      exact hbase _ _ _ _
    rw [this]
  · refine normalizeBracket_congr_bare _ hbeq (by rw [totalH_outAtom, totalH_outAtom, hO.hs i]) ?_
    have hcb := (hby i hn).1
    simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb ⊢
    simp only [Molecule.outAtom, hcy]
    exact ⟨⟨⟨⟨⟨rfl, hcb.1.1.1.1.2⟩, hcb.1.1.1.2⟩, hcb.1.1.2⟩, hcb.1.2⟩, hcb.2⟩
  · refine normalizeBracket_congr_bare _ hbeq (by rw [totalH_outAtom, totalH_outAtom, hO.hs i]) ?_
    rw [hbeq]
    have hcb := (hbx i hn).1
    simp only [Atom.canBeBare, Bool.and_eq_true, beq_iff_eq] at hcb ⊢
    simp only [Molecule.outAtom, hcx]
    exact ⟨⟨⟨⟨⟨rfl, hcb.1.1.1.1.2⟩, hcb.1.1.1.2⟩, hcb.1.1.2⟩, hcb.1.2⟩, hcb.2⟩

open Aromaticity in
/-- An input's hydrogen count: its written hydrogens and RDKit's implicit count. -/
lemma sanitizedH_eq (x : Molecule n) (i : Fin n) :
    x.sanitizedH i = (x.atom i).explicitH.getD 0 + (Work.ofMolecule x).implicitHs i := by
  unfold sanitizedH Work.totalHs
  rw [Work.ofMolecule_atom]
  rfl

open Aromaticity in
/-- `freezeHs` changes no valence and no implicit count. -/
lemma freezeHs_explicitValence_implicitHs (x : Molecule n) (i : Fin n) :
    (Work.ofMolecule x).freezeHs.explicitValence i = (Work.ofMolecule x).explicitValence i ∧
      (Work.ofMolecule x).freezeHs.implicitHs i = (Work.ofMolecule x).implicitHs i := by
  have hfa := Work.freezeHs_ofMolecule_atom x i
  have hoa := Work.ofMolecule_atom x i
  have hk : (Work.ofMolecule x).freezeHs.kindsAt i = (Work.ofMolecule x).kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.freezeHs_bonds]
  have har : (Work.ofMolecule x).freezeHs.isAromaticAtom i =
      (Work.ofMolecule x).isAromaticAtom i := by
    rw [Work.isAromaticAtom_eq_loc, Work.isAromaticAtom_eq_loc, hk, hfa, hoa]
  constructor
  · rw [Work.explicitValence_eq_loc, Work.explicitValence_eq_loc, Work.bondHalfSum_eq_loc,
      Work.bondHalfSum_eq_loc, hk, har, hfa, hoa]
    exact Loc.ev_congr rfl rfl rfl _ _
  · rw [Work.implicitHs_eq_loc, Work.implicitHs_eq_loc, Work.bondHalfSum_eq_loc,
      Work.bondHalfSum_eq_loc, hk, har, hfa, hoa]
    exact Loc.impl_congr rfl rfl rfl rfl _ _

open Aromaticity in
/-- A Kekulé input's valence is its bond-order sum and its written hydrogens. -/
lemma IsKekule.explicitValence {x : Molecule n} (hx : x.IsKekule) (i : Fin n) :
    (Work.ofMolecule x).explicitValence i =
      (x.atom i).explicitH.getD 0 + (Work.ofMolecule x).bondHalfSum i / 2 := by
  have hna := Work.noArom_ofMolecule x hx.1 hx.2
  have hk : ((Work.ofMolecule x).kindsAt i).any (· == .aromatic) = false := by
    rw [List.any_eq_false]
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    have hlt := Work.lt_of_mem_bondsOf hk
    rw [getElem!_pos _ k hlt]
    simpa using hna.2 _ (Array.getElem_mem hlt)
  have har : (Work.ofMolecule x).isAromaticAtom i = false := by
    rw [Work.isAromaticAtom_eq_loc, hk, Work.ofMolecule_atom]
    simpa using hx.1 i
  have he := Work.bhs_even_of_noArom hk
  have hev : ∀ (a : WAtom) (h : ℕ), Loc.ev a h false = (2 * a.explicitHs + h + 1) / 2 := by
    intro a h
    unfold Loc.ev
    simp only [Id.run, Bool.and_false]
    split <;> rfl
  rw [Work.explicitValence_eq_loc, har, Work.bondHalfSum_eq_loc, hev, Work.ofMolecule_atom]
  simp only
  omega

set_option maxHeartbeats 4000000 in -- the two runs, atom by atom
open Aromaticity in
/-- **The run on `m` and the run on a Kekulé spelling of it give the same output**, when
kekulization gives every atom the bond-order sum the spelling does and the hydrogen count `m`
has.  The kekulized copy with the spelling's bonds is a bond swap of it, perceived alike
(`swapped_spelling`, `Work.Swapped.finish_eq`); its records and the spelling's copy's are equal
or swap written for implied hydrogens at RDKit's count (`Work.readAlike_of_swap`); both get
their hydrogens back; and the outputs are written alike (`aromatizeOutput_respell`). -/
theorem aromatize_of_spelling_core {m k a a' : Molecule n} {K : Work}
    (hK : (Work.prepare m).kekulize (Work.prepare m).relevantCycles = .ok K)
    (ha : m.aromatizeOutput (K.finish (Work.prepare m).relevantCycles) = a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (hs : k.IsKekuleSpellingOf m)
    (h' : k.aromatize = .ok a') (hc' : k.ChargesKept a')
    (hw : m.AromaticWritten) (hbw : m.BareWritable) (hbk : k.BareWritable)
    (hsum : ∀ i, (Work.prepare k).bondHalfSum i = K.bondHalfSum i)
    (htotK : ∀ i : Fin n, K.cachedTotalHs i = m.sanitizedH i) : a' = a := by
  obtain ⟨Kk, hKk, hak⟩ := aromatize_eq_ok.mp h'
  rw [hs.kekule.kekulize_prepare] at hKk
  cases hKk
  have hqm := hc.cleanUp_eq_of_kekulize hK ha
  have hqk := hc'.cleanUp_eq _ (.refl _) _ hak
  have hPm : Work.prepare m = (Work.ofMolecule m).freezeHs.cacheValences := by
    simp only [Work.prepare, hqm]
  have hPk : Work.prepare k = (Work.ofMolecule k).freezeHs.cacheValences := by
    simp only [Work.prepare, hqk]
  have hbPm : (Work.prepare m).bonds = (Work.ofMolecule m).bonds := by
    rw [hPm, Work.cacheValences_bonds, Work.freezeHs_bonds]
  have hbPk : (Work.prepare k).bonds = (Work.ofMolecule k).bonds := by
    rw [hPk, Work.cacheValences_bonds, Work.freezeHs_bonds]
  have hsw := swapped_spelling hK ha hc hw hs hqk hsum
  have hKR := Work.kekulize_kindsRel hK
  have hnK : K.atoms.size = n := by rw [hKR.atoms_size, size_prepare_atoms]
  have hnPk : (Work.prepare k).atoms.size = n := size_prepare_atoms k
  have hna := Work.kekulize_noArom hK
  -- the same rings
  have hR1 : (Work.prepare k).relevantCycles =
      ({ K with bonds := (Work.prepare k).bonds } : Work).relevantCycles :=
    Work.relevantCycles_eq_of_ends (by change _ = K.atoms.size; rw [hnPk, hnK]) rfl (fun _ ↦ rfl)
  have hR3 : K.relevantCycles = (Work.prepare m).relevantCycles :=
    Work.relevantCycles_eq_of_ends hKR.atoms_size hKR.bonds_size (fun j ↦ by
      have := congrArg (Option.map fun b : WBond ↦ (b.src, b.dst)) (hKR.bonds j)
      simpa [Option.map_map, Function.comp_def] using this)
  have hR : (Work.prepare k).relevantCycles = (Work.prepare m).relevantCycles :=
    hR1.trans (hsw.relevantCycles_eq.trans hR3)
  rw [hR] at hak
  set R := (Work.prepare m).relevantCycles with hRdef
  set Pk := Work.prepare k with hPkdef
  set K' : Work := { K with bonds := Pk.bonds } with hK'
  -- the bonds `m` writes aromatic come out aromatic
  set Fs : ℕ → Bool := fun j ↦ (m.bonds[j]?.map (·.kind == .aromatic)).getD false with hFs
  have hFsize : (K.finish R).bonds.size = m.bonds.length := by
    rw [Work.finish, Work.finalizeHs_bonds, (Work.afterRel_setAromaticity _ R).bonds_size,
      Work.assignRadicals_bonds, size_kekulized hK]
  have hA : ∀ j, Fs j = true → (K.assignRadicals.setAromaticity R).kind? j = some .aromatic := by
    intro j hj
    cases hmj : m.bonds[j]? with
    | none => simp [hFs, hmj] at hj
    | some b =>
      simp only [hFs, hmj, Option.map_some, Option.getD_some, beq_iff_eq] at hj
      rcases hk.getElem? j with ⟨h1, -⟩ | ⟨x, y, hx, hy, hxy⟩
      · rw [h1] at hmj; cases hmj
      · rw [hmj] at hx
        cases hx
        have hya := hxy hj
        rw [← ha, aromatizeOutput_bonds, getElem?_withKinds, hmj] at hy
        have hjl : j < (K.finish R).bonds.size := by
          rw [hFsize]; exact (List.getElem?_eq_some_iff.mp hmj).1
        simp only [Option.map_some, Array.getElem?_eq_getElem hjl, Option.getD_some,
          Option.some.injEq] at hy
        rw [← hy] at hya
        simp only at hya
        have e : (K.finish R).kind? j = some .aromatic := by
          simp [Work.kind?, Array.getElem?_eq_getElem hjl, hya]
        simpa [Work.finish, Work.kind?, Work.finalizeHs_bonds] using e
  have h0 : ∀ j, K.assignRadicals.kind? j ≠ some .aromatic := by
    intro j e
    rw [Work.kind?, Work.assignRadicals_bonds, Option.map_eq_some_iff] at e
    obtain ⟨x, hx, hxk⟩ := e
    exact hna.2 x (Array.mem_of_getElem? hx) hxk
  have hF : ∀ j, Fs j = true → j ∈ R.toList.flatMap K.ringBonds := by
    intro j hj
    obtain ⟨-, -, hmem, -⟩ := Work.of_kind?_setAromaticity _ R (hA j hj) (h0 j)
    rwa [Work.ringBonds_of_bonds_eq (Work.assignRadicals_bonds _)] at hmem
  have hFin := hsw.finish_eq R hF hA
  have hSet := hsw.setAromaticity_eq R hF hA
  -- the inputs, atom by atom
  have hel : ∀ i, (k.atom i).element = (m.atom i).element := fun i ↦ by
    have := congrArg Atom.element (hs.atoms i); simpa using this
  have hch : ∀ i, (k.atom i).charge = (m.atom i).charge := fun i ↦ by
    have := congrArg Atom.charge (hs.atoms i); simpa using this
  have hzn : ∀ i, (k.atom i).atomicNumber = (m.atom i).atomicNumber := fun i ↦ by
    simp [Atom.atomicNumber, hel i]
  have hCl : Work.cleaned m = (Work.ofMolecule m).freezeHs := hqm
  have hCc : ∀ i : Fin n, ((Work.cleaned m).atoms[i.val]! : WAtom).charge = (m.atom i).charge :=
    fun i ↦ by rw [hCl, Work.freezeHs_ofMolecule_atom]
  have hKz : ∀ j : ℕ, (K'.atoms[j]! : WAtom) = (K.atoms[j]! : WAtom) := fun _ ↦ rfl
  have hbK' : ∀ j : ℕ, K'.bondHalfSum j = Pk.bondHalfSum j := fun j ↦
    congrFun (Work.bondHalfSum_congr (rfl : K'.bonds = Pk.bonds)) j
  have hkP : ∀ j : ℕ, K'.kindsAt j = Pk.kindsAt j := fun _ ↦ rfl
  have hzz : ∀ j : ℕ, (Pk.atoms[j]! : WAtom).z = (K'.atoms[j]! : WAtom).z := fun j ↦ by
    by_cases hj : j < n
    · rw [hKz, (hs.kekule.prepare_record hqk ⟨j, hj⟩).1,
        (kekulize_record hK hw hbw hj).2.1, hzn]
    · rw [getElem!_neg _ j (by omega), getElem!_neg K'.atoms j
        (by change ¬ j < K.atoms.size; omega)]
  have hcc : ∀ j : ℕ, (Pk.atoms[j]! : WAtom).charge = (K'.atoms[j]! : WAtom).charge := fun j ↦ by
    by_cases hj : j < n
    · rw [hKz, (hs.kekule.prepare_record hqk ⟨j, hj⟩).2.1,
        (kekulize_record hK hw hbw hj).2.2.1, hCc ⟨j, hj⟩, hch]
    · rw [getElem!_neg _ j (by omega), getElem!_neg K'.atoms j
        (by change ¬ j < K.atoms.size; omega)]
  have htot : ∀ j : ℕ, Pk.cachedTotalHs j = K'.cachedTotalHs j := fun j ↦ by
    by_cases hj : j < n
    · rw [(hs.kekule.prepare_record hqk ⟨j, hj⟩).2.2.2.2.2.2, hs.hydrogens]
      exact (htotK ⟨j, hj⟩).symm
    · simp only [Work.cachedTotalHs]
      rw [getElem!_neg _ j (by omega), getElem!_neg K'.atoms j
        (by change ¬ j < K.atoms.size; omega)]
  have hr0 : ∀ j : ℕ, (K'.atoms[j]! : WAtom).radicals = 0 := fun j ↦ by
    by_cases hj : j < n
    · exact (kekulize_record hK hw hbw hj).1
    · rw [getElem!_neg K'.atoms j
        (by change ¬ j < K.atoms.size; omega)]; rfl
  have hr0' : ∀ j : ℕ, (Pk.atoms[j]! : WAtom).radicals = 0 := fun j ↦ by
    by_cases hj : j < n
    · exact (hs.kekule.prepare_record hqk ⟨j, hj⟩).2.2.2.2.1
    · rw [getElem!_neg _ j (by omega)]; rfl
  -- the valence the copy with the spelling's bonds caches is its bond-order sum
  have hval : ∀ i : Fin n, ((Work.cleaned m).explicitValence i : ℤ) - (m.atom i).explicitH.getD 0 =
      ((Pk.bondHalfSum i / 2 : ℕ) : ℤ) := by
    intro i
    have e1 := (freezeHs_explicitValence_implicitHs m i).1
    have e2 := hs.valence i
    have e3 := hs.hydrogens i
    rw [sanitizedH_eq, sanitizedH_eq] at e3
    unfold sanitizedValence at e2
    rw [hs.kekule.explicitValence] at e2
    have e4 : Pk.bondHalfSum i = (Work.ofMolecule k).bondHalfSum i := by
      rw [Work.bondHalfSum_congr hbPk]
    rw [hCl, e1, e4]
    omega
  have hkek : ∀ j : ℕ, (K'.assignRadicals.cachedValence j : ℤ) -
      (K'.assignRadicals.atoms[j]! : WAtom).explicitHs = ((K'.bondHalfSum j / 2 : ℕ) : ℤ) := by
    intro j
    rw [Work.cachedValence_assignRadicals, Work.explicitHs_assignRadicals, hbK']
    unfold Work.cachedValence
    rw [hKz]
    by_cases hj : j < n
    · rcases (kekulize_record hK hw hbw hj).2.2.2 with ⟨he, -, -, hv, -, -⟩ |
        ⟨-, -, he, -, -, hv, -⟩
      · rw [hv, he, Option.getD_some]
        exact hval ⟨j, hj⟩
      · rw [hv, he, Option.getD_some, ← hsum]
        simp
    · rw [getElem!_neg K.atoms j (by omega)]
      simp only [Work.kekuleValence, hbK']
      change ((Option.none : Option ℕ).getD _ : ℤ) - 0 = _
      simp only [Option.getD_none]
      rw [hKz, getElem!_neg K.atoms j (by omega)]
      simp
  have hkek' : ∀ j : ℕ, (Pk.assignRadicals.cachedValence j : ℤ) -
      (Pk.assignRadicals.atoms[j]! : WAtom).explicitHs = ((Pk.bondHalfSum j / 2 : ℕ) : ℤ) := by
    intro j
    have hk' := Work.cachedValence_sub_of_noArom
      (Work.noArom_freezeHs (Work.noArom_ofMolecule k hs.kekule.1 hs.kekule.2)) j
    rw [← hPk, Work.bondHalfSum_congr (Work.assignRadicals_bonds _)] at hk'
    exact hk'
  -- written alike, or swapped at RDKit's count
  have hcls : ∀ i : Fin n,
      ((Pk.atoms[i.val]! : WAtom).explicitHs = (K'.atoms[i.val]! : WAtom).explicitHs ∧
        (Pk.atoms[i.val]! : WAtom).noImplicit = (K'.atoms[i.val]! : WAtom).noImplicit) ∨
      ∃ e ∈ Loc.organic, (K'.atoms[i.val]! : WAtom).z = e.atomicNumber ∧
        (K'.atoms[i.val]! : WAtom).charge = 0 ∧
        K'.cachedTotalHs i.val = Loc.rdCount e.atomicNumber 0 (Loc.bhs (K'.kindsAt i.val)) ∧
        (((K'.atoms[i.val]! : WAtom).explicitHs = 0 ∧
            (K'.atoms[i.val]! : WAtom).noImplicit = false ∧
            (Pk.atoms[i.val]! : WAtom).explicitHs = K'.cachedTotalHs i.val ∧
            (Pk.atoms[i.val]! : WAtom).noImplicit = true) ∨
          ((Pk.atoms[i.val]! : WAtom).explicitHs = 0 ∧
            (Pk.atoms[i.val]! : WAtom).noImplicit = false ∧
            (K'.atoms[i.val]! : WAtom).explicitHs = K'.cachedTotalHs i.val ∧
            (K'.atoms[i.val]! : WAtom).noImplicit = true)) := by
    intro i
    obtain ⟨yz, yc, ye, yn, -, yci, -⟩ := hs.kekule.prepare_record hqk i
    obtain ⟨-, kz, kc, hrec⟩ := kekulize_record hK hw hbw i.isLt
    have hT := htot i.val
    have hTx : K'.cachedTotalHs i.val = (K'.atoms[i.val]! : WAtom).explicitHs +
        (K'.atoms[i.val]! : WAtom).cachedImplicit := rfl
    have hTy : Pk.cachedTotalHs i.val = (Pk.atoms[i.val]! : WAtom).explicitHs +
        (Pk.atoms[i.val]! : WAtom).cachedImplicit := rfl
    have hbhs : Loc.bhs (K.kindsAt i.val) = Loc.bhs (K'.kindsAt i.val) := by
      rw [← Work.bondHalfSum_eq_loc, ← Work.bondHalfSum_eq_loc, hbK', hsum]
    rw [← hPkdef] at yz yc ye yn yci
    rw [← hkP] at yci
    have hyc0 : (Pk.atoms[i.val]! : WAtom).noImplicit = true →
        (Pk.atoms[i.val]! : WAtom).cachedImplicit = 0 := fun h ↦ by
      rw [yci]; exact Loc.impl_of_noImplicit h _ _
    -- the spelling's atom bare: RDKit's count on its bonds
    have hyBare : ∀ e, (k.atom i).explicitH = none → (k.atom i).element = some e →
        e ∈ Loc.organic ∧ (k.atom i).charge = 0 ∧
        Pk.cachedTotalHs i.val = Loc.rdCount e.atomicNumber 0 (Loc.bhs (K'.kindsAt i.val)) := by
      intro e hn he
      obtain ⟨hcb, -⟩ := hbk i hn
      have hcb' := hcb
      simp only [Atom.canBeBare, hn, he, Option.isNone_none, Bool.true_and,
        Bool.and_eq_true, beq_iff_eq] at hcb'
      obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
      refine ⟨Loc.mem_organic e (by simpa using horg), hch0, ?_⟩
      rw [hTy, ye, hn, Option.getD_none, Nat.zero_add, yci]
      apply Loc.impl_congr
      · rw [yz]; simp [Atom.atomicNumber, he]
      · rw [yc, hch0]
      · rw [ye, hn]; rfl
      · rw [yn, hn, he]; rfl
    rcases hrec with ⟨ke, kn, kci, -, kC0, kMN⟩ | ⟨hm1, kc0, ke0, kn0, kci, -, kz7⟩
    · cases hme : (m.atom i).explicitH with
      | some a =>
        have hxn : (K'.atoms[i.val]! : WAtom).noImplicit = true := by
          rw [hKz, kn, hme]; rfl
        have hxci : (K'.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
          rw [hKz, kci]; exact kC0 (by simp [hme])
        cases hke : (k.atom i).explicitH with
        | some b =>
          have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hke]; rfl
          left
          refine ⟨?_, by rw [hxn, hyn]⟩
          have := hyc0 hyn
          omega
        | none =>
          cases hel' : (k.atom i).element with
          | none =>
            have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = true := by
              rw [yn, hke, hel']; rfl
            left
            refine ⟨?_, by rw [hxn, hyn]⟩
            have := hyc0 hyn
            have hy0 : (Pk.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [ye, hke]; rfl
            omega
          | some e =>
            obtain ⟨horg, hch0, hTr⟩ := hyBare e hke hel'
            right
            have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = false := by
              rw [yn, hke, hel']; rfl
            have hy0 : (Pk.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [ye, hke]; rfl
            refine ⟨e, horg, ?_, ?_, by rw [← hT, hTr], .inr ⟨hy0, hyn, by omega, hxn⟩⟩
            · rw [hKz, kz, ← hzn]; simp [Atom.atomicNumber, hel']
            · rw [hKz, kc, hCc i, ← hch]; exact hch0
      | none =>
        cases hme' : (m.atom i).element with
        | none =>
          have hxn : (K'.atoms[i.val]! : WAtom).noImplicit = true := by
            rw [hKz, kn, hme, hme']; rfl
          have hxci : (K'.atoms[i.val]! : WAtom).cachedImplicit = 0 := by
            rw [hKz, kci]; exact kC0 (by simp [hme'])
          have hx0 : (K'.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [hKz, ke, hme]; rfl
          have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = true := by
            rw [yn, hel, hme']; simp
          left
          refine ⟨?_, by rw [hxn, hyn]⟩
          have := hyc0 hyn
          omega
        | some e =>
          obtain ⟨hcb, -⟩ := hbw i hme
          have hcb' := hcb
          simp only [Atom.canBeBare, hme, hme', Option.isNone_none, Bool.true_and,
            Bool.and_eq_true, beq_iff_eq] at hcb'
          obtain ⟨⟨⟨⟨-, hch0⟩, -⟩, -⟩, horg⟩ := hcb'
          have hxn : (K'.atoms[i.val]! : WAtom).noImplicit = false := by
            rw [hKz, kn, hme, hme']; rfl
          have hx0 : (K'.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [hKz, ke, hme]; rfl
          have hz : (K'.atoms[i.val]! : WAtom).z = e.atomicNumber := by
            rw [hKz, kz]; simp [Atom.atomicNumber, hme']
          have hc0 : (K'.atoms[i.val]! : WAtom).charge = 0 := by rw [hKz, kc, hCc i]; exact hch0
          have hTr : K'.cachedTotalHs i.val =
              Loc.rdCount e.atomicNumber 0 (Loc.bhs (K'.kindsAt i.val)) := by
            rw [hTx, hx0, Nat.zero_add, hKz, kci, kMN hme e hme', ← hbhs, hCc i, hch0]
            simp [Atom.atomicNumber, hme']
          cases hke : (k.atom i).explicitH with
          | none =>
            left
            refine ⟨by rw [ye, hke, hx0]; rfl, by rw [yn, hke, hel, hxn, hme']; rfl⟩
          | some b =>
            right
            have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hke]; rfl
            have := hyc0 hyn
            refine ⟨e, Loc.mem_organic e (by simpa using horg), hz, hc0, hTr,
              .inl ⟨hx0, hxn, by omega, hyn⟩⟩
    · -- the `[nH]`/`[pH]` rewrite
      have hxn : (K'.atoms[i.val]! : WAtom).noImplicit = false := by rw [hKz]; exact kn0
      have hx0 : (K'.atoms[i.val]! : WAtom).explicitHs = 0 := by rw [hKz]; exact ke0
      obtain ⟨e, he, hez⟩ : ∃ e ∈ Loc.organic, (K'.atoms[i.val]! : WAtom).z = e.atomicNumber := by
        rw [hKz]
        rcases kz7 with h | h
        · exact ⟨.N, by decide, h⟩
        · exact ⟨.P, by decide, h⟩
      have hTr : K'.cachedTotalHs i.val =
          Loc.rdCount e.atomicNumber 0 (Loc.bhs (K'.kindsAt i.val)) := by
        rw [hTx, hx0, Nat.zero_add, hKz, kci, ← hbhs, ← hKz, hez]
      cases hke : (k.atom i).explicitH with
      | some b =>
        right
        have hyn : (Pk.atoms[i.val]! : WAtom).noImplicit = true := by rw [yn, hke]; rfl
        have := hyc0 hyn
        refine ⟨e, he, hez, by rw [hKz]; exact kc0, hTr, .inl ⟨hx0, hxn, by omega, hyn⟩⟩
      | none =>
        left
        refine ⟨by rw [ye, hke, hx0]; rfl, ?_⟩
        rw [yn, hke, hxn, hel]
        have hzm : (m.atom i).atomicNumber ≠ 0 := by
          rw [← kz]; rcases kz7 with h | h <;> omega
        cases hme' : (m.atom i).element with
        | none => simp [Atom.atomicNumber, hme'] at hzm
        | some _ => rfl
  -- perception reads the two copies alike
  have hbR : Pk.assignRadicals.bonds = K'.assignRadicals.bonds := by
    rw [Work.assignRadicals_bonds, Work.assignRadicals_bonds]
  have hzR : ∀ j : ℕ, (Pk.assignRadicals.atoms[j]! : WAtom).z =
      (K'.assignRadicals.atoms[j]! : WAtom).z := fun j ↦ by
    have e1 := congrArg WAtom.z
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms K') j)
    have e2 := congrArg WAtom.z
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Pk) j)
    simp only at e1 e2
    rw [e1, e2, hzz]
  have hcR : ∀ j : ℕ, (Pk.assignRadicals.atoms[j]! : WAtom).charge =
      (K'.assignRadicals.atoms[j]! : WAtom).charge := fun j ↦ by
    have e1 := congrArg WAtom.charge
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms K') j)
    have e2 := congrArg WAtom.charge
      (Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms Pk) j)
    simp only at e1 e2
    rw [e1, e2, hcc]
  have hnoarP := hs.kekule.noArom_prepare
  have hRA : ∀ ring ∈ R.toList, ∀ i ∈ ring, ∀ (rbs : List ℕ) (big : Bool),
      Loc.readAlike (K'.assignRadicals.atoms[i]! : WAtom) (Pk.assignRadicals.atoms[i]! : WAtom)
        (K'.assignRadicals.kindsAt i) (K'.assignRadicals.whoS rbs i)
        (K'.assignRadicals.pullsB rbs i) (K'.assignRadicals.ringMultB rbs i) big = true := by
    intro ring hring i hir rbs big
    by_cases hi : i < n
    · have hlen : 2 ≤ (K'.kindsAt i).length := by
        have hIs := Work.isRing_of_mem_relevantCycles Pk (by rw [hR]; simpa using hring)
        obtain ⟨k₁, k₂, hne, -, -, hk₁, hk₂⟩ := hIs.two_bonds hir
        rw [hkP]
        simp only [Work.kindsAt, List.length_map]
        exact Work.two_le_length_of_ne hne hk₁ hk₂
      have hnoar : (K'.kindsAt i).any (· == .aromatic) = false := by
        rw [hkP, List.any_eq_false]
        intro y' hy'
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy'
        have hlt := Work.lt_of_mem_bondsOf hj
        rw [getElem!_pos _ j hlt]
        simpa using hnoarP.2 _ (Array.getElem_mem hlt)
      exact Work.readAlike_of_swap (w := K') (w' := Pk) rfl (by change i < K.atoms.size; omega)
        (by omega) hlen hnoar
        (hzz i) (hcc i) (htot i) (hkek i) (hkek' i) (hr0 i) (hr0' i) (hcls ⟨i, hi⟩) rbs big
    · rw [getElem!_neg _ i (by
          rw [Work.size_atoms_assignRadicals]; change ¬ i < K.atoms.size; omega),
        getElem!_neg _ i (by rw [Work.size_atoms_assignRadicals]; omega)]
      exact Loc.readAlike_self _ _ _ _ _ _
  have beq : ∀ d d' : Donor, (d == d') = true → d = d' := by
    intro d d' h
    cases d <;> cases d' <;> first | rfl | exact absurd h (by decide)
  have loc : ∀ rbs i len, Pk.assignRadicals.ringDonor rbs len i =
        Loc.ringDonorL (Pk.assignRadicals.atoms[i]! : WAtom) (K'.assignRadicals.kindsAt i)
          (K'.assignRadicals.whoS rbs i) (K'.assignRadicals.pullsB rbs i)
          (K'.assignRadicals.ringMultB rbs i) (decide (9 ≤ len)) ∧
      ∀ d, Pk.assignRadicals.isAromaticCandidate i d =
        Loc.candD (Pk.assignRadicals.atoms[i]! : WAtom) (K'.assignRadicals.kindsAt i) d := by
    intro rbs i len
    have hk : Pk.assignRadicals.kindsAt i = K'.assignRadicals.kindsAt i := by
      simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, hbR]
    refine ⟨?_, fun d ↦ ?_⟩
    · rw [Work.ringDonor_eq_loc, hk, Work.whoS_congr hbR, Work.pullsB_congr hbR hzR,
        Work.ringMultB_congr hbR]
    · rw [Work.isAromaticCandidate_eq_candD, hk]
  have hnK' : K'.atoms.size = n := hnK
  set rbs0 := (R.toList.flatMap K'.assignRadicals.ringBonds).eraseDups with hrbs0
  have hp : Work.PerceiveAgree R K'.assignRadicals Pk.assignRadicals := by
    refine ⟨hbR, by rw [Work.size_atoms_assignRadicals, Work.size_atoms_assignRadicals, hnK',
        hnPk], hzR, hcR, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, ?_, fun ring hring i hir len ↦ ?_,
      fun ring hring i hir len hcd ↦ ?_⟩
    · rw [Work.cachedTotalHs_assignRadicals, Work.cachedTotalHs_assignRadicals, htot]
    · rw [hkek, hkek', hbK']
    · rw [Work.bondHalfSum_congr (Work.assignRadicals_bonds _)]; exact hkek j
    · rw [Work.assignRadicals_bonds]
      exact hnoarP.2
    · have h := hRA ring hring i hir rbs0 (decide (9 ≤ len))
      rw [(loc rbs0 i len).2, (loc rbs0 i len).1, Work.isAromaticCandidate_eq_candD,
        Work.ringDonor_eq_loc]
      unfold Loc.readAlike at h
      rw [Bool.and_eq_true] at h
      exact (beq_iff_eq.1 h.1).symm
    · have h := hRA ring hring i hir rbs0 (decide (9 ≤ len))
      rw [Work.isAromaticCandidate_eq_candD, Work.ringDonor_eq_loc] at hcd
      rw [(loc rbs0 i len).1, Work.ringDonor_eq_loc]
      unfold Loc.readAlike at h
      rw [Bool.and_eq_true, hcd, Bool.not_true, Bool.false_or] at h
      exact (beq _ _ h.2).symm
  have hm : Work.SameMarks K'.assignRadicals Pk.assignRadicals := by
    refine ⟨hbR, fun j ↦ ?_⟩
    rw [Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl),
      Work.getElem?_assignRadicals_map _ _ (fun _ ↦ rfl)]
    by_cases hj : j < n
    · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)]
      simp only [Option.map_some, Option.some.injEq]
      rw [hnoarP.1 _ (Array.getElem_mem _), hna.1 _ (Array.getElem_mem _)]
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  have hr : ∀ i < n, Work.HsRestored (K'.assignRadicals.setAromaticity R) i := fun i hi ↦ by
    rw [hSet]; exact Work.hsRestored_kekulize hw.1 hw.2 hbw hK ⟨i, hi⟩
  have hr' : ∀ i < n, Work.HsRestored (Pk.assignRadicals.setAromaticity R) i := fun i hi ↦ by
    have := hs.kekule.hsRestored hbk hqk hi
    rw [hR] at this
    exact this
  have hO := outAgree_finish hnK' hp hm hr hr'
  rw [hFin] at hO
  -- the outputs
  subst ha hak
  refine aromatizeOutput_respell hO hFsize (hs.bonds.imp fun _ _ h ↦ ⟨h.1, h.2.1, h.2.2.1⟩)
    hs.stereo hs.atoms ?_ hbw hbk ?_
  · intro i
    cases hxe : (m.atom i).explicitH with
    | none => exact .inr (.inr rfl)
    | some a =>
      cases hye : (k.atom i).explicitH with
      | none => exact .inr (.inl rfl)
      | some b =>
        left
        have h0 : ∀ x : Molecule n, ∀ c, (x.atom i).explicitH = some c → x.sanitizedH i = c := by
          intro x c hxc
          rw [sanitizedH_eq, hxc, Work.implicitHs_eq_loc, Work.ofMolecule_atom,
            Loc.impl_of_noImplicit (by simp [hxc])]
          rfl
        rw [← h0 m a hxe, ← h0 k b hye, hs.hydrogens]
  · intro i
    have := hc i
    rw [atom_aromatizeOutput, charge_normalizeBracket] at this
    simpa [Molecule.outAtom] using this

/-- **A Kekulé spelling of a molecule aromatizes to what the molecule does.**  If `m`
aromatizes to `a` keeping its charges and every bond written aromatic, and a Kekulé spelling `k`
of `m` aromatizes keeping its charges, and `m`'s valences are allowed, the two outputs are
equal.  This is `c1cc[nH]c1` against `C1=CNC=C1`.  `ValenceOk` is needed: for the five-valent
`CC1=CC=C[nH](=C1)C=O`, which RDKit rejects, RDKit's GitHub #141 step drops the bracket hydrogen
of the lowercase `[nH]` and not that of its Kekulé spelling `[NH]`. -/
theorem aromatize_of_isKekuleSpellingOf {m k a a' : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (hs : k.IsKekuleSpellingOf m)
    (h' : k.aromatize = .ok a') (hc' : k.ChargesKept a') (hvm : m.ValenceOk) : a' = a := by
  sorry

/-- **A lowercase molecule and its Kekulé spellings have one canonical SMILES.**  With `m`, `k`
as in `aromatize_of_isKekuleSpellingOf`, renumber the atoms of `k` by any `σ` and list the
renumbered bonds in any order and orientation: the result `k₂` aromatizes, and to the canonical
SMILES of `a`.  From `aromatize_of_isKekuleSpellingOf`, `IsKekule.aromatize_relabel`,
`aromatize_of_sameBonds` and `canonicalSmiles_eq_of_sameBonds_relabel`. -/
theorem canonicalSmiles_aromatize_of_isKekuleSpellingOf {m k k₂ a a' : Molecule n}
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (hk : m.AromaticKept a)
    (hs : k.IsKekuleSpellingOf m) (h' : k.aromatize = .ok a') (hc' : k.ChargesKept a')
    (hvm : m.ValenceOk)
    (σ : Equiv.Perm (Fin n)) (hat : k₂.atoms = (k.relabel σ).atoms)
    (hst : k₂.stereo = (k.relabel σ).stereo) (hb : k₂.SameBonds (k.relabel σ)) :
    ∃ a₂, k₂.aromatize = .ok a₂ ∧ a₂.canonicalSmiles = a.canonicalSmiles := by
  have h₂ := hs.kekule.aromatize_relabel h' hc' σ
  obtain ⟨a₂, h₂', ha, hst', hb'⟩ := aromatize_of_sameBonds h₂ (hc'.relabel σ) hat hst hb
  refine ⟨a₂, h₂', ?_⟩
  rw [canonicalSmiles_eq_of_sameBonds_relabel σ ha hst' hb',
    aromatize_of_isKekuleSpellingOf h hc hk hs h' hc' hvm]

end Molecule

end LeanSMILES
