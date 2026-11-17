/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import LeanSMILES.Aromaticity.Passes
public import LeanSMILES.SMILES.Canonicity

/-!
# LeanSMILES.Aromaticity.Invariance

What `Molecule.aromatize` does not depend on: the numbering of the atoms, the
listing of the bonds, and which Kekulé structure of an aromatic system was
written.  With `canonicalSmiles_relabel` and `canonicalSmiles_eq_of_sameBonds`
this gives the statement a user wants: every Kekulé structure of a molecule,
with its atoms in any order and its bonds listed any way, aromatizes to one
canonical SMILES (`canonicalSmiles_aromatize_eq`).

**Status: statements only.**  Every proof in this file is `sorry`.  The
definitions are complete and decidable, and each statement was tested as
written (below) before it was fixed.

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
Kekulé structure of itself (`exists_kekule_aromatize`): its own atoms with the
aromatic flags cleared and each aromatic bond single or double.  Every other
Kekulé structure with the same bond-order sums then has the same image
(`aromatize_of_kekuleVariant`).

## What was tested

Each statement was checked as written — the hypotheses decided by the
instances below, the conclusions as equalities of molecules — by
`lake exe invariance-test` (`LeanSMILES/Tests/AromatizeInvariance.lean`) on
20 216 SMILES: every Kekulé structure and the lowercase form of 1 147 aromatic
molecules in random atom orders (13 701 strings); 2 719 lowercase rewrites of
stereo-rich molecules; the 2 992 strings of `datasets/*-oracle.csv`; and the
805 hard cases of `datasets/aromatize-invariance.smi` (lowercase rings that
stay non-aromatic, fused systems with one aromatic and one non-aromatic ring,
charged rings, exocyclic double bonds, annulenes, cyclophanes, large
polycyclic aromatics, the inputs `cleanUp` rewrites; in lowercase and Kekulé
form and in random atom orders).  Per string: five renumberings (a rotation,
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
| `aromatize_of_kekuleVariant` | 77 310 | 0 |
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

/-- Nothing written aromatic: no lowercase atom, no aromatic bond.  A Kekulé structure. -/
def IsKekule (m : Molecule n) : Prop :=
  (∀ i, (m.atom i).aromatic = false) ∧ ∀ b ∈ m.bonds, b.kind ≠ .aromatic

instance (m : Molecule n) : Decidable m.IsKekule :=
  inferInstanceAs (Decidable ((∀ i, (m.atom i).aromatic = false) ∧
    ∀ b ∈ m.bonds, b.kind ≠ .aromatic))

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

/-- `aromatize` changes bond kinds and nothing else about the bond list: its order, and every
bond's two atoms, orientation and `/` `\` mark, are the input's. -/
theorem sameSkeleton_aromatize {m a : Molecule n} (h : m.aromatize = .ok a) :
    m.SameSkeleton a := by
  sorry

/-- `aromatize` keeps the configurations. -/
theorem stereo_aromatize {m a : Molecule n} (h : m.aromatize = .ok a) : a.stereo = m.stereo := by
  sorry

/-- A Kekulé structure always aromatizes: the only step that can fail is kekulization, which has
nothing to do. -/
theorem IsKekule.exists_aromatize {m : Molecule n} (hk : m.IsKekule) :
    ∃ a, m.aromatize = .ok a := by
  sorry

/-- A Kekulé structure keeps every aromatic bond written in it: there is none. -/
theorem IsKekule.aromaticKept {m a : Molecule n} (hk : m.IsKekule) (h : m.aromatize = .ok a) :
    m.AromaticKept a := by
  sorry

/-- **Rings that stay non-aromatic keep their double bonds.**  For a Kekulé input whose charges
are kept, each bond of the output is either aromatic or has the kind it was written with. -/
theorem kind_aromatize {m a : Molecule n} (hk : m.IsKekule) (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) :
    List.Forall₂ (fun b b' ↦ b'.kind = .aromatic ∨ b'.kind = b.kind) m.bonds a.bonds := by
  sorry

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
  sorry

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

/-- **Every Kekulé structure of an aromatic system aromatizes to the same molecule.**  If the
Kekulé structure `m` aromatizes to `a`, so does every `m'` that differs from `m` only on bonds
aromatic in `a`, with each atom keeping its bond-order sum. -/
theorem aromatize_of_kekuleVariant {m m' a : Molecule n} (hk : m.IsKekule)
    (h : m.aromatize = .ok a) (hv : KekuleVariant a m m') : m'.aromatize = .ok a := by
  sorry

/-- **`aromatize` is idempotent**: an output that aromatizes again aromatizes to itself.  This
is the lowercase form of a molecule as an input: a fixed point. -/
theorem aromatize_aromatize {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (h' : a.aromatize = .ok a') : a' = a := by
  sorry

/-- **Every output is the image of a Kekulé structure of itself.**  A witness is the structure
the pipeline computes on the way: the output's atoms with the aromatic flags cleared, and each
aromatic bond with the kind `Work.kekulize` gave it. -/
theorem exists_kekule_aromatize {m a : Molecule n} (h : m.aromatize = .ok a) :
    ∃ k : Molecule n, k.IsKekule ∧ k.IsKekuleStructureOf a ∧ k.aromatize = .ok a := by
  sorry

/-! ### 4. The canonical string -/

/-- Renumbering the atoms does not change the canonical SMILES of the aromatized molecule.
From `aromatize_relabel` and `canonicalSmiles_relabel`. -/
theorem canonicalSmiles_aromatize_relabel {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (σ : Equiv.Perm (Fin n))
    (h' : (m.relabel σ).aromatize = .ok a') : a'.canonicalSmiles = a.canonicalSmiles := by
  sorry

/-- Relisting the bonds does not change the canonical SMILES of the aromatized molecule.  From
`aromatize_of_sameBonds` and `canonicalSmiles_eq_of_sameBonds`. -/
theorem canonicalSmiles_aromatize_of_sameBonds {m m' a : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hat : m'.atoms = m.atoms) (hst : m'.stereo = m.stereo)
    (hb : m'.SameBonds m) :
    ∃ a', m'.aromatize = .ok a' ∧ a'.canonicalSmiles = a.canonicalSmiles := by
  sorry

/-- Aromatizing an output again does not change its canonical SMILES.  From
`aromatize_aromatize`. -/
theorem canonicalSmiles_aromatize_aromatize {m a a' : Molecule n} (h : m.aromatize = .ok a)
    (h' : a.aromatize = .ok a') : a'.canonicalSmiles = a.canonicalSmiles := by
  sorry

/-- **One molecule, one aromatic canonical SMILES.**  Let the Kekulé structure `m` aromatize to
`a`, keeping its charges.  Take any other Kekulé structure `m₁` of it over the aromatic bonds,
renumber its atoms by any `σ`, and list the renumbered bonds in any order and orientation: the
result `m₂` aromatizes, and to the canonical SMILES of `a`.  From `aromatize_of_kekuleVariant`,
`IsKekule.aromatize_relabel`, `aromatize_of_sameBonds` and
`canonicalSmiles_eq_of_sameBonds_relabel`. -/
theorem canonicalSmiles_aromatize_eq {m m₁ m₂ a : Molecule n} (hk : m.IsKekule)
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (hv : KekuleVariant a m m₁)
    (σ : Equiv.Perm (Fin n)) (hat : m₂.atoms = (m₁.relabel σ).atoms)
    (hst : m₂.stereo = (m₁.relabel σ).stereo) (hb : m₂.SameBonds (m₁.relabel σ)) :
    ∃ a₂, m₂.aromatize = .ok a₂ ∧ a₂.canonicalSmiles = a.canonicalSmiles := by
  sorry

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

The built spellings are from the 805 hard cases, the 2 992 oracle strings and
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

/-- **A Kekulé spelling of a molecule aromatizes to what the molecule does.**  If `m`
aromatizes to `a` keeping its charges and every bond written aromatic, and a Kekulé spelling `k`
of `m` aromatizes keeping its charges, the two outputs are equal.  This is `c1cc[nH]c1` against
`C1=CNC=C1`. -/
theorem aromatize_of_isKekuleSpellingOf {m k a a' : Molecule n} (h : m.aromatize = .ok a)
    (hc : m.ChargesKept a) (hk : m.AromaticKept a) (hs : k.IsKekuleSpellingOf m)
    (h' : k.aromatize = .ok a') (hc' : k.ChargesKept a') : a' = a := by
  sorry

/-- **A lowercase molecule and its Kekulé spellings have one canonical SMILES.**  With `m`, `k`
as in `aromatize_of_isKekuleSpellingOf`, renumber the atoms of `k` by any `σ` and list the
renumbered bonds in any order and orientation: the result `k₂` aromatizes, and to the canonical
SMILES of `a`.  From `aromatize_of_isKekuleSpellingOf`, `IsKekule.aromatize_relabel`,
`aromatize_of_sameBonds` and `canonicalSmiles_eq_of_sameBonds_relabel`. -/
theorem canonicalSmiles_aromatize_of_isKekuleSpellingOf {m k k₂ a a' : Molecule n}
    (h : m.aromatize = .ok a) (hc : m.ChargesKept a) (hk : m.AromaticKept a)
    (hs : k.IsKekuleSpellingOf m) (h' : k.aromatize = .ok a') (hc' : k.ChargesKept a')
    (σ : Equiv.Perm (Fin n)) (hat : k₂.atoms = (k.relabel σ).atoms)
    (hst : k₂.stereo = (k.relabel σ).stereo) (hb : k₂.SameBonds (k.relabel σ)) :
    ∃ a₂, k₂.aromatize = .ok a₂ ∧ a₂.canonicalSmiles = a.canonicalSmiles := by
  sorry

end Molecule

end LeanSMILES
