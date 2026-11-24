/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.Invariance
public import LeanSMILES.Aromaticity.ResonanceProofs

/-!
# LeanSMILES.Aromaticity.CleanUpRelabel

**On Kekulé input, `aromatize` commutes with renumbering the atoms** when the atoms `cleanUp` may
rewrite are apart: property 3 of `LeanSMILES.Aromaticity.Resonance`
(`Aromaticity.aromatizeRelabelKekule`).

`Molecule.IsKekule.aromatize_relabel` proves this when `cleanUp` rewrites nothing. Here it may
rewrite. `cleanUp` makes three passes: `nitroStep` over the atoms in index order, `azideStep` over
the nitrogens the first pass remembered, and `cleanUpStep` over the atoms again. On a renumbered
copy each pass visits the same atoms in another order, and the order does not matter:

* A step at atom `c` reads and writes only `c`, its neighbours and the bonds at `c`
  (`Work.LocalStep`), so steps at two atoms that are not bonded and share no neighbour commute
  (`Work.LocalStep.comm`).
* A step at an atom `cleanUp` may not rewrite does nothing, and a step makes no other atom one it
  may rewrite: every atom it changes ends up charged (`Work.Rewrite.center`). So the atoms that
  are rewritten along the way are among those of the start (`Work.NoNewCenters`), which are apart.
* So a pass over a permuted list of atoms gives the same copy (`foldl_perm_rel`,
  `Work.foldl_nitroStep_perm`, `Work.foldl_azideStep_perm`, `Work.foldl_cleanUpStep_perm`).

Each single step commutes with renumbering (`Work.nitroW_relabelW`, `Work.azideStep_relabelW`,
`Work.cleanUpStep_relabelW`): `Work.relabelW` keeps the bond list in order, so the first `=O` in
bond order is the same oxygen. Hence `cleanUp` commutes with renumbering
(`Work.cleanUp_relabelW`), and so does the copy `aromatize` kekulizes (`prepare_relabel`). A
Kekulé structure is kekulized to itself, and the passes after kekulization commute with
renumbering (`Work.finish_relabelW`, `Molecule.aromatizeOutput_relabel`), over the renumbered
copy's own ring set (`Work.WorkIso.setAromaticity_relevantCycles`).

## Main definitions

* `Work.Near`, `Work.Apart`: an atom or one of its neighbours; two atoms with no atom near both.
* `Work.AgreeNear`: two copies agree near an atom, which is all a step there reads.
* `Work.Rewrite`: a copy rewritten near an atom, every other atom it changes left charged.
* `Work.LocalStep`: a step that rewrites only near its atom and reads only there.
* `Work.nitroW`: what `nitroStep` does to the working copy.
* `Work.CentersApart`: any two atoms `cleanUp` may rewrite are apart.
* `Work.NoNewCenters`: what the steps of `cleanUp` keep of the copy they started from.

## Main statements

* `foldl_perm_rel`: a fold over a permuted list, when steps commute from the states it reaches.
* `Work.LocalStep.comm`: local steps at atoms apart commute.
* `Work.localStep_nitroW`, `Work.localStep_azideStep`, `Work.localStep_cleanUpStep`: the steps of
  `cleanUp` are local.
* `Work.NoNewCenters.comm`: two steps commute from any copy the passes of `cleanUp` reach.
* `Work.cleanUp_relabelW`: `cleanUp` commutes with renumbering when its atoms are apart.
* `centersApart_of_cleanUpTargetsApart`: `Molecule.CleanUpTargetsApart`, on the working copy.
* `prepare_relabel`: the copy `aromatize` kekulizes commutes with renumbering.
* `aromatizeRelabelKekule`: property 3.
* `Molecule.aromaticCanonicalSmiles_relabel_of_isKekule`,
  `Molecule.aromaticCanonicalSmiles_eq_of_eqvGen_redraw`: the aromatic canonical SMILES of a
  Kekulé structure does not depend on the numbering, nor on any chain of renumberings and
  resonance moves, with no property assumed.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

/-! ### Folding over a permuted list -/

/-- A property the step keeps holds after a fold. -/
lemma foldl_invariant {α β : Type*} {P : β → Prop} {f : β → α → β} (l : List α)
    (hf : ∀ z x, x ∈ l → P z → P (f z x)) {z : β} (h : P z) : P (l.foldl f z) :=
  foldl_lockstep (R := fun a _ ↦ P a) l (fun a _ x hx ha ↦ hf a x hx ha) (a₂ := z) h

/-- **Folding over a permuted list gives a related result**, when two steps taken in either order
give related results from any state the fold can reach. `P` is what the reachable states satisfy,
`A` what the members of the list do, and `E` the relation, which the step carries. -/
lemma foldl_perm_rel {α β : Type*} {E : β → β → Prop} {P : β → Prop} {A : α → Prop}
    {f : β → α → β} (refl : ∀ z, E z z) (trans : ∀ {a b c}, E a b → E b c → E a c)
    (hP : ∀ z x, A x → P z → P (f z x)) (congr : ∀ z z' x, E z z' → E (f z x) (f z' x))
    (comm : ∀ z x y, A x → A y → P z → E (f (f z x) y) (f (f z y) x)) {l₁ l₂ : List α}
    (h : l₁.Perm l₂) : ∀ z, P z → (∀ x ∈ l₁, A x) → E (l₁.foldl f z) (l₂.foldl f z) := by
  induction h with
  | nil => exact fun z _ _ ↦ refl z
  | cons x _ ih =>
    exact fun z hz hA ↦ ih _ (hP z x (hA x List.mem_cons_self) hz) fun y hy ↦
      hA y (List.mem_cons_of_mem _ hy)
  | swap x y l =>
    intro z hz hA
    exact foldl_lockstep l (fun a₁ a₂ b _ h ↦ congr a₁ a₂ b h)
      (comm z y x (hA y List.mem_cons_self) (hA x (List.mem_cons_of_mem _ List.mem_cons_self)) hz)
  | trans h₁ _ ih₁ ih₂ =>
    exact fun z hz hA ↦ trans (ih₁ z hz hA) (ih₂ z hz fun x hx ↦ hA x (h₁.mem_iff.2 hx))

namespace Work

/-! ### Near an atom -/

/-- Atom `i` is `c` or a neighbour of `c`: where a step of `cleanUp` at `c` reads and writes. -/
def Near (w : Work) (c i : ℕ) : Prop := i = c ∨ w.Adj c i

/-- Copies with the same skeleton have the same atoms near `c`. -/
lemma SameSkel.near {w w' : Work} (h : SameSkel w w') (c i : ℕ) : w.Near c i ↔ w'.Near c i := by
  simp only [Near, Adj, h.neighbors]

/-- Copies with the same skeleton have the same bonds at `c`. -/
lemma SameSkel.mem_bondsOf {w w' : Work} (h : SameSkel w w') {c k : ℕ} :
    k ∈ w.bondsOf c ↔ k ∈ w'.bondsOf c := by
  rw [h.bondsOf]

/-- The other end of a bond at `c` is near `c`. -/
lemma near_other {w : Work} {c k : ℕ} (hk : k ∈ w.bondsOf c) :
    w.Near c ((w.bonds[k]! : WBond).other c) :=
  Or.inr ⟨k, List.mem_map.2 ⟨k, hk, rfl⟩⟩

/-- An atom sharing a bond with `c` is near `c`. -/
lemma near_of_mem_bondsOf {w : Work} {c y k : ℕ} (hc : k ∈ w.bondsOf c) (hy : k ∈ w.bondsOf y) :
    w.Near c y := by
  rcases touches_other (touches_of_mem_bondsOf hc) (touches_of_mem_bondsOf hy) with e | e
  · exact Or.inl e
  · exact e ▸ near_other hc

/-- A neighbour pair of `c` has its atom near `c`. -/
lemma near_of_mem_neighbors {w : Work} {c : ℕ} {x : ℕ × ℕ} (hx : x ∈ w.neighbors c) :
    w.Near c x.2 :=
  Or.inr ⟨x.1, hx⟩

/-- No atom is near both `x` and `y`: they are distinct, not bonded, and have no common
neighbour. -/
def Apart (w : Work) (x y : ℕ) : Prop := ∀ i, w.Near x i → ¬ w.Near y i

/-- Being apart is symmetric. -/
lemma Apart.symm {w : Work} {x y : ℕ} (h : Apart w x y) : Apart w y x := fun i hy hx ↦ h i hx hy

/-- Atoms apart in one copy are apart in any copy with the same skeleton. -/
lemma SameSkel.apart {w w' : Work} (h : SameSkel w w') {x y : ℕ} (ha : Apart w x y) :
    Apart w' x y :=
  fun i hx hy ↦ ha i ((h.near x i).2 hx) ((h.near y i).2 hy)

/-- Two bonds with the same ends and the same kind are equal. -/
lemma wbond_ext {b b' : WBond} (h₁ : b.src = b'.src) (h₂ : b.dst = b'.dst)
    (h₃ : b.kind = b'.kind) : b = b' := by
  cases b
  cases b'
  simp_all

/-- Looking the same at an atom is transitive. -/
lemma SameAt.trans {w w' w'' : Work} {i : ℕ} (h₁ : SameAt w w' i) (h₂ : SameAt w' w'' i) :
    SameAt w w'' i :=
  ⟨h₁.atom.trans h₂.atom, h₁.bondsOf.trans h₂.bondsOf, fun k hk ↦
    (h₁.kind k hk).trans (h₂.kind k (h₁.bondsOf ▸ hk))⟩

/-- An atom that looks the same is a `nitroCand` in both or neither. -/
lemma SameAt.nitroCand {w w' : Work} {i : ℕ} (h : SameAt w w' i) :
    w.nitroCand i = w'.nitroCand i := by
  simp only [Work.nitroCand, h.atom, h.explicitValence]

/-- `w` and `w'` agree near `c`: the same skeleton, the same records at `c` and its neighbours,
the same kinds on the bonds at `c`. This is all a step of `cleanUp` at `c` reads. -/
structure AgreeNear (w w' : Work) (c : ℕ) : Prop where
  /-- The same skeleton. -/
  skel : SameSkel w w'
  /-- The same record at every atom near `c`. -/
  atom : ∀ i, w.Near c i → (w.atoms[i]! : WAtom) = w'.atoms[i]!
  /-- The same kind on every bond at `c`. -/
  kind : ∀ k ∈ w.bondsOf c, (w.bonds[k]! : WBond).kind = (w'.bonds[k]! : WBond).kind

namespace AgreeNear

variable {w w' : Work} {c : ℕ} (h : AgreeNear w w' c)
include h

/-- Copies that agree near `c` look the same at `c`. -/
lemma sameAt : SameAt w w' c :=
  ⟨h.atom c (Or.inl rfl), h.skel.bondsOf ▸ rfl, h.kind⟩

/-- Copies that agree near `c` have the same record and bond kind at each neighbour pair of
`c`. -/
lemma nbr {x : ℕ × ℕ} (hx : x ∈ w.neighbors c) :
    (w.atoms[x.2]! : WAtom) = w'.atoms[x.2]! ∧
      (w.bonds[x.1]! : WBond).kind = (w'.bonds[x.1]! : WBond).kind :=
  ⟨h.atom _ (near_of_mem_neighbors hx), h.kind _ (mem_neighbors (j := x.2) hx).1⟩

/-- Rewriting one bond the same way on both sides keeps the agreement. -/
lemma setKind (k : ℕ) (o : BondKind) : AgreeNear (w.setKind k o) (w'.setKind k o) c where
  skel := ((skel_setKind w k o).symm.trans h.skel).trans (skel_setKind w' k o)
  atom i hi := h.atom i (((skel_setKind w k o).near c i).2 hi)
  kind j hj := by
    have hn : w.bonds.size = w'.bonds.size := h.skel.numBonds
    rw [kind_setKind, kind_setKind, ← hn, h.kind j ((skel_setKind w k o).mem_bondsOf.2 hj)]

/-- Rewriting one atom the same way on both sides keeps the agreement. -/
lemma modifyAtom (j : ℕ) (F : WAtom → WAtom) :
    AgreeNear (w.modifyAtom j F) (w'.modifyAtom j F) c where
  skel := ((skel_modifyAtom w j F).symm.trans h.skel).trans (skel_modifyAtom w' j F)
  atom i hi := by
    have hn : w.atoms.size = w'.atoms.size := h.skel.numAtoms
    rw [atom_modifyAtom, atom_modifyAtom, ← hn, h.atom i (((skel_modifyAtom w j F).near c i).2 hi)]
  kind := h.kind

/-- Searching the neighbours of `c` finds the same pair on both sides, for a search that reads
the neighbour's record and the bond's kind. -/
lemma find? {p : Work → ℕ × ℕ → Bool} (hp : ∀ x ∈ w.neighbors c, p w x = p w' x) :
    (w.neighbors c).find? (p w) = (w'.neighbors c).find? (p w') := by
  rw [← h.skel.neighbors]
  exact find?_congr_mem hp

end AgreeNear

/-- `w'` is `w` rewritten near `c`: the same skeleton, changes only to atoms near `c` and to
bonds at `c`, and every atom other than `c` either looks as it did or ends up charged. -/
structure Rewrite (w w' : Work) (c : ℕ) : Prop where
  /-- The same skeleton. -/
  skel : SameSkel w w'
  /-- Atoms not near `c` are unchanged. -/
  atom : ∀ i, ¬ w.Near c i → (w'.atoms[i]! : WAtom) = w.atoms[i]!
  /-- Bonds not at `c` keep their kind. -/
  kind : ∀ k, k ∉ w.bondsOf c → (w'.bonds[k]! : WBond).kind = (w.bonds[k]! : WBond).kind
  /-- An atom other than `c` looks as it did, or is charged. -/
  charged : ∀ i, i ≠ c → SameAt w w' i ∨ (w'.atoms[i]! : WAtom).charge ≠ 0

/-- Rewriting nothing is a rewrite. -/
lemma Rewrite.refl (w : Work) (c : ℕ) : Rewrite w w c :=
  ⟨SameSkel.refl w, fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ Or.inl ⟨rfl, rfl, fun _ _ ↦ rfl⟩⟩

namespace Rewrite

variable {w w' : Work} {c : ℕ} (h : Rewrite w w' c)
include h

/-- Rewrites near `c` compose. -/
lemma trans {w'' : Work} (h' : Rewrite w' w'' c) : Rewrite w w'' c where
  skel := h.skel.trans h'.skel
  atom i hi := (h'.atom i fun hn ↦ hi ((h.skel.near c i).2 hn)).trans (h.atom i hi)
  kind k hk := (h'.kind k fun hn ↦ hk (h.skel.mem_bondsOf.2 hn)).trans (h.kind k hk)
  charged i hi := by
    rcases h.charged i hi with h₁ | h₁ <;> rcases h'.charged i hi with h₂ | h₂
    · exact Or.inl (h₁.trans h₂)
    · exact Or.inr h₂
    · exact Or.inr (h₂.atom ▸ h₁)
    · exact Or.inr h₂

/-- A rewrite near `c` leaves the copy as it was near any atom apart from `c`. -/
lemma agreeNear {y : ℕ} (ha : Apart w c y) : AgreeNear w w' y where
  skel := h.skel
  atom i hi := (h.atom i fun hc ↦ ha i hc hi).symm
  kind k hk := (h.kind k fun hc ↦ ha y (near_of_mem_bondsOf hc hk) (Or.inl rfl)).symm

/-- A rewrite near `c` makes no atom other than `c` one `cleanUp` may rewrite. -/
lemma center {x : ℕ} (hx : x ≠ c) (hc : w'.cleanUpCenter x = true) : w.cleanUpCenter x = true := by
  rcases h.charged x hx with hs | hch
  · rwa [hs.cleanUpCenter]
  · simp [Work.cleanUpCenter, hch] at hc

end Rewrite

/-- A `Local` rewrite at `c` and an atom `j` near `c` is a rewrite near `c`. -/
lemma Local.rewrite {w w' : Work} {c j : ℕ} (h : Local w w' c j) (hwf : WF w)
    (hj : w.Near c j) : Rewrite w w' c where
  skel := h.skel
  atom i hi := h.atom i (fun e ↦ hi (Or.inl e)) (fun e ↦ hi (e ▸ hj))
  kind k hk := by
    by_contra hne
    have ht := h.kind k hne
    by_cases hlt : k < w.numBonds
    · obtain ⟨-, -, hsd⟩ := hwf k hlt
      have hc : (w.bonds[k]! : WBond).touches c = true := by
        simp only [WBond.touches, Bool.or_eq_true, beq_iff_eq]
        rcases ht (w.bonds[k]! : WBond).src (by simp [WBond.touches]) with e | e
        · exact Or.inl e
        · rcases ht (w.bonds[k]! : WBond).dst (by simp [WBond.touches]) with e' | e'
          · exact Or.inr e'
          · exact absurd (e.trans e'.symm) hsd
      exact hk (List.mem_filter.2 ⟨List.mem_range.2 hlt, hc⟩)
    · have hlt' : ¬ k < w'.bonds.size := fun hh ↦ hlt (h.skel.numBonds ▸ hh)
      exact hne (by rw [getElem!_neg _ k hlt', getElem!_neg _ k hlt])
  charged i hi := by
    by_cases hij : i = j
    · exact Or.inr (hij ▸ h.charged (hij ▸ hi))
    · refine Or.inl ⟨(h.atom i hi hij).symm, by rw [h.skel.bondsOf], fun k hk ↦ ?_⟩
      by_contra hne
      rcases h.kind k (Ne.symm hne) i (touches_of_mem_bondsOf hk) with e | e
      · exact hi e
      · exact hij e

/-! ### Steps at atoms apart commute -/

/-- A step that rewrites only near its atom, and reads only there. -/
structure LocalStep (f : Work → ℕ → Work) : Prop where
  /-- The step at `c` rewrites near `c`. -/
  rewrite : ∀ w c, WF w → Rewrite w (f w c) c
  /-- Copies that agree near `c` still agree near `c` after the step at `c`. -/
  agree : ∀ w w' c, AgreeNear w w' c → AgreeNear (f w c) (f w' c) c

/-- **Local steps at atoms apart commute.** Each leaves the copy as it was near the other's atom,
so the other does there what it would have done, and away from both atoms nothing changes. -/
theorem LocalStep.comm {f g : Work → ℕ → Work} (hf : LocalStep f) (hg : LocalStep g) {w : Work}
    (hwf : WF w) {x y : ℕ} (hxy : Apart w x y) : g (f w x) y = f (g w y) x := by
  have rf := hf.rewrite w x hwf
  have rg := hg.rewrite w y hwf
  have rgf := hg.rewrite (f w x) y (rf.skel.wf hwf)
  have rfg := hf.rewrite (g w y) x (rg.skel.wf hwf)
  have af := hf.agree w (g w y) x (rg.agreeNear hxy.symm)
  have ag := hg.agree w (f w x) y (rf.agreeNear hxy)
  have s₁ : SameSkel w (g (f w x) y) := rf.skel.trans rgf.skel
  have s₂ : SameSkel w (f (g w y) x) := rg.skel.trans rfg.skel
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) s₁.numAtoms.symm s₂.numAtoms.symm
    intro i _
    by_cases hx : w.Near x i
    · rw [rgf.atom i fun h ↦ hxy i hx ((rf.skel.near y i).2 h)]
      exact af.atom i ((rf.skel.near x i).1 hx)
    · by_cases hy : w.Near y i
      · rw [rfg.atom i fun h ↦ hx ((rg.skel.near x i).2 h)]
        exact (ag.atom i ((rg.skel.near y i).1 hy)).symm
      · rw [rgf.atom i fun h ↦ hy ((rf.skel.near y i).2 h), rf.atom i hx,
          rfg.atom i fun h ↦ hx ((rg.skel.near x i).2 h), rg.atom i hy]
  · apply array_ext_of_getElem! (n := w.bonds.size) s₁.numBonds.symm s₂.numBonds.symm
    intro k _
    refine wbond_ext ((s₁.src k).symm.trans (s₂.src k)) ((s₁.dst k).symm.trans (s₂.dst k)) ?_
    by_cases hx : k ∈ w.bondsOf x
    · rw [rgf.kind k fun h ↦ hxy y (near_of_mem_bondsOf hx (rf.skel.mem_bondsOf.2 h)) (Or.inl rfl)]
      exact af.kind k (rf.skel.mem_bondsOf.1 hx)
    · by_cases hy : k ∈ w.bondsOf y
      · rw [rfg.kind k fun h ↦ hx (rg.skel.mem_bondsOf.2 h)]
        exact (ag.kind k (rg.skel.mem_bondsOf.1 hy)).symm
      · rw [rgf.kind k fun h ↦ hy (rf.skel.mem_bondsOf.2 h), rf.kind k hx,
          rfg.kind k fun h ↦ hx (rg.skel.mem_bondsOf.2 h), rg.kind k hy]

/-! ### The steps of `cleanUp` are local -/

/-- What `nitroStep` does to the working copy at atom `i`: `nitrogenOxideAt` at a `nitroCand`. -/
def nitroW (w : Work) (i : ℕ) : Work := if w.nitroCand i then w.nitrogenOxideAt i else w

/-- The working copy after `nitroStep` is `nitroW` of the copy before. -/
lemma nitroStep_fst_eq (s : Work × List ℕ) (i : ℕ) : (nitroStep s i).1 = nitroW s.1 i := by
  rw [nitroStep_eq, nitroW]
  split <;> rfl

/-- `phosphorusCleanup`, with its guard named and its scan matched at once. -/
lemma phosphorusCleanup_eq_ite (w : Work) (c : ℕ) :
    w.phosphorusCleanup c = if w.phosphorusGuard c then w else
      match w.phosphorusScan c with
      | (some (k, j), true) =>
        ((w.setKind k .single).modifyAtom j ({ · with charge := -1 })).modifyAtom c
          ({ · with charge := 1 })
      | _ => w := by
  unfold phosphorusCleanup phosphorusGuard
  dsimp only
  split
  · rfl
  · rcases w.phosphorusScan c with ⟨_ | ⟨k, j⟩, _ | _⟩ <;> rfl

/-- `halogenCleanup`, with its guard named. -/
lemma halogenCleanup_eq_ite (w : Work) (c : ℕ) :
    w.halogenCleanup c = if w.halogenGuard c then w else
      ((w.neighbors c).foldl halogenStep (w, 0)).1.modifyAtom c
        ({ · with charge := ((w.neighbors c).foldl halogenStep (w, 0)).2 }) := by
  unfold halogenCleanup halogenGuard
  dsimp only
  split
  · rename_i hg
    rw [hg, Bool.true_or, if_pos rfl]
  · rename_i hg
    rw [Bool.not_eq_true] at hg
    rw [hg, Bool.false_or]

/-- `halogenGuard`, with the test on the neighbours read off the pair. -/
lemma halogenGuard_eq (w : Work) (c : ℕ) :
    w.halogenGuard c = (w.atoms[c]!.charge != 0 ||
      !([3, 5, 7] : List ℕ).contains (w.explicitValence c) ||
      !(w.neighbors c).all (fun x ↦ w.atoms[x.2]!.z == 8)) := by
  unfold halogenGuard
  rfl

/-- `nitrogenOxideAt` at `c` rewrites near `c`. -/
lemma rewrite_nitrogenOxideAt {w : Work} (hwf : WF w) (c : ℕ) :
    Rewrite w (w.nitrogenOxideAt c) c := by
  unfold nitrogenOxideAt
  rcases hf : (w.neighbors c).find? w.nitroO with _ | ⟨k, j⟩
  · exact Rewrite.refl w c
  · obtain ⟨hk, rfl⟩ := mem_neighbors (List.mem_of_find?_eq_some hf)
    exact (local_kcj w hwf hk .single (by decide) ({ · with charge := 1 })
      ({ · with charge := -1 }) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ by simp)).rewrite hwf
      (near_other hk)

/-- `azideStep` at `c` rewrites near `c`. -/
lemma rewrite_azideStep {w : Work} (hwf : WF w) (c : ℕ) : Rewrite w (w.azideStep c) c := by
  rw [azideStep_eq]
  rcases hf : (w.neighbors c).find? w.azideN with _ | ⟨k, j⟩
  · exact Rewrite.refl w c
  · obtain ⟨hk, rfl⟩ := mem_neighbors (List.mem_of_find?_eq_some hf)
    exact (local_kcj w hwf hk .double (by decide) ({ · with charge := 1 })
      ({ · with charge := -1 }) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ by simp)).rewrite hwf
      (near_other hk)

/-- `phosphorusCleanup` at `c` rewrites near `c`. -/
lemma rewrite_phosphorusCleanup {w : Work} (hwf : WF w) (c : ℕ) :
    Rewrite w (w.phosphorusCleanup c) c := by
  rw [phosphorusCleanup_eq_ite]
  split
  · exact Rewrite.refl w c
  rcases hs : w.phosphorusScan c with ⟨_ | ⟨k, j⟩, _ | _⟩
  · exact Rewrite.refl w c
  · exact Rewrite.refl w c
  · exact Rewrite.refl w c
  · have hmem : (k, j) ∈ w.neighbors c := by
      rcases phosphorusScan_mem w _ _
        (congrArg Prod.fst ((phosphorusScan_eq w c).symm.trans hs)) with e | e
      · simp at e
      · exact e
    obtain ⟨hk, rfl⟩ := mem_neighbors hmem
    exact (local_kjc w hwf hk .single (by decide) ({ · with charge := 1 })
      ({ · with charge := -1 }) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ by simp)).rewrite hwf
      (near_other hk)

/-- `halogenCleanup` at `c` rewrites near `c`: each `=O` in turn, then `c` itself. -/
lemma rewrite_halogenCleanup {w : Work} (hwf : WF w) (c : ℕ) :
    Rewrite w (w.halogenCleanup c) c := by
  rw [halogenCleanup_eq_ite]
  split
  · exact Rewrite.refl w c
  have hfold : Rewrite w ((w.neighbors c).foldl halogenStep (w, 0)).1 c := by
    refine foldl_invariant (P := fun s : Work × ℤ ↦ Rewrite w s.1 c) _ (fun s x hx hs ↦ ?_)
      (Rewrite.refl w c)
    obtain ⟨hk, hj⟩ := mem_neighbors (j := x.2) hx
    have hk' : x.1 ∈ s.1.bondsOf c := hs.skel.mem_bondsOf.1 hk
    rw [halogenStep_eq]
    split
    · rw [hj, hs.skel.other x.1 c]
      exact hs.trans ((local_kj s.1 (hs.skel.wf hwf) hk' .single (by decide)
        ({ · with charge := -1 }) (fun _ ↦ rfl) (fun _ ↦ by simp)).rewrite (hs.skel.wf hwf)
        (near_other hk'))
    · exact hs
  exact hfold.trans ((local_c _ c
    ({ · with charge := ((w.neighbors c).foldl halogenStep (w, 0)).2 }) fun _ ↦ rfl).rewrite
    (hfold.skel.wf hwf) (Or.inl rfl))

/-- `cleanUpStep` at `c` rewrites near `c`. -/
lemma rewrite_cleanUpStep {w : Work} (hwf : WF w) (c : ℕ) : Rewrite w (cleanUpStep w c) c := by
  unfold cleanUpStep
  dsimp only
  split
  · exact rewrite_phosphorusCleanup hwf c
  · split
    · exact rewrite_halogenCleanup hwf c
    · exact Rewrite.refl w c

namespace AgreeNear

variable {w w' : Work} {c : ℕ} (h : AgreeNear w w' c)
include h

/-- `nitrogenOxideAt` at `c` keeps copies that agree near `c` agreeing there. -/
lemma nitrogenOxideAt : AgreeNear (w.nitrogenOxideAt c) (w'.nitrogenOxideAt c) c := by
  have hfind := h.find? (p := nitroO) fun x hx ↦ by
    simp only [Work.nitroO, (h.nbr hx).1, (h.nbr hx).2]
  unfold Work.nitrogenOxideAt
  rw [← hfind]
  rcases (w.neighbors c).find? w.nitroO with _ | ⟨k, j⟩
  · exact h
  · exact ((h.setKind k _).modifyAtom _ _).modifyAtom _ _

/-- `azideStep` at `c` keeps copies that agree near `c` agreeing there. -/
lemma azideStep : AgreeNear (w.azideStep c) (w'.azideStep c) c := by
  have hfind := h.find? (p := azideN) fun x hx ↦ by
    simp only [Work.azideN, (h.nbr hx).1, (h.nbr hx).2]
  rw [azideStep_eq, azideStep_eq, ← hfind]
  rcases (w.neighbors c).find? w.azideN with _ | ⟨k, j⟩
  · exact h
  · exact ((h.setKind k _).modifyAtom _ _).modifyAtom _ _

/-- Copies that agree near `c` give `phosphorusCleanup` the same guard at `c`. -/
lemma phosphorusGuard : w.phosphorusGuard c = w'.phosphorusGuard c := by
  simp only [Work.phosphorusGuard, h.sameAt.atom, h.sameAt.explicitValence, h.skel.degree]

/-- Copies that agree near `c` give `phosphorusScan` the same result at `c`. -/
lemma phosphorusScan : w.phosphorusScan c = w'.phosphorusScan c := by
  rw [phosphorusScan_eq, phosphorusScan_eq, ← h.skel.neighbors]
  refine List.foldl_ext _ _ _ fun s x hx ↦ ?_
  simp only [Work.phosphorusStep, (h.nbr hx).1, (h.nbr hx).2, h.skel.degree]

/-- `phosphorusCleanup` at `c` keeps copies that agree near `c` agreeing there. -/
lemma phosphorusCleanup : AgreeNear (w.phosphorusCleanup c) (w'.phosphorusCleanup c) c := by
  rw [phosphorusCleanup_eq_ite, phosphorusCleanup_eq_ite, ← h.phosphorusGuard, ← h.phosphorusScan]
  split
  · exact h
  rcases w.phosphorusScan c with ⟨_ | ⟨k, j⟩, _ | _⟩
  · exact h
  · exact h
  · exact h
  · exact ((h.setKind k _).modifyAtom _ _).modifyAtom _ _

/-- Copies that agree near `c` give `halogenCleanup` the same guard at `c`. -/
lemma halogenGuard : w.halogenGuard c = w'.halogenGuard c := by
  have hall : ((w.neighbors c).all fun x ↦ w.atoms[x.2]!.z == 8) =
      (w'.neighbors c).all fun x ↦ w'.atoms[x.2]!.z == 8 := by
    rw [← h.skel.neighbors, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact forall₂_congr fun x hx ↦ by rw [(h.nbr hx).1]
  rw [halogenGuard_eq, halogenGuard_eq, hall, h.sameAt.atom, h.sameAt.explicitValence]

/-- The halogen fold over bonds at `c` keeps copies that agree near `c` agreeing there, with the
same count. -/
lemma foldl_halogenStep (l : List (ℕ × ℕ)) (hl : ∀ x ∈ l, x.1 ∈ w.bondsOf c) (fc : ℤ) :
    AgreeNear (l.foldl halogenStep (w, fc)).1 (l.foldl halogenStep (w', fc)).1 c ∧
      (l.foldl halogenStep (w, fc)).2 = (l.foldl halogenStep (w', fc)).2 := by
  induction l generalizing w w' fc with
  | nil => exact ⟨h, rfl⟩
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons, halogenStep_eq, halogenStep_eq]
    dsimp only
    rw [← h.kind x.1 (hl x List.mem_cons_self)]
    split
    · exact ih ((h.setKind _ _).modifyAtom _ _)
        (fun y hy ↦ ((skel_setKind w _ _).trans (skel_modifyAtom _ _ _)).mem_bondsOf.1
          (hl y (List.mem_cons_of_mem _ hy))) _
    · exact ih h (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)) _

/-- `halogenCleanup` at `c` keeps copies that agree near `c` agreeing there. -/
lemma halogenCleanup : AgreeNear (w.halogenCleanup c) (w'.halogenCleanup c) c := by
  rw [halogenCleanup_eq_ite, halogenCleanup_eq_ite, ← h.halogenGuard, ← h.skel.neighbors]
  split
  · exact h
  · obtain ⟨h₁, h₂⟩ := h.foldl_halogenStep (w.neighbors c)
      (fun x hx ↦ (mem_neighbors (j := x.2) hx).1) 0
    rw [← h₂]
    exact h₁.modifyAtom _ _

/-- `cleanUpStep` at `c` keeps copies that agree near `c` agreeing there. -/
lemma cleanUpStep : AgreeNear (cleanUpStep w c) (cleanUpStep w' c) c := by
  unfold Work.cleanUpStep
  dsimp only
  rw [← h.sameAt.atom]
  split
  · exact h.phosphorusCleanup
  · split
    · exact h.halogenCleanup
    · exact h

end AgreeNear

/-- `nitroW` is a local step. -/
lemma localStep_nitroW : LocalStep nitroW where
  rewrite w c hwf := by
    unfold nitroW
    split
    · exact rewrite_nitrogenOxideAt hwf c
    · exact Rewrite.refl w c
  agree w w' c h := by
    unfold nitroW
    rw [← h.sameAt.nitroCand]
    split
    · exact h.nitrogenOxideAt
    · exact h

/-- `azideStep` is a local step. -/
lemma localStep_azideStep : LocalStep azideStep :=
  ⟨fun _ c hwf ↦ rewrite_azideStep hwf c, fun _ _ _ h ↦ h.azideStep⟩

/-- `cleanUpStep` is a local step. -/
lemma localStep_cleanUpStep : LocalStep cleanUpStep :=
  ⟨fun _ c hwf ↦ rewrite_cleanUpStep hwf c, fun _ _ _ h ↦ h.cleanUpStep⟩

/-- `nitroW` does nothing at an atom `cleanUp` may not rewrite. -/
lemma nitroW_of_not_center {w : Work} {c : ℕ} (hc : w.cleanUpCenter c = false) :
    nitroW w c = w := by
  unfold nitroW
  rw [if_neg fun h ↦ by simp [cleanUpCenter_of_nitroCand h] at hc]

/-- `cleanUpStep` does nothing at an atom `cleanUp` may not rewrite. -/
lemma cleanUpStep_of_not_center {w : Work} {c : ℕ} (hc : w.cleanUpCenter c = false) :
    cleanUpStep w c = w := by
  unfold cleanUpStep
  dsimp only
  split
  · rename_i hz
    rw [phosphorusCleanup_eq_ite, if_pos]
    by_contra hg
    simp only [phosphorusGuard, Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hg
    simp [Work.cleanUpCenter, hz, hg.1.1, hg.1.2] at hc
  · split
    · rename_i hz
      rw [halogenCleanup_eq_ite, if_pos]
      by_contra hg
      simp only [halogenGuard_eq, Bool.not_eq_true, Bool.or_eq_false_iff, bne_eq_false_iff_eq,
        Bool.not_eq_false'] at hg
      have hcen : w.cleanUpCenter c = true := by
        unfold Work.cleanUpCenter
        dsimp only
        rw [hz, hg.1.2, hg.1.1]
        simp
      rw [hcen] at hc
      cases hc
    · rfl

/-! ### Each step commutes with renumbering -/

section Relabel

variable {w : Work} {σ ψ : ℕ → ℕ}

/-- Rewriting a bond's kind commutes with renumbering the atoms. -/
lemma setKind_relabelW (k : ℕ) (o : BondKind) :
    (w.relabelW σ ψ).setKind k o = (w.setKind k o).relabelW σ ψ := by
  apply ext_work
  · rfl
  · apply array_ext_of_getElem! (n := w.bonds.size) (by simp [setKind, relabelW])
      (by simp [setKind, relabelW])
    intro j hj
    rw [bond_setKind, bond_relabelW hj,
      bond_relabelW (w := w.setKind k o) (by simpa [setKind] using hj), bond_setKind,
      relabelW_bonds_size]
    split <;> rfl

/-- Rewriting an atom commutes with renumbering the atoms. -/
lemma modifyAtom_relabelW (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} (hi : i < w.atoms.size)
    (F : WAtom → WAtom) :
    (w.relabelW σ ψ).modifyAtom (σ i) F = (w.modifyAtom i F).relabelW σ ψ := by
  apply ext_work
  · apply array_ext_of_getElem! (n := w.atoms.size) (by simp [modifyAtom]) (by simp [modifyAtom])
    intro j hj
    have hpj := hb.lt' j hj
    have e : (σ i = j ∧ j < w.atoms.size) ↔ (i = ψ j ∧ ψ j < w.atoms.size) :=
      ⟨fun h ↦ ⟨by rw [← h.1, hb.left i hi], hpj⟩, fun h ↦ ⟨by rw [h.1, hb.right j hj], hj⟩⟩
    rw [atom_modifyAtom, atom_relabelW' hj,
      atom_relabelW' (w := w.modifyAtom i F) (by simpa using hj), atom_modifyAtom,
      relabelW_atoms_size]
    by_cases h : σ i = j ∧ j < w.atoms.size
    · rw [if_pos h, if_pos (e.1 h)]
    · rw [if_neg h, if_neg fun h' ↦ h (e.2 h')]
  · rfl

/-- A bond rewritten and two atoms rewritten, all renumbered: the rewrites of `cleanUp`. -/
lemma rewrites_relabelW (hb : IdxBij w.numAtoms σ ψ) (k : ℕ) (o : BondKind) {i j : ℕ}
    (hi : i < w.atoms.size) (hj : j < w.atoms.size) (F G : WAtom → WAtom) :
    (((w.relabelW σ ψ).setKind k o).modifyAtom (σ i) F).modifyAtom (σ j) G =
      (((w.setKind k o).modifyAtom i F).modifyAtom j G).relabelW σ ψ := by
  rw [setKind_relabelW, modifyAtom_relabelW (w := w.setKind k o) hb hi,
    modifyAtom_relabelW (w := (w.setKind k o).modifyAtom i F) (by simpa using hb)
      (by simpa using hj)]

/-- `nitrogenOxideAt` commutes with renumbering: the first `=O` in bond order is the same one. -/
lemma nitrogenOxideAt_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).nitrogenOxideAt (σ i) = (w.nitrogenOxideAt i).relabelW σ ψ := by
  have hfind := find?_congr_mem (p := (w.relabelW σ ψ).nitroO ∘ fun e : ℕ × ℕ ↦ (e.1, σ e.2))
    (q := w.nitroO) (l := w.neighbors i) fun x hx ↦ nitroO_relabelW hwf hb hx
  unfold nitrogenOxideAt
  rw [neighbors_relabelW hwf hb hi, List.find?_map, hfind]
  rcases hf : (w.neighbors i).find? w.nitroO with _ | ⟨k, j⟩
  · rfl
  · exact rewrites_relabelW hb k .single hi (nbr_lt hwf (List.mem_of_find?_eq_some hf)).2 _ _

/-- `nitroW` commutes with renumbering. -/
lemma nitroW_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ} (hi : i < w.atoms.size) :
    nitroW (w.relabelW σ ψ) (σ i) = (nitroW w i).relabelW σ ψ := by
  unfold nitroW
  rw [nitroCand_relabelW hwf hb hi]
  split
  · exact nitrogenOxideAt_relabelW hwf hb hi
  · rfl

/-- `azideStep` commutes with renumbering: the first `#N` in bond order is the same one. -/
lemma azideStep_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).azideStep (σ i) = (w.azideStep i).relabelW σ ψ := by
  have hfind := find?_congr_mem (p := (w.relabelW σ ψ).azideN ∘ fun e : ℕ × ℕ ↦ (e.1, σ e.2))
    (q := w.azideN) (l := w.neighbors i) fun x hx ↦ azideN_relabelW hwf hb hx
  rw [azideStep_eq, azideStep_eq, neighbors_relabelW hwf hb hi, List.find?_map, hfind]
  rcases hf : (w.neighbors i).find? w.azideN with _ | ⟨k, j⟩
  · rfl
  · exact rewrites_relabelW hb k .double hi (nbr_lt hwf (List.mem_of_find?_eq_some hf)).2 _ _

/-- At a renamed atom `phosphorusScan` finds the same `=O`, renamed, and the same `=C`/`=N`
flag. -/
lemma phosphorusScan_relabelW_eq (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).phosphorusScan (σ i) =
      ((w.phosphorusScan i).1.map fun e ↦ (e.1, σ e.2), (w.phosphorusScan i).2) := by
  rw [phosphorusScan_eq, phosphorusScan_eq, neighbors_relabelW hwf hb hi, List.foldl_map]
  refine foldl_sim (fun (p q : Option (ℕ × ℕ) × Bool) ↦ q = (p.1.map fun e ↦ (e.1, σ e.2), p.2))
    _ _ _ _ _ rfl ?_
  rintro p q x hx rfl
  have hj := (nbr_lt hwf hx).2
  simp only [phosphorusStep, atom_relabelW hb hj, degree_relabelW hwf hb hj, kind_relabelW]
  split_ifs <;> rfl

/-- `phosphorusCleanup` commutes with renumbering. -/
lemma phosphorusCleanup_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).phosphorusCleanup (σ i) = (w.phosphorusCleanup i).relabelW σ ψ := by
  have hg : (w.relabelW σ ψ).phosphorusGuard (σ i) = w.phosphorusGuard i := by
    simp only [phosphorusGuard, atom_relabelW hb hi, explicitValence_relabelW hwf hb hi,
      degree_relabelW hwf hb hi]
  rw [phosphorusCleanup_eq_ite, phosphorusCleanup_eq_ite, hg, phosphorusScan_relabelW_eq hwf hb hi]
  split
  · rfl
  rcases hs : w.phosphorusScan i with ⟨_ | ⟨k, j⟩, _ | _⟩
  · rfl
  · rfl
  · rfl
  · have hmem : (k, j) ∈ w.neighbors i := by
      rcases phosphorusScan_mem w _ _
        (congrArg Prod.fst ((phosphorusScan_eq w i).symm.trans hs)) with e | e
      · simp at e
      · exact e
    exact rewrites_relabelW hb k .single (nbr_lt hwf hmem).2 hi _ _

/-- The halogen fold commutes with renumbering. -/
lemma foldl_halogenStep_relabelW (hb : IdxBij w.numAtoms σ ψ) (l : List (ℕ × ℕ))
    (hl : ∀ x ∈ l, x.2 < w.atoms.size) (fc : ℤ) :
    (l.map fun e ↦ (e.1, σ e.2)).foldl halogenStep (w.relabelW σ ψ, fc) =
      ((l.foldl halogenStep (w, fc)).1.relabelW σ ψ, (l.foldl halogenStep (w, fc)).2) := by
  induction l generalizing w fc with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, halogenStep_eq, halogenStep_eq]
    dsimp only
    rw [kind_relabelW]
    split
    · rw [setKind_relabelW, modifyAtom_relabelW (w := w.setKind x.1 .single) hb
        (hl x List.mem_cons_self)]
      exact ih (by simpa using hb) (fun y hy ↦ by simpa using hl y (List.mem_cons_of_mem _ hy)) _
    · exact ih hb (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)) _

/-- `halogenCleanup` commutes with renumbering. -/
lemma halogenCleanup_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    (w.relabelW σ ψ).halogenCleanup (σ i) = (w.halogenCleanup i).relabelW σ ψ := by
  have hall : ((w.neighbors i).all ((fun x ↦ (w.relabelW σ ψ).atoms[x.2]!.z == 8) ∘
      fun e ↦ (e.1, σ e.2))) = (w.neighbors i).all (fun x ↦ w.atoms[x.2]!.z == 8) := by
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    exact forall₂_congr fun y hy ↦ by
      simp only [Function.comp_apply, atom_relabelW hb (nbr_lt hwf hy).2]
  have hg : (w.relabelW σ ψ).halogenGuard (σ i) = w.halogenGuard i := by
    rw [halogenGuard_eq, halogenGuard_eq, neighbors_relabelW hwf hb hi, List.all_map, hall,
      atom_relabelW hb hi, explicitValence_relabelW hwf hb hi]
  rw [halogenCleanup_eq_ite, halogenCleanup_eq_ite, hg, neighbors_relabelW hwf hb hi,
    foldl_halogenStep_relabelW hb _ (fun x hx ↦ (nbr_lt hwf hx).2) 0]
  split
  · rfl
  · exact modifyAtom_relabelW (by simpa [numAtoms, foldl_halogenStep_size] using hb)
      (by simpa [foldl_halogenStep_size] using hi) _

/-- `cleanUpStep` commutes with renumbering. -/
lemma cleanUpStep_relabelW (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ) {i : ℕ}
    (hi : i < w.atoms.size) :
    cleanUpStep (w.relabelW σ ψ) (σ i) = (cleanUpStep w i).relabelW σ ψ := by
  unfold cleanUpStep
  dsimp only
  rw [atom_relabelW hb hi]
  split
  · exact phosphorusCleanup_relabelW hwf hb hi
  · split
    · exact halogenCleanup_relabelW hwf hb hi
    · rfl

end Relabel

/-! ### The order of the atoms does not matter -/

/-- Any two atoms `cleanUp` may rewrite are apart. -/
def CentersApart (w : Work) : Prop :=
  ∀ x y, x ≠ y → w.cleanUpCenter x = true → w.cleanUpCenter y = true → Apart w x y

/-- An atom `cleanUp` may rewrite is an atom of the copy. -/
lemma lt_size_of_cleanUpCenter {w : Work} {i : ℕ} (h : w.cleanUpCenter i = true) :
    i < w.atoms.size := by
  apply w.lt_size_of_z_ne_zero
  intro hz
  simp [Work.cleanUpCenter, hz] at h

/-- What the steps of `cleanUp` keep of the start `w₀`: its skeleton, and no atom to rewrite that
was not one at the start. -/
structure NoNewCenters (w₀ w : Work) : Prop where
  /-- The skeleton is that of `w₀`. -/
  skel : SameSkel w₀ w
  /-- An atom `cleanUp` may rewrite was one in `w₀`. -/
  center : ∀ x, w.cleanUpCenter x = true → w₀.cleanUpCenter x = true

/-- The start satisfies the invariant. -/
lemma NoNewCenters.refl (w : Work) : NoNewCenters w w := ⟨SameSkel.refl w, fun _ h ↦ h⟩

namespace NoNewCenters

variable {w₀ w : Work} {f : Work → ℕ → Work} (h : NoNewCenters w₀ w) (hwf : WF w₀)
  (hf : LocalStep f)
include h hwf hf

/-- A local step at an atom `cleanUp` could rewrite at the start keeps the invariant. -/
lemma step {c : ℕ} (hc : w₀.cleanUpCenter c = true) : NoNewCenters w₀ (f w c) := by
  have hr := hf.rewrite w c (h.skel.wf hwf)
  refine ⟨h.skel.trans hr.skel, fun x hx ↦ ?_⟩
  by_cases hxc : x = c
  · exact hxc ▸ hc
  · exact h.center x (hr.center hxc hx)

/-- Two local steps at atoms `cleanUp` could rewrite at the start commute. -/
lemma comm_of_center (hap : CentersApart w₀) {x y : ℕ} (hx : w₀.cleanUpCenter x = true)
    (hy : w₀.cleanUpCenter y = true) : f (f w x) y = f (f w y) x := by
  by_cases hxy : x = y
  · rw [hxy]
  · exact hf.comm hf (h.skel.wf hwf) (h.skel.apart (hap x y hxy hx hy))

variable (hoff : ∀ w c, w.cleanUpCenter c = false → f w c = w)
include hoff

/-- A local step that does nothing off the atoms `cleanUp` may rewrite keeps the invariant. -/
lemma step' (c : ℕ) : NoNewCenters w₀ (f w c) := by
  by_cases hc : w.cleanUpCenter c = true
  · exact h.step hwf hf (h.center c hc)
  · rw [hoff w c (by simpa using hc)]
    exact h

/-- At an atom `cleanUp` may not rewrite, the step still does nothing after a step elsewhere. -/
lemma step_off {x y : ℕ} (hxy : x ≠ y) (hx : w.cleanUpCenter x = false) : f (f w y) x = f w y := by
  refine hoff _ _ ?_
  by_contra hc
  have := (hf.rewrite w y (h.skel.wf hwf)).center hxy (by simpa using hc)
  rw [hx] at this
  cases this

/-- **Two steps commute** from any copy the passes of `cleanUp` reach: at two atoms it may
rewrite because these are apart, and otherwise because one of the steps does nothing. -/
lemma comm (hap : CentersApart w₀) (x y : ℕ) : f (f w x) y = f (f w y) x := by
  by_cases hxy : x = y
  · rw [hxy]
  by_cases hx : w.cleanUpCenter x = true
  · by_cases hy : w.cleanUpCenter y = true
    · exact h.comm_of_center hwf hf hap (h.center x hx) (h.center y hy)
    · have hy' : w.cleanUpCenter y = false := by simpa using hy
      rw [h.step_off hwf hf hoff (Ne.symm hxy) hy', hoff w y hy']
  · have hx' : w.cleanUpCenter x = false := by simpa using hx
    rw [hoff w x hx', h.step_off hwf hf hoff hxy hx']

/-- A step at another atom does not change whether an atom is a `nitroCand`. -/
lemma nitroCand_step (hap : CentersApart w₀) {x y : ℕ} (hxy : x ≠ y) :
    (f w x).nitroCand y = w.nitroCand y := by
  by_cases hx : w.cleanUpCenter x = true
  · have hr := hf.rewrite w x (h.skel.wf hwf)
    by_cases hy : w.cleanUpCenter y = true
    · exact (hr.agreeNear
        (h.skel.apart (hap x y hxy (h.center x hx) (h.center y hy)))).sameAt.nitroCand.symm
    · have h1 : w.nitroCand y = false := by
        by_contra hc
        exact hy (cleanUpCenter_of_nitroCand (by simpa using hc))
      have h2 : (f w x).nitroCand y = false := by
        by_contra hc
        exact hy (hr.center (Ne.symm hxy) (cleanUpCenter_of_nitroCand (by simpa using hc)))
      rw [h1, h2]
  · rw [hoff w x (by simpa using hx)]

end NoNewCenters

section Passes

variable {w₀ : Work} (hwf : WF w₀)
include hwf

/-- The first pass of `nitrogensCleanup` keeps the invariant, and remembers only atoms `cleanUp`
could rewrite at the start. -/
lemma foldl_nitroStep_inv (l : List ℕ) {s : Work × List ℕ} (hs : NoNewCenters w₀ s.1)
    (hc : ∀ i ∈ s.2, w₀.cleanUpCenter i = true) :
    NoNewCenters w₀ (l.foldl nitroStep s).1 ∧
      ∀ i ∈ (l.foldl nitroStep s).2, w₀.cleanUpCenter i = true := by
  refine foldl_invariant (P := fun s : Work × List ℕ ↦
    NoNewCenters w₀ s.1 ∧ ∀ i ∈ s.2, w₀.cleanUpCenter i = true) l (fun z x _ hz ↦ ?_) ⟨hs, hc⟩
  dsimp only at hz ⊢
  rw [nitroStep_fst_eq, nitroStep_snd]
  refine ⟨hz.1.step' hwf localStep_nitroW (fun _ _ ↦ nitroW_of_not_center) x, ?_⟩
  split
  · rename_i hx
    intro i hi
    rcases List.mem_append.1 hi with hi | hi
    · exact hz.2 i hi
    · rw [List.mem_singleton.1 hi]
      exact hz.1.center x (cleanUpCenter_of_nitroCand hx)
  · exact hz.2

/-- The second pass of `nitrogensCleanup` keeps the invariant. -/
lemma foldl_azideStep_inv (l : List ℕ) (hc : ∀ i ∈ l, w₀.cleanUpCenter i = true) {w : Work}
    (hw : NoNewCenters w₀ w) : NoNewCenters w₀ (l.foldl azideStep w) :=
  foldl_invariant l (fun _ x hx hz ↦ hz.step hwf localStep_azideStep (hc x hx)) hw

variable (hap : CentersApart w₀)
include hap

/-- **The first pass of `nitrogensCleanup` over a permuted list of atoms** gives the same working
copy, and the same nitrogens to revisit in another order. -/
lemma foldl_nitroStep_perm {l₁ l₂ : List ℕ} (hl : l₁.Perm l₂) {s : Work × List ℕ}
    (hs : NoNewCenters w₀ s.1) :
    (l₁.foldl nitroStep s).1 = (l₂.foldl nitroStep s).1 ∧
      (l₁.foldl nitroStep s).2.Perm (l₂.foldl nitroStep s).2 := by
  have hoff : ∀ w c, w.cleanUpCenter c = false → nitroW w c = w :=
    fun _ _ ↦ nitroW_of_not_center
  refine foldl_perm_rel (E := fun s t : Work × List ℕ ↦ s.1 = t.1 ∧ s.2.Perm t.2)
    (P := fun s ↦ NoNewCenters w₀ s.1) (A := fun _ ↦ True) (fun _ ↦ ⟨rfl, List.Perm.refl _⟩)
    (fun h₁ h₂ ↦ ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩) (fun z x _ hz ↦ ?_) (fun z z' x hzz ↦ ?_)
    (fun z x y _ _ hz ↦ ?_) hl s hs (fun _ _ ↦ trivial)
  · dsimp only at hz ⊢
    rw [nitroStep_fst_eq]
    exact hz.step' hwf localStep_nitroW hoff x
  · dsimp only at hzz ⊢
    rw [nitroStep_fst_eq, nitroStep_fst_eq, nitroStep_snd, nitroStep_snd, hzz.1]
    refine ⟨rfl, ?_⟩
    split
    · exact hzz.2.append_right _
    · exact hzz.2
  · dsimp only at hz
    simp only [nitroStep_fst_eq, nitroStep_snd]
    refine ⟨hz.comm hwf localStep_nitroW hoff hap x y, ?_⟩
    by_cases hxy : x = y
    · rw [hxy]
    · rw [hz.nitroCand_step hwf localStep_nitroW hoff hap hxy,
        hz.nitroCand_step hwf localStep_nitroW hoff hap (Ne.symm hxy)]
      split <;> split
      · rw [List.append_assoc, List.append_assoc]
        exact List.Perm.append_left _ (List.Perm.swap y x [])
      · exact List.Perm.refl _
      · exact List.Perm.refl _
      · exact List.Perm.refl _

/-- **The second pass of `nitrogensCleanup` gives the same copy in any order** of the nitrogens
it revisits. -/
lemma foldl_azideStep_perm {l₁ l₂ : List ℕ} (hl : l₁.Perm l₂)
    (hc : ∀ i ∈ l₁, w₀.cleanUpCenter i = true) {w : Work} (hw : NoNewCenters w₀ w) :
    l₁.foldl azideStep w = l₂.foldl azideStep w :=
  foldl_perm_rel (E := Eq) (P := NoNewCenters w₀) (A := fun i ↦ w₀.cleanUpCenter i = true)
    (fun _ ↦ rfl) (fun h₁ h₂ ↦ h₁.trans h₂) (fun _ _ hx hz ↦ hz.step hwf localStep_azideStep hx)
    (fun _ _ _ h ↦ by rw [h])
    (fun _ _ _ hx hy hz ↦ hz.comm_of_center hwf localStep_azideStep hap hx hy) hl w hw hc

/-- **The last pass of `cleanUp` gives the same copy in any order** of the atoms. -/
lemma foldl_cleanUpStep_perm {l₁ l₂ : List ℕ} (hl : l₁.Perm l₂) {w : Work}
    (hw : NoNewCenters w₀ w) :
    l₁.foldl cleanUpStep w = l₂.foldl cleanUpStep w :=
  foldl_perm_rel (E := Eq) (P := NoNewCenters w₀) (A := fun _ ↦ True) (fun _ ↦ rfl)
    (fun h₁ h₂ ↦ h₁.trans h₂)
    (fun _ x _ hz ↦ hz.step' hwf localStep_cleanUpStep (fun _ _ ↦ cleanUpStep_of_not_center) x)
    (fun _ _ _ h ↦ by rw [h])
    (fun _ x y _ _ hz ↦
      hz.comm hwf localStep_cleanUpStep (fun _ _ ↦ cleanUpStep_of_not_center) hap x y)
    hl w hw (fun _ _ ↦ trivial)

end Passes

/-! ### `cleanUp` commutes with renumbering -/

/-- Renumbering `0, …, n - 1` back and forth gives `0, …, n - 1`. -/
lemma IdxBij.map_map_range {n : ℕ} {σ ψ : ℕ → ℕ} (hb : IdxBij n σ ψ) :
    ((List.range n).map ψ).map σ = List.range n := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (List.range n)]
  exact List.map_congr_left fun i hi ↦ hb.right i (List.mem_range.1 hi)

/-- `0, …, n - 1` renumbered is `0, …, n - 1` in another order. -/
lemma IdxBij.perm_map_range {n : ℕ} {σ ψ : ℕ → ℕ} (hb : IdxBij n σ ψ) :
    ((List.range n).map ψ).Perm (List.range n) := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun j ↦ ?_
  · exact List.nodup_range.map_on fun a ha b hb' e ↦
      hb.symm.inj (List.mem_range.1 ha) (List.mem_range.1 hb') e
  · rw [List.mem_map, List.mem_range]
    exact ⟨fun ⟨i, hi, e⟩ ↦ e ▸ hb.lt' i (List.mem_range.1 hi),
      fun hj ↦ ⟨σ j, List.mem_range.2 (hb.lt j hj), hb.left j hj⟩⟩

section Folds

variable {σ ψ : ℕ → ℕ}

/-- **A pass of a local step over renumbered atoms** is the pass over the atoms, renumbered, when
each step commutes with renumbering. -/
lemma LocalStep.foldl_relabelW {f : Work → ℕ → Work} (hf : LocalStep f)
    (hrel : ∀ w i, w.WF → IdxBij w.numAtoms σ ψ → i < w.atoms.size →
      f (w.relabelW σ ψ) (σ i) = (f w i).relabelW σ ψ) :
    ∀ (l : List ℕ) (w : Work), w.WF → IdxBij w.numAtoms σ ψ → (∀ i ∈ l, i < w.atoms.size) →
      (l.map σ).foldl f (w.relabelW σ ψ) = (l.foldl f w).relabelW σ ψ
  | [], _, _, _, _ => rfl
  | i :: l, w, hwf, hb, hl => by
    have hs := (hf.rewrite w i hwf).skel
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, hrel w i hwf hb (hl i List.mem_cons_self)]
    exact hf.foldl_relabelW hrel l _ (hs.wf hwf) (hs.numAtoms ▸ hb) fun j hj ↦
      Nat.lt_of_lt_of_eq (hl j (List.mem_cons_of_mem _ hj)) hs.numAtoms

/-- The first pass of `nitrogensCleanup` over renumbered atoms is the pass over the atoms,
renumbered, the nitrogens to revisit included. -/
lemma foldl_nitroStep_relabelW :
    ∀ (l : List ℕ) (s : Work × List ℕ), s.1.WF → IdxBij s.1.numAtoms σ ψ →
      (∀ i ∈ l, i < s.1.atoms.size) →
      (l.map σ).foldl nitroStep (s.1.relabelW σ ψ, s.2.map σ) =
        ((l.foldl nitroStep s).1.relabelW σ ψ, (l.foldl nitroStep s).2.map σ)
  | [], _, _, _, _ => rfl
  | i :: l, s, hwf, hb, hl => by
    have hs := (localStep_nitroW.rewrite s.1 i hwf).skel
    have hi := hl i List.mem_cons_self
    have e : nitroStep (s.1.relabelW σ ψ, s.2.map σ) (σ i) =
        ((nitroStep s i).1.relabelW σ ψ, (nitroStep s i).2.map σ) := by
      refine Prod.ext ?_ ?_
      · rw [nitroStep_fst_eq, nitroStep_fst_eq]
        exact nitroW_relabelW hwf hb hi
      · rw [nitroStep_snd, nitroStep_snd]
        dsimp only
        rw [nitroCand_relabelW hwf hb hi]
        split <;> simp
    rw [← nitroStep_fst_eq] at hs
    rw [List.map_cons, List.foldl_cons, List.foldl_cons, e]
    exact foldl_nitroStep_relabelW l (nitroStep s i) (hs.wf hwf) (hs.numAtoms ▸ hb) fun j hj ↦
      Nat.lt_of_lt_of_eq (hl j (List.mem_cons_of_mem _ hj)) hs.numAtoms

end Folds

/-- `nitrogensCleanup` as its two passes. -/
lemma nitrogensCleanup_eq_foldl (w : Work) :
    w.nitrogensCleanup = ((List.range w.numAtoms).foldl nitroStep (w, [])).2.foldl azideStep
      ((List.range w.numAtoms).foldl nitroStep (w, [])).1 := rfl

section CleanUp

variable {w : Work} {σ ψ : ℕ → ℕ} (hwf : w.WF) (hb : IdxBij w.numAtoms σ ψ)
  (hap : CentersApart w)
include hwf hb hap

/-- **`nitrogensCleanup` commutes with renumbering** when the atoms `cleanUp` may rewrite are
apart, and it keeps the invariant. -/
lemma nitrogensCleanup_relabelW :
    (w.relabelW σ ψ).nitrogensCleanup = w.nitrogensCleanup.relabelW σ ψ ∧
      NoNewCenters w w.nitrogensCleanup := by
  have hlp : ((List.range w.numAtoms).map ψ).Perm (List.range w.numAtoms) := hb.perm_map_range
  have hlt : ∀ i ∈ (List.range w.numAtoms).map ψ, i < w.atoms.size := fun i hi ↦
    List.mem_range.1 (hlp.mem_iff.1 hi)
  have h1 := foldl_nitroStep_relabelW ((List.range w.numAtoms).map ψ) (w, []) hwf hb hlt
  rw [hb.map_map_range] at h1
  obtain ⟨e1, e2⟩ := foldl_nitroStep_perm hwf hap hlp (s := (w, [])) (NoNewCenters.refl w)
  obtain ⟨i1, c1⟩ := foldl_nitroStep_inv hwf ((List.range w.numAtoms).map ψ) (s := (w, []))
    (NoNewCenters.refl w) (by simp)
  have h2 := localStep_azideStep.foldl_relabelW (σ := σ) (ψ := ψ)
    (fun _ _ hwf' hb' hi' ↦ azideStep_relabelW hwf' hb' hi') _ _ (i1.skel.wf hwf)
    (i1.skel.numAtoms ▸ hb) fun i hi ↦
      Nat.lt_of_lt_of_eq (lt_size_of_cleanUpCenter (c1 i hi)) i1.skel.numAtoms
  rw [foldl_azideStep_perm hwf hap e2 c1 i1, e1] at h2
  rw [e1] at h1
  rw [nitrogensCleanup_eq_foldl, nitrogensCleanup_eq_foldl, numAtoms_relabelW]
  refine ⟨?_, foldl_azideStep_inv hwf _ (fun i hi ↦ c1 i (e2.mem_iff.2 hi)) (e1 ▸ i1)⟩
  rw [← h2]
  exact congrArg (fun p : Work × List ℕ ↦ p.2.foldl azideStep p.1) h1

/-- **`cleanUp` commutes with renumbering the atoms** when the atoms it may rewrite are apart:
each of its three passes visits the atoms in another order, which changes nothing. -/
theorem cleanUp_relabelW : (w.relabelW σ ψ).cleanUp = w.cleanUp.relabelW σ ψ := by
  obtain ⟨hN, i2⟩ := nitrogensCleanup_relabelW hwf hb hap
  have hn : w.nitrogensCleanup.numAtoms = w.numAtoms := i2.skel.numAtoms.symm
  have hlp : ((List.range w.numAtoms).map ψ).Perm (List.range w.numAtoms) := hb.perm_map_range
  have h3 := localStep_cleanUpStep.foldl_relabelW (σ := σ) (ψ := ψ)
    (fun _ _ hwf' hb' hi' ↦ cleanUpStep_relabelW hwf' hb' hi') ((List.range w.numAtoms).map ψ)
    w.nitrogensCleanup (i2.skel.wf hwf) (i2.skel.numAtoms ▸ hb) fun i hi ↦
      Nat.lt_of_lt_of_eq (List.mem_range.1 (hlp.mem_iff.1 hi)) i2.skel.numAtoms
  rw [hb.map_map_range, foldl_cleanUpStep_perm hwf hap hlp i2] at h3
  unfold cleanUp
  dsimp only
  rw [hN, numAtoms_relabelW, hn]
  exact h3

end CleanUp

end Work

open Work

variable {n : ℕ}

/-! ### From the molecule to its working copy -/

/-- Atoms joined in a molecule's working copy are atoms of the molecule, and joined in it. -/
lemma adj_of_adj_ofMolecule (m : Molecule n) {u v : ℕ} (h : (Work.ofMolecule m).Adj u v) :
    ∃ (hu : u < n) (hv : v < n), m.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨hk', hv⟩ := mem_neighbors hk
  have hlt : k < m.bonds.length := by
    rw [← ofMolecule_numBonds]
    exact lt_of_mem_bondsOf hk'
  have ht := touches_of_mem_bondsOf hk'
  rw [ofMolecule_bond m hlt] at ht hv
  simp only [toWBond, WBond.touches, WBond.other, Bool.or_eq_true, beq_iff_eq] at ht hv
  have hmem : m.bonds[k] ∈ m.bonds := List.getElem_mem hlt
  rcases ht with rfl | rfl
  · rw [if_pos rfl] at hv
    subst hv
    exact ⟨m.bonds[k].src.isLt, m.bonds[k].dst.isLt, (m.adj_iff _ _).2 ⟨_, hmem, rfl⟩⟩
  · rw [if_neg fun e ↦ m.bonds[k].ne (Fin.ext e)] at hv
    subst hv
    exact ⟨m.bonds[k].dst.isLt, m.bonds[k].src.isLt, (m.adj_iff _ _).2 ⟨_, hmem, Sym2.eq_swap⟩⟩

/-- **The hypothesis on molecules, as the working copy needs it**: when the atoms `cleanUp` may
rewrite in a Kekulé structure are apart, they are apart in the copy `cleanUp` runs on. -/
lemma centersApart_of_cleanUpTargetsApart {m : Molecule n} (hk : m.IsKekule)
    (ha : m.CleanUpTargetsApart) : CentersApart (Work.ofMolecule m).freezeHs := by
  intro x y hxy hx hy i hxi hyi
  rw [cleanUpCenter_freezeHs] at hx hy
  have hxn : x < n := by simpa [Work.ofMolecule] using lt_size_of_cleanUpCenter hx
  have hyn : y < n := by simpa [Work.ofMolecule] using lt_size_of_cleanUpCenter hy
  obtain ⟨h1, h2⟩ := ha ⟨x, hxn⟩ ⟨y, hyn⟩ (fun e ↦ hxy (congrArg Fin.val e))
    (cleanUpTarget_of_center m hk ⟨x, hxn⟩ hx) (cleanUpTarget_of_center m hk ⟨y, hyn⟩ hy)
  rw [← (skel_freezeHs _).near] at hxi hyi
  rcases hxi with hxi | hxi <;> rcases hyi with hyi | hyi
  · exact hxy (hxi.symm.trans hyi)
  · obtain ⟨_, _, hadj⟩ := adj_of_adj_ofMolecule m (hxi ▸ hyi)
    exact h1 hadj.symm
  · obtain ⟨_, _, hadj⟩ := adj_of_adj_ofMolecule m (hyi ▸ hxi)
    exact h1 hadj
  · obtain ⟨_, hi, hadj⟩ := adj_of_adj_ofMolecule m hxi
    obtain ⟨_, _, hadj'⟩ := adj_of_adj_ofMolecule m hyi
    exact h2 ⟨i, hi⟩ ⟨hadj, hadj'⟩

/-- **The copy `aromatize` kekulizes commutes with renumbering**, for a Kekulé structure whose
atoms `cleanUp` may rewrite are apart. -/
theorem prepare_relabel {m : Molecule n} (hk : m.IsKekule) (ha : m.CleanUpTargetsApart)
    (σ : Equiv.Perm (Fin n)) :
    Work.prepare (m.relabel σ) =
      (Work.prepare m).relabelW (finPermFun σ) (finPermFun σ.symm) := by
  have hwf0 := ofMolecule_wf m
  have hb0 : IdxBij (Work.ofMolecule m).numAtoms (finPermFun σ) (finPermFun σ.symm) := by
    rw [ofMolecule_numAtoms]
    exact idxBij_finPermFun σ
  have hsF := skel_freezeHs (Work.ofMolecule m)
  have hsC := (cleanRel_cleanUp (Work.ofMolecule m).freezeHs).skel
  unfold Work.prepare
  rw [ofMolecule_relabel, freezeHs_relabelW hwf0 hb0,
    cleanUp_relabelW (hsF.wf hwf0) (hsF.numAtoms ▸ hb0) (centersApart_of_cleanUpTargetsApart hk ha),
    cacheValences_relabelW (hsC.wf (hsF.wf hwf0)) (hsC.numAtoms ▸ hsF.numAtoms ▸ hb0)]

/-- The passes after kekulization, over the renumbered copy's own rings, give the renumbered
result. -/
lemma finish_relevantCycles_relabelW {w : Work} {σ ψ : ℕ → ℕ} (hwf : w.WF)
    (hb : IdxBij w.numAtoms σ ψ) :
    (w.relabelW σ ψ).finish (w.relabelW σ ψ).relevantCycles =
      (w.finish w.relevantCycles).relabelW σ ψ := by
  rw [← finish_relabelW hwf hb fun r hr x hx ↦
    WorkIso.IsRing.lt hwf (relevantCycles_isRing w r hr) x hx]
  simp only [Work.finish]
  rw [(workIso_relabelW hwf hb).setAromaticity_relevantCycles hwf (wf_relabelW hwf hb)
    (skel_assignRadicals _).bondBetween?.symm]

/-- **Property 3.** On Kekulé input, aromatizing commutes with renumbering the atoms, as long as
the atoms `cleanUp` rewrites are apart. A Kekulé structure needs no kekulizing, so `aromatize` is
`cleanUp` and passes that commute with renumbering; `cleanUp` commutes with it because its
rewrites, being apart, can be made in any order (`Work.cleanUp_relabelW`). -/
theorem aromatizeRelabelKekule : AromatizeRelabelKekule := by
  intro n m σ hk ha
  have hwfP := (wf_nbrsDistinct_prepare m).1
  have hnP : (Work.prepare m).atoms.size = n := Molecule.size_prepare_atoms m
  have hbP : IdxBij (Work.prepare m).numAtoms (finPermFun σ) (finPermFun σ.symm) := by
    rw [numAtoms, hnP]
    exact idxBij_finPermFun σ
  have hF := (Work.prepare m).afterRel_finish (Work.prepare m).relevantCycles
  have h₁ : m.aromatize = .ok (m.aromatizeOutput
      ((Work.prepare m).finish (Work.prepare m).relevantCycles)) :=
    Molecule.aromatize_eq_ok.mpr ⟨_, hk.kekulize_prepare, rfl⟩
  have h₂ : (m.relabel σ).aromatize = .ok ((m.relabel σ).aromatizeOutput
      ((Work.prepare (m.relabel σ)).finish (Work.prepare (m.relabel σ)).relevantCycles)) :=
    Molecule.aromatize_eq_ok.mpr ⟨_, (hk.relabel σ).kekulize_prepare, rfl⟩
  rw [h₁, h₂, prepare_relabel hk ha σ, finish_relevantCycles_relabelW hwfP hbP,
    Molecule.aromatizeOutput_relabel m (Molecule.wf_of_afterRel hwfP hF)
      (hF.atoms_size.trans hnP) σ]
  rfl

end LeanSMILES.Aromaticity

namespace LeanSMILES.Molecule

open Aromaticity

/-- The aromatic canonical SMILES of a Kekulé structure does not depend on how its atoms are
numbered, as long as the atoms `cleanUp` rewrites are apart. This is
`aromaticCanonicalSmiles_relabel` with property 3 proved. -/
theorem aromaticCanonicalSmiles_relabel_of_isKekule {n : ℕ} (m : Molecule n)
    (σ : Equiv.Perm (Fin n)) (hk : m.IsKekule) (ha : m.CleanUpTargetsApart) :
    (m.relabel σ).aromaticCanonicalSmiles = m.aromaticCanonicalSmiles :=
  aromaticCanonicalSmiles_relabel aromatizeRelabelKekule m σ hk ha

/-- **One aromatic canonical SMILES for every drawing.** Any two Kekulé structures related by
renumbering and resonance moves, in any order and either direction, have one aromatic canonical
SMILES, as long as the atoms `cleanUp` rewrites are apart. This is the bridge
`aromaticCanonicalSmiles_eq_of_eqvGen` with properties 2 and 3 proved. -/
theorem aromaticCanonicalSmiles_eq_of_eqvGen_redraw {n : ℕ} {m₁ m₂ : Molecule n}
    (hk : m₁.IsKekule) (ha : m₁.CleanUpTargetsApart) (h : Relation.EqvGen Redraw m₁ m₂) :
    m₁.aromaticCanonicalSmiles = m₂.aromaticCanonicalSmiles :=
  aromaticCanonicalSmiles_eq_of_eqvGen' aromatizeRelabelKekule hk ha h

end LeanSMILES.Molecule
