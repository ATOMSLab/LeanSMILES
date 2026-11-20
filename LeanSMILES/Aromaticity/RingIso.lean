/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.RingCands

/-!
# LeanSMILES.Aromaticity.RingIso

Renumbering atoms and bonds

A `Work.WorkIso` renames the atoms of a copy by `σ` and its bonds by `π` (inverses `ψ`, `ρ`):
the bond between `σ u` and `σ v` is `π` of the bond between `u` and `v`. Relabeling a molecule's
atoms is one (`π` the identity); relisting its bonds is another. Distances, shortest paths and
candidate cycles follow the renaming (`Work.WorkIso.dist`, `Work.WorkIso.cyclesFrom`), and a
ring's bonds are renamed by `π` (`Work.WorkIso.ringBonds`).

## Main definitions

* `Work.WorkIso`: a renaming of a copy's atoms and bonds that carries one copy to another.

## Main statements

* `Work.WorkIso.dist`: distances follow the renaming.
* `Work.WorkIso.pathOK`, `Work.WorkIso.cand`: shortest paths and candidates follow it.
* `Work.WorkIso.cyclesFrom`: the cycles found from a root follow it, up to `RingEq`.
* `Work.WorkIso.isRing`, `Work.WorkIso.ringBonds`: rings follow it, their bonds renamed by `π`.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Work

/-- A bond `bondBetween?` finds is in range. -/
lemma bondBetween?_lt {m : Work} {u v k : ℕ} (h : m.bondBetween? u v = some k) : k < m.numBonds :=
  List.mem_range.1 (List.mem_of_find?_eq_some h)

/-- On a copy without loops, two atoms are bonded exactly when `bondBetween?` finds a bond. -/
lemma adj_iff_bondBetween? {m : Work} (hwf : m.WF) (u v : ℕ) :
    m.Adj u v ↔ (m.bondBetween? u v).isSome := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := bondBetween?_of_adj h
    rw [hk]; rfl
  · intro h
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨hku, -, -⟩ := bondBetween?_spec hk
    have hne := (hwf k (bondBetween?_lt hk)).2.2
    refine ⟨k, List.mem_map.2 ⟨k, hku, ?_⟩⟩
    rcases bondBetween?_ends hk with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · simp [WBond.other, e1, e2]
    · have : v ≠ u := fun h ↦ hne (by rw [e1, e2, h])
      simp [WBond.other, e1, this]

/-- `w'` is `w` with atom `u` renamed `σ u` and bond `k` renamed `π k`. -/
structure WorkIso (w w' : Work) (σ ψ π ρ : ℕ → ℕ) : Prop where
  /-- `σ` and `ψ` are inverse renumberings of the atoms. -/
  atoms : IdxBij w.numAtoms σ ψ
  /-- `π` and `ρ` are inverse renumberings of the bonds. -/
  bonds : IdxBij w.numBonds π ρ
  /-- The two copies have the same number of atoms. -/
  natoms : w'.numAtoms = w.numAtoms
  /-- The two copies have the same number of bonds. -/
  nbonds : w'.numBonds = w.numBonds
  /-- The bond between `σ u` and `σ v` is `π` of the bond between `u` and `v`. -/
  bond : ∀ u v, u < w.numAtoms → v < w.numAtoms →
    w'.bondBetween? (σ u) (σ v) = (w.bondBetween? u v).map π

namespace WorkIso

variable {w w' : Work} {σ ψ π ρ : ℕ → ℕ}

/-- Renamed atoms are bonded exactly when the atoms are. -/
lemma adj (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {u v : ℕ}
    (hu : u < w.numAtoms) (hv : v < w.numAtoms) : w'.Adj (σ u) (σ v) ↔ w.Adj u v := by
  rw [adj_iff_bondBetween? hwf', adj_iff_bondBetween? hwf, I.bond u v hu hv, Option.isSome_map]

/-- The renaming read backwards. -/
lemma symm (I : WorkIso w w' σ ψ π ρ) : WorkIso w' w ψ σ ρ π := by
  refine ⟨I.natoms ▸ I.atoms.symm, I.nbonds ▸ I.bonds.symm, I.natoms.symm, I.nbonds.symm, ?_⟩
  intro u v hu hv
  rw [I.natoms] at hu hv
  have e := I.bond (ψ u) (ψ v) (I.atoms.lt' u hu) (I.atoms.lt' v hv)
  rw [I.atoms.right u hu, I.atoms.right v hv] at e
  rw [e, Option.map_map]
  cases hk : w.bondBetween? (ψ u) (ψ v) with
  | none => rfl
  | some k => simp [I.bonds.left k (bondBetween?_lt hk)]

/-- A walk renamed is a walk of the same length. -/
lemma walk (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r v d : ℕ}
    (h : w.Walk r v d) : w'.Walk (σ r) (σ v) d := by
  induction h with
  | refl => exact .refl
  | step _ hadj ih =>
    have hl := Adj.lt hwf hadj
    exact .step ih ((I.adj hwf hwf' hl.1 hl.2).2 hadj)

/-- There is a walk of `d` bonds between renamed atoms exactly when there is one between the
atoms. -/
lemma walk_iff (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r v d : ℕ}
    (hr : r < w.numAtoms) (hv : v < w.numAtoms) : w'.Walk (σ r) (σ v) d ↔ w.Walk r v d := by
  refine ⟨fun h ↦ ?_, I.walk hwf hwf'⟩
  have := I.symm.walk hwf' hwf h
  rwa [I.atoms.left r hr, I.atoms.left v hv] at this

/-- Renamed atoms are `d` bonds apart exactly when the atoms are. -/
lemma isDist_iff (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r v d : ℕ}
    (hr : r < w.numAtoms) (hv : v < w.numAtoms) :
    w'.IsDist (σ r) (σ v) d ↔ w.IsDist r v d := by
  unfold IsDist
  simp only [I.walk_iff hwf hwf' hr hv]

/-- **Distances follow the renaming.** -/
lemma dist (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r v : ℕ}
    (hr : r < w.numAtoms) (hv : v < w.numAtoms) :
    (w'.bfs (σ r)).1[σ v]! = (w.bfs r).1[v]! := by
  have hr' : σ r < w'.numAtoms := I.natoms ▸ I.atoms.lt r hr
  cases h : (w.bfs r).1[v]! with
  | none =>
    rw [bfs_dist_none hwf' hr']
    intro d hd
    exact (bfs_dist_none hwf hr v).1 h d ((I.walk_iff hwf hwf' hr hv).1 hd)
  | some d =>
    rw [bfs_dist hwf' hr', I.isDist_iff hwf hwf' hr hv]
    exact (bfs_dist hwf hr v d).1 h

/-- An atom the search from an in-range root gives a distance is in range. -/
lemma lt_of_dist {m : Work} (hwf : m.WF) {r x e : ℕ} (hr : r < m.numAtoms)
    (hx : (m.bfs r).1[x]! = some e) : x < m.numAtoms := by
  by_contra h
  rw [getElem!_neg _ x (by rw [(bfs_inv hwf hr).size]; exact h)] at hx
  cases hx

/-- Every atom of a shortest path from an in-range root is in range. -/
lemma PathOK.lt {m : Work} (hwf : m.WF) {r x d : ℕ} {p : List ℕ} (hr : r < m.numAtoms)
    (hp : m.PathOK (m.bfs r).1 r x d p) : ∀ a ∈ p, a < m.numAtoms := fun a ha ↦ by
  obtain ⟨i, -, hi⟩ := hp.dist_le ha
  exact lt_of_dist hwf hr hi

/-- **Shortest paths follow the renaming.** -/
lemma pathOK (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r x d : ℕ} {p : List ℕ}
    (hr : r < w.numAtoms) (hp : w.PathOK (w.bfs r).1 r x d p) :
    w'.PathOK (w'.bfs (σ r)).1 (σ r) (σ x) d (p.map σ) := by
  have hlt := PathOK.lt hwf hr hp
  refine ⟨by simp [hp.length], by simp [hp.head], by simp [hp.last], ?_, fun i hi ↦ ?_⟩
  · rw [List.isChain_map]
    exact hp.chain.imp_of_mem_imp fun a b ha hb h ↦ (I.adj hwf hwf' (hlt a ha) (hlt b hb)).2 h
  · simp only [List.getElem_map]
    rw [I.dist hwf hwf' hr (hlt _ (List.getElem_mem _))]
    exact hp.dist i (by simpa using hi)

end WorkIso

/-- `disjointTails p q` holds when no atom of `p.tail` is in `q.tail`. -/
lemma disjointTails_iff {p q : List ℕ} : disjointTails p q = true ↔ ∀ a ∈ p.tail, a ∉ q.tail := by
  simp only [disjointTails, List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.contains_eq_mem, decide_eq_false_iff_not]

/-- Renaming two paths by a map injective on their atoms keeps `disjointTails`. -/
lemma disjointTails_map {σ : ℕ → ℕ} {p q : List ℕ}
    (hinj : ∀ a ∈ p, ∀ b ∈ q, σ a = σ b → a = b) :
    disjointTails (p.map σ) (q.map σ) = disjointTails p q := by
  rw [Bool.eq_iff_iff, disjointTails_iff, disjointTails_iff, ← List.map_tail, ← List.map_tail]
  constructor
  · intro h a ha hq
    exact h _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hq)
  · intro h b hb hq
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    obtain ⟨a', ha', e⟩ := List.mem_map.1 hq
    rw [← hinj a (List.mem_of_mem_tail ha) a' (List.mem_of_mem_tail ha') e.symm] at ha'
    exact h a ha ha'

namespace WorkIso

variable {w w' : Work} {σ ψ π ρ : ℕ → ℕ}

/-- **Candidates follow the renaming.** -/
lemma cand (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r : ℕ} {c : List ℕ}
    (hr : r < w.numAtoms) (hc : w.Cand r c) : w'.Cand (σ r) (c.map σ) := by
  have hinj : ∀ {a b}, a < w.numAtoms → b < w.numAtoms → σ a = σ b → a = b :=
    fun ha hb e ↦ I.atoms.inj ha hb e
  rcases hc with ⟨x, y, dx, p, q, hx, hdx, hy, hxy, hp, hq, hdis, rfl⟩ |
    ⟨x, u₁, u₂, dx, p, q, hx, hdx, hx1, hx2, hne, hd1, hd2, hp, hq, hdis, rfl⟩
  · have hxl := lt_of_dist hwf hr hx
    have hyl := lt_of_dist hwf hr hy
    refine .inl ⟨σ x, σ y, dx, p.map σ, q.map σ, by rw [I.dist hwf hwf' hr hxl, hx], hdx,
      by rw [I.dist hwf hwf' hr hyl, hy], (I.adj hwf hwf' hxl hyl).2 hxy, I.pathOK hwf hwf' hr hp,
      I.pathOK hwf hwf' hr hq, ?_, by simp⟩
    rw [disjointTails_map fun a ha b hb e ↦
      hinj (PathOK.lt hwf hr hp a ha) (PathOK.lt hwf hr hq b hb) e]
    exact hdis
  · have hxl := lt_of_dist hwf hr hx
    have h1l := lt_of_dist hwf hr hd1
    have h2l := lt_of_dist hwf hr hd2
    refine .inr ⟨σ x, σ u₁, σ u₂, dx, p.map σ, q.map σ, by rw [I.dist hwf hwf' hr hxl, hx], hdx,
      (I.adj hwf hwf' hxl h1l).2 hx1, (I.adj hwf hwf' hxl h2l).2 hx2,
      fun e ↦ hne (hinj h1l h2l e), by rw [I.dist hwf hwf' hr h1l, hd1],
      by rw [I.dist hwf hwf' hr h2l, hd2], I.pathOK hwf hwf' hr hp, I.pathOK hwf hwf' hr hq, ?_,
      by simp⟩
    rw [disjointTails_map fun a ha b hb e ↦
      hinj (PathOK.lt hwf hr hp a ha) (PathOK.lt hwf hr hq b hb) e]
    exact hdis

/-- **The cycles found from a root follow the renaming**, perhaps started elsewhere and run the
other way. -/
theorem cyclesFrom (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {r : ℕ} {c : List ℕ}
    (hr : r < w.numAtoms) (hc : c ∈ w.cyclesFrom r) :
    ∃ c' ∈ w'.cyclesFrom (σ r), RingEq (c.map σ) c' :=
  exists_mem_cyclesFrom_of_cand hwf' (I.natoms ▸ I.atoms.lt r hr)
    (I.cand hwf hwf' hr (cand_of_mem_cyclesFrom w hr hc))

/-- On a well-formed copy, every atom of a ring is in range. -/
lemma IsRing.lt {m : Work} (hwf : m.WF) {c : List ℕ} (hc : m.IsRing c) :
    ∀ a ∈ c, a < m.numAtoms := fun a ha ↦ by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  have := (Adj.lt hwf (hc.adj_get ht)).1
  rwa [getElem!_pos c t ht] at this

/-- **Rings follow the renaming.** -/
lemma isRing (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) (hwf' : w'.WF) {c : List ℕ}
    (hc : w.IsRing c) : w'.IsRing (c.map σ) := by
  have hlt := IsRing.lt hwf hc
  refine ⟨hc.nodup.map_on fun a ha b hb e ↦ I.atoms.inj (hlt a ha) (hlt b hb) e,
    by simpa using hc.three, ?_, ?_⟩
  · rw [List.isChain_map]
    exact hc.chain.imp_of_mem_imp fun a b ha hb h ↦ (I.adj hwf hwf' (hlt a ha) (hlt b hb)).2 h
  · intro a ha b hb
    rw [List.getLast?_map] at ha
    rw [List.head?_map] at hb
    obtain ⟨a', ha', rfl⟩ := Option.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Option.mem_map.1 hb
    exact (I.adj hwf hwf' (hlt a' (List.mem_of_getLast? ha'))
      (hlt b' (List.mem_of_mem_head? hb'))).2 (hc.close a' ha' b' hb')

/-- **A ring's bonds are renamed by `π`.** -/
lemma ringBonds (I : WorkIso w w' σ ψ π ρ) (hwf : w.WF) {c : List ℕ} (hc : w.IsRing c) :
    w'.ringBonds (c.map σ) = (w.ringBonds c).map π := by
  have hlt := IsRing.lt hwf hc
  rw [ringBonds_eq_filterMap, ringBonds_eq_filterMap, List.length_map, List.map_filterMap]
  apply List.filterMap_congr
  intro t ht
  rw [List.mem_range] at ht
  have h1 : t < c.length := ht
  have h2 : (t + 1) % c.length < c.length := Nat.mod_lt _ (by omega)
  rw [getElem!_pos _ t (by simpa using h1), getElem!_pos _ _ (by simpa using h2),
    List.getElem_map, List.getElem_map, I.bond _ _ (hlt _ (List.getElem_mem _))
      (hlt _ (List.getElem_mem _)), ← getElem!_pos c t h1, ← getElem!_pos c _ h2]

end WorkIso

end Work

end LeanSMILES.Aromaticity
