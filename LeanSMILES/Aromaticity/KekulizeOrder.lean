/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.KekulizeRelist

/-!
# LeanSMILES.Aromaticity.KekulizeOrder

Kekulization does not depend on the order of the rings

`kekulize` works through the fused ring systems in the order its ring list gives.  Two systems
can share atoms only where an atom has more than three bonds (`Work.fusedSystems_spec`); when no
such atom is aromatic with a bond written aromatic, kekulizing one system leaves alone everything
the other reads and writes, so the two commute (`Work.kekulizeSystem_comm`).  A system's result
also does not depend on the order in which its atoms are listed (`Work.kekulizeSystem_perm`).

## Main statements

* `Work.kekulizeSystem_perm`: a system's result does not depend on how its atoms are listed.
* `Work.kekulizeSystem_comm`: two fused systems commute when no atom aromatic with a bond written
  aromatic lies in both.
* `Work.components_ringsEquiv`: an equivalent ring list has the same fused systems, in some order.
* `Work.kekulize_ringsEquiv`: kekulization reads the ring list only up to equivalence.
* `Work.Relisted.walkRel`: a relisting relates the walks.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity.Work

/-! ### Same copy, related to itself -/

/-- A copy is related to itself, bonds not renumbered. -/
lemma WalkRel.refl (Q : ℕ → Prop) (m : Work) : WalkRel Q id id m m :=
  ⟨rfl, rfl, ⟨fun _ h ↦ h, fun _ h ↦ h, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩,
    fun _ _ ↦ .inl ⟨rfl, rfl⟩, fun _ _ ↦ by simp, fun _ ↦ by simp, fun _ _ _ ↦ rfl⟩

/-- A copy with the same bonds and atoms, its kinds agreeing where `Q` says. -/
lemma walkRel_id {Q : ℕ → Prop} {u v : Work} (hs : SameSkel u v) (ha : v.atoms = u.atoms)
    (hk : ∀ k < u.bonds.size, Q k → (v.bonds[k]! : WBond).kind = (u.bonds[k]! : WBond).kind) :
    WalkRel Q id id u v :=
  (WalkRel.refl (fun _ ↦ True) u).of_skel (SameSkel.refl u) hs ha hk

/-- Two bonds with the same endpoints and kind are equal. -/
lemma WBond.ext' {a b : WBond} (h1 : a.src = b.src) (h2 : a.dst = b.dst) (h3 : a.kind = b.kind) :
    a = b := by
  cases a; cases b; simp_all

/-- Two copies with the bonds and atoms of `u` and the same kinds are equal. -/
lemma eq_of_kinds {u r r' : Work} (hs : SameSkel u r) (hs' : SameSkel u r')
    (ha : r'.atoms = r.atoms)
    (hk : ∀ k < u.bonds.size, (r'.bonds[k]! : WBond).kind = (r.bonds[k]! : WBond).kind) :
    r' = r := by
  have e : r.bonds.size = u.bonds.size := hs.numBonds.symm
  have e' : r'.bonds.size = u.bonds.size := hs'.numBonds.symm
  refine ext_work ha (Array.ext (by rw [e, e']) fun i hi hi' ↦ ?_)
  have hiu : i < u.bonds.size := e' ▸ hi
  rw [← getElem!_pos r'.bonds i hi, ← getElem!_pos r.bonds i hi']
  exact WBond.ext' (by rw [← hs'.src, ← hs.src]) (by rw [← hs'.dst, ← hs.dst]) (hk i hiu)

/-! ### A system's atoms in any order -/

/-- `kekulizeSystem` is `kekSys` on the system's `systemAtoms`. -/
lemma kekulizeSystem_eq' (wa : ℕ → Bool) (ev0 : List ℕ) (rings : Array (List ℕ)) (out : Work)
    (system : List ℕ) :
    kekulizeSystem wa ev0 rings out system = kekSys wa ev0 out (systemAtoms rings system) := by
  unfold systemAtoms
  exact kekulizeSystem_eq wa ev0 rings out system

/-- **A system's result does not depend on how its atoms are listed.** -/
theorem kekulizeSystem_perm {wa : ℕ → Bool} {ev0 : List ℕ} {R R' : Array (List ℕ)}
    {out : Work} (hwf : WF out) (hnd : out.NbrsDistinct) {C C' : List ℕ}
    (hp : (systemAtoms R' C').Perm (systemAtoms R C)) :
    kekulizeSystem wa ev0 R' out C' = kekulizeSystem wa ev0 R out C := by
  have h := kekSys_rel (WalkRel.refl (fun _ ↦ True) out) (wa := wa) (wa' := wa)
    (fun _ _ ↦ rfl) (ev0 := ev0) (ev0' := ev0) hp fun _ _ _ ↦ rfl
  rw [kekulizeSystem_eq', kekulizeSystem_eq']
  revert h
  rcases hx : kekSys wa ev0 out (systemAtoms R C) with e | r <;>
    rcases hx' : kekSys wa ev0 out (systemAtoms R' C') with e' | r' <;> intro h
  · rw [show e' = e from h.symm]
  · exact h.elim
  · exact h.elim
  · have c1 := kekulizeSystem_correct hwf hnd (by rw [kekulizeSystem_eq']; exact hx)
    have c2 := kekulizeSystem_correct hwf hnd (by rw [kekulizeSystem_eq']; exact hx')
    rw [eq_of_kinds c1.2.1 c2.2.1 h.atoms fun k hk ↦ h.kind k
      (by have := c1.2.1.numBonds; simp only [numBonds] at this; omega) (.inl trivial)]

/-! ### Two systems commute -/

/-- The only error `kekSys` gives is "Can't kekulize mol". -/
lemma kekSys_error {wa : ℕ → Bool} {ev0 : List ℕ} {out : Work} {atoms : List ℕ} {e : String}
    (h : kekSys wa ev0 out atoms = .error e) : e = "Can't kekulize mol" := by
  unfold kekSys at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · cases h; rfl

/-- `SabSet` is the same on two copies with the same skeleton and atoms. -/
lemma SabSet.congr {wa : ℕ → Bool} {u a : Work} (hs : SameSkel u a) (ha : a.atoms = u.atoms)
    (X : List ℕ) (k : ℕ) : SabSet wa a X k ↔ SabSet wa u X k := by
  simp only [SabSet, ha, hs.bondsOf]

/-- What one system's result is: the input with the bonds `D` double and the other bonds written
aromatic at an aromatic atom of the system single; `D` lies among the latter, between aromatic
atoms of the system. -/
lemma kekSys_char {wa : ℕ → Bool} {ev0 : List ℕ} {R : Array (List ℕ)} {out r : Work}
    {C : List ℕ} (hwf : WF out) (hnd : out.NbrsDistinct)
    (h : kekSys wa ev0 out (systemAtoms R C) = .ok r) :
    r.atoms = out.atoms ∧ SameSkel out r ∧ ∃ D : ℕ → Prop,
      (∀ k, D k → SabSet wa out (systemAtoms R C) k ∧ ∀ x,
        (out.bonds[k]! : WBond).touches x = true →
          x ∈ systemAtoms R C ∧ (out.atoms[x]! : WAtom).aromatic = true) ∧
      ∀ k, ¬ D k → (r.bonds[k]! : WBond).kind =
        if SabSet wa out (systemAtoms R C) k then .single else (out.bonds[k]! : WBond).kind := by
  obtain ⟨ha, hs, D, hk, hD, -, -⟩ := kekulizeSystem_correct hwf hnd
    (by rw [kekulizeSystem_eq']; exact h)
  refine ⟨ha, hs, fun k ↦ D[k]! = true, fun k hd ↦ ?_, fun k hd ↦ ?_⟩
  · obtain ⟨hks, hw, hx⟩ := hD k hd
    have hts : (out.bonds[k]! : WBond).touches (out.bonds[k]! : WBond).src = true := by
      simp [WBond.touches]
    obtain ⟨hxs, hc⟩ := hx _ hts
    have har : ∀ x, ((out.atoms[x]! : WAtom).aromatic && out.needsDoubleBond wa ev0[x]! x) = true →
        (out.atoms[x]! : WAtom).aromatic = true := fun x h ↦ by
      simp only [Bool.and_eq_true] at h; exact h.1
    refine ⟨⟨_, hxs, har _ hc, List.mem_filter.2 ⟨List.mem_range.2 hks, hts⟩, hw⟩,
      fun x ht ↦ ⟨(hx x ht).1, har _ (hx x ht).2⟩⟩
  · rw [hk k, if_neg hd]
    rfl

/-- **A system's result depends only on what it reads**: two copies with the same bonds and atoms
whose kinds differ only on bonds written aromatic in `Y` give the same result where they agree or
the system rewrites. -/
lemma kekSys_det {wa : ℕ → Bool} {ev0 : List ℕ} {atoms : List ℕ} {u v : Work} {Y : ℕ → Prop}
    (hs : SameSkel u v) (ha : v.atoms = u.atoms) (hY : ∀ k, Y k → wa k = true)
    (hk : ∀ k < u.bonds.size, ¬ Y k → (v.bonds[k]! : WBond).kind = (u.bonds[k]! : WBond).kind) :
    ExRel (WalkRel (fun k ↦ ¬ Y k ∨ SabSet wa u atoms k) id id)
      (kekSys wa ev0 u atoms) (kekSys wa ev0 v atoms) := by
  refine kekSys_rel (walkRel_id hs ha hk) (fun _ _ ↦ rfl) (List.Perm.refl _) fun x _ _ ↦ ?_
  refine needsDoubleBond_congr ha (fun j ↦ by rw [hs.bondsOf]) fun k hw ↦ ?_
  by_cases hlt : k < u.bonds.size
  · exact hk k hlt fun hy ↦ hw (hY k hy)
  · have hv : ¬ k < v.bonds.size := by
      have := hs.numBonds; simp only [numBonds] at this; omega
    rw [getElem!_neg _ k hv, getElem!_neg _ k hlt]

/-- **Two fused systems commute** when no atom aromatic with a bond written aromatic lies in
both. -/
theorem kekulizeSystem_comm {wa : ℕ → Bool} {ev0 : List ℕ} {R : Array (List ℕ)} {u : Work}
    (hwf : WF u) (hnd : u.NbrsDistinct) {C1 C2 : List ℕ}
    (hdisj : ∀ z ∈ systemAtoms R C1, z ∈ systemAtoms R C2 →
      (u.atoms[z]! : WAtom).aromatic = true → ∀ k ∈ u.bondsOf z, wa k = false) :
    (kekulizeSystem wa ev0 R u C1).bind (fun v ↦ kekulizeSystem wa ev0 R v C2) =
      (kekulizeSystem wa ev0 R u C2).bind (fun v ↦ kekulizeSystem wa ev0 R v C1) := by
  simp only [kekulizeSystem_eq']
  have hSwa : ∀ X k, SabSet wa u X k → wa k = true := fun X k ⟨_, _, _, _, h⟩ ↦ h
  -- a system's result agrees with its input off the bonds it rewrites
  have hoff : ∀ {X : List ℕ} {C : List ℕ} {r : Work}, X = systemAtoms R C →
      kekSys wa ev0 u X = .ok r → ∀ k < u.bonds.size, ¬ SabSet wa u X k →
        (r.bonds[k]! : WBond).kind = (u.bonds[k]! : WBond).kind := by
    rintro X C r rfl h k _ hy
    obtain ⟨-, -, D, hD, hk⟩ := kekSys_char hwf hnd h
    rw [hk k (fun hd ↦ hy (hD k hd).1), if_neg hy]
  rcases ha : kekSys wa ev0 u (systemAtoms R C1) with e1 | a <;>
    rcases hb : kekSys wa ev0 u (systemAtoms R C2) with e2 | b
  · simp only [Except.bind]
    rw [kekSys_error ha, kekSys_error hb]
  · obtain ⟨hab, hsb, -⟩ := kekSys_char hwf hnd hb
    have hd := kekSys_det (atoms := systemAtoms R C1) (ev0 := ev0) hsb hab (hSwa _)
      (hoff rfl hb)
    rw [ha] at hd
    simp only [Except.bind]
    revert hd
    rcases kekSys wa ev0 b (systemAtoms R C1) with e | x <;> intro hd
    · have hd' : e1 = e := hd
      rw [hd']
    · exact hd.elim
  · obtain ⟨haa, hsa, -⟩ := kekSys_char hwf hnd ha
    have hd := kekSys_det (atoms := systemAtoms R C2) (ev0 := ev0) hsa haa (hSwa _)
      (hoff rfl ha)
    rw [hb] at hd
    simp only [Except.bind]
    revert hd
    rcases kekSys wa ev0 a (systemAtoms R C2) with e | y <;> intro hd
    · have hd' : e2 = e := hd
      rw [hd']
    · exact hd.elim
  · obtain ⟨haa, hsa, Da, hDa, hka⟩ := kekSys_char hwf hnd ha
    obtain ⟨hab, hsb, Db, hDb, hkb⟩ := kekSys_char hwf hnd hb
    have hdB := kekSys_det (atoms := systemAtoms R C2) (ev0 := ev0) hsa haa (hSwa _)
      (hoff rfl ha)
    have hdA := kekSys_det (atoms := systemAtoms R C1) (ev0 := ev0) hsb hab (hSwa _)
      (hoff rfl hb)
    rw [hb] at hdB
    rw [ha] at hdA
    simp only [Except.bind]
    revert hdB hdA
    rcases hy : kekSys wa ev0 a (systemAtoms R C2) with e3 | y <;>
      rcases hx : kekSys wa ev0 b (systemAtoms R C1) with e4 | x <;> intro hdB hdA
    · exact hdB.elim
    · exact hdB.elim
    · exact hdA.elim
    · obtain ⟨hya, hsy, Dy, hDy, hky⟩ := kekSys_char (hsa.wf hwf) (hsa.nbrsDistinct hnd) hy
      obtain ⟨hxb, hsx, Dx, hDx, hkx⟩ := kekSys_char (hsb.wf hwf) (hsb.nbrsDistinct hnd) hx
      have hSa := SabSet.congr (wa := wa) hsa haa
      have hSb := SabSet.congr (wa := wa) hsb hab
      congr 1
      refine (eq_of_kinds (hsa.trans hsy) (hsb.trans hsx) (by rw [hxb, hab, hya, haa])
        fun k hk ↦ ?_).symm
      have hka' : k < a.bonds.size := by have := hsa.numBonds; simp only [numBonds] at this; omega
      have hkb' : k < b.bonds.size := by have := hsb.numBonds; simp only [numBonds] at this; omega
      have eA := fun hq ↦ hdA.kind k hka' hq
      have eB := fun hq ↦ hdB.kind k hkb' hq
      simp only [id] at eA eB
      -- a bond rewritten by both systems is made single by both
      have hboth : ∀ {X Y : List ℕ} {w : Work} {Dr : ℕ → Prop},
          (∀ z ∈ X, z ∈ Y → (u.atoms[z]! : WAtom).aromatic = true → ∀ k ∈ u.bondsOf z,
            wa k = false) → SameSkel u w → w.atoms = u.atoms →
          (∀ k, Dr k → ∀ x, (w.bonds[k]! : WBond).touches x = true →
            x ∈ X ∧ (w.atoms[x]! : WAtom).aromatic = true) →
          SabSet wa u Y k → ¬ Dr k := by
        rintro X Y w Dr hXY hs hwa hD ⟨z, hzY, hzar, hkz, hwk⟩ hd
        have ht : (w.bonds[k]! : WBond).touches z = true := by
          rw [← hs.touches]; exact (List.mem_filter.1 hkz).2
        obtain ⟨hzX, -⟩ := hD k hd z ht
        rw [hXY z hzX hzY hzar k hkz] at hwk
        cases hwk
      have hdisj' : ∀ z ∈ systemAtoms R C2, z ∈ systemAtoms R C1 →
          (u.atoms[z]! : WAtom).aromatic = true → ∀ k ∈ u.bondsOf z, wa k = false :=
        fun z h2 h1 ↦ hdisj z h1 h2
      by_cases kA : SabSet wa u (systemAtoms R C1) k <;>
        by_cases kB : SabSet wa u (systemAtoms R C2) k
      · rw [hkx k (hboth hdisj hsb hab (fun k hd ↦ (hDx k hd).2) kB), if_pos ((hSb _ k).2 kA),
          hky k (hboth hdisj' hsa haa (fun k hd ↦ (hDy k hd).2) kA), if_pos ((hSa _ k).2 kB)]
      · rw [eA (.inl kB), hky k (fun hd ↦ kB ((hSa _ k).1 (hDy k hd).1)),
          if_neg (fun h ↦ kB ((hSa _ k).1 h))]
      · rw [eB (.inl kA), hkx k (fun hd ↦ kA ((hSb _ k).1 (hDx k hd).1)),
          if_neg (fun h ↦ kA ((hSb _ k).1 h))]
      · rw [eA (.inl kB), eB (.inl kA), hoff rfl ha k hk kA, hoff rfl hb k hk kB]

/-! ### The fused systems of an equivalent ring list -/

/-- `dfsComp` keeps every vertex already in the component. -/
lemma dfsComp_sub {nbrs : Array (List ℕ)} : ∀ (fuel : ℕ) (seen : Array Bool) (comp stack : List ℕ),
    ∀ x ∈ comp, x ∈ (dfsComp nbrs fuel (seen, comp, stack)).2
  | 0, _, _, _, x, hx => by unfold dfsComp; exact hx
  | _ + 1, _, _, [], x, hx => by unfold dfsComp; exact hx
  | fuel + 1, seen, comp, u :: rest, x, hx => by
    unfold dfsComp
    generalize nbrs[u]!.foldl pushNbr (seen, rest) = p
    obtain ⟨s', st'⟩ := p
    exact dfsComp_sub fuel _ _ _ x (List.mem_cons_of_mem _ hx)

/-- With fuel left, the vertex on top of the stack ends up in the component. -/
lemma dfsComp_root {nbrs : Array (List ℕ)} (fuel : ℕ) (seen : Array Bool) (comp rest : List ℕ)
    (u : ℕ) : u ∈ (dfsComp nbrs (fuel + 1) (seen, comp, u :: rest)).2 := by
  unfold dfsComp
  generalize nbrs[u]!.foldl pushNbr (seen, rest) = p
  obtain ⟨s', st'⟩ := p
  exact dfsComp_sub fuel _ _ _ u List.mem_cons_self

/-- Every component has a vertex. -/
lemma components_ne_nil {n : ℕ} {nbrs : Array (List ℕ)} {C : List ℕ}
    (hC : C ∈ components n nbrs) : C ≠ [] := by
  have key : ∀ (l : List ℕ) (st : Array Bool × List (List ℕ)), (∀ s ∈ l, s < n) →
      (∀ C ∈ st.2, C ≠ []) → ∀ C ∈ (l.foldl (componentsStep n nbrs) st).2, C ≠ [] := by
    intro l
    induction l with
    | nil => exact fun st _ h ↦ h
    | cons s l ih =>
      rintro ⟨seen, comps⟩ hl hc
      rw [List.foldl_cons]
      apply ih _ (fun s hs ↦ hl s (List.mem_cons_of_mem _ hs))
      have hs : s < n := hl s List.mem_cons_self
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have hmem := dfsComp_root (nbrs := nbrs) n' (seen.set! s true) [] [] s
      unfold componentsStep
      dsimp only
      rw [hn']
      generalize dfsComp nbrs (n' + 1) (seen.set! s true, [], [s]) = res at hmem
      obtain ⟨seen', comp'⟩ := res
      dsimp only at hmem ⊢
      split
      · exact hc
      · intro C hC
        rcases List.mem_append.1 hC with hC | hC
        · exact hc C hC
        · rw [List.mem_singleton] at hC
          subst hC
          exact List.ne_nil_of_mem (List.mem_mergeSort.2 hmem)
  unfold components at hC
  exact key _ _ (fun s hs ↦ List.mem_range.1 hs) (by simp) C hC

/-- Every ring `kekFusedNbrs` lists is a ring of the list. -/
lemma kekFusedNbrs_lt (m : Work) (R : Array (List ℕ)) :
    ∀ i : ℕ, ∀ j ∈ (m.kekFusedNbrs R)[i]!, j < R.size :=
  fun _ _ h ↦ (mem_kekFusedNbrs.1 h).2.1

/-- `kekFusedNbrs` is symmetric. -/
lemma kekFusedNbrs_symm (m : Work) (R : Array (List ℕ)) :
    ∀ i j : ℕ, j ∈ (m.kekFusedNbrs R)[i]! → i ∈ (m.kekFusedNbrs R)[j]! := fun i j h ↦ by
  obtain ⟨h1, h2, h3, k, hk1, hk2⟩ := mem_kekFusedNbrs.1 h
  exact mem_kekFusedNbrs.2 ⟨h2, h1, Ne.symm h3, k, hk2, hk1⟩

/-- On a symmetric graph on `[0, n)`, no component is listed twice. -/
lemma components_nodup {n : ℕ} {nbrs : Array (List ℕ)} (hlt : ∀ i : ℕ, ∀ j ∈ nbrs[i]!, j < n)
    (hsym : ∀ i j : ℕ, j ∈ nbrs[i]! → i ∈ nbrs[j]!) : (components n nbrs).Nodup :=
  (components_spec hlt hsym).2.1.imp_of_mem fun {C D} hC _ h e ↦ by
    subst e
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (components_ne_nil hC)
    exact h x hx hx

/-- **An equivalent ring list has the same fused systems**, in some order: matched systems have
the same atoms. -/
theorem components_ringsEquiv (m : Work) {R R' : Array (List ℕ)}
    (h : RingsEquiv R.toList R'.toList) :
    R'.size = R.size ∧ ∃ L2 : List (List ℕ),
      List.Forall₂ (fun C' D ↦ (systemAtoms R' C').Perm (systemAtoms R D))
        (components R'.size (m.kekFusedNbrs R')) L2 ∧
      L2.Perm (components R.size (m.kekFusedNbrs R)) := by
  obtain ⟨L, hf, hp⟩ := h
  obtain ⟨hlenL, hgetL⟩ := List.forall₂_iff_get.1 hf
  obtain ⟨σ, ψ, hb0, hidx⟩ := perm_index hp
  have hn : R'.size = R.size := by
    rw [← Array.length_toList, ← hp.length_eq, ← hlenL, Array.length_toList]
  have hLn : L.length = R.size := by rw [← hlenL, Array.length_toList]
  rw [hLn] at hb0
  set n := R.size
  -- matched rings
  have hre : ∀ i < n, RingEq R[σ i]! R'[i]! := by
    intro i hi
    have hσ := hb0.lt i hi
    rw [getElem!_eq_toList R', hidx i (hLn ▸ hi), getElem!_eq_toList R,
      getElem!_pos L _ (hLn ▸ hσ), getElem!_pos R.toList _ (by simpa using hσ)]
    exact hgetL _ (by simpa using hσ) (hLn ▸ hσ)
  set nb := m.kekFusedNbrs R
  set nb' := m.kekFusedNbrs R'
  have H : GraphIso n σ nb nb' := by
    intro i j
    rw [mem_kekFusedNbrs, mem_kekFusedNbrs, hn]
    constructor
    · rintro ⟨hi, hj, hne, k, hk1, hk2⟩
      refine ⟨hi, hj, hb0.lt i hi, hb0.lt j hj, fun e ↦ hne (hb0.inj hj hi e), k,
        ((hre i hi).ringBonds m).mem_iff.1 hk1, ((hre j hj).ringBonds m).mem_iff.1 hk2⟩
    · rintro ⟨hi, hj, -, -, hne, k, hk1, hk2⟩
      exact ⟨hi, hj, fun e ↦ hne (by rw [e]), k, ((hre i hi).ringBonds m).mem_iff.2 hk1,
        ((hre j hj).ringBonds m).mem_iff.2 hk2⟩
  have hlt := kekFusedNbrs_lt m R
  have hlt' : ∀ i : ℕ, ∀ j ∈ nb'[i]!, j < n := fun i j h ↦ hn ▸ kekFusedNbrs_lt m R' i j h
  have hsym := kekFusedNbrs_symm m R
  have hsym' := kekFusedNbrs_symm m R'
  rw [hn]
  refine ⟨rfl, ?_⟩
  obtain ⟨hcov, hdis, hin, -⟩ := components_spec hlt hsym
  obtain ⟨hcov', hdis', hin', -⟩ := components_spec hlt' hsym'
  have hex : ∀ C' ∈ components n nb', ∃ D ∈ components n nb, (C'.map σ).Perm D := by
    intro C' hC'
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (components_ne_nil hC')
    exact components_map hb0 H hlt hlt' hsym hsym' hC' hx
  classical
  let f : List ℕ → List ℕ := fun C' ↦
    if hh : ∃ D ∈ components n nb, (C'.map σ).Perm D then Classical.choose hh else []
  have hf' : ∀ C' ∈ components n nb', f C' ∈ components n nb ∧ (C'.map σ).Perm (f C') := by
    intro C' hC'
    simp only [f, dif_pos (hex C' hC')]
    exact Classical.choose_spec (hex C' hC')
  have hsymR : Symmetric fun C D : List ℕ ↦ ∀ x ∈ C, x ∉ D :=
    fun C D h x hx hx' ↦ h x hx' hx
  refine ⟨(components n nb').map f, ?_, ?_⟩
  · rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun C' hC' ↦ ?_
    obtain ⟨hD, hpD⟩ := hf' C' hC'
    refine (List.perm_ext_iff_of_nodup (nodup_eraseDups' _) (nodup_eraseDups' _)).2 fun x ↦ ?_
    change x ∈ systemAtoms R' C' ↔ x ∈ systemAtoms R (f C')
    rw [mem_systemAtoms, mem_systemAtoms]
    constructor
    · rintro ⟨i, hi, hx⟩
      have hin := hin' C' hC' i hi
      exact ⟨σ i, hpD.subset (List.mem_map_of_mem hi), ((hre i hin).mem x).1 hx⟩
    · rintro ⟨j, hj, hx⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (hpD.symm.subset hj)
      exact ⟨i, hi, ((hre i (hin' C' hC' i hi)).mem x).2 hx⟩
  · refine (List.perm_ext_iff_of_nodup ((components_nodup hlt' hsym').map_on ?_)
      (components_nodup hlt hsym)).2 fun D ↦ ?_
    · intro C1 h1 C2 h2 e
      by_contra hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (components_ne_nil h1)
      have hxD : σ x ∈ f C2 := e ▸ (hf' C1 h1).2.subset (List.mem_map_of_mem hx)
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 ((hf' C2 h2).2.symm.subset hxD)
      have := hb0.inj (hin' C2 h2 y hy) (hin' C1 h1 x hx) hyx
      subst this
      exact hdis'.forall hsymR h1 h2 hne y hx hy
    · rw [List.mem_map]
      constructor
      · rintro ⟨C', hC', rfl⟩
        exact (hf' C' hC').1
      · intro hD
        obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ (components_ne_nil hD)
        have hzn := hin D hD z hz
        obtain ⟨C', hC', hψ⟩ := hcov' (ψ z) (hb0.lt' z hzn)
        refine ⟨C', hC', ?_⟩
        obtain ⟨hD', hp'⟩ := hf' C' hC'
        have hzD' : z ∈ f C' := by
          have := hp'.subset (List.mem_map_of_mem hψ)
          rwa [hb0.right z hzn] at this
        by_contra hne
        exact hdis.forall hsymR hD' hD hne z hzD' hz

/-! ### Kekulization over an equivalent ring list -/

/-- Two `foldlM`s over lists related elementwise by `P` agree, if the steps agree on related
elements from every state satisfying `Inv`, and the second step keeps `Inv`. -/
lemma foldlM_forall₂ {α γ δ : Type} {f : α → γ → Except String α} {g : α → δ → Except String α}
    {P : γ → δ → Prop} (Inv : α → Prop) (hpres : ∀ a c b, Inv a → g a c = .ok b → Inv b)
    (hfg : ∀ a, Inv a → ∀ x y, P x y → f a x = g a y) :
    ∀ {l1 : List γ} {l2 : List δ}, List.Forall₂ P l1 l2 → ∀ a, Inv a →
      l1.foldlM f a = l2.foldlM g a
  | [], [], .nil, _, _ => rfl
  | x :: _, y :: _, .cons hxy h, a, ha => by
    rw [List.foldlM_cons, List.foldlM_cons, hfg a ha x y hxy]
    rcases hg : g a y with e | b
    · rfl
    · exact foldlM_forall₂ Inv hpres hfg h b (hpres a y b ha hg)

/-- A `foldlM` over a list without repeats does not depend on its order, if any two distinct steps
on elements satisfying `S` commute from every state satisfying `Inv`, and steps keep `Inv`. -/
lemma foldlM_perm_comm {α γ : Type} {f : α → γ → Except String α} (Inv : α → Prop)
    (S : γ → Prop) (hpres : ∀ a c b, Inv a → f a c = .ok b → Inv b)
    (hcomm : ∀ a, Inv a → ∀ x y, S x → S y → x ≠ y →
      (f a x).bind (f · y) = (f a y).bind (f · x)) {l1 l2 : List γ} (hp : l1.Perm l2) :
    l1.Nodup → (∀ x ∈ l1, S x) → ∀ a, Inv a → l1.foldlM f a = l2.foldlM f a := by
  induction hp with
  | nil => intros; rfl
  | cons x _ ih =>
    intro hnd hS a ha
    rw [List.foldlM_cons, List.foldlM_cons]
    rcases hx : f a x with e | b
    · rfl
    · exact ih (List.nodup_cons.1 hnd).2 (fun z hz ↦ hS z (List.mem_cons_of_mem _ hz)) b
        (hpres a x b ha hx)
  | swap x y l =>
    intro hnd hS a ha
    simp only [List.foldlM_cons]
    have hyx : y ≠ x := fun e ↦ (List.nodup_cons.1 hnd).1 (by rw [e]; exact List.mem_cons_self)
    have hc : (f a y >>= fun b ↦ f b x) = (f a x >>= fun b ↦ f b y) :=
      hcomm a ha y x (hS y List.mem_cons_self) (hS x (List.mem_cons_of_mem _ List.mem_cons_self))
        hyx
    rw [← bind_assoc, ← bind_assoc, hc]
  | trans h1 _ ih1 ih2 =>
    intro hnd hS a ha
    rw [ih1 hnd hS a ha]
    exact ih2 (h1.nodup_iff.1 hnd) (fun z hz ↦ hS z (h1.symm.subset hz)) a ha

/-- `clearAromatic` reads its ring-atom list only through membership. -/
lemma clearAromatic_congr {ra ra' : List ℕ} (h : ∀ x, ra'.contains x = ra.contains x) :
    clearAromatic ra' = clearAromatic ra := by
  funext out i
  unfold clearAromatic
  simp only [h]

/-- **Kekulization reads the ring list only up to equivalence**, when no atom aromatic with a
bond written aromatic has more than three bonds. -/
theorem kekulize_ringsEquiv {m : Work} {R R' : Array (List ℕ)} (hwf : WF m)
    (hnd : m.NbrsDistinct) (hr : ∀ ring ∈ R, m.IsRing ring)
    (hdeg : ∀ x, (m.atoms[x]! : WAtom).aromatic = true → (∃ k ∈ m.bondsOf x, m.kekWa k = true) →
      (m.bondsOf x).length ≤ 3)
    (h : RingsEquiv R.toList R'.toList) : m.kekulize R' = m.kekulize R := by
  obtain ⟨-, L2, hf2, hp2⟩ := components_ringsEquiv m h
  rw [kekulize_eq, kekulize_eq]
  split
  · rfl
  · let Inv : Work → Prop := fun out ↦ SameSkel m out ∧ out.atoms = m.atoms
    have hpres : ∀ a c b, Inv a → kekulizeSystem m.kekWa m.kekEv0 R a c = .ok b → Inv b := by
      rintro a c b ⟨hs, ha⟩ hb
      have := kekulizeSystem_correct (hs.wf hwf) (hs.nbrsDistinct hnd) hb
      exact ⟨hs.trans this.2.1, this.1.trans ha⟩
    have e1 : (components R'.size (m.kekFusedNbrs R')).foldlM
        (kekulizeSystem m.kekWa m.kekEv0 R') m = L2.foldlM (kekulizeSystem m.kekWa m.kekEv0 R) m :=
      foldlM_forall₂ (f := kekulizeSystem m.kekWa m.kekEv0 R')
        (g := kekulizeSystem m.kekWa m.kekEv0 R) Inv hpres (fun a ha _ _ hxy ↦
        kekulizeSystem_perm (ha.1.wf hwf) (ha.1.nbrsDistinct hnd) hxy) hf2 m
        ⟨SameSkel.refl m, rfl⟩
    have hSpw := (fusedSystems_spec m hr).2
    have hsymR : Symmetric fun C D : List ℕ ↦ ∀ x, x ∈ systemAtoms R C → x ∈ systemAtoms R D →
        3 < (m.bondsOf x).length := fun C D h x h1 h2 ↦ h x h2 h1
    have e2 : L2.foldlM (kekulizeSystem m.kekWa m.kekEv0 R) m =
        (components R.size (m.kekFusedNbrs R)).foldlM (kekulizeSystem m.kekWa m.kekEv0 R) m := by
      refine foldlM_perm_comm Inv (· ∈ components R.size (m.kekFusedNbrs R)) hpres
        (fun a ha C1 C2 h1 h2 hne ↦ kekulizeSystem_comm (ha.1.wf hwf) (ha.1.nbrsDistinct hnd)
          fun z hz1 hz2 hzar k hk ↦ ?_) hp2
        (hp2.nodup_iff.2 (components_nodup (kekFusedNbrs_lt m R) (kekFusedNbrs_symm m R)))
        (fun x hx ↦ hp2.subset hx) m ⟨SameSkel.refl m, rfl⟩
      have h3 := hSpw.forall hsymR h1 h2 hne z hz1 hz2
      rw [ha.2] at hzar
      rw [← ha.1.bondsOf] at hk
      by_contra hw
      have := hdeg z hzar ⟨k, hk, by simpa using hw⟩
      omega
    have hra : ∀ x, (R'.toList.flatten.eraseDups).contains x =
        (R.toList.flatten.eraseDups).contains x := by
      intro x
      rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem, List.mem_eraseDups,
        List.mem_eraseDups, List.mem_flatten, List.mem_flatten]
      constructor
      · rintro ⟨r', hr', hx⟩
        obtain ⟨r, hr, hrr⟩ := h.forall_exists r' hr'
        exact ⟨r, hr, (hrr.mem x).1 hx⟩
      · rintro ⟨r, hr, hx⟩
        obtain ⟨r', hr', hrr⟩ := h.exists_forall r hr
        exact ⟨r', hr', (hrr.mem x).2 hx⟩
    rw [e1, e2, clearAromatic_congr hra]

/-! ### Bridges to the pipeline -/

/-- A relisting, with no two bonds between the same atoms, relates the walks. -/
lemma Relisted.walkRel {w w' : Work} {π ρ : ℕ → ℕ} (h : Relisted w w' π ρ) (hwf : w.WF)
    (hnd : w.NbrsDistinct) (hnd' : w'.NbrsDistinct) : WalkRel (fun _ ↦ True) π ρ w w' :=
  ⟨h.atoms, h.size, h.bij, h.ends, fun u v ↦ h.bondBetween? hwf hnd hnd' u v,
    fun u ↦ by simpa [List.map_map, Function.comp_def] using (h.neighbors_perm hwf u).map Prod.snd,
    fun k hk _ ↦ h.kind k hk⟩

/-- Kekulization keeps which atoms each bond joins. -/
lemma skel_of_kindsRel {o w : Work} (h : KindsRel o w) : SameSkel o w :=
  ⟨by simp [numAtoms, h.atoms_size], by simp [numBonds, size_of_kindsRel h],
    fun k ↦ (ends_getElem! (size_of_kindsRel h) (ends_of_kindsRel h) k).1.symm,
    fun k ↦ (ends_getElem! (size_of_kindsRel h) (ends_of_kindsRel h) k).2.symm⟩

/-- A ring of `x` is a ring of any copy with the same skeleton. -/
lemma SameSkel.isRing {x y : Work} (hs : SameSkel x y) {c : List ℕ} (hc : x.IsRing c) :
    y.IsRing c := by
  have ha : ∀ u v, y.Adj u v ↔ x.Adj u v := fun u v ↦ by simp only [Adj, hs.neighbors]
  refine ⟨hc.nodup, hc.three, hc.chain.imp fun a b h' ↦ (ha a b).2 h', fun a ha' b hb ↦ ?_⟩
  exact (ha _ _).2 (hc.close a ha' b hb)

end LeanSMILES.Aromaticity.Work
