/-
Copyright (c) 2026 Samiha Sharlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samiha Sharlin
-/
module

public import LeanSMILES.Aromaticity.DonorDecide
public import LeanSMILES.Aromaticity.HsRestoreK

/-!
# LeanSMILES.Aromaticity.DonorFacts

What the decided swap check (`Loc.swap_ok`) gives about the records of an atom in two working
copies. A record whose cached valence is its Kekulé bond-order sum plus its written hydrogens, and
whose radicals are those `assignRadicals` gives it, reads like its canonical record (`Loc.canon`);
two such records with the same element, charge and hydrogen total are read alike by perception
(`Loc.readAlike`) when they write the same hydrogens, when the atom has more than three bonds or
takes no more than one bond, and in the two swaps of `swapCheck`.

## Main definitions

* `Loc.canonOf`, `Loc.Canonish`: the canonical record of a record, and the records that read
  like theirs.
* `Loc.rdCount`, `Loc.smCount`: RDKit's and OpenSMILES's hydrogen counts for a bare atom.
* `Loc.restoreAromCheck`, `Loc.bareRestoreCheck`: the `adjustHs` checks at an atom perception
  makes aromatic.

## Main statements

* `Loc.readAlike_rd`, `Loc.readAlike_sm`: the RDKit swap and the OpenSMILES swap.
* `Loc.restore_sm`, `Loc.restore_bare`: `adjustHs` gives back the hydrogens of an atom written
  bare and made aromatic.
* `Work.readAlike_of_swap`: perception reads an atom alike in two Kekulé copies.
-/

@[expose] public section

namespace LeanSMILES.Aromaticity

namespace Loc

/-- The canonical record of `x`, at bonds of kinds `ks`. -/
def canonOf (x : WAtom) (ks : List BondKind) : WAtom :=
  canon x.z x.charge (x.explicitHs + x.cachedImplicit) (bhs ks) x.explicitHs x.noImplicit

/-- A record as the witness argument meets it: the cached valence is the Kekulé bond-order sum
plus the written hydrogens, and the radicals are `assignRadicals`'s. -/
def Canonish (x : WAtom) (ks : List BondKind) : Prop :=
  cv x ks = bhs ks / 2 + x.explicitHs ∧
    x.radicals = if x.noImplicit && x.z != 0 then radC x.z x.charge (bhs ks / 2 + x.explicitHs)
      else 0

/-- RDKit's hydrogen count for a bare atom of element `z` and charge `c` at bond half-sum `h`. -/
def rdCount (z : ℕ) (c : ℤ) (h : ℕ) : ℕ :=
  impl { z := z, aromatic := false, charge := c, explicitHs := 0, noImplicit := false } h false

/-- OpenSMILES's hydrogen count for a bare atom of element `e` with bonds of kinds `sk`. -/
def smCount (e : Element) (sk : List BondKind) : ℕ :=
  Molecule.implicitHydrogens ({ element := some e, aromatic := sk.any (· == .aromatic) } : Atom)
    ((sk.map BondKind.order).sum)

/-- A `Canonish` record has the candidate verdicts and donor types of its canonical record. -/
lemma canon_read {x : WAtom} {ks : List BondKind} (h : Canonish x ks) :
    (∀ d, candD x ks d = candD (canonOf x ks) ks d) ∧
      ∀ w p r g, ringDonorL x ks w p r g = ringDonorL (canonOf x ks) ks w p r g := by
  obtain ⟨hcv, hr⟩ := h
  have hcv' : cv x ks = cv (canonOf x ks) ks := by rw [hcv]; rfl
  have hr' : x.radicals = (canonOf x ks).radicals := by rw [hr]; rfl
  have hi : x.cachedImplicit = (canonOf x ks).cachedImplicit := by simp [canonOf, canon]
  exact ⟨fun d ↦ candD_congr (a := x) (b := canonOf x ks) rfl rfl hi hr' ks hcv' d,
    fun w p r g ↦ ringDonorL_congr (a := x) (b := canonOf x ks) rfl rfl rfl hi hr' ks hcv' w p r g⟩

/-- Perception reads two `Canonish` records alike exactly when it reads their canonical records
alike. -/
lemma readAlike_canonOf {x y : WAtom} {ks : List BondKind} (hx : Canonish x ks)
    (hy : Canonish y ks) (w p r g : Bool) :
    readAlike x y ks w p r g = readAlike (canonOf x ks) (canonOf y ks) ks w p r g := by
  obtain ⟨cx, dx⟩ := canon_read hx
  obtain ⟨cy, dy⟩ := canon_read hy
  simp only [readAlike, cx, cy, dx, dy]

/-- Perception reads a record alike with itself. -/
lemma readAlike_self (a : WAtom) (ks : List BondKind) (w p r g : Bool) :
    readAlike a a ks w p r g = true := by
  unfold readAlike
  generalize ringDonorL a ks w p r g = d
  generalize candD a ks d = c
  cases c <;> cases d <;> rfl

/-- An environment is in `envs kk` when its exocyclic or ring multiple bond comes with a multiple
bond in `kk`, and a pulling atom with an exocyclic multiple bond. -/
lemma mem_envs {kk : List BondKind} {w p r g : Bool} (hm : (w || r) = true → kk.any isMultiple)
    (hp : p = true → w = true) : (w, p, r, g) ∈ envs kk := by
  simp only [envs, List.mem_filter]
  refine ⟨by cases w <;> cases p <;> cases r <;> cases g <;> decide, ?_⟩
  cases w <;> cases p <;> cases r <;> simp_all

/-- An element whose default valence is at most one gives no donor, in any environment. -/
lemma ringDonorL_none_of_dv {a : WAtom} {ks : List BondKind} (h : defaultValence a.z ≤ 1)
    (w p r g : Bool) : ringDonorL a ks w p r g = .none := by
  refine ringDonorL_none_of_elec ?_ w p r g
  unfold elec
  have : (defaultValence a.z : ℤ) ≤ 1 := by exact_mod_cast h
  simp only [Id.run, this, if_true]
  rfl

/-- Two records that both give no donor are read alike. -/
lemma readAlike_of_none {x y : WAtom} {ks : List BondKind} {w p r g : Bool}
    (hx : ringDonorL x ks w p r g = .none) (hy : ringDonorL y ks w p r g = .none) :
    readAlike x y ks w p r g = true := by
  unfold readAlike candD
  rw [hx, hy]
  rfl

/-- At more than three bonds, neither record is a donor. -/
lemma readAlike_of_deg {x y : WAtom} {ks : List BondKind} (h : 3 < ks.length) (w p r g : Bool) :
    readAlike x y ks w p r g = true :=
  readAlike_of_none (ringDonorL_none_of_deg (by omega) w p r g)
    (ringDonorL_none_of_deg (by omega) w p r g)

/-- An element that takes at most one bond is no donor. -/
lemma readAlike_of_dv {x y : WAtom} {ks : List BondKind} (h : defaultValence x.z ≤ 1)
    (hz : y.z = x.z) (w p r g : Bool) : readAlike x y ks w p r g = true :=
  readAlike_of_none (ringDonorL_none_of_dv h w p r g) (ringDonorL_none_of_dv (hz ▸ h) w p r g)

/-- **The RDKit swap**: hydrogens implied in the first copy, written in the second, RDKit's count
on the Kekulé bonds. -/
lemma readAlike_rd {e : Element} (he : e ∈ organic) {kk : List BondKind} (hkk : kk ∈ nonArom 3)
    (hlen : 2 ≤ kk.length) {c : ℤ} (hc : c = -1 ∨ c = 0 ∨ c = 1) {w p r g : Bool}
    (henv : (w, p, r, g) ∈ envs kk) :
    readAlike (canon e.atomicNumber c (rdCount e.atomicNumber c (bhs kk)) (bhs kk) 0 false)
      (canon e.atomicNumber c (rdCount e.atomicNumber c (bhs kk)) (bhs kk)
        (rdCount e.atomicNumber c (bhs kk)) true) kk w p r g = true := by
  have h := swap_ok
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (h e he) kk hkk
  unfold swapCheck at h2
  simp only [if_neg (by omega : ¬ kk.length < 2), Bool.and_eq_true, List.all_eq_true] at h2
  have hcm : c ∈ ([-1, 0, 1] : List ℤ) := by
    rcases hc with rfl | rfl | rfl <;> decide
  exact h2.1 c hcm (w, p, r, g) henv

/-- **The OpenSMILES swap**: hydrogens written in the first copy, implied in the second,
OpenSMILES's count on the bonds perception leaves. -/
lemma readAlike_sm {e : Element} (he : e ∈ organic) {kk : List BondKind} (hkk : kk ∈ nonArom 3)
    (hlen : 2 ≤ kk.length) {sk : List BondKind} (hsk : sk ∈ marks kk)
    (hrd : Molecule.readsDifferentlyInRDKit
      ({ element := some e, aromatic := sk.any (· == .aromatic) } : Atom)
      ((sk.map BondKind.order).sum) = false)
    (hd2 : sk.any (· == .aromatic) = true → sk.length = 2 →
      ((sk.zip kk).all fun sk ↦ sk.1 == .aromatic || !Work.isSD sk.2) = true)
    (hex : sk.any (· == .aromatic) = true → ∃ w' p' r' g', (w', p', r', g') ∈ envs kk ∧
      candD (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk
        (ringDonorL (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk
          w' p' r' g') = true)
    {w p r g : Bool} (henv : (w, p, r, g) ∈ envs kk) :
    readAlike (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true)
      (canon e.atomicNumber 0 (smCount e sk) (bhs kk) 0 false) kk w p r g = true := by
  have h := swap_ok
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (h e he) kk hkk
  unfold swapCheck at h2
  simp only [if_neg (by omega : ¬ kk.length < 2), Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.1 h2.2 sk hsk
  simp only [hrd, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h3
  rcases h3 with (⟨⟨har, hl⟩, hany⟩ | ⟨har, hno⟩) | hall
  · exfalso
    have := hd2 har hl
    rw [List.all_eq_true] at this
    obtain ⟨⟨s', k'⟩, hp, hpv⟩ := List.any_eq_true.1 hany
    have h2' := this _ hp
    revert hpv h2'
    cases s' <;> cases k' <;> decide
  · exfalso
    obtain ⟨w', p', r', g', hm, hc⟩ := hex har
    rw [Bool.not_eq_true', List.any_eq_false] at hno
    exact absurd hc (by simpa using hno _ hm)
  · exact List.all_eq_true.1 hall (w, p, r, g) henv

/-- `elec` reads the cached valence only through `cv`. -/
lemma elec_congr_cv {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (ks : List BondKind) (hcv : cv a ks = cv b ks) :
    elec a ks = elec b ks := by
  simp only [elec, hz, hc, he, hi, hr, hcv]

/-- `cand` reads the cached valence only through `cv`. -/
lemma cand_congr_cv {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (hi : a.cachedImplicit = b.cachedImplicit) (hr : a.radicals = b.radicals)
    (ks : List BondKind) (hcv : cv a ks = cv b ks) : cand a ks = cand b ks := by
  simp only [cand, hz, hc, hi, hr, hcv]

/-- `donorOk` reads the cached valence only through `cv`. -/
lemma donorOk_congr_cv {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hi : a.cachedImplicit = b.cachedImplicit)
    (hr : a.radicals = b.radicals) (ks : List BondKind) (hcv : cv a ks = cv b ks) :
    donorOk a ks = donorOk b ks := by
  simp only [donorOk, elec_congr_cv hz hc he hi hr ks hcv, hcv, he, hc]

/-- The canonical-record reading of `elec`, `cand` and `donorOk`. -/
lemma canon_gates {x : WAtom} {ks : List BondKind} (h : Canonish x ks) :
    elec x ks = elec (canonOf x ks) ks ∧ cand x ks = cand (canonOf x ks) ks ∧
      donorOk x ks = donorOk (canonOf x ks) ks := by
  obtain ⟨hcv, hr⟩ := h
  have hcv' : cv x ks = cv (canonOf x ks) ks := by rw [hcv]; rfl
  have hr' : x.radicals = (canonOf x ks).radicals := by rw [hr]; rfl
  have hi : x.cachedImplicit = (canonOf x ks).cachedImplicit := by simp [canonOf, canon]
  exact ⟨elec_congr_cv (a := x) (b := canonOf x ks) rfl rfl rfl hi hr' ks hcv',
    cand_congr_cv (a := x) (b := canonOf x ks) rfl rfl hi hr' ks hcv',
    donorOk_congr_cv (a := x) (b := canonOf x ks) rfl rfl rfl hi hr' ks hcv'⟩

/-- A bare record of element `z`, with `T` implicit hydrogens cached. -/
def bareRec (z T : ℕ) : WAtom :=
  { z := z, aromatic := false, charge := 0, explicitHs := 0, noImplicit := false,
    cachedImplicit := T }

/-- An atom bracketed in the kekulized copy and written bare in the witness's, made aromatic by
perception: on the witness's copy, the `adjustHs` step gives back its hydrogens. -/
def restoreAromCheck (e : Element) (kk : List BondKind) : Bool :=
  let z := e.atomicNumber
  let h := bhs kk
  (marks kk).all fun sk ↦
    let b : Atom := { element := some e, aromatic := sk.any (· == .aromatic) }
    let q : ℚ := ((sk.map BondKind.order).sum)
    let T := smCount e sk
    let aK := canon z 0 T h T true
    let a' := bareRec z T
    !sk.any (· == .aromatic) || decide (sk.length < 2) ||
      (sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) ||
      Molecule.readsDifferentlyInRDKit b q || decide (elec aK kk < 0) || !cand aK kk ||
      !donorOk aK kk || restore a' sk true

/-- `restoreAromCheck` holds at every organic-subset element and every list of at most three
non-aromatic bond kinds. -/
theorem restoreArom_ok : (organic.all fun e ↦ (nonArom 3).all (restoreAromCheck e)) = true := by
  decide +kernel

/-- A neutral bare record with OpenSMILES's count cached, made aromatic by perception where the
bracketed canonical record is a candidate donor: the `adjustHs` step gives back its hydrogens. -/
lemma restore_sm {e : Element} (he : e ∈ organic) {kk : List BondKind} (hkk : kk ∈ nonArom 3)
    {sk : List BondKind} (hsk : sk ∈ marks kk) (har : sk.any (· == .aromatic) = true)
    (hl : 2 ≤ sk.length)
    (hd2 : sk.length = 2 →
      ((sk.zip kk).all fun sk ↦ sk.1 == .aromatic || !Work.isSD sk.2) = true)
    (hrd : Molecule.readsDifferentlyInRDKit
      ({ element := some e, aromatic := sk.any (· == .aromatic) } : Atom)
      ((sk.map BondKind.order).sum) = false)
    (hel : 0 ≤ elec (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk)
    (hc : cand (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk = true)
    (hdo : donorOk (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk =
      true)
    {a : WAtom} (hz : a.z = e.atomicNumber) (hch : a.charge = 0) (he0 : a.explicitHs = 0)
    (hn : a.noImplicit = false) (hi : a.cachedImplicit = smCount e sk)
    (hadj : a.adjustHs = false) : restore a sk true = true := by
  have h := restoreArom_ok
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 (h e he) kk hkk) sk hsk
  rw [restore_congr (b := bareRec e.atomicNumber (smCount e sk)) hz hch he0 hn hi hadj]
  have g1 : decide (sk.length < 2) = false := by simp; omega
  have g2 : (sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) =
      false := by
    by_cases h2l : sk.length = 2
    · have := hd2 h2l
      rw [List.all_eq_true] at this
      rw [Bool.and_eq_false_iff]
      right
      rw [List.any_eq_false]
      intro ⟨s, k⟩ hp
      have h' := this _ hp
      revert h'
      cases s <;> cases k <;> decide
    · simp [h2l]
  have g3 : decide (elec (canon e.atomicNumber 0 (smCount e sk) (bhs kk) (smCount e sk) true) kk
      < 0) = false := by simpa using hel
  dsimp only at h2
  rw [har] at hrd
  simp only [har, Bool.not_true, Bool.false_or, Bool.or_false, g1, g2, hrd, g3, hc, hdo] at h2
  exact h2

/-- At an aromatic atom, `adjustHs` runs whatever the atom's own flag says. -/
lemma restore_congr_true {a b : WAtom} (hz : a.z = b.z) (hc : a.charge = b.charge)
    (he : a.explicitHs = b.explicitHs) (hn : a.noImplicit = b.noImplicit)
    (hi : a.cachedImplicit = b.cachedImplicit) (ks : List BondKind) :
    restore a ks true = restore b ks true := by
  have key : ∀ e : ℕ, impl { a with explicitHs := e } (bhs ks) true =
      impl { b with explicitHs := e } (bhs ks) true := fun e ↦
    impl_congr (a := { a with explicitHs := e }) (b := { b with explicitHs := e }) hz hc rfl hn _ _
  have h1 : impl a (bhs ks) true = impl b (bhs ks) true := impl_congr hz hc he hn _ _
  unfold restore
  simp only [h1, Bool.or_true, Bool.true_and]
  rw [key]
  simp only [he, hi]

/-- A bracketed atom gets no implicit hydrogens. -/
lemma impl_of_noImplicit {a : WAtom} (h : a.noImplicit = true) (b : ℕ) (ar : Bool) :
    impl a b ar = 0 := by
  simp [impl, h]

/-- A bracketed atom with no implicit hydrogen cached keeps its hydrogens. -/
lemma restore_of_noImplicit {a : WAtom} (h : a.noImplicit = true) (hi : a.cachedImplicit = 0)
    (ks : List BondKind) (ar : Bool) : restore a ks ar = true := by
  simp [restore, impl_of_noImplicit h, hi]

/-- Without the aromatic step, `adjustHs` gives back the count cached on the same bonds. -/
lemma restore_of_cached {a : WAtom} {ks : List BondKind} (hadj : a.adjustHs = false)
    (hi : a.cachedImplicit = impl a (bhs ks) false) : restore a ks false = true := by
  simp [restore, hadj, ← hi]

/-- Perception reads `b` and `a` alike when it reads `a` and `b` alike. -/
lemma readAlike_symm {a b : WAtom} {ks : List BondKind} {w p r g : Bool}
    (h : readAlike a b ks w p r g = true) : readAlike b a ks w p r g = true := by
  unfold readAlike at h ⊢
  generalize ringDonorL a ks w p r g = da at h ⊢
  generalize ringDonorL b ks w p r g = db at h ⊢
  generalize candD a ks da = ca at h ⊢
  generalize candD b ks db = cb at h ⊢
  cases ca <;> cases cb <;> cases da <;> cases db <;> revert h <;> decide

/-- A bare atom of a Kekulé input, with RDKit's count on its bonds, made aromatic by perception:
the `adjustHs` step gives back its hydrogens. -/
def bareRestoreCheck (e : Element) (kk : List BondKind) : Bool :=
  let z := e.atomicNumber
  let h := bhs kk
  let Tr := rdCount z 0 h
  let aB := canon z 0 Tr h 0 false
  (marks kk).all fun sk ↦
    !sk.any (· == .aromatic) || decide (sk.length < 2) ||
      (sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) ||
      decide (elec aB kk < 0) || !cand aB kk || !donorOk aB kk ||
      restore (bareRec z Tr) sk true

/-- `bareRestoreCheck` holds at every organic-subset element and every list of at most three
non-aromatic bond kinds. -/
theorem bareRestore_ok : (organic.all fun e ↦ (nonArom 3).all (bareRestoreCheck e)) = true := by
  decide +kernel

/-- A neutral bare record with RDKit's count on the Kekulé bonds cached, made aromatic by
perception where its canonical record is a candidate donor: `adjustHs` gives back its hydrogens. -/
lemma restore_bare {e : Element} (he : e ∈ organic) {kk : List BondKind} (hkk : kk ∈ nonArom 3)
    {sk : List BondKind} (hsk : sk ∈ marks kk) (har : sk.any (· == .aromatic) = true)
    (hl : 2 ≤ sk.length)
    (hd2 : sk.length = 2 →
      ((sk.zip kk).all fun sk ↦ sk.1 == .aromatic || !Work.isSD sk.2) = true)
    (hel : 0 ≤ elec (canon e.atomicNumber 0 (rdCount e.atomicNumber 0 (bhs kk)) (bhs kk) 0 false)
      kk)
    (hc : cand (canon e.atomicNumber 0 (rdCount e.atomicNumber 0 (bhs kk)) (bhs kk) 0 false) kk =
      true)
    (hdo : donorOk (canon e.atomicNumber 0 (rdCount e.atomicNumber 0 (bhs kk)) (bhs kk) 0 false)
      kk = true)
    {a : WAtom} (hz : a.z = e.atomicNumber) (hch : a.charge = 0) (he0 : a.explicitHs = 0)
    (hn : a.noImplicit = false) (hi : a.cachedImplicit = rdCount e.atomicNumber 0 (bhs kk))
    (hadj : a.adjustHs = false) : restore a sk true = true := by
  have h := bareRestore_ok
  rw [List.all_eq_true] at h
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 (h e he) kk hkk) sk hsk
  rw [restore_congr (b := bareRec e.atomicNumber (rdCount e.atomicNumber 0 (bhs kk))) hz hch he0
    hn hi hadj]
  have g1 : decide (sk.length < 2) = false := by simp; omega
  have g2 : (sk.length == 2 && (sk.zip kk).any fun (s, k) ↦ s != .aromatic && Work.isSD k) =
      false := by
    by_cases h2l : sk.length = 2
    · have := hd2 h2l
      rw [List.all_eq_true] at this
      rw [Bool.and_eq_false_iff]
      right
      rw [List.any_eq_false]
      intro ⟨s, k⟩ hp
      have h' := this _ hp
      revert h'
      cases s <;> cases k <;> decide
    · simp [h2l]
  have g3 : decide (elec (canon e.atomicNumber 0 (rdCount e.atomicNumber 0 (bhs kk)) (bhs kk) 0
      false) kk < 0) = false := by simpa using hel
  dsimp only at h2
  simp only [har, Bool.not_true, Bool.false_or, Bool.or_false, g1, g2, g3, hc, hdo] at h2
  exact h2

end Loc

namespace Work

/-- `assignRadicals` leaves an atom alone that is not in brackets or is `*`. -/
lemma assignRadicals_atom_of_skip (w : Work) {j : ℕ}
    (hj : (w.atoms[j]! : WAtom).noImplicit = false ∨ (w.atoms[j]! : WAtom).z = 0) :
    (w.assignRadicals.atoms[j]! : WAtom) = w.atoms[j]! := by
  unfold assignRadicals
  refine foldl_induction (fun x : Work ↦ (x.atoms[j]! : WAtom) = w.atoms[j]!) _ _ _ rfl ?_
  intro x i _ hx
  unfold radicalStep
  dsimp only
  split
  · exact hx
  · rename_i h
    by_cases hij : i = j
    · subst hij
      exfalso
      rcases hj with hj | hj <;> simp [hx, hj] at h
    · rw [modifyAtom_atom_of_ne x hij]
      exact hx

/-- The radicals `assignRadicals` gives an atom. -/
lemma radicals_assignRadicals_eq (w : Work) {i : ℕ} (hi : i < w.atoms.size) :
    (w.assignRadicals.atoms[i]! : WAtom).radicals =
      if (w.atoms[i]! : WAtom).noImplicit && (w.atoms[i]! : WAtom).z != 0 then
        Loc.radC (w.atoms[i]! : WAtom).z (w.atoms[i]! : WAtom).charge
          (w.bondHalfSum i / 2 + (w.atoms[i]! : WAtom).explicitHs)
      else (w.atoms[i]! : WAtom).radicals := by
  by_cases hn : (w.atoms[i]! : WAtom).noImplicit = true
  · by_cases hz : (w.atoms[i]! : WAtom).z = 0
    · rw [assignRadicals_atom_of_skip w (.inr hz)]; simp [hz]
    · rw [radicals_assignRadicals w hi hn hz, radicalCount_eq_loc]; simp [hn, hz]
  · rw [assignRadicals_atom_of_skip w (.inl (by simpa using hn))]; simp [hn]

/-- An atom whose exocyclic partner pulls electrons has an exocyclic multiple bond. -/
lemma whoS_of_pullsB {w : Work} {rbs : List ℕ} {i : ℕ} (h : w.pullsB rbs i = true) :
    w.whoS rbs i = true := by
  unfold pullsB at h
  unfold whoS
  cases hx : w.exocyclicMultiple? rbs i with
  | none => rw [hx] at h; cases h
  | some _ => rfl

/-- `exocyclicMultiple?` reads only the bonds of the working copy. -/
lemma exocyclicMultiple?_congr {w w' : Work} (hb : w'.bonds = w.bonds) (rbs : List ℕ) (i : ℕ) :
    w'.exocyclicMultiple? rbs i = w.exocyclicMultiple? rbs i := by
  simp only [exocyclicMultiple?, neighbors, bondsOf, numBonds, hb]

/-- `whoS` reads only the bonds of the working copy. -/
lemma whoS_congr {w w' : Work} (hb : w'.bonds = w.bonds) (rbs : List ℕ) (i : ℕ) :
    w'.whoS rbs i = w.whoS rbs i := by
  simp only [whoS, exocyclicMultiple?_congr hb]

/-- `pullsB` reads only the bonds and the atomic numbers of the working copy. -/
lemma pullsB_congr {w w' : Work} (hb : w'.bonds = w.bonds)
    (hz : ∀ j : ℕ, (w'.atoms[j]! : WAtom).z = (w.atoms[j]! : WAtom).z) (rbs : List ℕ) (i : ℕ) :
    w'.pullsB rbs i = w.pullsB rbs i := by
  simp only [pullsB, exocyclicMultiple?_congr hb, hz]

/-- `ringMultB` reads only the bonds of the working copy. -/
lemma ringMultB_congr {w w' : Work} (hb : w'.bonds = w.bonds) (rbs : List ℕ) (i : ℕ) :
    w'.ringMultB rbs i = w.ringMultB rbs i := by
  simp only [ringMultB, bondsOf, numBonds, hb]

/-- The environment of an atom is one `envs` lists. -/
lemma env_mem (w : Work) (rbs : List ℕ) (i : ℕ) (g : Bool) :
    (w.whoS rbs i, w.pullsB rbs i, w.ringMultB rbs i, g) ∈ Loc.envs (w.kindsAt i) := by
  refine Loc.mem_envs (fun h ↦ ?_) whoS_of_pullsB
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact any_isMultiple_of_whoS w rbs i h
  · exact any_isMultiple_of_ringMultB w rbs i h

/-- **Perception reads an atom alike in two Kekulé copies** whose records at it, before radicals,
write the same hydrogens, or swap them between written and implied at RDKit's count on the
Kekulé bonds (`Loc.readAlike_rd`). -/
theorem readAlike_of_swap {w w' : Work} (hb : w'.bonds = w.bonds) {i : ℕ}
    (hi : i < w.atoms.size) (hi' : i < w'.atoms.size) (hlen : 2 ≤ (w.kindsAt i).length)
    (hnoar : (w.kindsAt i).any (· == .aromatic) = false)
    (hzz : (w'.atoms[i]! : WAtom).z = (w.atoms[i]! : WAtom).z)
    (hcc : (w'.atoms[i]! : WAtom).charge = (w.atoms[i]! : WAtom).charge)
    (htot : w'.cachedTotalHs i = w.cachedTotalHs i)
    (hkek : (w.assignRadicals.cachedValence i : ℤ) -
      (w.assignRadicals.atoms[i]! : WAtom).explicitHs =
      ((w.bondHalfSum i / 2 : ℕ) : ℤ))
    (hkek' : (w'.assignRadicals.cachedValence i : ℤ) -
      (w'.assignRadicals.atoms[i]! : WAtom).explicitHs = ((w'.bondHalfSum i / 2 : ℕ) : ℤ))
    (hr0 : (w.atoms[i]! : WAtom).radicals = 0) (hr0' : (w'.atoms[i]! : WAtom).radicals = 0)
    (hcls : ((w'.atoms[i]! : WAtom).explicitHs = (w.atoms[i]! : WAtom).explicitHs ∧
        (w'.atoms[i]! : WAtom).noImplicit = (w.atoms[i]! : WAtom).noImplicit) ∨
      ∃ e ∈ Loc.organic, (w.atoms[i]! : WAtom).z = e.atomicNumber ∧
        (w.atoms[i]! : WAtom).charge = 0 ∧
        w.cachedTotalHs i = Loc.rdCount e.atomicNumber 0 (Loc.bhs (w.kindsAt i)) ∧
        (((w.atoms[i]! : WAtom).explicitHs = 0 ∧ (w.atoms[i]! : WAtom).noImplicit = false ∧
            (w'.atoms[i]! : WAtom).explicitHs = w.cachedTotalHs i ∧
            (w'.atoms[i]! : WAtom).noImplicit = true) ∨
          ((w'.atoms[i]! : WAtom).explicitHs = 0 ∧ (w'.atoms[i]! : WAtom).noImplicit = false ∧
            (w.atoms[i]! : WAtom).explicitHs = w.cachedTotalHs i ∧
            (w.atoms[i]! : WAtom).noImplicit = true)))
    (rbs : List ℕ) (big : Bool) :
    Loc.readAlike (w.assignRadicals.atoms[i]! : WAtom) (w'.assignRadicals.atoms[i]! : WAtom)
      (w.assignRadicals.kindsAt i) (w.assignRadicals.whoS rbs i) (w.assignRadicals.pullsB rbs i)
      (w.assignRadicals.ringMultB rbs i) big = true := by
  have hKk : w.assignRadicals.kindsAt i = w.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds]
  have hKk' : w'.assignRadicals.kindsAt i = w.kindsAt i := by
    simp only [Work.kindsAt, Work.bondsOf, Work.numBonds, Work.assignRadicals_bonds, hb]
  have hbh : w'.bondHalfSum i = w.bondHalfSum i := by
    simp only [Work.bondHalfSum, Work.bondsOf, Work.numBonds, hb]
  have eqK := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms w) i
  have eqP := Work.getElem!_eq_of_map_radicals (Work.getElem?_assignRadicals_atoms w') i
  have tK : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f (w.assignRadicals.atoms[i]! : WAtom) = f (w.atoms[i]! : WAtom) := by
    intro α f h2; rw [← h2, eqK, h2]
  have tP : ∀ {α : Type} (f : WAtom → α), (∀ x : WAtom, f { x with radicals := 0 } = f x) →
      f (w'.assignRadicals.atoms[i]! : WAtom) = f (w'.atoms[i]! : WAtom) := by
    intro α f h2; rw [← h2, eqP, h2]
  rw [hKk]
  set kk := w.kindsAt i with hkk
  set x := (w.assignRadicals.atoms[i]! : WAtom) with hx
  set y := (w'.assignRadicals.atoms[i]! : WAtom) with hy
  have hxz : x.z = (w.atoms[i]! : WAtom).z := tK WAtom.z (fun _ ↦ rfl)
  have hxc : x.charge = (w.atoms[i]! : WAtom).charge := tK WAtom.charge (fun _ ↦ rfl)
  have hxe : x.explicitHs = (w.atoms[i]! : WAtom).explicitHs := tK WAtom.explicitHs (fun _ ↦ rfl)
  have hxn : x.noImplicit = (w.atoms[i]! : WAtom).noImplicit := tK WAtom.noImplicit (fun _ ↦ rfl)
  have hxi : x.cachedImplicit = (w.atoms[i]! : WAtom).cachedImplicit :=
    tK WAtom.cachedImplicit (fun _ ↦ rfl)
  have hyz : y.z = (w'.atoms[i]! : WAtom).z := tP WAtom.z (fun _ ↦ rfl)
  have hyc : y.charge = (w'.atoms[i]! : WAtom).charge := tP WAtom.charge (fun _ ↦ rfl)
  have hye : y.explicitHs = (w'.atoms[i]! : WAtom).explicitHs := tP WAtom.explicitHs (fun _ ↦ rfl)
  have hyn : y.noImplicit = (w'.atoms[i]! : WAtom).noImplicit := tP WAtom.noImplicit (fun _ ↦ rfl)
  have hyi : y.cachedImplicit = (w'.atoms[i]! : WAtom).cachedImplicit :=
    tP WAtom.cachedImplicit (fun _ ↦ rfl)
  -- both records are canonical
  have hcx : Loc.Canonish x kk := by
    constructor
    · rw [Work.cachedValence_eq_loc, Work.bondHalfSum_eq_loc, hKk, ← hx, ← hkk] at hkek
      omega
    · rw [Work.radicals_assignRadicals_eq w hi, hr0, Work.bondHalfSum_eq_loc, ← hkk, ← hxz, ← hxc,
        ← hxe, ← hxn]
  have hcy : Loc.Canonish y kk := by
    constructor
    · rw [Work.cachedValence_eq_loc, hbh, Work.bondHalfSum_eq_loc, hKk', ← hy, ← hkk] at hkek'
      omega
    · rw [Work.radicals_assignRadicals_eq w' hi', hr0', hbh, Work.bondHalfSum_eq_loc, ← hkk,
        ← hyz, ← hyc, ← hye, ← hyn]
  have hzyx : y.z = x.z := by rw [hyz, hxz, hzz]
  have hcyx : y.charge = x.charge := by rw [hyc, hxc, hcc]
  have hxT : x.explicitHs + x.cachedImplicit = w.cachedTotalHs i := by rw [hxe, hxi]; rfl
  have htyx : y.explicitHs + y.cachedImplicit = x.explicitHs + x.cachedImplicit := by
    rw [hye, hyi, hxT, ← htot]; rfl
  by_cases hdeg : 3 < kk.length
  · exact Loc.readAlike_of_deg hdeg _ _ _ _
  by_cases hdv : defaultValence x.z ≤ 1
  · exact Loc.readAlike_of_dv hdv hzyx _ _ _ _
  have hkk3 : kk ∈ Loc.nonArom 3 := Loc.mem_nonArom 3 kk hnoar (by omega)
  have henv := Work.env_mem w.assignRadicals rbs i big
  rw [hKk] at henv
  rw [Loc.readAlike_canonOf hcx hcy]
  unfold Loc.canonOf
  rw [hzyx, hcyx, htyx, hxT]
  rcases hcls with ⟨he, hn⟩ |
    ⟨e, he, hez, hc0, hTr, ⟨hxe0, hxn0, hye1, hyn1⟩ | ⟨hye0, hyn0, hxe1, hxn1⟩⟩
  · rw [hye, hyn, he, hn, ← hxe, ← hxn]
    exact Loc.readAlike_self _ _ _ _ _ _
  · rw [hye, hyn, hye1, hyn1, hxe, hxn, hxe0, hxn0, hTr, hxz.trans hez, hxc.trans hc0]
    exact Loc.readAlike_rd he hkk3 hlen (.inr (.inl rfl)) henv
  · rw [hye, hyn, hye0, hyn0, hxe, hxn, hxe1, hxn1, hTr, hxz.trans hez, hxc.trans hc0]
    exact Loc.readAlike_symm (Loc.readAlike_rd he hkk3 hlen (.inr (.inl rfl)) henv)

end Work

end LeanSMILES.Aromaticity
