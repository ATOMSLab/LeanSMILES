/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases

/-!
# LeanSMILES.Chem.Stereo

A tetrahedral configuration as a quotient: the four ligands of a centre,
listed in some order, up to **even** permutations of the list.

SMILES writes `@` when, looking from the first listed ligand, the other three
run anticlockwise.  Swapping any two ligands in the list turns `@` into `@@`;
a 3-cycle of the last three is a rotation about the first and changes nothing.
In general a reordering `π` keeps the mark exactly when `Equiv.Perm.sign π = 1`
— which is a theorem here, `isAnticlockwise_comp`, not a convention.  So the
configuration *is* the class of `@`-orderings under the alternating group, and
the mark a writer must emit for any listing it chooses is decided by that
class (`isAnticlockwise`).

Ligands are `Option (Fin n)`: an atom of the molecule, or `none` for the
centre's implicit hydrogen or lone pair.  A listing with distinct ligands has
exactly two classes, one per hand (`mirror_ne`, `eq_or_eq_mirror`).

Relabeling the atoms acts on the ligands, not on their order, so it commutes
with the quotient (`map`), and the mark is label-independent
(`isAnticlockwise_map`) — the property canonical SMILES needs.
-/

@[expose] public section

namespace LeanSMILES

open Equiv

variable {n : ℕ}

/-- The four ligands of a tetrahedral centre, listed in some order: atoms, or
`none` for an implicit hydrogen or a lone pair. -/
abbrev Ligands (n : ℕ) := Fin 4 → Option (Fin n)

namespace Ligands

/-- Same hand: some even permutation of the listing `o` gives the listing `o'`. -/
def SameHand (o o' : Ligands n) : Prop := ∃ π : Perm (Fin 4), Perm.sign π = 1 ∧ o' = o ∘ π

lemma SameHand.refl (o : Ligands n) : SameHand o o := ⟨1, by simp, rfl⟩

lemma SameHand.symm {o o' : Ligands n} : SameHand o o' → SameHand o' o := by
  rintro ⟨π, hπ, rfl⟩
  refine ⟨π⁻¹, by simpa using hπ, ?_⟩
  funext k
  simp

lemma SameHand.trans {o o' o'' : Ligands n} : SameHand o o' → SameHand o' o'' → SameHand o o'' := by
  rintro ⟨π, hπ, rfl⟩ ⟨ρ, hρ, rfl⟩
  exact ⟨π * ρ, by simp [hπ, hρ], rfl⟩

/-- Listings of the same hand. -/
instance setoid : Setoid (Ligands n) := ⟨SameHand, ⟨SameHand.refl, SameHand.symm, SameHand.trans⟩⟩

instance : DecidableRel (SameHand (n := n)) := fun o o' ↦
  inferInstanceAs (Decidable (∃ π : Perm (Fin 4), Perm.sign π = 1 ∧ o' = o ∘ π))

instance : DecidableRel (α := Ligands n) (· ≈ ·) :=
  inferInstanceAs (DecidableRel (SameHand (n := n)))

lemma sameHand_iff {o o' : Ligands n} : o ≈ o' ↔ SameHand o o' := Iff.rfl

/-- Reordering by `π` keeps the hand when `π` is even. -/
lemma sameHand_comp (o : Ligands n) {π : Perm (Fin 4)} (hπ : Perm.sign π = 1) :
    SameHand o (o ∘ π) := ⟨π, hπ, rfl⟩

/-- For distinct ligands the converse holds: a reordering keeps the hand only
when it is even. -/
lemma sign_eq_one_of_sameHand {o : Ligands n} (ho : Function.Injective o) {π : Perm (Fin 4)}
    (h : SameHand o (o ∘ π)) : Perm.sign π = 1 := by
  obtain ⟨ρ, hρ, e⟩ := h
  have : π = ρ := Perm.ext fun k ↦ ho (congrFun e k)
  rwa [this]

/-- Relabeling the atoms keeps the hand. -/
lemma SameHand.map (f : Fin n → Fin n) {o o' : Ligands n} (h : SameHand o o') :
    SameHand (Option.map f ∘ o) (Option.map f ∘ o') := by
  obtain ⟨π, hπ, rfl⟩ := h
  exact ⟨π, hπ, rfl⟩

/-- The listing `(p, q, r, s)`. -/
def of4 (p q r s : Option (Fin n)) : Ligands n
  | 0 => p
  | 1 => q
  | 2 => r
  | 3 => s

/-- A list of exactly four ligands as a listing. -/
def ofList? : List (Option (Fin n)) → Option (Ligands n)
  | [p, q, r, s] => some (of4 p q r s)
  | _ => none

/-- The transposition of the last two places, which turns `@` into `@@`. -/
abbrev swapLast : Perm (Fin 4) := swap 2 3

lemma sign_swapLast : Perm.sign swapLast = -1 := Perm.sign_swap (by decide)

/-- Precomposing with a fixed permutation keeps the hand. -/
lemma SameHand.comp (τ : Perm (Fin 4)) {o o' : Ligands n} (h : SameHand o o') :
    SameHand (o ∘ τ) (o' ∘ τ) := by
  obtain ⟨π, hπ, rfl⟩ := h
  refine ⟨τ⁻¹ * π * τ, by simp [hπ, mul_comm], ?_⟩
  funext k
  simp

end Ligands

/-- A tetrahedral configuration: ligand listings up to even permutation.
`Tetra.ofMark o true` is the centre SMILES writes `@` with its ligands listed
in the order `o`. -/
def Tetra (n : ℕ) := Quotient (Ligands.setoid (n := n))

namespace Tetra

open Ligands

instance : DecidableEq (Tetra n) :=
  inferInstanceAs (DecidableEq (Quotient (Ligands.setoid (n := n))))

/-- The configuration that is `@` with the ligands listed as `o`. -/
def mk (o : Ligands n) : Tetra n := Quotient.mk _ o

lemma mk_eq_mk {o o' : Ligands n} : mk o = mk o' ↔ SameHand o o' := Quotient.eq

@[elab_as_elim] lemma ind {motive : Tetra n → Prop} (h : ∀ o, motive (mk o)) (t : Tetra n) :
    motive t :=
  Quotient.inductionOn t h

/-- For distinct ligands, reordering by `π` gives the same configuration
exactly when `π` is even. -/
lemma mk_comp_eq_mk_iff {o : Ligands n} (ho : Function.Injective o) (π : Perm (Fin 4)) :
    mk (o ∘ π) = mk o ↔ Perm.sign π = 1 := by
  rw [mk_eq_mk]
  exact ⟨fun h ↦ sign_eq_one_of_sameHand ho h.symm, fun h ↦ (sameHand_comp o h).symm⟩

/-- The configuration written `@` (if `anticlockwise`) or `@@` with the ligands
listed in the order `o`. -/
def ofMark (o : Ligands n) (anticlockwise : Bool) : Tetra n :=
  if anticlockwise then mk o else mk (o ∘ swapLast)

instance : Inhabited (Tetra n) := ⟨mk fun _ ↦ none⟩

/-- The mark a writer emits for `t` with the ligands listed in the order `o`:
`true` for `@`, `false` for `@@`. -/
def isAnticlockwise (t : Tetra n) (o : Ligands n) : Bool := decide (mk o = t)

/-- The mirror image: every listing changes hand. -/
def mirror : Tetra n → Tetra n :=
  Quotient.map (· ∘ swapLast) fun _ _ h ↦ SameHand.comp swapLast h

/-- Relabel the ligand atoms by `σ`. -/
def map (σ : Perm (Fin n)) : Tetra n → Tetra n :=
  Quotient.map (fun o ↦ Option.map σ ∘ o) fun _ _ h ↦ SameHand.map σ h

@[simp] lemma map_mk (σ : Perm (Fin n)) (o : Ligands n) :
    map σ (mk o) = mk (Option.map σ ∘ o) := rfl

@[simp] lemma mirror_mk (o : Ligands n) : mirror (mk o) = mk (o ∘ swapLast) := rfl

/-! ### The mark of a listing -/

lemma units_eq_neg_iff (a b : ℤˣ) : a = -b ↔ ¬ a = b := by
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;> decide

lemma neg_units_eq_iff (a b : ℤˣ) : -a = b ↔ ¬ a = b := by
  rcases Int.units_eq_one_or a with rfl | rfl <;>
    rcases Int.units_eq_one_or b with rfl | rfl <;> decide

/-- **The mark of a listing.** If the configuration is `@` in the listing
`o ∘ ρ` of distinct ligands, then in the listing `o ∘ π` it is `@` exactly
when `π` and `ρ` have the same sign. -/
theorem isAnticlockwise_mk_comp {o : Ligands n} (ho : Function.Injective o)
    (ρ π : Perm (Fin 4)) :
    (mk (o ∘ ρ)).isAnticlockwise (o ∘ π) = decide (Perm.sign π = Perm.sign ρ) := by
  have e : o ∘ π = (o ∘ ρ) ∘ (ρ⁻¹ * π : Perm (Fin 4)) := by funext k; simp
  unfold isAnticlockwise
  rw [e, decide_eq_decide, mk_comp_eq_mk_iff (ho.comp ρ.injective), map_mul, map_inv,
    inv_mul_eq_one, eq_comm]

/-- The special case `ρ = 1`: `@` in the listing `o` stays `@` in the listing
`o ∘ π` exactly when `π` is even. -/
theorem isAnticlockwise_comp {o : Ligands n} (ho : Function.Injective o) (π : Perm (Fin 4)) :
    (mk o).isAnticlockwise (o ∘ π) = decide (Perm.sign π = 1) := by
  simpa using isAnticlockwise_mk_comp ho 1 π

/-- Reading a mark back: the configuration written with mark `b` in the order
`o` carries mark `b` in that order. -/
theorem isAnticlockwise_ofMark {o : Ligands n} (ho : Function.Injective o) (b : Bool) :
    (ofMark o b).isAnticlockwise o = b := by
  cases b
  · have h := isAnticlockwise_mk_comp ho swapLast 1
    simp only [map_one, sign_swapLast] at h
    simpa [ofMark] using h
  · simp [ofMark, isAnticlockwise]

/-- Swapping two places of a listing flips the mark. -/
theorem isAnticlockwise_comp_swap {o : Ligands n} (ho : Function.Injective o)
    (ρ π : Perm (Fin 4)) {i j : Fin 4} (hij : i ≠ j) :
    (mk (o ∘ ρ)).isAnticlockwise ((o ∘ π) ∘ swap i j)
      = !(mk (o ∘ ρ)).isAnticlockwise (o ∘ π) := by
  have e : (o ∘ π) ∘ swap i j = o ∘ (π * swap i j : Perm (Fin 4)) := rfl
  rw [e, isAnticlockwise_mk_comp ho, isAnticlockwise_mk_comp ho, map_mul, Perm.sign_swap hij,
    mul_neg, mul_one, decide_eq_decide.mpr (neg_units_eq_iff _ _), decide_not]

/-- A configuration of distinct ligands is one of the two hands of any listing
of them. -/
theorem eq_or_eq_mirror {o : Ligands n} (ho : Function.Injective o) (π : Perm (Fin 4)) :
    mk (o ∘ π) = mk o ∨ mk (o ∘ π) = mirror (mk o) := by
  rcases Int.units_eq_one_or (Perm.sign π) with h | h
  · exact Or.inl ((mk_comp_eq_mk_iff ho π).mpr h)
  · refine Or.inr ?_
    rw [mirror_mk, mk_eq_mk]
    refine ⟨π⁻¹ * swapLast, by simp [h], ?_⟩
    funext k
    simp

/-! ### Mirror images -/

theorem mirror_mirror (t : Tetra n) : mirror (mirror t) = t := by
  induction t using ind with
  | h o =>
    simp only [mirror_mk]
    congr 1
    funext k
    simp

/-- The mirror image of a centre with distinct ligands is a different
configuration: a tetrahedral centre is chiral. -/
theorem mirror_ne {o : Ligands n} (ho : Function.Injective o) : mirror (mk o) ≠ mk o := by
  rw [mirror_mk, Ne, mk_comp_eq_mk_iff ho, sign_swapLast]
  decide

/-- The mirror image carries the opposite mark in every listing. -/
theorem isAnticlockwise_mirror {o : Ligands n} (ho : Function.Injective o)
    (ρ π : Perm (Fin 4)) :
    (mirror (mk (o ∘ ρ))).isAnticlockwise (o ∘ π) = !(mk (o ∘ ρ)).isAnticlockwise (o ∘ π) := by
  have e : (o ∘ ρ) ∘ swapLast = o ∘ (ρ * swapLast : Perm (Fin 4)) := rfl
  rw [mirror_mk, e, isAnticlockwise_mk_comp ho, isAnticlockwise_mk_comp ho, map_mul,
    sign_swapLast, mul_neg, mul_one]
  simp [units_eq_neg_iff]

/-- Reading back the mark of either hand of a listing of distinct ligands. -/
lemma ofMark_isAnticlockwise_of_hand {p : Ligands n} (hp : Function.Injective p) (t : Tetra n)
    (ht : t = mk p ∨ t = mirror (mk p)) : ofMark p (t.isAnticlockwise p) = t := by
  rcases ht with rfl | rfl
  · simp [ofMark, isAnticlockwise]
  · have hf : (mirror (mk p)).isAnticlockwise p = false := by
      simp only [isAnticlockwise, decide_eq_false_iff_not]
      exact fun h ↦ mirror_ne hp h.symm
    rw [hf]
    rfl

/-- **Writing then reading a mark gives the configuration back.** For a
configuration of distinct ligands and any listing `o ∘ π` of them, the mark
`isAnticlockwise` computes (what the writer emits) read back in that listing
by `ofMark` (what the parser does) is the configuration itself. -/
theorem ofMark_isAnticlockwise {o : Ligands n} (ho : Function.Injective o) (ρ π : Perm (Fin 4))
    (t : Tetra n) (ht : t = mk (o ∘ ρ) ∨ t = mirror (mk (o ∘ ρ))) :
    ofMark (o ∘ π) (t.isAnticlockwise (o ∘ π)) = t := by
  refine ofMark_isAnticlockwise_of_hand (ho.comp π.injective) t ?_
  rcases eq_or_eq_mirror (ho.comp π.injective) (π⁻¹ * ρ) with h | h <;>
  · have e : (o ∘ π) ∘ (π⁻¹ * ρ : Perm (Fin 4)) = o ∘ ρ := by funext k; simp
    rw [e] at h
    rcases ht with rfl | rfl
    · first | exact Or.inl h | exact Or.inr h
    · first | (right; rw [h]; done) | (left; rw [h, mirror_mirror])

/-! ### Relabeling -/

@[simp] theorem map_refl (t : Tetra n) : map (Equiv.refl _) t = t := by
  induction t using ind with
  | h o => simp only [map_mk]; congr 1; funext k; simp

theorem map_map (σ τ : Perm (Fin n)) (t : Tetra n) : map τ (map σ t) = map (σ.trans τ) t := by
  induction t using ind with
  | h o => simp only [map_mk]; congr 1; funext k; simp [Option.map_map]

lemma map_injective (σ : Perm (Fin n)) : Function.Injective (map σ) := fun s t h ↦ by
  have := congrArg (map σ.symm) h
  rwa [map_map, map_map, Equiv.self_trans_symm, map_refl, map_refl] at this

theorem map_mirror (σ : Perm (Fin n)) (t : Tetra n) : map σ (mirror t) = mirror (map σ t) := by
  induction t using ind with
  | h o => rfl

/-- **The mark is label-independent**: relabel the configuration and the
listing together and the mark is unchanged. -/
theorem isAnticlockwise_map (σ : Perm (Fin n)) (t : Tetra n) (o : Ligands n) :
    (map σ t).isAnticlockwise (Option.map σ ∘ o) = t.isAnticlockwise o := by
  unfold isAnticlockwise
  rw [decide_eq_decide, ← map_mk]
  exact (map_injective σ).eq_iff

end Tetra

/-! ## Double bonds

A double bond `u=v` with substituents `a, a'` on `u` and `c, c'` on `v`
(`none` for an implicit hydrogen or lone pair) is listed as `(a, a', c, c')`,
meaning *`a` lies cis to `c`, and `a'` to `c'`*.  Swapping the two ends, or
both pairs at once, lists the same arrangement; the listings up to the Klein
four-group `{1, (01)(23), (02)(13), (03)(12)}` (`kleinFour`) are the
arrangements, `Planar n`.  Swapping one pair alone gives the other
arrangement, cis for trans (`Planar.flip`), so a double bond with distinct
substituents at each end has exactly two (`flip_ne`, `eq_or_eq_flip`).
SMILES writes the arrangement with `/` `\` on the single bonds around the
double bond; `cis` reads it back for any pair of substituents. -/

namespace Ligands

/-- The Klein four-group on the places of a double-bond listing: the
identity, both pairs swapped, the ends swapped, and both. -/
def kleinFour : List (Fin 4 → Fin 4) :=
  [id, (fun | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2), (fun | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1),
    (fun | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0)]

/-- Swap the substituents of the second end: the other arrangement. -/
def swapEnd : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 2

lemma id_mem_kleinFour : id ∈ kleinFour := List.mem_cons_self

lemma comp_mem_kleinFour : ∀ f ∈ kleinFour, ∀ g ∈ kleinFour, f ∘ g ∈ kleinFour := by
  decide +kernel

lemma comp_self_of_mem_kleinFour : ∀ f ∈ kleinFour, f ∘ f = id := by decide +kernel

lemma swapEnd_conj_mem_kleinFour : ∀ f ∈ kleinFour, swapEnd ∘ f ∘ swapEnd ∈ kleinFour := by
  decide +kernel

lemma swapEnd_not_mem_kleinFour : swapEnd ∉ kleinFour := by decide +kernel

lemma swapEnd_comp_swapEnd : swapEnd ∘ swapEnd = id := by decide +kernel

/-- Same arrangement: an element of the Klein four-group turns the listing `o`
into `o'`. -/
def SameArrangement (o o' : Ligands n) : Prop := ∃ f ∈ kleinFour, o' = o ∘ f

lemma SameArrangement.refl (o : Ligands n) : SameArrangement o o := ⟨id, id_mem_kleinFour, rfl⟩

lemma SameArrangement.symm {o o' : Ligands n} : SameArrangement o o' → SameArrangement o' o := by
  rintro ⟨f, hf, rfl⟩
  exact ⟨f, hf, by rw [Function.comp_assoc, comp_self_of_mem_kleinFour f hf, Function.comp_id]⟩

lemma SameArrangement.trans {o o' o'' : Ligands n} :
    SameArrangement o o' → SameArrangement o' o'' → SameArrangement o o'' := by
  rintro ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
  exact ⟨f ∘ g, comp_mem_kleinFour f hf g hg, rfl⟩

/-- Double-bond listings of the same arrangement. Not an instance: the
instance on `Ligands n` is `SameHand`. -/
def planarSetoid : Setoid (Ligands n) :=
  ⟨SameArrangement, ⟨SameArrangement.refl, SameArrangement.symm, SameArrangement.trans⟩⟩

instance : DecidableRel (SameArrangement (n := n)) := fun o o' ↦
  inferInstanceAs (Decidable (∃ f ∈ kleinFour, o' = o ∘ f))

/-- Whether the listing `o` puts `a` and `c` cis: in places 0 and 2, or 1 and 3. -/
def CisIn (o : Ligands n) (a c : Option (Fin n)) : Prop :=
  (o 0 = a ∧ o 2 = c) ∨ (o 2 = a ∧ o 0 = c) ∨ (o 1 = a ∧ o 3 = c) ∨ (o 3 = a ∧ o 1 = c)

instance (o : Ligands n) (a c : Option (Fin n)) : Decidable (CisIn o a c) := by
  unfold CisIn; infer_instance

lemma cisIn_iff_of_sameArrangement {o o' : Ligands n} (h : SameArrangement o o')
    (a c : Option (Fin n)) : CisIn o' a c ↔ CisIn o a c := by
  obtain ⟨f, hf, rfl⟩ := h
  simp only [kleinFour, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl <;>
    simp only [CisIn, Function.comp_apply, id] <;> tauto

end Ligands

/-- A double bond's cis/trans arrangement: listings `(a, a', c, c')`, `a` cis
to `c`, up to the Klein four-group. -/
def Planar (n : ℕ) := Quotient (Ligands.planarSetoid (n := n))

namespace Planar

open Ligands

/-- The arrangement with `o 0` cis to `o 2` and `o 1` cis to `o 3`. -/
def mk (o : Ligands n) : Planar n := Quotient.mk _ o

lemma mk_eq_mk {o o' : Ligands n} : mk o = mk o' ↔ SameArrangement o o' :=
  ⟨@Quotient.exact _ planarSetoid _ _, @Quotient.sound _ planarSetoid _ _⟩

@[elab_as_elim] lemma ind {motive : Planar n → Prop} (h : ∀ o, motive (mk o)) (p : Planar n) :
    motive p :=
  Quotient.inductionOn p h

instance : DecidableEq (Planar n) := fun p q ↦
  Quotient.recOnSubsingleton₂ p q fun o o' ↦ decidable_of_iff _ (mk_eq_mk (o := o) (o' := o')).symm

instance : Inhabited (Planar n) := ⟨mk fun _ ↦ none⟩

/-- The other arrangement: cis and trans exchanged. -/
def flip : Planar n → Planar n :=
  Quotient.map' (· ∘ swapEnd) fun o o' h ↦ by
    obtain ⟨f, hf, e⟩ := h
    refine ⟨swapEnd ∘ f ∘ swapEnd, swapEnd_conj_mem_kleinFour f hf, ?_⟩
    funext k
    have := congrFun swapEnd_comp_swapEnd (f (swapEnd k))
    simp only [Function.comp_apply, id] at this ⊢
    rw [e, Function.comp_apply, this]

/-- Relabel the substituent atoms by `σ`. -/
def map (σ : Perm (Fin n)) : Planar n → Planar n :=
  Quotient.map' (fun o ↦ Option.map σ ∘ o) fun o o' h ↦ by
    obtain ⟨f, hf, e⟩ := h
    exact ⟨f, hf, by rw [e]; rfl⟩

/-- Whether the arrangement puts `a` and `c` cis. -/
def cis (p : Planar n) (a c : Option (Fin n)) : Bool :=
  Quotient.lift (s := planarSetoid) (fun o ↦ decide (CisIn o a c))
    (fun _ _ h ↦ decide_eq_decide.mpr (cisIn_iff_of_sameArrangement h a c).symm) p

@[simp] lemma flip_mk (o : Ligands n) : flip (mk o) = mk (o ∘ swapEnd) := rfl

@[simp] lemma map_mk (σ : Perm (Fin n)) (o : Ligands n) : map σ (mk o) = mk (Option.map σ ∘ o) :=
  rfl

@[simp] lemma cis_mk (o : Ligands n) (a c : Option (Fin n)) :
    (mk o).cis a c = decide (CisIn o a c) := rfl

/-- The arrangement putting `a` cis to `c` (if `cis`) or trans, where `a, a'`
are the substituents of one end and `c, c'` of the other. -/
def ofCis (a a' c c' : Option (Fin n)) (cis : Bool) : Planar n :=
  if cis then mk (of4 a a' c c') else mk (of4 a a' c' c)

theorem flip_flip (p : Planar n) : flip (flip p) = p := by
  induction p using ind with
  | h o =>
    simp only [flip_mk]
    rw [Function.comp_assoc, swapEnd_comp_swapEnd, Function.comp_id]

/-- A double bond with four distinct substituent places has two arrangements:
its flip is a different one. -/
theorem flip_ne {o : Ligands n} (ho : Function.Injective o) : flip (mk o) ≠ mk o := by
  rw [flip_mk, Ne, mk_eq_mk]
  rintro ⟨f, hf, e⟩
  have : f = swapEnd := funext fun k ↦ by
    have hk : k = swapEnd (f k) := ho (congrFun e k)
    have := congrFun swapEnd_comp_swapEnd (f k)
    simp only [Function.comp_apply, id] at this
    exact this.symm.trans (congrArg swapEnd hk.symm)
  exact swapEnd_not_mem_kleinFour (this ▸ hf)

/-- **Reading back what was written.** For distinct substituents, the
arrangement built from "`a` cis to `c`: `b`" puts `a` cis to `c` exactly when
`b`. -/
theorem cis_ofCis {a a' c c' : Option (Fin n)} (h : [a, a', c, c'].Nodup) (b : Bool) :
    (ofCis a a' c c' b).cis a c = b := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at h
  obtain ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, -⟩ := h
  cases b <;> simp [ofCis, CisIn, of4, h2, h4, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h6]

/-- **The other arrangement exchanges cis and trans**: for distinct
substituents, a pair across the double bond — one from each end — is cis in
the flipped arrangement exactly when it is trans in the original. -/
theorem cis_flip {o : Ligands n} (ho : Function.Injective o) (i j : Fin 4) (hi : i.val < 2)
    (hj : 2 ≤ j.val) : (flip (mk o)).cis (o i) (o j) = !(mk o).cis (o i) (o j) := by
  have h : ∀ x y, o x = o y ↔ x = y := fun _ _ ↦ ho.eq_iff
  fin_cases i <;> fin_cases j <;> simp_all [CisIn, swapEnd]

theorem map_refl (p : Planar n) : map (Equiv.refl _) p = p := by
  induction p using ind with
  | h o => simp only [map_mk]; congr 1; funext k; simp

theorem map_map (σ τ : Perm (Fin n)) (p : Planar n) : map τ (map σ p) = map (σ.trans τ) p := by
  induction p using ind with
  | h o => simp only [map_mk]; congr 1; funext k; simp [Option.map_map]

lemma map_injective (σ : Perm (Fin n)) : Function.Injective (map σ) := fun p q h ↦ by
  have := congrArg (map σ.symm) h
  rwa [map_map, map_map, Equiv.self_trans_symm, map_refl, map_refl] at this

theorem map_flip (σ : Perm (Fin n)) (p : Planar n) : map σ (flip p) = flip (map σ p) := by
  induction p using ind with
  | h o => rfl

/-- **Cis is label-independent**: relabel the arrangement and the pair
together and the answer is unchanged. -/
theorem cis_map (σ : Perm (Fin n)) (p : Planar n) (a c : Option (Fin n)) :
    (map σ p).cis (a.map σ) (c.map σ) = p.cis a c := by
  induction p using ind with
  | h o =>
    simp only [map_mk, cis_mk, decide_eq_decide, CisIn, Function.comp_apply]
    have hinj : Function.Injective (Option.map σ) := Option.map_injective σ.injective
    simp only [hinj.eq_iff]

end Planar

/-! ## The stereochemistry of an atom -/

/-- What an atom's stereochemistry is: a tetrahedral centre, or an end of a
double bond with a cis/trans arrangement (both ends carry the same one). -/
inductive Stereo (n : ℕ) where
  | tetra (t : Tetra n)
  | planar (p : Planar n)
  deriving DecidableEq

namespace Stereo

/-- Relabel the atoms by `σ`. -/
def map (σ : Perm (Fin n)) : Stereo n → Stereo n
  | tetra t => tetra (t.map σ)
  | planar p => planar (p.map σ)

/-- The other configuration: the mirror image of a centre, the other
arrangement of a double bond. -/
def mirror : Stereo n → Stereo n
  | tetra t => tetra t.mirror
  | planar p => planar p.flip

/-- Whether this is a double-bond arrangement. -/
def isPlanar : Stereo n → Bool
  | tetra _ => false
  | planar _ => true

/-- A numeric code for the kind, for invariant vectors. -/
def code : Stereo n → ℕ
  | tetra _ => 1
  | planar _ => 2

@[simp] lemma map_tetra (σ : Perm (Fin n)) (t : Tetra n) : map σ (tetra t) = tetra (t.map σ) := rfl

@[simp] lemma map_planar (σ : Perm (Fin n)) (p : Planar n) :
    map σ (planar p) = planar (p.map σ) := rfl

theorem map_map (σ τ : Perm (Fin n)) (s : Stereo n) : map τ (map σ s) = map (σ.trans τ) s := by
  cases s <;> simp [map, Tetra.map_map, Planar.map_map]

theorem map_refl (s : Stereo n) : map (Equiv.refl _) s = s := by
  cases s <;> simp [map, Tetra.map_refl, Planar.map_refl]

lemma map_injective (σ : Perm (Fin n)) : Function.Injective (map σ) := by
  intro s s' h
  cases s <;> cases s' <;> simp only [map, tetra.injEq, planar.injEq, reduceCtorEq] at h ⊢
  · exact Tetra.map_injective σ h
  · exact Planar.map_injective σ h

theorem map_mirror (σ : Perm (Fin n)) (s : Stereo n) : map σ (mirror s) = mirror (map σ s) := by
  cases s <;> simp [map, mirror, Tetra.map_mirror, Planar.map_flip]

theorem mirror_mirror (s : Stereo n) : mirror (mirror s) = s := by
  cases s <;> simp [mirror, Tetra.mirror_mirror, Planar.flip_flip]

@[simp] lemma isPlanar_map (σ : Perm (Fin n)) (s : Stereo n) : (map σ s).isPlanar = s.isPlanar := by
  cases s <;> rfl

@[simp] lemma code_map (σ : Perm (Fin n)) (s : Stereo n) : (map σ s).code = s.code := by
  cases s <;> rfl

end Stereo

end LeanSMILES
