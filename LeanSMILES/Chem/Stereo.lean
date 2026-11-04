/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi

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

/-- A list of exactly four ligands as a listing. -/
def ofList? : List (Option (Fin n)) → Option (Ligands n)
  | [p, q, r, s] => some fun
    | 0 => p
    | 1 => q
    | 2 => r
    | 3 => s
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

end LeanSMILES
