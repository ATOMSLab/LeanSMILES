/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

/-!
# LeanSMILES.Chem.Bond

Bond *kinds* are an enumeration — single, double, triple, quadruple, aromatic —
and the bond *order* is a view of the kind into `ℚ`, with the aromatic bond at
`3/2`.  Keeping the enumeration as the data and the rational as a function
means featurization can one-hot the kind, matrices can sum the order, and no
`Float` is involved anywhere.

A `Bond n` joins two *distinct* atoms of an `n`-atom molecule — the proof of
distinctness is a field, so a molecular graph is loopless by construction, and
the two endpoints are `Fin n`, so a bond cannot dangle.  `src`/`dst` keep the
order the SMILES string introduced the endpoints in, which is what the `/` `\`
stereo marks refer to; the undirected edge `s(src, dst) : Sym2 (Fin n)` is
what Mathlib's `SimpleGraph` sees.
-/

@[expose] public section

namespace LeanSMILES

/-- The kind of a bond, as SMILES writes it. There is no zero-order kind: the
SMILES dot `.` is the *absence* of a bond. -/
inductive BondKind
  | single
  | double
  | triple
  | quadruple
  | aromatic
  deriving DecidableEq, Repr, Inhabited, Ord

namespace BondKind

/-- Bond order, exact: `3/2` for an aromatic bond. -/
def order : BondKind → ℚ
  | single => 1
  | double => 2
  | triple => 3
  | quadruple => 4
  | aromatic => 3 / 2

/-- Every bond order is positive: the smallest, `single.order`, is `1`. -/
lemma order_pos (k : BondKind) : 0 < k.order := by cases k <;> norm_num [order]

/-- No bond kind has order `0`: a zero entry in a bond matrix means no bond, never a kind. -/
lemma order_ne_zero (k : BondKind) : k.order ≠ 0 := (order_pos k).ne'

/-- The SMILES bond symbol. -/
def symbol : BondKind → String
  | single => "-"
  | double => "="
  | triple => "#"
  | quadruple => "$"
  | aromatic => ":"

/-- The kind written by a bond symbol, if the character is one. -/
def ofChar? : Char → Option BondKind
  | '-' => some single
  | '=' => some double
  | '#' => some triple
  | '$' => some quadruple
  | ':' => some aromatic
  | _ => none

/-- The bond kind with a given order, if any: the inverse of `order`. -/
def ofOrder? (q : ℚ) : Option BondKind :=
  if q = 1 then some single
  else if q = 2 then some double
  else if q = 3 then some triple
  else if q = 4 then some quadruple
  else if q = 3 / 2 then some aromatic
  else none

/-- `ofOrder?` is a left inverse of `order`: a kind's order reads back as that kind. -/
@[simp] lemma ofOrder?_order (k : BondKind) : ofOrder? k.order = some k := by
  cases k <;> norm_num [ofOrder?, order]

/-- When `ofOrder? q` returns a kind, `q` is exactly that kind's order: the converse of
`ofOrder?_order`. -/
lemma ofOrder?_eq_some {q : ℚ} {k : BondKind} (h : ofOrder? q = some k) : q = k.order := by
  grind [ofOrder?, order]

/-- Distinct kinds have distinct orders: an order determines the kind. -/
lemma order_injective : Function.Injective order := fun k k' h ↦ by simpa using congrArg ofOrder? h

end BondKind

/-- The directional single-bond marks `/` (up) and `\` (down) that encode
cis/trans configuration about a neighboring double bond. Recorded relative to
the bond's `src → dst` direction, not interpreted. -/
inductive BondDir
  | up
  | down
  deriving DecidableEq, Repr, Inhabited

namespace BondDir

/-- The SMILES character: `/` or `\`. -/
def toChar : BondDir → Char
  | up => '/'
  | down => '\\'

/-- The mark seen from the other end of the bond. -/
def flip : BondDir → BondDir
  | up => down
  | down => up

end BondDir

/-- A bond between two distinct atoms of an `n`-atom molecule. -/
structure Bond (n : ℕ) where
  /-- The atom the SMILES string introduced first. -/
  src : Fin n
  /-- The other atom. -/
  dst : Fin n
  /-- The bond kind. -/
  kind : BondKind := .single
  /-- The `/` `\` mark, if written, relative to `src → dst`. -/
  dir : Option BondDir := none
  /-- The endpoints are distinct: a molecule has no self-bonds, by construction. -/
  ne : src ≠ dst
  deriving DecidableEq

namespace Bond

variable {n m : ℕ}

/-- The undirected edge, for Mathlib. -/
def edge (b : Bond n) : Sym2 (Fin n) := s(b.src, b.dst)

/-- Whether `i` is an endpoint. -/
def touches (b : Bond n) (i : Fin n) : Bool := b.src == i || b.dst == i

/-- The endpoint that is not `i` (or `src`, if `i` is not an endpoint). -/
def other (b : Bond n) (i : Fin n) : Fin n := if b.src = i then b.dst else b.src

/-- The same bond read from the other end. -/
def flip (b : Bond n) : Bond n :=
  { b with src := b.dst, dst := b.src, dir := b.dir.map BondDir.flip, ne := b.ne.symm }

/-- Transport along an injective relabeling of the atoms. -/
def map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) : Bond m :=
  { src := σ b.src, dst := σ b.dst, kind := b.kind, dir := b.dir, ne := hσ.ne b.ne }

/-- `map` acts on the edge as `Sym2.map`: relabeling commutes with taking the undirected edge. -/
@[simp] lemma edge_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) :
    (b.map σ hσ).edge = Sym2.map σ b.edge := rfl

/-- Two relabelings in a row are one relabeling along the composite. -/
@[simp] lemma map_map {k : ℕ} (σ : Fin n → Fin m) (hσ : Function.Injective σ)
    (τ : Fin m → Fin k) (hτ : Function.Injective τ) (b : Bond n) :
    (b.map σ hσ).map τ hτ = b.map (τ ∘ σ) (hτ.comp hσ) := rfl

/-- Relabeling the atoms leaves the bond kind alone. -/
@[simp] lemma kind_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) :
    (b.map σ hσ).kind = b.kind := rfl

/-- Relabeling preserves incidence: the relabeled bond touches `σ i` exactly when `b` touches
`i`. -/
@[simp] lemma touches_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n)
    (i : Fin n) : (b.map σ hσ).touches (σ i) = b.touches i := by grind [touches, map]

/-- Relabeling commutes with `other`: the far endpoint of the relabeled bond is the relabeled far
endpoint. -/
@[simp] lemma other_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n)
    (i : Fin n) : (b.map σ hσ).other (σ i) = σ (b.other i) := by grind [other, map]

/-- Reading a bond from the other end does not change its undirected edge. -/
@[simp] lemma edge_flip (b : Bond n) : b.flip.edge = b.edge := Sym2.eq_swap

/-- A bond's edge is never a loop: `Sym2.IsDiag` fails because `src ≠ dst`. -/
lemma edge_not_isDiag (b : Bond n) : ¬ b.edge.IsDiag := Sym2.mk_isDiag_iff.not.mpr b.ne

/-- A bond's edge is `s(i, j)` exactly when its endpoints are `i` and `j` in either order:
`Sym2.eq_iff` with `edge` unfolded. -/
lemma edge_eq_mk_iff {b : Bond n} {i j : Fin n} :
    b.edge = s(i, j) ↔ (b.src = i ∧ b.dst = j) ∨ (b.src = j ∧ b.dst = i) :=
  Sym2.eq_iff

/-- A bond never joins an atom to itself. -/
lemma edge_ne_diag (b : Bond n) (i : Fin n) : b.edge ≠ s(i, i) :=
  fun h ↦ b.edge_not_isDiag (h ▸ Sym2.mk_isDiag_iff.2 rfl)

/-- A bond touches `i` with `j` at the other end exactly when its edge is `s(i, j)`. -/
lemma touches_and_other_iff (b : Bond n) (i j : Fin n) :
    (b.touches i = true ∧ (b.other i == j) = true) ↔ b.edge = s(i, j) := by
  grind [touches, other, edge_eq_mk_iff, b.ne]

/-- `touches` agrees with `Sym2` membership: `i` is an endpoint exactly when `i ∈ b.edge`. -/
lemma touches_iff {b : Bond n} {i : Fin n} : b.touches i = true ↔ i ∈ b.edge := by
  grind [touches, edge]

/-- `0-1`, `1=2`, `2:3`, … -/
def toString (b : Bond n) : String :=
  s!"{b.src.val}{b.kind.symbol}{b.dst.val}"

instance : ToString (Bond n) := ⟨toString⟩

instance : Repr (Bond n) := ⟨fun b _ ↦ Std.Format.text b.toString⟩

end Bond

end LeanSMILES
