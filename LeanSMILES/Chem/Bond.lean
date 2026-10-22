/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Rat.Defs
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

lemma order_pos (k : BondKind) : 0 < k.order := by
  cases k <;> norm_num [order]

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

@[simp] lemma ofOrder?_order (k : BondKind) : ofOrder? k.order = some k := by
  cases k <;> norm_num [ofOrder?, order]

lemma ofOrder?_eq_some {q : ℚ} {k : BondKind} (h : ofOrder? q = some k) : q = k.order := by
  unfold ofOrder? at h
  split_ifs at h with h1 h2 h3 h4 h5
  · obtain rfl := Option.some.inj h; exact h1
  · obtain rfl := Option.some.inj h; exact h2
  · obtain rfl := Option.some.inj h; exact h3
  · obtain rfl := Option.some.inj h; exact h4
  · obtain rfl := Option.some.inj h; exact h5

/-- Distinct kinds have distinct orders: an order determines the kind. -/
lemma order_injective : Function.Injective order := by
  intro k k' h
  have := congrArg ofOrder? h
  rwa [ofOrder?_order, ofOrder?_order, Option.some.injEq] at this

end BondKind

/-- The directional single-bond marks `/` (up) and `\` (down) that encode
cis/trans configuration about a neighboring double bond. Recorded relative to
the bond's `src → dst` direction, not interpreted. -/
inductive BondDir
  | up
  | down
  deriving DecidableEq, Repr, Inhabited

namespace BondDir

/-- The SMILES character: `/` or `\\`. -/
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
  /-- The `/` `\\` mark, if written, relative to `src → dst`. -/
  dir : Option BondDir := none
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

@[simp] lemma edge_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) :
    (b.map σ hσ).edge = Sym2.map σ b.edge := rfl

@[simp] lemma edge_flip (b : Bond n) : b.flip.edge = b.edge := Sym2.eq_swap

lemma edge_not_isDiag (b : Bond n) : ¬ b.edge.IsDiag := by
  simpa [edge, Sym2.mk_isDiag_iff] using b.ne

lemma edge_eq_mk_iff {b : Bond n} {i j : Fin n} :
    b.edge = s(i, j) ↔ (b.src = i ∧ b.dst = j) ∨ (b.src = j ∧ b.dst = i) :=
  Sym2.eq_iff

/-- A bond never joins an atom to itself. -/
lemma edge_ne_diag (b : Bond n) (i : Fin n) : b.edge ≠ s(i, i) := by
  intro h
  rcases edge_eq_mk_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact b.ne (h1.trans h2.symm)

lemma touches_iff {b : Bond n} {i : Fin n} : b.touches i = true ↔ i ∈ b.edge := by
  simp only [touches, edge, Bool.or_eq_true, beq_iff_eq, Sym2.mem_iff]
  exact ⟨fun h ↦ h.imp Eq.symm Eq.symm, fun h ↦ h.imp Eq.symm Eq.symm⟩

/-- `0-1`, `1=2`, `2:3`, … -/
def toString (b : Bond n) : String :=
  s!"{b.src.val}{b.kind.symbol}{b.dst.val}"

instance : ToString (Bond n) := ⟨toString⟩

instance : Repr (Bond n) := ⟨fun b _ ↦ Std.Format.text b.toString⟩

end Bond

end LeanSMILES
