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
SMILES dot `.` is the *absence* of a bond, and a molecule with a dot is a
disconnected graph. -/
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

theorem order_pos (k : BondKind) : 0 < k.order := by
  cases k <;> norm_num [order]

theorem order_ne_zero (k : BondKind) : k.order ≠ 0 := (order_pos k).ne'

/-- The SMILES bond symbol. -/
def symbol : BondKind → String
  | single => "-"
  | double => "="
  | triple => "#"
  | quadruple => "$"
  | aromatic => ":"

def ofChar? : Char → Option BondKind
  | '-' => some single
  | '=' => some double
  | '#' => some triple
  | '$' => some quadruple
  | ':' => some aromatic
  | _ => none

end BondKind

/-- The directional single-bond marks `/` (up) and `\` (down) that encode
cis/trans configuration about a neighbouring double bond. Recorded relative to
the bond's `src → dst` direction, not interpreted. -/
inductive BondDir
  | up
  | down
  deriving DecidableEq, Repr, Inhabited

namespace BondDir

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
  src : Fin n
  dst : Fin n
  kind : BondKind := .single
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

/-- Transport along an injective relabelling of the atoms. -/
def map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) : Bond m :=
  { src := σ b.src, dst := σ b.dst, kind := b.kind, dir := b.dir, ne := hσ.ne b.ne }

@[simp] theorem edge_map (σ : Fin n → Fin m) (hσ : Function.Injective σ) (b : Bond n) :
    (b.map σ hσ).edge = Sym2.map σ b.edge := rfl

@[simp] theorem edge_flip (b : Bond n) : b.flip.edge = b.edge := Sym2.eq_swap

theorem edge_not_isDiag (b : Bond n) : ¬ b.edge.IsDiag := by
  simpa [edge, Sym2.mk_isDiag_iff] using b.ne

theorem edge_eq_mk_iff {b : Bond n} {i j : Fin n} :
    b.edge = s(i, j) ↔ (b.src = i ∧ b.dst = j) ∨ (b.src = j ∧ b.dst = i) :=
  Sym2.eq_iff

/-- A bond never joins an atom to itself. -/
theorem edge_ne_diag (b : Bond n) (i : Fin n) : b.edge ≠ s(i, i) := by
  intro h
  rcases edge_eq_mk_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact b.ne (h1.trans h2.symm)

theorem touches_iff {b : Bond n} {i : Fin n} : b.touches i = true ↔ i ∈ b.edge := by
  simp only [touches, edge, Bool.or_eq_true, beq_iff_eq, Sym2.mem_iff]
  exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩

/-- `0-1`, `1=2`, `2:3`, … -/
def toString (b : Bond n) : String :=
  s!"{b.src.val}{b.kind.symbol}{b.dst.val}"

instance : ToString (Bond n) := ⟨toString⟩

instance : Repr (Bond n) := ⟨fun b _ => Std.Format.text b.toString⟩

end Bond

end LeanSMILES
