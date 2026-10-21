import LeanSMILES.SMILES.Token
import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.SMILES.Parse

From tokens to a `Molecule`.  The grammar is a small state machine, the same
one RDKit and pysmiles run:

* an **anchor** — the atom the next bond attaches to;
* a **pending bond** — a bond symbol read since the last atom;
* a **branch stack** — anchors saved by `(` and restored by `)`;
* **open rings** — ring-closure labels waiting for their partner, each
  remembering the atom that opened it and any bond symbol written there;
* an **after-dot** flag — the next atom starts a new component.

Atom indices are the order of appearance in the string, exactly as in RDKit,
so a `Molecule` remembers the string's traversal order (which is what `@`/`@@`
and `/`/`\` refer to); `LeanSMILES.SMILES.Canon` is what forgets it.

The syntactic checks — self-bond, duplicate bond, unmatched branch or ring,
dangling bond symbol — are reported as `ParseError`s.  The result is a
`Molecule`, whose type already guarantees in-range endpoints, no self-bonds
and no duplicate bonds, so the checks are not repeated downstream.

`parse` also runs `Molecule.assignImplicitH`; `parseRaw` does not.
-/

namespace LeanSMILES.SMILES

/-- A bond symbol read and not yet attached. -/
structure PendingBond where
  kind : Option BondKind := none
  dir : Option BondDir := none
  pos : ℕ
  deriving Repr, Inhabited

/-- A bond between atom indices, before they are known to be in range. -/
structure RawBond where
  src : ℕ
  dst : ℕ
  kind : BondKind
  dir : Option BondDir
  pos : ℕ
  deriving Repr, Inhabited

/-- A ring-closure label waiting for its partner. -/
structure RingOpen where
  atom : ℕ
  bond : Option PendingBond
  pos : ℕ
  deriving Repr, Inhabited

/-- Parser state. -/
structure State where
  atoms : Array Atom := #[]
  bonds : Array RawBond := #[]
  anchor : Option ℕ := none
  pending : Option PendingBond := none
  afterDot : Bool := false
  /-- The previous token was `(`: RDKit rejects `()` and a ring digit here. -/
  justOpened : Bool := false
  branches : List ℕ := []
  rings : List (ℕ × RingOpen) := []
  deriving Repr, Inhabited

namespace State

/-- The bond kind when none is written: aromatic between two aromatic atoms,
single otherwise. -/
def implicitKind (a b : Atom) : BondKind :=
  if a.aromatic && b.aromatic then .aromatic else .single

def atomAt (st : State) (i : ℕ) : Atom := st.atoms.getD i default

def hasBond (st : State) (i j : ℕ) : Bool :=
  st.bonds.any fun b => (b.src == i && b.dst == j) || (b.src == j && b.dst == i)

def addBond (st : State) (src dst : ℕ) (kind : BondKind) (dir : Option BondDir) (pos : ℕ) :
    Except ParseError State :=
  if src == dst then .error (.selfBond pos src)
  else if st.hasBond src dst then .error (.duplicateBond pos src dst)
  else .ok { st with bonds := st.bonds.push ⟨src, dst, kind, dir, pos⟩ }

def setPending (st : State) (p : PendingBond) : Except ParseError State :=
  match st.pending with
  | some q => .error (.bondWithoutAtom q.pos)
  | none => .ok { st with pending := some p }

/-- Consume one token. -/
def step (st : State) (t : Token) : Except ParseError State :=
  match t.kind with
  | .atom a =>
    let idx := st.atoms.size
    let st' := { st with atoms := st.atoms.push a }
    match st.anchor, st.afterDot with
    | some k, false => do
      let kind := (st.pending.bind (·.kind)).getD (implicitKind (st.atomAt k) a)
      let dir := st.pending.bind (·.dir)
      let st'' ← st'.addBond k idx kind dir t.pos
      pure { st'' with anchor := some idx, pending := none, justOpened := false }
    | _, _ =>
      match st.pending with
      | some p => .error (.bondWithoutAtom p.pos)
      | none => .ok { st' with anchor := some idx, afterDot := false, justOpened := false }
  | .bond k => st.setPending ⟨some k, none, t.pos⟩
  -- `/` and `\` leave the kind implicit: between two aromatic atoms the bond
  -- stays aromatic (RDKit's reading), otherwise it is single.
  | .dirBond d => st.setPending ⟨none, some d, t.pos⟩
  -- RDKit rejects a `.` before the first atom and `..`; a trailing `.` is caught by `finish`.
  | .dot =>
    match st.pending with
    | some p => .error (.bondWithoutAtom p.pos)
    | none =>
      if st.anchor.isNone || st.afterDot then .error (.danglingDot t.pos)
      else .ok { st with afterDot := true, justOpened := false }
  | .branchOpen =>
    match st.anchor, st.pending with
    | none, _ => .error (.branchWithoutAtom t.pos)
    | _, some p => .error (.bondWithoutAtom p.pos)
    | some k, none => .ok { st with branches := k :: st.branches, justOpened := true }
  | .branchClose =>
    match st.branches, st.pending with
    | [], _ => .error (.unmatchedBranchClose t.pos)
    | _, some p => .error (.bondWithoutAtom p.pos)
    | k :: rest, none =>
      if st.justOpened then .error (.emptyBranch t.pos)
      else .ok { st with anchor := some k, branches := rest, afterDot := false }
  | .ring num =>
    match st.anchor with
    | none => .error (.ringWithoutAtom t.pos)
    | some a =>
      if st.justOpened then .error (.ringAfterBranchOpen t.pos) else
      match st.rings.lookup num with
      | some ro => do
        let kind ← match ro.bond.bind (·.kind), st.pending.bind (·.kind) with
          | some k₁, some k₂ =>
            if k₁ == k₂ then pure k₁ else throw (.conflictingRingBond t.pos num)
          | some k, none | none, some k => pure k
          | none, none => pure (implicitKind (st.atomAt ro.atom) (st.atomAt a))
        let dir := (st.pending.bind (·.dir)) <|> (ro.bond.bind (·.dir))
        let st' ← st.addBond ro.atom a kind dir t.pos
        pure { st' with rings := st.rings.filter (·.1 != num), pending := none }
      | none =>
        .ok { st with rings := (num, ⟨a, st.pending, t.pos⟩) :: st.rings, pending := none }

/-- End-of-input checks. -/
def finish (st : State) : Except ParseError State :=
  match st.pending with
  | some p => .error (.bondWithoutAtom p.pos)
  | none =>
    if st.afterDot then .error (.unexpectedEnd "an atom after '.'")
    else if !st.branches.isEmpty then .error (.unclosedBranch st.branches.length)
    else if !st.rings.isEmpty then .error (.unclosedRing (st.rings.map (·.1)))
    else .ok st

/-- Package the state as a `Molecule`, discharging the type's invariants by
decision: endpoints in range, no self-bond, no duplicate edge. -/
def toMolecule (st : State) : Except ParseError Mol := do
  let bonds ← st.bonds.toList.mapM fun (b : RawBond) =>
    if h₁ : b.src < st.atoms.size then
      if h₂ : b.dst < st.atoms.size then
        if h₃ : b.src ≠ b.dst then
          pure (⟨⟨b.src, h₁⟩, ⟨b.dst, h₂⟩, b.kind, b.dir, Fin.ne_of_val_ne h₃⟩ :
            Bond st.atoms.size)
        else throw (.selfBond b.pos b.src)
      else throw (.internal "bond endpoint out of range")
    else throw (.internal "bond endpoint out of range")
  if h : (bonds.map Bond.edge).Nodup then
    pure ⟨st.atoms.size, { atoms := ⟨st.atoms, rfl⟩, bonds := bonds, nodup := h }⟩
  else throw (.internal "duplicate bond survived parsing")

end State

/-- Run the state machine over a token array. -/
def run (toks : Array Token) : Except ParseError State :=
  toks.foldlM State.step {} >>= State.finish

/-- Parse a SMILES string to a molecule, without assigning implicit hydrogens. -/
def parseRaw (s : String) : Except ParseError Mol := do
  let toks ← tokenize s
  let st ← run toks
  st.toMolecule

/-- Parse a SMILES string to a molecule, with implicit hydrogens assigned by
the default-valence rule. -/
def parse (s : String) : Except ParseError Mol := do
  let M ← parseRaw s
  pure ⟨M.n, M.mol.assignImplicitH⟩

end LeanSMILES.SMILES

namespace LeanSMILES

instance : Inhabited Mol :=
  ⟨⟨0, { atoms := ⟨#[], rfl⟩, bonds := [], nodup := List.nodup_nil }⟩⟩

/-- Parse, or panic with the error: for examples and tests. -/
def Mol.ofSmiles! (s : String) : Mol :=
  match SMILES.parse s with
  | .ok M => M
  | .error e => panic! s!"invalid SMILES {s.quote}: {e}"

end LeanSMILES
