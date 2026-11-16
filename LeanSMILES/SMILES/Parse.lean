/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson, Hao Liu
-/
module

public import LeanSMILES.SMILES.Token
public import LeanSMILES.Chem.Molecule

/-!
# LeanSMILES.SMILES.Parse

From tokens to a `Molecule`.  The grammar is a small state machine, the same
one RDKit and pysmiles run:

* an **anchor** — the atom the next bond attaches to;
* a **pending bond** — a bond symbol read since the last atom;
* a **branch stack** — anchors saved by `(` and restored by `)`;
* **open rings** — ring-closure labels waiting for their partner, each
  remembering the atom that opened it and any bond symbol written there;
* an **after-dot** flag — the next atom starts a new component;
* an **after-branch** flag — `)` was just read, so a ring-closure label is an
  error: OpenSMILES puts labels before branches (`atom ringbond* branch*`),
  which RDKit does not enforce.  This is the one place the grammar is
  deliberately stricter than RDKit on real-world input; see "What the parser
  accepts" in the README.

Atom indices are the order of appearance in the string, exactly as in RDKit,
so a `Molecule` remembers the string's traversal order (which is what `/`/`\`
refer to); `LeanSMILES.SMILES.Canon` is what forgets it.

**Tetrahedral marks.** `@` and `@@` are relative to the order in which the
string lists a centre's neighbors (OpenSMILES §3.7): the atom it was reached
from, then the implicit hydrogen of `[C@H]`, then its ring-closure digits in
the order written, then its branches and the chain.  The state keeps that
order for every atom (`nbrs`); a ring-closure digit takes its place at the
*opening* atom when it is read and is filled in when the ring closes.  A
centre with three listed neighbors and no hydrogen (a sulfoxide sulfur) gets
its lone pair as the fourth, last — RDKit's reading.  `toMolecule` turns each
mark and order into an order-independent configuration (`Molecule.stereo`,
`Tetra.ofMark`) and clears the mark from the atom; a tetrahedral mark on an
atom without four such ligands is dropped.

**Cis/trans marks.** `/` and `\` are relative to the direction the string
writes a single bond in (`Bond.dir`, from `src` to `dst`): seen from one end,
a mark is a *flag* for the atom at the other end (`dirFlagAt`), and two
substituents of a double bond with equal flags are cis.  A double bond with
a marked substituent at each end gets the arrangement those two determine,
each end's other substituent — or its hydrogen — lying opposite (`planarOf`);
both ends carry it.  A double bond on a ring of fewer than eight atoms gets
none, as in RDKit and InChI.  The marks stay on the bonds as written.

The syntactic checks — self-bond, duplicate bond, unmatched branch or ring,
dangling bond symbol — are reported as `ParseError`s.  The result is a
`Molecule`, whose type already guarantees in-range endpoints, no self-bonds
and no duplicate bonds, so the checks are not repeated downstream.

`parse` also runs `Molecule.assignImplicitH`; `parseRaw` does not.
-/

@[expose] public section

namespace LeanSMILES.SMILES

/-- A bond symbol read and not yet attached. -/
structure PendingBond where
  /-- The kind written, if any. -/
  kind : Option BondKind := none
  /-- The `/` `\` mark, if written. -/
  dir : Option BondDir := none
  /-- Position of the symbol. -/
  pos : ℕ
  deriving Repr, Inhabited

/-- A bond between atom indices, before they are known to be in range. -/
structure RawBond where
  /-- Index of the first atom. -/
  src : ℕ
  /-- Index of the second atom. -/
  dst : ℕ
  /-- The bond kind. -/
  kind : BondKind
  /-- The `/` `\` mark, if written. -/
  dir : Option BondDir
  /-- Position of the token that created the bond. -/
  pos : ℕ
  deriving Repr, Inhabited

/-- A ring-closure label waiting for its partner. -/
structure RingOpen where
  /-- The atom that opened the ring. -/
  atom : ℕ
  /-- The bond symbol written at the opening, if any. -/
  bond : Option PendingBond
  /-- Position of the opening label. -/
  pos : ℕ
  /-- The digit's place in the opening atom's neighbor order (`State.nbrs`). -/
  slot : ℕ
  deriving Repr, Inhabited

/-- Parser state: the state machine of the module docstring, advanced by `step` on each token and
checked by `finish` at end of input. -/
structure State where
  /-- Atoms so far, in order of appearance. -/
  atoms : Array Atom := #[]
  /-- Bonds so far. -/
  bonds : Array RawBond := #[]
  /-- The atom the next bond attaches to. -/
  anchor : Option ℕ := none
  /-- A bond symbol read and not yet attached. -/
  pending : Option PendingBond := none
  /-- The next atom starts a new component. -/
  afterDot : Bool := false
  /-- The previous token was `(`: RDKit rejects `()` and a ring digit here. -/
  justOpened : Bool := false
  /-- The previous token was `)` (possibly followed by a bond symbol): a
  ring-closure label here is rejected, as OpenSMILES orders labels before
  branches. -/
  afterBranch : Bool := false
  /-- Anchors saved by `(`, innermost first. -/
  branches : List ℕ := []
  /-- Open ring labels with the atom and bond symbol that opened them. -/
  rings : List (ℕ × RingOpen) := []
  /-- Each atom's neighbors in the order the string lists them, `none` for a
  written hydrogen: what `@`/`@@` are relative to. -/
  nbrs : Array (Array (Option ℕ)) := #[]
  deriving Repr, Inhabited

namespace State

/-- The bond kind when none is written: aromatic between two aromatic atoms,
single otherwise. -/
def implicitKind (a b : Atom) : BondKind :=
  if a.aromatic && b.aromatic then .aromatic else .single

/-- The atom with index `i` (a default atom if out of range). -/
def atomAt (st : State) (i : ℕ) : Atom := st.atoms.getD i default

/-- Whether a bond between `i` and `j`, in either orientation, has already been created. -/
def hasBond (st : State) (i j : ℕ) : Bool :=
  st.bonds.any fun b ↦ (b.src == i && b.dst == j) || (b.src == j && b.dst == i)

/-- Add the bond `src`–`dst`; `src = dst` is `ParseError.selfBond` and a pair already bonded is
`ParseError.duplicateBond`, both reported at `pos`. -/
def addBond (st : State) (src dst : ℕ) (kind : BondKind) (dir : Option BondDir) (pos : ℕ) :
    Except ParseError State :=
  if src == dst then .error (.selfBond pos src)
  else if st.hasBond src dst then .error (.duplicateBond pos src dst)
  else .ok { st with bonds := st.bonds.push ⟨src, dst, kind, dir, pos⟩ }

/-- Record a bond symbol as pending; a second symbol before an atom is `ParseError.bondWithoutAtom`
at the position of the first. -/
def setPending (st : State) (p : PendingBond) : Except ParseError State :=
  match st.pending with
  | some q => .error (.bondWithoutAtom q.pos)
  | none => .ok { st with pending := some p }

/-- Consume one token, advancing the state machine of the module docstring.  The bond, branch,
dot and ring-closure `ParseError`s are raised here; `finish` raises the end-of-input ones. -/
def step (st : State) (t : Token) : Except ParseError State :=
  match t.kind with
  | .atom a =>
    let idx := st.atoms.size
    let st' := { st with atoms := st.atoms.push a }
    let hs : Array (Option ℕ) := Array.replicate (a.explicitH.getD 0) none
    match st.anchor, st.afterDot with
    | some k, false => do
      let kind := (st.pending.bind (·.kind)).getD (implicitKind (st.atomAt k) a)
      let dir := st.pending.bind (·.dir)
      let st'' ← st'.addBond k idx kind dir t.pos
      pure { st'' with anchor := some idx, pending := none, justOpened := false,
                       afterBranch := false,
                       nbrs := (st.nbrs.modify k (·.push (some idx))).push (#[some k] ++ hs) }
    | _, _ =>
      match st.pending with
      | some p => .error (.bondWithoutAtom p.pos)
      | none => .ok { st' with anchor := some idx, afterDot := false, justOpened := false,
                               afterBranch := false, nbrs := st.nbrs.push hs }
  | .bond k => st.setPending ⟨some k, none, t.pos⟩
  -- `/` and `\` leave the kind implicit: between two aromatic atoms the bond
  -- stays aromatic (RDKit's reading), otherwise it is single.
  | .dirBond d => st.setPending ⟨none, some d, t.pos⟩
  -- RDKit rejects a `.` before the first atom and `..`; a trailing `.` is caught by `finish`.
  | .dot =>
    match st.pending with
    | some p => .error (.bondWithoutAtom p.pos)
    | none =>
      if st.anchor.isNone || st.afterDot || st.justOpened then .error (.danglingDot t.pos)
      else .ok { st with afterDot := true, justOpened := false }
  | .branchOpen =>
    match st.anchor, st.pending with
    | none, _ => .error (.branchWithoutAtom t.pos)
    | _, some p => .error (.bondWithoutAtom p.pos)
    | some k, none =>
      if st.afterDot then .error (.branchWithoutAtom t.pos)
      else .ok { st with branches := k :: st.branches, justOpened := true, afterBranch := false }
  | .branchClose =>
    match st.branches, st.pending with
    | [], _ => .error (.unmatchedBranchClose t.pos)
    | _, some p => .error (.bondWithoutAtom p.pos)
    | k :: rest, none =>
      if st.afterDot then .error (.danglingDot (t.pos - 1))
      else if st.justOpened then .error (.emptyBranch t.pos)
      else .ok { st with anchor := some k, branches := rest, afterDot := false,
                         afterBranch := true }
  | .ring num =>
    match st.anchor with
    | none => .error (.ringWithoutAtom t.pos)
    | some a =>
      if st.afterDot then .error (.ringWithoutAtom t.pos)
      else if st.justOpened then .error (.ringAfterBranchOpen t.pos)
      else if st.afterBranch then .error (.ringAfterBranch t.pos) else
      match st.rings.lookup num with
      | some ro => do
        let kind ← match ro.bond.bind (·.kind), st.pending.bind (·.kind) with
          | some k₁, some k₂ =>
            if k₁ == k₂ then pure k₁ else throw (.conflictingRingBond t.pos num)
          | some k, none | none, some k => pure k
          | none, none => pure (implicitKind (st.atomAt ro.atom) (st.atomAt a))
        -- the bond is stored opening → closing; a `/` `\` at the closing digit is
        -- written from the closing atom towards the opening one, so it flips
        let dir := (st.pending.bind (·.dir)).map BondDir.flip <|> (ro.bond.bind (·.dir))
        let st' ← st.addBond ro.atom a kind dir t.pos
        pure { st' with rings := st.rings.filter (·.1 != num), pending := none,
                        nbrs := (st.nbrs.modify ro.atom (·.set! ro.slot (some a))).modify a
                          (·.push (some ro.atom)) }
      | none =>
        -- the slot is a placeholder until the ring closes (`finish` rejects open rings)
        let ro : RingOpen := ⟨a, st.pending, t.pos, (st.nbrs.getD a #[]).size⟩
        .ok { st with rings := (num, ro) :: st.rings, pending := none,
                      nbrs := st.nbrs.modify a (·.push (some a)) }

/-- End-of-input checks: a pending bond symbol, a trailing `.`, an unclosed branch or an unclosed
ring is a `ParseError`; otherwise the state is returned unchanged. -/
def finish (st : State) : Except ParseError State :=
  match st.pending with
  | some p => .error (.bondWithoutAtom p.pos)
  | none =>
    if st.afterDot then .error (.unexpectedEnd "an atom after '.'")
    else if !st.branches.isEmpty then .error (.unclosedBranch st.branches.length)
    else if !st.rings.isEmpty then .error (.unclosedRing (st.rings.reverse.map (·.1)))
    else .ok st

/-- An atom's listed neighbors as the four ligands of a tetrahedral centre, a
lone pair appended when three neighbors and no hydrogen are listed; `none`
unless there are exactly four. -/
def ligandsOf (N : ℕ) (a : Atom) (listed : Array (Option ℕ)) : Option (Ligands N) :=
  let listed := if listed.size == 3 && a.explicitH.getD 0 == 0 then listed.push none else listed
  let toFin : Option ℕ → Option (Option (Fin N))
    | none => some none
    | some i => if h : i < N then some (some ⟨i, h⟩) else none
  listed.toList.mapM toFin >>= Ligands.ofList?

/-- The configuration an atom's tetrahedral mark writes with its neighbors
listed as `listed`. -/
def tetraOf (N : ℕ) (a : Atom) (listed : Array (Option ℕ)) : Option (Tetra N) := do
  let anticlockwise ← a.chirality.bind Chirality.tetrahedral
  let o ← ligandsOf N a listed
  pure (Tetra.ofMark o anticlockwise)

/-- The atom without its tetrahedral mark, which `toMolecule` moves into
`Molecule.stereo`. -/
def clearTetrahedral (a : Atom) : Atom :=
  if (a.chirality.bind Chirality.tetrahedral).isSome then { a with chirality := none } else a

/-- A `/` `\` mark as seen from `atom`, one end of the bond: a flag for the
atom at the other end. Two substituents of a double bond whose flags, seen
from its two ends, are equal lie cis. -/
def dirFlagAt {N : ℕ} (b : Bond N) (atom : Fin N) : Option Bool :=
  b.dir.map fun d ↦ if b.src = atom then d != .up else d == .up

/-- Whether the bond `b` lies on a ring of fewer than eight atoms: its ends are
joined by a path of at most six other bonds (`adj`: neighbors by index). In so
small a ring a double bond has only one possible arrangement, and RDKit and
InChI give it none. -/
def inSmallRing {N : ℕ} (adj : Array (List ℕ)) (b : Bond N) : Bool := Id.run do
  let (u, v) := (b.src.val, b.dst.val)
  let mut frontier := [u]
  let mut seen := [u]
  for depth in [0:6] do
    let mut next := []
    for x in frontier do
      for y in adj.getD x [] do
        if depth == 0 && y == v then continue
        if y == v then return true
        if !seen.contains y then
          seen := y :: seen
          next := y :: next
    frontier := next
  return false

/-- The cis/trans arrangement the marks give the double bond `b`: at each end
the first substituent (in bond order) whose bond carries a mark, with its
flag; the end's other substituent, or `none` for its hydrogen, opposite.
`none` unless both ends have a marked substituent, and for a double bond on a
ring of fewer than eight atoms (`inSmallRing`). -/
def planarOf {N : ℕ} (bonds : List (Bond N)) (adj : Array (List ℕ)) (b : Bond N) :
    Option (Planar N) := do
  guard (b.kind == .double && !inSmallRing adj b)
  let around (x : Fin N) : List (Bond N) :=
    bonds.filter fun e ↦ e.touches x && e.edge != b.edge
  let marked (x : Fin N) : Option (Fin N × Bool) :=
    (around x).findSome? fun e ↦ (dirFlagAt e x).map (e.other x, ·)
  let other (x s : Fin N) : Option (Fin N) := ((around x).map (·.other x)).find? (· != s)
  let (a, fa) ← marked b.src
  let (c, fc) ← marked b.dst
  pure (Planar.ofCis (some a) (other b.src a) (some c) (other b.dst c) (fa == fc))

/-- Package the state as a `Molecule`, discharging the type's invariants by
decision: endpoints in range, no self-bond, no duplicate edge.  Tetrahedral
marks become configurations (`tetraOf`), and `/` `\` around a double bond its
arrangement (`planarOf`), at both of its ends. -/
def toMolecule (st : State) : Except ParseError Mol := do
  let bonds ← st.bonds.toList.mapM fun (b : RawBond) ↦
    if h₁ : b.src < st.atoms.size then
      if h₂ : b.dst < st.atoms.size then
        if h₃ : b.src ≠ b.dst then
          pure (⟨⟨b.src, h₁⟩, ⟨b.dst, h₂⟩, b.kind, b.dir, Fin.ne_of_val_ne h₃⟩ :
            Bond st.atoms.size)
        else throw (.selfBond b.pos b.src)
      else throw (.internal "bond endpoint out of range")
    else throw (.internal "bond endpoint out of range")
  if h : (bonds.map Bond.edge).Nodup then
    let adj : Array (List ℕ) := bonds.foldl (init := Array.replicate st.atoms.size [])
      fun adj b ↦ (adj.modify b.src (b.dst.val :: ·)).modify b.dst (b.src.val :: ·)
    let planarAt (i : Fin st.atoms.size) : Option (Planar st.atoms.size) :=
      (bonds.filter (·.touches i)).findSome? (planarOf bonds adj)
    let stereo : Vector (Option (Stereo st.atoms.size)) st.atoms.size :=
      Vector.ofFn fun i ↦
        (tetraOf st.atoms.size st.atoms[i] (st.nbrs.getD i #[])).map .tetra <|>
          (planarAt i).map .planar
    pure ⟨st.atoms.size, { atoms := ⟨st.atoms.map clearTetrahedral, Array.size_map ..⟩,
                           bonds := bonds, nodup := h, stereo := stereo }⟩
  else throw (.internal "duplicate bond survived parsing")

end State

/-- Run the state machine over a token array: `State.step` on each token, then `State.finish`. -/
def run (toks : Array Token) : Except ParseError State :=
  toks.foldlM State.step {} >>= State.finish

/-- Parse a SMILES string to a molecule, without assigning implicit hydrogens: `tokenize`, `run`,
`State.toMolecule`, each of which may return a `ParseError`. -/
def parseRaw (s : String) : Except ParseError Mol := do
  let toks ← tokenize s
  let st ← run toks
  st.toMolecule

/-- Parse a SMILES string to a molecule, with implicit hydrogens assigned by the default-valence
rule (`Molecule.assignImplicitH`): the parser callers want; `parseRaw` skips that pass. -/
def parse (s : String) : Except ParseError Mol := do
  let M ← parseRaw s
  pure ⟨M.n, M.mol.assignImplicitH⟩

end LeanSMILES.SMILES

namespace LeanSMILES

-- The empty molecule, so that `Mol.ofSmiles!` may `panic!`.
instance : Inhabited Mol :=
  ⟨⟨0, { atoms := ⟨#[], rfl⟩, bonds := [], nodup := List.nodup_nil, stereo := ⟨#[], rfl⟩ }⟩⟩

-- Irreducible so that `(Mol.ofSmiles! s).n` is atomic to the elaborator: a `#eval` whose result
-- type mentions it (a `Molecule (Mol.ofSmiles! s).n`, a `Vector α (Mol.ofSmiles! s).n`) would
-- otherwise make `whnf` run the parser symbolically, which does not terminate in practice for an
-- aromatic ring.  Compiled code is unaffected (design notes §8).
/-- Parse, or panic with the error: for examples and tests.  Irreducible, so that a type mentioning
`(Mol.ofSmiles! s).n` does not make the elaborator run the parser symbolically. -/
@[irreducible] def Mol.ofSmiles! (s : String) : Mol :=
  match SMILES.parse s with
  | .ok M => M
  | .error e => panic! s!"invalid SMILES {s.quote}: {e}"

end LeanSMILES
