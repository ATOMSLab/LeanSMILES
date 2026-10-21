import LeanSMILES.Canonical.Molecule

/-!
# LeanSMILES.Canonical.Parse

SMILES text → molecule graph.
-/

/-!
# SMILES parser

Turns a SMILES string into a `Chem.Mol`, following what RDKit's parser does
*before* sanitization:

* atoms are numbered in the order they appear;
* a bond with no symbol is aromatic if both atoms are lowercase, otherwise single;
* ring-closure digits (`1`–`9`, `%nn`) join the two atoms that carry them;
* `(` `)` open and close branches, `.` starts a new fragment.

Supported: organic-subset atoms, lowercase aromatic atoms, bracket atoms
(isotope, element, chirality marks, H count, charge, atom class), bonds
`- = # :` and `/ \` (read as single; stereo is ignored).
-/

namespace Smiles

open Chem

/-- Kind of the last token read, for the SMILES syntax rules. -/
private inductive Tok where
  | start | atom | ring | openBranch | closeBranch | dot | bond
  /-- a bond symbol directly after `(`, as in `C(=O)` -/
  | branchBond
  deriving BEq

/-- A bond written in the SMILES; `directional` for `/` and `\`. -/
private structure WrittenBond where
  order : BondOrder
  directional : Bool := false

/-- An open ring-closure digit: the atom it is on and the bond written there. -/
private structure OpenRing where
  digit : Nat
  atom : Nat
  bond : Option WrittenBond

private structure St where
  pos : Nat := 0
  atoms : Array Atom := #[]
  bonds : Array Bond := #[]
  prev : Option Nat := none
  branches : List (Option Nat) := []
  pending : Option WrittenBond := none
  rings : List OpenRing := []
  last : Tok := .start

private def defaultOrder (atoms : Array Atom) (i j : Nat) : BondOrder :=
  if atoms[i]!.aromatic && atoms[j]!.aromatic then .aromatic else .single

private def bondSymbol? : Char → Option WrittenBond
  | '-' => some ⟨.single, false⟩ | '=' => some ⟨.double, false⟩ | '#' => some ⟨.triple, false⟩
  | ':' => some ⟨.aromatic, false⟩ | '/' => some ⟨.single, true⟩ | '\\' => some ⟨.single, true⟩
  | _ => none

/-- RDKit's syntax rules: which tokens may come directly before each kind of token
(checked against `MolFromSmiles`: e.g. `=CC`, `CC=`, `C-=C`, `C()C`, `C=(C)C`,
`(C)C`, `C(1)CC1`, `C(=1)CC1`, `C..C` and `C.` are all rejected). -/
private def allowedBefore : Tok → List Tok
  | .openBranch | .closeBranch | .dot => [.atom, .ring, .closeBranch]
  | .bond => [.atom, .ring, .closeBranch]
  | .branchBond => [.openBranch]
  | .ring => [.atom, .ring, .closeBranch, .bond]
  | .atom | .start => [.start, .atom, .ring, .openBranch, .closeBranch, .dot, .bond, .branchBond]

private def tokName : Tok → String
  | .start => "start" | .atom => "atom" | .ring => "ring-closure digit"
  | .openBranch => "'('" | .closeBranch => "')'" | .dot => "'.'"
  | .bond | .branchBond => "bond symbol"

/-- Check that token `t` may follow the previous token. -/
private def expect (st : St) (t : Tok) : Except String Unit :=
  if (allowedBefore t).contains st.last then pure ()
  else throw s!"{tokName t} cannot follow {tokName st.last} at position {st.pos}"

/-- Read a run of decimal digits starting at `pos`. -/
private def readNat (cs : Array Char) (pos : Nat) : Option (Nat × Nat) := Id.run do
  let mut p := pos
  let mut n := 0
  while h : p < cs.size do
    let c := cs[p]
    if c.isDigit then
      n := 10 * n + (c.toNat - '0'.toNat)
      p := p + 1
    else break
  return if p == pos then none else some (n, p)

/-- Element symbol at `pos` inside brackets. A bracket holds a single atom, so an
uppercase letter followed by a lowercase one is always a two-letter symbol. -/
private def readBracketElement (cs : Array Char) (pos : Nat) :
    Except String (Nat × Bool × Nat) := do
  let c0 := cs.getD pos ' '
  let c1 := cs.getD (pos + 1) ' '
  if c0.isUpper then
    let sym := if c1.isLower then String.ofList [c0, c1] else String.singleton c0
    match ofSymbol? sym with
    | some z => return (z, false, pos + sym.length)
    | none => throw s!"unsupported element {sym} at position {pos}"
  else
    let two := String.ofList [c0, c1]
    if aromaticSymbols.contains two then
      if let some z := ofSymbol? (two.capitalize) then return (z, true, pos + 2)
    if aromaticSymbols.contains (String.singleton c0) then
      if let some z := ofSymbol? (String.singleton c0.toUpper) then return (z, true, pos + 1)
    throw s!"unsupported element at position {pos}"

/-- Parse a bracket atom starting just after `[`. Returns the atom and the position after `]`. -/
private def readBracketAtom (cs : Array Char) (pos : Nat) : Except String (Atom × Nat) := do
  let mut p := pos
  let mut isotope := none
  if let some (n, q) := readNat cs p then
    isotope := some n
    p := q
  let (z, arom, q) ← readBracketElement cs p
  p := q
  -- chirality marks are skipped (stereo is not modelled), but must be well formed:
  -- `@`, `@@`, or `@` + class TH/AL/SP/TB/OH + optional number (as RDKit accepts)
  let mut nonTetrahedral := false
  if cs.getD p ' ' == '@' then
    p := p + 1
    if cs.getD p ' ' == '@' then
      p := p + 1
    else
      let cls := String.ofList [cs.getD p ' ', cs.getD (p + 1) ' ']
      if ["TH", "AL", "SP", "TB", "OH"].contains cls then
        nonTetrahedral := ["SP", "TB", "OH"].contains cls
        p := p + 2
        if let some (_, q) := readNat cs p then p := q
  let mut hs := 0
  if cs.getD p ' ' == 'H' then
    p := p + 1
    match readNat cs p with
    | some (n, q) => hs := n; p := q
    | none => hs := 1
  let mut charge : Int := 0
  let sign := cs.getD p ' '
  if sign == '+' || sign == '-' then
    let s : Int := if sign == '+' then 1 else -1
    p := p + 1
    match readNat cs p with
    | some (n, q) => charge := s * n; p := q
    | none =>
      charge := s
      while cs.getD p ' ' == sign do
        charge := charge + s
        p := p + 1
  if cs.getD p ' ' == ':' then
    match readNat cs (p + 1) with
    | some (_, q) => p := q
    | none => throw s!"atom class without number at position {p}"
  if cs.getD p ' ' != ']' then throw s!"expected ']' at position {p}"
  return ({ atomicNum := z, aromatic := arom, charge, isotope, explicitHs := hs,
            noImplicit := true, nonTetrahedral }, p + 1)

/-- Unbracketed atom at `pos` (organic subset or lowercase aromatic). -/
private def readOrganicAtom (cs : Array Char) (pos : Nat) : Option (Atom × Nat) :=
  let c0 := cs.getD pos ' '
  let c1 := cs.getD (pos + 1) ' '
  if (c0 == 'C' && c1 == 'l') || (c0 == 'B' && c1 == 'r') then
    (ofSymbol? (String.ofList [c0, c1])).map fun z => ({ atomicNum := z }, pos + 2)
  else if organicSubset.contains (String.singleton c0) then
    (ofSymbol? (String.singleton c0)).map fun z => ({ atomicNum := z }, pos + 1)
  else if aromaticSymbols.contains (String.singleton c0) then
    (ofSymbol? (String.singleton c0.toUpper)).map fun z =>
      ({ atomicNum := z, aromatic := true }, pos + 1)
  else none

/-- Order of a bond written as `w` (or not written) between atoms `j` and `i`.
`/` and `\` only add a direction: between two aromatic atoms the bond stays
aromatic, as in RDKit (`Cc1coc/c1C`). -/
private def writtenOrder (w : Option WrittenBond) (atoms : Array Atom) (j i : Nat) : BondOrder :=
  match w with
  | some b => if b.directional then defaultOrder atoms j i else b.order
  | none => defaultOrder atoms j i

/-- Add an atom and bond it to the previous atom, if any. -/
private def addAtom (st : St) (a : Atom) (next : Nat) : St :=
  let i := st.atoms.size
  let atoms := st.atoms.push a
  let bonds := match st.prev with
    | some j => st.bonds.push { src := j, dst := i, order := writtenOrder st.pending atoms j i,
                                directional := (st.pending.map (·.directional)).getD false }
    | none => st.bonds
  { st with pos := next, atoms, bonds, prev := some i, pending := none, last := .atom }

/-- Open or close ring-closure digit `d` at the current atom. -/
private def ringClosure (st : St) (d next : Nat) : Except String St := do
  let some i := st.prev | throw s!"ring-closure digit {d} before any atom"
  match st.rings.find? (·.digit == d) with
  | some r =>
    let j := r.atom
    if j == i then throw s!"ring closure {d} bonds an atom to itself"
    if st.bonds.any fun b => (b.src == j && b.dst == i) || (b.src == i && b.dst == j) then
      throw s!"ring closure {d} duplicates an existing bond"
    let directional := (r.bond.map (·.directional)).getD false ||
      (st.pending.map (·.directional)).getD false
    -- RDKit: the bond written at the opening digit wins, unless it is / or \
    let order := match r.bond with
      | some ob => if ob.directional then writtenOrder st.pending st.atoms j i else ob.order
      | none => writtenOrder st.pending st.atoms j i
    return { st with pos := next, pending := none, last := .ring,
                     bonds := st.bonds.push { src := j, dst := i, order, directional },
                     rings := st.rings.filter (·.digit != d) }
  | none =>
    return { st with pos := next, pending := none, last := .ring,
                     rings := { digit := d, atom := i, bond := st.pending } :: st.rings }

/-- Ring-closure number after `%`: two digits (`%12`) or any number in
parentheses (`%(123)`). Returns the number and the position after it. -/
private def readPercent (cs : Array Char) (pos : Nat) : Except String (Nat × Nat) := do
  if cs.getD pos ' ' == '(' then
    match readNat cs (pos + 1) with
    | some (d, q) => if cs.getD q ' ' == ')' then return (d, q + 1)
                     else throw s!"expected ')' after '%(' at position {q}"
    | none => throw s!"'%(' without digits at position {pos}"
  let c1 := cs.getD pos ' '
  let c2 := cs.getD (pos + 1) ' '
  if c1.isDigit && c2.isDigit then
    return (10 * (c1.toNat - '0'.toNat) + (c2.toNat - '0'.toNat), pos + 2)
  throw s!"'%' must be followed by two digits at position {pos}"

def parse (s : String) : Except String Mol := do
  let cs := s.trimAscii.toString.toList.toArray
  let mut st : St := {}
  while h : st.pos < cs.size do
    let c := cs[st.pos]
    if c == '(' then
      expect st .openBranch
      st := { st with pos := st.pos + 1, branches := st.prev :: st.branches, last := .openBranch }
    else if c == ')' then
      expect st .closeBranch
      match st.branches with
      | top :: rest =>
        st := { st with pos := st.pos + 1, prev := top, branches := rest, last := .closeBranch }
      | [] => throw s!"unmatched ')' at position {st.pos}"
    else if c == '.' then
      expect st .dot
      st := { st with pos := st.pos + 1, prev := none, last := .dot }
    else if let some o := bondSymbol? c then
      let t := if st.last == .openBranch then Tok.branchBond else .bond
      expect st t
      st := { st with pos := st.pos + 1, pending := some o, last := t }
    else if c.isDigit then
      expect st .ring
      st ← ringClosure st (c.toNat - '0'.toNat) (st.pos + 1)
    else if c == '%' then
      expect st .ring
      let (d, q) ← readPercent cs (st.pos + 1)
      st ← ringClosure st d q
    else if c == '[' then
      let (a, q) ← readBracketAtom cs (st.pos + 1)
      st := addAtom st a q
    else match readOrganicAtom cs st.pos with
      | some (a, q) => st := addAtom st a q
      | none => throw s!"unexpected '{c}' at position {st.pos}"
  if ![Tok.start, .atom, .ring, .closeBranch].contains st.last then
    throw s!"SMILES cannot end with a {tokName st.last}"
  if !st.branches.isEmpty then throw "unclosed '('"
  if let some r := st.rings.head? then throw s!"ring closure {r.digit} never closed"
  return { atoms := st.atoms, bonds := st.bonds }

end Smiles
