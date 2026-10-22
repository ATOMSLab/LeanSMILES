module

public import LeanSMILES.Polymorphic.Chem.Graph

/-!
# SMILES — Parsing, writing and canonical form

* **Parsing** `SMILES → Molecule`: a tokenizer (`tokenize`) followed by a left fold over
  the tokens (`Molecule.ofTokens`).
* **Writing** `Molecule → SMILES`: a depth-first traversal that visits atoms in the order
  given by a ranking (`Molecule.toSMILESWith`).
* **Canonical SMILES**: writing with canonical ranks (`canonicalRanks`), which come from
  iterated neighbourhood refinement with tie-breaking (Weininger's CANON / CANGEN).

Every function is total and terminates by structural recursion, on the input or on an
explicit `fuel : Nat` bound, so everything runs with `#eval` and unfolds in proofs.

Supported SMILES: the organic subset (`B C N O P S F Cl Br I *` and aromatic
`b c n o p s`), bracket atoms with isotope, any element, hydrogen count and charge, bonds
`- = # :`, branches, ring closures `0-9` and `%nn`, and `.` for disconnected components.
Stereo marks (`/ \ @`) and atom classes are accepted but dropped. There is no
aromaticity perception, so the Kekulé and aromatic forms of a ring are different
molecules.
-/

@[expose] public section

namespace Chem

/-! ## Tokenizer -/

inductive Token where
  | atom (a : Atom)
  | bond (b : BondOrder)
  | openBranch
  | closeBranch
  | ring (d : Nat)
  | dot
  deriving DecidableEq, Repr

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Read a (possibly empty) run of decimal digits. -/
def readNat (cs : List Char) : Option Nat × List Char :=
  let ds := cs.takeWhile Char.isDigit
  if ds.isEmpty then (none, cs)
  else (some (ds.foldl (fun n c => 10 * n + digitVal c) 0), cs.drop ds.length)

/-- Single-character atoms outside brackets. -/
def organicAtom? : Char → Option Atom
  | 'B' => some { element := 5 }
  | 'C' => some { element := 6 }
  | 'N' => some { element := 7 }
  | 'O' => some { element := 8 }
  | 'F' => some { element := 9 }
  | 'P' => some { element := 15 }
  | 'S' => some { element := 16 }
  | 'I' => some { element := 53 }
  | 'b' => some { element := 5, aromatic := true }
  | 'c' => some { element := 6, aromatic := true }
  | 'n' => some { element := 7, aromatic := true }
  | 'o' => some { element := 8, aromatic := true }
  | 'p' => some { element := 15, aromatic := true }
  | 's' => some { element := 16, aromatic := true }
  | '*' => some { element := 0 }
  | _ => none

/-- Bond symbols. The directional bonds `/` and `\` are read as single bonds. -/
def bondSymbol? : Char → Option BondOrder
  | '-' => some .single
  | '=' => some .double
  | '#' => some .triple
  | ':' => some .aromatic
  | '/' => some .single
  | '\\' => some .single
  | _ => none

/-- The element symbol at the start of a bracket atom: `(atomic number, aromatic, rest)`. -/
def readElement : List Char → Except String (Nat × Bool × List Char)
  | 's' :: 'e' :: rest => .ok (34, true, rest)
  | 'a' :: 's' :: rest => .ok (33, true, rest)
  | 't' :: 'e' :: rest => .ok (52, true, rest)
  | c :: rest =>
    if c.isLower then
      match organicAtom? c with
      | some a => if a.aromatic then .ok (a.element, true, rest)
                  else .error s!"unknown aromatic element '{c}'"
      | none => .error s!"unknown aromatic element '{c}'"
    else
      let two := match rest with
        | d :: rest' => if d.isLower then (elementOf? (String.ofList [c, d])).map (·, rest')
                        else none
        | [] => none
      match two with
      | some (z, rest') => .ok (z, false, rest')
      | none =>
        match elementOf? (String.ofList [c]) with
        | some z => .ok (z, false, rest)
        | none => .error s!"unknown element '{c}'"
  | [] => .error "empty bracket atom"

/-- A charge `+`, `-`, `+n`, `-n`, `++`, `--`, … (or none). -/
def readCharge : List Char → Int × List Char
  | '+' :: rest =>
    match readNat rest with
    | (some k, rest') => (k, rest')
    | (none, _) => let k := (rest.takeWhile (· == '+')).length; (k + 1, rest.drop k)
  | '-' :: rest =>
    match readNat rest with
    | (some k, rest') => (-(k : Int), rest')
    | (none, _) => let k := (rest.takeWhile (· == '-')).length; (-((k + 1 : Nat) : Int), rest.drop k)
  | cs => (0, cs)

/-- The inside of `[...]`: isotope, element, chirality (dropped), H count, charge and atom
class (dropped). -/
def parseBracket (cs : List Char) : Except String Atom := do
  let (iso, cs) := readNat cs
  let (z, arom, cs) ← readElement cs
  let cs := cs.dropWhile (· == '@')
  let (h, cs) := match cs with
    | 'H' :: rest => let (k, rest) := readNat rest; (k.getD 1, rest)
    | _ => (0, cs)
  let (chg, cs) := readCharge cs
  let cs := match cs with
    | ':' :: rest => (readNat rest).2
    | _ => cs
  unless cs.isEmpty do throw s!"unexpected '{String.ofList cs}' in bracket atom"
  return { element := z, aromatic := arom, charge := chg, isotope := iso, explicitH := some h }

/-- Read one token. -/
def nextToken : List Char → Except String (Token × List Char)
  | 'C' :: 'l' :: rest => .ok (.atom { element := 17 }, rest)
  | 'B' :: 'r' :: rest => .ok (.atom { element := 35 }, rest)
  | '[' :: rest =>
    let inner := rest.takeWhile (· ≠ ']')
    match rest.drop inner.length with
    | ']' :: rest' => do return (.atom (← parseBracket inner), rest')
    | _ => .error "unclosed '['"
  | '(' :: rest => .ok (.openBranch, rest)
  | ')' :: rest => .ok (.closeBranch, rest)
  | '.' :: rest => .ok (.dot, rest)
  | '%' :: d₁ :: d₂ :: rest =>
    if d₁.isDigit && d₂.isDigit then .ok (.ring (10 * digitVal d₁ + digitVal d₂), rest)
    else .error "expected two digits after '%'"
  | c :: rest =>
    if c.isDigit then .ok (.ring (digitVal c), rest)
    else match organicAtom? c with
      | some a => .ok (.atom a, rest)
      | none => match bondSymbol? c with
        | some b => .ok (.bond b, rest)
        | none => .error s!"unexpected character '{c}'"
  | [] => .error "unexpected end of input"

/-- Split into tokens. Each token consumes at least one character, so `fuel = cs.length`
is enough. -/
def tokenize : Nat → List Char → Except String (List Token)
  | _, [] => .ok []
  | 0, _ :: _ => .error "tokenizer ran out of fuel"
  | fuel + 1, cs => do
    let (tok, rest) ← nextToken cs
    return tok :: (← tokenize fuel rest)

/-! ## Parser -/

/-- State of the left fold that turns tokens into a molecule. -/
structure BuildState where
  atoms : Array Atom := #[]
  bonds : Array Bond := #[]
  /-- The atom the next atom bonds to. -/
  prev : Option Nat := none
  /-- Atoms where open branches started. -/
  branches : List Nat := []
  /-- An explicit bond symbol waiting for the next atom or ring closure. -/
  pending : Option BondOrder := none
  /-- Open ring closures: `(digit, atom, bond symbol at the opening)`. -/
  rings : List (Nat × Nat × Option BondOrder) := []

/-- The bond implied by juxtaposition: aromatic between two aromatic atoms, else single. -/
def defaultBond (a b : Atom) : BondOrder :=
  if a.aromatic && b.aromatic then .aromatic else .single

def BuildState.addBond (st : BuildState) (i j : Nat) (explicit : Option BondOrder) :
    BuildState :=
  let order := explicit.getD (defaultBond (st.atoms.getD i default) (st.atoms.getD j default))
  { st with bonds := st.bonds.push ⟨i, j, order⟩ }

def buildStep (st : BuildState) : Token → Except String BuildState
  | .atom a => do
    let i := st.atoms.size
    let st := { st with atoms := st.atoms.push a }
    match st.prev with
    | some p => return { st.addBond p i st.pending with prev := some i, pending := none }
    | none =>
      if st.pending.isSome then throw "bond symbol before the first atom"
      return { st with prev := some i }
  | .bond b => do
    if st.pending.isSome then throw "two consecutive bond symbols"
    if st.prev.isNone then throw "bond symbol without a preceding atom"
    return { st with pending := some b }
  | .openBranch =>
    match st.prev with
    | some p => .ok { st with branches := p :: st.branches }
    | none => .error "branch without a preceding atom"
  | .closeBranch => do
    if st.pending.isSome then throw "bond symbol before ')'"
    match st.branches with
    | p :: bs => return { st with prev := some p, branches := bs }
    | [] => throw "unmatched ')'"
  | .ring d =>
    match st.prev with
    | none => .error "ring closure without a preceding atom"
    | some p =>
      match st.rings.find? (·.1 == d) with
      | some (_, q, opening) =>
        if q = p then .error "ring closure to the same atom"
        else
          let order := match st.pending with
            | some b => some b
            | none => opening
          .ok { st.addBond q p order with
                rings := st.rings.filter (·.1 != d), pending := none }
      | none => .ok { st with rings := (d, p, st.pending) :: st.rings, pending := none }
  | .dot => do
    if st.pending.isSome then throw "bond symbol before '.'"
    return { st with prev := none }

def Molecule.ofTokens (toks : List Token) : Except String Molecule := do
  let st ← toks.foldlM buildStep {}
  unless st.rings.isEmpty do throw "unclosed ring"
  unless st.branches.isEmpty do throw "unclosed branch"
  if st.pending.isSome then throw "dangling bond symbol"
  return ⟨st.atoms, st.bonds⟩

def SMILES.parse (s : SMILES) : Except String Molecule := do
  let cs := s.str.toList
  Molecule.ofTokens (← tokenize cs.length cs)

/-! ## Writer -/

def ringDigitString (d : Nat) : String := if d < 10 then toString d else "%" ++ toString d

/-- Smallest ring digit `≥ 1` not in use. -/
def smallestFree (used : List Nat) : Nat :=
  ((List.range (used.length + 2)).find? fun d => d ≥ 1 && !used.contains d).getD 1

def chargeString (q : Int) : String :=
  if q = 0 then "" else if q = 1 then "+" else if q = -1 then "-"
  else if q > 0 then s!"+{q}" else s!"-{-q}"

/-- The bond symbol to write between `a` and `b` (empty when implied). -/
def bondString (a b : Atom) : BondOrder → String
  | .single => if a.aromatic && b.aromatic then "-" else ""
  | .double => "="
  | .triple => "#"
  | .aromatic => if a.aromatic && b.aromatic then "" else ":"

/-- Atom `i` as written in SMILES. It goes without brackets whenever the organic-subset
reading (`implicitH`) gives back the same atom, so `[CH4]` and `C` are written alike. -/
def Molecule.atomString (m : Molecule) (i : Nat) : String :=
  let a := m.atom i
  let sym := if a.aromatic then (symbolOf a.element).map Char.toLower else symbolOf a.element
  let h := m.totalH i
  let organic := a.element ∈ organicSubset &&
    (!a.aromatic || a.element ∈ [5, 6, 7, 8, 15, 16]) &&
    a.charge == 0 && a.isotope.isNone && h == m.implicitH i
  if organic then sym
  else
    let iso := match a.isotope with | some k => toString k | none => ""
    let hs := if h = 0 then "" else if h = 1 then "H" else s!"H{h}"
    s!"[{iso}{sym}{hs}{chargeString a.charge}]"

/-- Depth-first search state: preorder and the tree children of each atom. -/
structure DFSState where
  visited : Array Bool
  order : Array Nat
  children : Array (List Nat)

/-- Depth-first search from `v`, trying neighbours in the order of `nbrs`. Depth is
bounded by `fuel` (the number of atoms suffices). -/
def dfs (nbrs : Array (List Nat)) : Nat → Nat → DFSState → DFSState
  | 0, _, st => st
  | fuel + 1, v, st =>
    let st := { st with visited := st.visited.setIfInBounds v true, order := st.order.push v }
    (nbrs.getD v []).foldl (fun st u =>
      if st.visited.getD u true then st
      else dfs nbrs fuel u { st with children := st.children.modify v (· ++ [u]) }) st

/-- Emit the subtree rooted at `v`: the atom, its ring-closure digits, then its children,
all but the last in parentheses. -/
def emitTree (atomStr ringStr : Nat → String) (bondStr : Nat → Nat → String)
    (children : Array (List Nat)) : Nat → Nat → String
  | 0, _ => ""
  | fuel + 1, v =>
    let sub := fun u => bondStr v u ++ emitTree atomStr ringStr bondStr children fuel u
    let head := atomStr v ++ ringStr v
    match (children.getD v []).reverse with
    | [] => head
    | last :: revInit =>
      head ++ String.join (revInit.reverse.map fun u => "(" ++ sub u ++ ")") ++ sub last

/-- Write `m` as SMILES. Lower `rank` means visited first: components start at their
lowest-ranked atom, and neighbours (branches and ring closures) are taken in rank order. -/
def Molecule.toSMILESWith (m : Molecule) (rank : Array Nat) : String :=
  let n := m.atoms.size
  let rk := fun i => rank.getD i 0
  let adj := m.adjacency.map fun l => l.mergeSort fun a b => rk a.1 ≤ rk b.1
  let starts := (List.range n).mergeSort fun a b => rk a ≤ rk b
  let init : DFSState :=
    { visited := Array.replicate n false, order := #[], children := Array.replicate n [] }
  -- pass 1: spanning forest
  let (st, roots) := starts.foldl (fun (st, roots) v =>
      if st.visited.getD v true then (st, roots)
      else (dfs (adj.map (·.map Prod.fst)) (n + 1) v st, roots ++ [v])) (init, [])
  let pos := (st.order.foldl (fun (p, k) v => (p.setIfInBounds v k, k + 1))
      (Array.replicate n 0, 0)).1
  let posOf := fun i => pos.getD i 0
  let isTree := fun (b : Bond) =>
    (st.children.getD b.src []).contains b.dst || (st.children.getD b.dst []).contains b.src
  -- ring bonds `(opener, closer, order)`, opened at the atom visited first
  let ringBonds : List ((Nat × Nat × BondOrder) × Nat) := (m.bonds.toList.filterMap fun b =>
      if isTree b then none
      else if posOf b.src < posOf b.dst then some (b.src, b.dst, b.order)
      else some (b.dst, b.src, b.order)).zipIdx
  let opensAt := fun v => (ringBonds.filter (·.1.1 = v)).mergeSort
    fun a b => rk a.1.2.1 ≤ rk b.1.2.1
  let closesAt := fun v => (ringBonds.filter (·.1.2.1 = v)).mergeSort
    fun a b => posOf a.1.1 ≤ posOf b.1.1
  -- pass 2: ring digits, allocated in preorder (opening before freeing, so no `C11`)
  let digits := (st.order.foldl (fun (digits, used) v =>
      let (digits, used) := (opensAt v).foldl (fun (digits, used) (_, k) =>
        let d := smallestFree used
        (digits.setIfInBounds k d, d :: used)) (digits, used)
      (digits, (closesAt v).foldl (fun used (_, k) => used.erase (digits.getD k 0)) used))
    (Array.replicate ringBonds.length 0, ([] : List Nat))).1
  let ringStr := fun v =>
    String.join ((closesAt v).map fun (_, k) => ringDigitString (digits.getD k 0)) ++
    String.join ((opensAt v).map fun ((o, c, b), k) =>
      bondString (m.atom o) (m.atom c) b ++ ringDigitString (digits.getD k 0))
  let bondStr := fun v u =>
    match (adj.getD v []).find? (·.1 = u) with
    | some (_, b) => bondString (m.atom v) (m.atom u) b
    | none => ""
  -- pass 3: emit each tree
  String.intercalate "." (roots.map (emitTree m.atomString ringStr bondStr st.children (n + 1)))

/-- SMILES in input atom order (not canonical). -/
def Molecule.toSMILES (m : Molecule) : SMILES := ⟨m.toSMILESWith (Array.range m.atoms.size)⟩

/-! ## Canonical ranking -/

/-- Dense ranks: `rank i` is the number of distinct keys strictly smaller than `keys[i]`. -/
def rankKeys (keys : Array (List Nat)) : Array Nat :=
  let distinct := (keys.toList.mergeSort lexLe).eraseDups
  keys.map distinct.idxOf

def numClasses (ranks : Array Nat) : Nat := ranks.toList.eraseDups.length

/-- Graph invariants of atom `i` that do not depend on atom numbering. Degree comes
first, so canonical SMILES start at a terminal atom (`CCO`, not `C(C)O`). -/
def Molecule.atomInvariant (m : Molecule) (i : Nat) : List Nat :=
  let a := m.atom i
  [m.degree i, a.element, a.isotope.getD 0, (a.charge + 1000).toNat,
   if a.aromatic then 1 else 0, m.totalH i]

/-- One refinement round: new key `(rank, sorted multiset of (bond, neighbour rank))`. -/
def refineRanks (adj : Array (List (Nat × BondOrder))) (ranks : Array Nat) : Array Nat :=
  let base := ranks.size + 1
  rankKeys <| ranks.mapIdx fun i r =>
    r :: ((adj.getD i []).map fun (u, b) => b.code * base + ranks.getD u 0).mergeSort

/-- Refine until the number of classes stops growing (at most `fuel` rounds). -/
def stabilize (adj : Array (List (Nat × BondOrder))) : Nat → Array Nat → Array Nat
  | 0, r => r
  | fuel + 1, r =>
    let r' := refineRanks adj r
    if numClasses r' = numClasses r then r else stabilize adj fuel r'

/-- Break the remaining ties: take the lowest tied rank, give its smallest-index atom a
rank of its own, and re-stabilize; repeat until all ranks differ. Refinement separates
atoms that are not symmetry-equivalent in practically all molecules, so the choice
inside a tied class does not change the output. -/
def breakTies (adj : Array (List (Nat × BondOrder))) : Nat → Array Nat → Array Nat
  | 0, r => r
  | fuel + 1, r =>
    let n := r.size
    if numClasses r = n then r
    else
      let tied := (List.range n).filter fun i => r.toList.count (r.getD i 0) ≥ 2
      let low := tied.foldl (fun acc i => min acc (r.getD i 0)) n
      match tied.find? (r.getD · 0 = low) with
      | none => r
      | some i =>
        let split := r.mapIdx fun j x => if j = i then [2 * x] else [2 * x + 1]
        breakTies adj fuel (stabilize adj (n + 1) (rankKeys split))

/-- Canonical ranks `0, …, n-1`. They don't depend on the input atom order (up to
symmetry). -/
def Molecule.canonicalRanks (m : Molecule) : Array Nat :=
  let n := m.atoms.size
  let adj := m.adjacency
  let initial := rankKeys ((Array.range n).map m.atomInvariant)
  breakTies adj (n + 1) (stabilize adj (n + 1) initial)

def Molecule.canonicalSMILES (m : Molecule) : CanonicalSMILES :=
  ⟨⟨m.toSMILESWith m.canonicalRanks⟩⟩

def SMILES.canonicalize (s : SMILES) : Except String CanonicalSMILES :=
  Molecule.canonicalSMILES <$> s.parse

/-- `s` parses and is its own canonical form. -/
def SMILES.isCanonical (s : SMILES) : Bool :=
  match s.canonicalize with
  | .ok c => c.smiles == s
  | .error _ => false

/-- Same molecule (as far as the canonical form can tell). -/
def SMILES.sameMolecule (s t : SMILES) : Bool :=
  match s.canonicalize, t.canonicalize with
  | .ok a, .ok b => a == b
  | _, _ => false

end Chem

end
