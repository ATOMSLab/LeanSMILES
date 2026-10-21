module

public import LeanSMILES.SMILES.Types
public import LeanSMILES.Primitives.LinAlg
public import LeanSMILES.Primitives.Decimal

/-!
# SMILES — Definitions

* **Parsing** `SMILES → Molecule`: a tokenizer (`tokenize`) followed by a left fold over
  the tokens (`Molecule.ofTokens`).
* **Writing** `Molecule → SMILES`: a depth-first traversal that visits atoms in the order
  given by a ranking (`Molecule.toSMILESWith`).
* **Canonical SMILES**: writing with canonical ranks (`canonicalRanks`), which come from
  iterated neighbourhood refinement with tie-breaking (Weininger's CANON / CANGEN).
* **Morgan fingerprints** (ECFP-style): iterated hashing of atom environments, then folding
  the identifiers into `nBits` bits.
* **Descriptors** (RDKit-style): molecular weight (exact, from decimal atomic masses),
  formula, H-bond donors, ring count, rotatable bonds, minimum degree.

Every function is total and terminates by structural recursion, on the input or on an
explicit `fuel : Nat` bound. Hashing is plain `Nat` arithmetic. So everything runs with
`#eval` and unfolds in proofs.

Supported SMILES: the organic subset (`B C N O P S F Cl Br I *` and aromatic
`b c n o p s`), bracket atoms with isotope, any element, hydrogen count and charge, bonds
`- = # :`, branches, ring closures `0-9` and `%nn`, and `.` for disconnected components.
Stereo marks (`/ \ @`) and atom classes are accepted but dropped. There is no
aromaticity perception, so the Kekulé and aromatic forms of a ring are different
molecules.
-/

@[expose] public section

namespace Chem

/-! ## Elements and valence -/

/-- Element symbols indexed by atomic number (`0` is the wildcard `*`). -/
def elementSymbols : Array String := #["*",
  "H", "He", "Li", "Be", "B", "C", "N", "O", "F", "Ne", "Na", "Mg", "Al", "Si", "P", "S",
  "Cl", "Ar", "K", "Ca", "Sc", "Ti", "V", "Cr", "Mn", "Fe", "Co", "Ni", "Cu", "Zn", "Ga",
  "Ge", "As", "Se", "Br", "Kr", "Rb", "Sr", "Y", "Zr", "Nb", "Mo", "Tc", "Ru", "Rh", "Pd",
  "Ag", "Cd", "In", "Sn", "Sb", "Te", "I", "Xe", "Cs", "Ba", "La", "Ce", "Pr", "Nd", "Pm",
  "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb", "Lu", "Hf", "Ta", "W", "Re", "Os",
  "Ir", "Pt", "Au", "Hg", "Tl", "Pb", "Bi", "Po", "At", "Rn", "Fr", "Ra", "Ac", "Th", "Pa",
  "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm", "Md", "No", "Lr", "Rf", "Db", "Sg",
  "Bh", "Hs", "Mt", "Ds", "Rg", "Cn", "Nh", "Fl", "Mc", "Lv", "Ts", "Og"]

def symbolOf (z : Nat) : String := elementSymbols.getD z "*"

def elementOf? (sym : String) : Option Nat := elementSymbols.findIdx? (· == sym)

/-- Elements that may be written without brackets. -/
def organicSubset : List Nat := [0, 5, 6, 7, 8, 9, 15, 16, 17, 35, 53]

/-- Normal valences of the organic-subset elements, in increasing order. -/
def normalValences : Nat → List Nat
  | 5 => [3]
  | 6 => [4]
  | 7 => [3, 5]
  | 8 => [2]
  | 15 => [3, 5]
  | 16 => [2, 4, 6]
  | 9 | 17 | 35 | 53 => [1]
  | _ => []

/-- Valence used by a bond. Aromatic bonds count `1`; the extra aromatic electron is
counted once per atom in `Molecule.bondValence`. -/
def BondOrder.valence : BondOrder → Nat
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 1

/-- Distinct numeric code per bond order, used in ranking and hashing. -/
def BondOrder.code : BondOrder → Nat
  | .single => 1
  | .double => 2
  | .triple => 3
  | .aromatic => 4

/-! ## Molecular graph -/

namespace Molecule

/-- Every bond joins two distinct existing atoms. -/
def WellFormed (m : Molecule) : Prop :=
  ∀ b ∈ m.bonds.toList, b.src < m.atoms.size ∧ b.dst < m.atoms.size ∧ b.src ≠ b.dst

instance (m : Molecule) : Decidable m.WellFormed := by
  unfold WellFormed; infer_instance

def atom (m : Molecule) (i : Nat) : Atom := m.atoms.getD i default

/-- The atoms bonded to atom `i`, with the bond orders. -/
def neighbors (m : Molecule) (i : Nat) : List (Nat × BondOrder) :=
  m.bonds.toList.filterMap fun b =>
    if b.src = i then some (b.dst, b.order)
    else if b.dst = i then some (b.src, b.order)
    else none

/-- `neighbors` for every atom. -/
def adjacency (m : Molecule) : Array (List (Nat × BondOrder)) :=
  (Array.range m.atoms.size).map m.neighbors

/-- Number of explicit (graph) neighbours. -/
def degree (m : Molecule) (i : Nat) : Nat := (m.neighbors i).length

/-- Valence used by the bonds of atom `i`, plus `1` if the atom is aromatic. -/
def bondValence (m : Molecule) (i : Nat) : Nat :=
  ((m.neighbors i).map (·.2.valence)).sum + (if (m.atom i).aromatic then 1 else 0)

/-- Hydrogens that atom `i` would carry if written without brackets: the smallest normal
valence that is at least `bondValence`, minus `bondValence`. Aromatic atoms use only
the lowest normal valence (so `c` ↦ 1 H, `n`, `o`, `s` ↦ 0 H). -/
def implicitH (m : Molecule) (i : Nat) : Nat :=
  let a := m.atom i
  let used := m.bondValence i
  let vs := normalValences a.element
  if a.aromatic then (vs.head?.map (· - used)).getD 0
  else ((vs.find? (used ≤ ·)).map (· - used)).getD 0

/-- Total hydrogens on atom `i`: the bracket count if given, otherwise `implicitH`. -/
def totalH (m : Molecule) (i : Nat) : Nat := (m.atom i).explicitH.getD (m.implicitH i)

end Molecule

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

/-- Lexicographic `≤` on lists of naturals. -/
def lexLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLe as bs)

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

/-! ## Morgan fingerprints -/

/-- 32-bit FNV-1a over a list of naturals: plain `Nat` arithmetic, so it computes in the
kernel and unfolds in proofs. -/
def fnv (xs : List Nat) : Nat :=
  xs.foldl (fun h x => ((h ^^^ x) * 16777619) % 4294967296) 2166136261

/-- Is `target` reachable from the atoms in `frontier` without using bond number `skip`?
Breadth-first search with at most `fuel` layers. -/
def reachableWithout (adjB : Array (List (Nat × Nat))) (skip target : Nat) :
    Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | fuel + 1, frontier, visited =>
    if target ∈ frontier then true
    else
      let next := (frontier.flatMap fun v => (adjB.getD v []).filterMap fun (u, k) =>
        if k = skip ∨ u ∈ visited then none else some u).eraseDups
      if next.isEmpty then false else reachableWithout adjB skip target fuel next (visited ++ next)

/-- A bond is in a ring iff its endpoints stay connected without it. -/
def Molecule.bondInRing (m : Molecule) (k : Nat) : Bool :=
  let n := m.atoms.size
  let adjB : Array (List (Nat × Nat)) := (Array.range n).map fun v =>
    (m.bonds.toList.zipIdx).filterMap fun (b, k) =>
      if b.src = v then some (b.dst, k) else if b.dst = v then some (b.src, k) else none
  match m.bonds[k]? with
  | some b => reachableWithout adjB k b.dst (n + 1) [b.src] [b.src]
  | none => false

/-- Is the bond between atoms `i` and `j` (if any) in a ring? -/
def Molecule.bondInRingBetween (m : Molecule) (i j : Nat) : Bool :=
  (m.bonds.toList.zipIdx).any fun (b, k) =>
    ((b.src = i && b.dst = j) || (b.src = j && b.dst = i)) && m.bondInRing k

def Molecule.atomInRing (m : Molecule) (i : Nat) : Bool :=
  (m.bonds.toList.zipIdx).any fun (b, k) => (b.src = i || b.dst = i) && m.bondInRing k

/-- Radius-0 identifier of atom `i` (the ECFP atom invariants): element, degree, total
hydrogens, charge, isotope and ring membership. -/
def Molecule.morganInvariant (m : Molecule) (i : Nat) : Nat :=
  let a := m.atom i
  fnv [a.element, m.degree i, m.totalH i, (a.charge + 1000).toNat, a.isotope.getD 0,
    if m.atomInRing i then 1 else 0]

/-- One Morgan round: hash the round number, the atom's own identifier and the sorted
`(bond, neighbour identifier)` pairs. -/
def morganRound (adj : Array (List (Nat × BondOrder))) (round : Nat) (ids : Array Nat) :
    Array Nat :=
  ids.mapIdx fun i h =>
    fnv (round :: h :: (((adj.getD i []).map fun (u, b) => [b.code, ids.getD u 0]).mergeSort
      lexLe).flatten)

/-- Identifiers of rounds `round, …, round + k`, starting from `ids`. -/
def morganRounds (adj : Array (List (Nat × BondOrder))) : Nat → Nat → Array Nat → List Nat
  | 0, _, ids => ids.toList
  | k + 1, round, ids =>
    ids.toList ++ morganRounds adj k (round + 1) (morganRound adj (round + 1) ids)

/-- All environment identifiers of radius `0, …, radius`. -/
def Molecule.morganIds (m : Molecule) (radius : Nat) : List Nat :=
  morganRounds m.adjacency radius 0 ((Array.range m.atoms.size).map m.morganInvariant)

/-- Morgan fingerprint: bit `j` is set iff some identifier is `≡ j (mod nBits)`. -/
def Molecule.morganFingerprint (m : Molecule) (radius nBits : Nat) : MorganFingerprint nBits :=
  let ids := m.morganIds radius
  ⟨Vector.ofFn fun j => ids.any (· % nBits == j.val)⟩

/-- `bits` with bit `x % nBits` also set for every `x ∈ xs`. -/
def setBits {nBits : Nat} (bits : Vector Bool nBits) : List Nat → Vector Bool nBits
  | [] => bits
  | x :: xs => setBits (bits.setIfInBounds (x % nBits) true) xs

theorem getElem_setBits {nBits : Nat} (bits : Vector Bool nBits) (xs : List Nat) (j : Nat)
    (hj : j < nBits) : (setBits bits xs)[j] = (bits[j] || xs.any (· % nBits == j)) := by
  induction xs generalizing bits with
  | nil => simp [setBits]
  | cons x xs ih =>
    simp only [setBits, ih, Vector.getElem_setIfInBounds, List.any_cons]
    by_cases h : x % nBits = j
    · simp [h]
    · have hb : (x % nBits == j) = false := by simpa using h
      simp [h, hb]

/-- `morganFingerprint` in one pass over the identifiers, instead of one pass per bit.
The compiler uses it in place of `morganFingerprint` (`morganFingerprint_eq_fast`). -/
def Molecule.morganFingerprintFast (m : Molecule) (radius nBits : Nat) :
    MorganFingerprint nBits :=
  ⟨setBits (Vector.replicate nBits false) (m.morganIds radius)⟩

@[csimp] theorem Molecule.morganFingerprint_eq_fast :
    @Molecule.morganFingerprint = @Molecule.morganFingerprintFast := by
  funext m radius nBits
  simp only [Molecule.morganFingerprint, Molecule.morganFingerprintFast, MorganFingerprint.mk.injEq]
  ext j hj
  simp [getElem_setBits]

def SMILES.morganFingerprint (s : SMILES) (radius nBits : Nat) :
    Except String (MorganFingerprint nBits) :=
  (·.morganFingerprint radius nBits) <$> s.parse

/-- Number of set bits. -/
def MorganFingerprint.popCount {nBits : Nat} (fp : MorganFingerprint nBits) : Nat :=
  fp.bits.toList.count true

/-- Tanimoto similarity `|a ∧ b| / |a ∨ b|` (RDKit's `TanimotoSimilarity`); `1` for two
empty fingerprints. -/
def MorganFingerprint.tanimoto {α : Type} [Primitives.Scalar α] {nBits : Nat}
    (a b : MorganFingerprint nBits) : α :=
  let both := ((a.bits.zip b.bits).toList.filter fun x => x.1 && x.2).length
  let either := ((a.bits.zip b.bits).toList.filter fun x => x.1 || x.2).length
  if either = 0 then 1 else Primitives.Scalar.fromNat both / Primitives.Scalar.fromNat either

/-- The fingerprint as an ML feature vector (`1` for set bits, `0` otherwise). -/
def MorganFingerprint.toFeatures {α : Type} [Primitives.Scalar α] {nBits : Nat}
    (fp : MorganFingerprint nBits) : Primitives.Vec α nBits :=
  fp.bits.map fun b => if b then 1 else 0

/-! ## Descriptors (RDKit-style) -/

open Primitives (Decimal)

/-- Standard atomic weights (the values RDKit uses), as exact decimals. `0` for elements
not in the table. -/
def atomicMass : Nat → Decimal
  | 1 => ⟨1008, -3⟩
  | 3 => ⟨6941, -3⟩
  | 5 => ⟨10812, -3⟩
  | 6 => ⟨12011, -3⟩
  | 7 => ⟨14007, -3⟩
  | 8 => ⟨15999, -3⟩
  | 9 => ⟨18998, -3⟩
  | 11 => ⟨22990, -3⟩
  | 12 => ⟨24305, -3⟩
  | 13 => ⟨26982, -3⟩
  | 14 => ⟨28086, -3⟩
  | 15 => ⟨30974, -3⟩
  | 16 => ⟨32067, -3⟩
  | 17 => ⟨35453, -3⟩
  | 19 => ⟨39098, -3⟩
  | 20 => ⟨40078, -3⟩
  | 26 => ⟨55845, -3⟩
  | 29 => ⟨63546, -3⟩
  | 30 => ⟨65390, -3⟩
  | 34 => ⟨78960, -3⟩
  | 35 => ⟨79904, -3⟩
  | 50 => ⟨118710, -3⟩
  | 53 => ⟨126904, -3⟩
  | 80 => ⟨200590, -3⟩
  | _ => 0

namespace Molecule

/-- Mass of atom `i` with its hydrogens. An isotope label replaces the average mass by
the mass number. -/
def atomMass (m : Molecule) (i : Nat) : Decimal :=
  let a := m.atom i
  let heavy := match a.isotope with
    | some k => ⟨k, 0⟩
    | none => atomicMass a.element
  heavy + Decimal.nsmul (m.totalH i) (atomicMass 1)

/-- Average molecular weight, exactly (RDKit's `Descriptors.MolWt`). -/
def molecularWeightExact (m : Molecule) : Decimal :=
  (List.range m.atoms.size).foldl (fun acc i => acc + m.atomMass i) 0

/-- Average molecular weight in any `Scalar` (exact over `ℝ`). -/
def molecularWeight {α : Type} [Primitives.Scalar α] (m : Molecule) : α :=
  m.molecularWeightExact.toScalar

def heavyAtomCount (m : Molecule) : Nat := (m.atoms.toList.filter (·.element != 1)).length

def hydrogenCount (m : Molecule) : Nat :=
  (List.range m.atoms.size).foldl (fun acc i => acc + m.totalH i) 0 +
    (m.atoms.toList.filter (·.element == 1)).length

/-- Hill formula: `C`, then `H`, then the other elements alphabetically (alphabetically
throughout if there is no carbon). -/
def formula (m : Molecule) : String :=
  let counts : List (String × Nat) :=
    (m.atoms.toList.map (symbolOf ·.element)).eraseDups.map fun sym =>
      (sym, (m.atoms.toList.filter (symbolOf ·.element == sym)).length)
  let counts := (counts.filter (·.1 != "H")) ++
    (let h := m.hydrogenCount; if h = 0 then [] else [("H", h)])
  let hasC := counts.any (·.1 == "C")
  let rank := fun (sym : String) =>
    if hasC && sym == "C" then "0" else if hasC && sym == "H" then "1" else "2" ++ sym
  let sorted := counts.mergeSort fun a b => decide (rank a.1 ≤ rank b.1)
  String.join (sorted.map fun (sym, k) => if k = 1 then sym else s!"{sym}{k}")

/-- Connected components (`.`-separated fragments), by repeated breadth-first search. -/
def componentLabels (m : Molecule) : Array Nat :=
  let n := m.atoms.size
  let adj := m.adjacency.map (·.map Prod.fst)
  let rec spread : Nat → List Nat → Nat → Array Nat → Array Nat
    | 0, _, _, labels => labels
    | _, [], _, labels => labels
    | fuel + 1, v :: rest, c, labels =>
      let new := (adj.getD v []).filter fun u => labels.getD u 0 == 0
      spread fuel (rest ++ new) c (new.foldl (fun l u => l.setIfInBounds u c) labels)
  ((List.range n).foldl (fun (labels, c) v =>
      if labels.getD v 0 != 0 then (labels, c)
      else (spread (n * n + 1) [v] (c + 1) (labels.setIfInBounds v (c + 1)), c + 1))
    (Array.replicate n 0, 0)).1

def componentCount (m : Molecule) : Nat := (m.componentLabels.toList.eraseDups).length

/-- Number of independent rings, `bonds − atoms + components` (equals RDKit's SSSR
`RingCount`). -/
def ringCount (m : Molecule) : Nat := m.bonds.size + m.componentCount - m.atoms.size

/-- Lipinski H-bond donors (RDKit's `NumHDonors`): N with hydrogens (neutral or +1), O
or S with exactly one hydrogen and no charge, aromatic `[nH]`. -/
def isHDonor (m : Molecule) (i : Nat) : Bool :=
  let a := m.atom i
  let h := m.totalH i
  (a.element == 7 && !a.aromatic && h > 0 && (a.charge == 0 || a.charge == 1)) ||
  ((a.element == 8 || a.element == 16) && h == 1 && a.charge == 0) ||
  (a.element == 7 && a.aromatic && h == 1 && a.charge == 0)

def hDonorCount (m : Molecule) : Nat := ((List.range m.atoms.size).filter m.isHDonor).length

def hasTripleBond (m : Molecule) (i : Nat) : Bool :=
  (m.neighbors i).any (·.2 == .triple)

/-- `C` with three neighbours of element `z` (CF₃, CCl₃, CBr₃). -/
def isTrihalomethyl (m : Molecule) (i : Nat) (z : Nat) : Bool :=
  (m.atom i).element == 6 && ((m.neighbors i).filter fun (u, _) => (m.atom u).element == z).length == 3

/-- `C` bonded to three methyl groups (the centre of a t-butyl group). -/
def isTertButylCenter (m : Molecule) (i : Nat) : Bool :=
  (m.atom i).element == 6 &&
    ((m.neighbors i).filter fun (u, _) =>
      (m.atom u).element == 6 && m.degree u == 1 && m.totalH u == 3).length == 3

/-- The carbon of an amide, ester, thioester or amidine group: degree 3, a double bond to
N, O or S (or to N⁺), and a single non-ring bond to a heteroatom. -/
def isAcylCarbon (m : Molecule) (i : Nat) : Bool :=
  let nbrs := (m.neighbors i)
  (m.atom i).element == 6 && m.degree i == 3 &&
    nbrs.any (fun (u, b) => b == .double && [7, 8, 16].contains (m.atom u).element) &&
    nbrs.any (fun (u, b) => b == .single && !m.bondInRingBetween i u &&
      ((m.atom u).element == 7 || (m.atom u).element == 8 ||
        ((m.atom u).element == 16 && m.degree u != 1)))

/-- A heteroatom single-bonded (outside rings) to an acyl carbon. -/
def isAcylHeteroatom (m : Molecule) (i : Nat) : Bool :=
  let a := m.atom i
  (a.element == 7 || a.element == 8 || (a.element == 16 && m.degree i != 1)) &&
    (m.neighbors i).any fun (u, b) => b == .single && !m.bondInRingBetween i u && m.isAcylCarbon u

/-- Right-hand atom of RDKit's strict rotatable-bond pattern. -/
def rotorEnd (m : Molecule) (i : Nat) : Bool :=
  !m.hasTripleBond i && m.degree i > 1 &&
    !m.isTrihalomethyl i 9 && !m.isTrihalomethyl i 17 && !m.isTrihalomethyl i 35 &&
    !m.isTertButylCenter i

/-- Left-hand atom: additionally not part of an amide/ester-like linkage. -/
def rotorStart (m : Molecule) (i : Nat) : Bool :=
  m.rotorEnd i && !m.isAcylCarbon i && !m.isAcylHeteroatom i

/-- RDKit's `NumRotatableBonds` with the default *strict* pattern: single (or aromatic),
non-ring bonds between non-terminal atoms that are not in triple bonds, excluding CF₃,
CCl₃, CBr₃ and t-butyl rotors and amide, ester, thioester and amidine C–X bonds. -/
def rotatableBondCount (m : Molecule) : Nat :=
  (m.bonds.toList.zipIdx.filter fun (b, k) =>
    (b.order == .single || b.order == .aromatic) && !m.bondInRing k &&
    ((m.rotorStart b.src && m.rotorEnd b.dst) || (m.rotorStart b.dst && m.rotorEnd b.src))).length

/-- Smallest number of heavy-atom neighbours (DeepChem's "Minimum Degree"). -/
def minDegree (m : Molecule) : Nat :=
  (List.range m.atoms.size).foldl (fun acc i => min acc (m.degree i)) m.atoms.size

end Molecule

/-- A summary of the computed descriptors. -/
structure Descriptors where
  formula : String
  molecularWeight : Decimal
  heavyAtoms : Nat
  hDonors : Nat
  rings : Nat
  rotatableBonds : Nat
  minDegree : Nat
  deriving Repr

def Molecule.descriptors (m : Molecule) : Descriptors :=
  { formula := m.formula, molecularWeight := m.molecularWeightExact
    heavyAtoms := m.heavyAtomCount, hDonors := m.hDonorCount, rings := m.ringCount
    rotatableBonds := m.rotatableBondCount, minDegree := m.minDegree }

end Chem

end
