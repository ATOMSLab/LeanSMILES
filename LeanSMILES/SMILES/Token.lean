/-
Copyright (c) 2026 Tyler Josephson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tyler Josephson, Hao Liu
-/
module

public import LeanSMILES.Chem.Atom
public import LeanSMILES.Chem.Bond

/-!
# LeanSMILES.SMILES.Token

The lexical layer of SMILES: a `String` becomes a list of `Token`s, each
tagged with its character position.  Atoms are fully decoded here — a bracket
atom `[13CH3+:2]` is one token carrying one `Atom` — so the parser proper
(`LeanSMILES.SMILES.Parse`) only has to deal with the graph grammar: bonds,
branches, ring closures and dots.

Leading whitespace is skipped, as RDKit does (the OpenSMILES grammar would read
`" C"` as an empty molecule followed by a title, and says a SMILES *file* line
starting with whitespace is to be ignored).  Reading then stops at the first
whitespace: what follows is a title, not SMILES.

The grammar is OpenSMILES §2.2.  Where RDKit and the spec disagree, the
decisions — which side was taken and why — are tabulated in the README under
"What the parser accepts".  Two of them are the tokenizer's: `[CH10]` and
`[C:]` are rejected with the spec, while a charge of any length (`[Fe+++]`,
`[C+123]`) is accepted and left to a post-parse chemistry check.
-/

@[expose] public section

namespace LeanSMILES.SMILES

/-- Everything that can go wrong between a string and a molecule. Positions
are 0-based character offsets into the input. -/
inductive ParseError
  | unexpectedChar (pos : ℕ) (c : Char)
  | unexpectedEnd (expected : String)
  | unknownElement (pos : ℕ) (symbol : String)
  | badBracket (pos : ℕ) (msg : String)
  | bondWithoutAtom (pos : ℕ)
  | branchWithoutAtom (pos : ℕ)
  | ringWithoutAtom (pos : ℕ)
  | unmatchedBranchClose (pos : ℕ)
  | emptyBranch (pos : ℕ)
  | ringAfterBranchOpen (pos : ℕ)
  | ringAfterBranch (pos : ℕ)
  | danglingDot (pos : ℕ)
  | unclosedBranch (count : ℕ)
  | unclosedRing (nums : List ℕ)
  | selfBond (pos : ℕ) (atom : ℕ)
  | duplicateBond (pos : ℕ) (i j : ℕ)
  | conflictingRingBond (pos : ℕ) (num : ℕ)
  | internal (msg : String)
  deriving Repr, DecidableEq, Inhabited

namespace ParseError

/-- A message with the position. -/
def toString : ParseError → String
  | unexpectedChar pos c => s!"unexpected character '{c}' at {pos}"
  | unexpectedEnd expected => s!"unexpected end of input, expected {expected}"
  | unknownElement pos s => s!"unknown element symbol '{s}' at {pos}"
  | badBracket pos msg => s!"malformed bracket atom at {pos}: {msg}"
  | bondWithoutAtom pos => s!"bond symbol at {pos} cannot connect two atoms"
  | branchWithoutAtom pos => s!"branch opened at {pos} without an atom to attach to"
  | ringWithoutAtom pos => s!"ring-closure label at {pos} without an atom to attach to"
  | unmatchedBranchClose pos => s!"')' at {pos} closes no branch"
  | emptyBranch pos => s!"empty branch '()' closed at {pos}"
  | ringAfterBranchOpen pos => s!"ring-closure label at {pos} directly after '('"
  | ringAfterBranch pos =>
    s!"ring-closure label at {pos} after a branch: labels must precede branches"
  | danglingDot pos => s!"'.' at {pos} is not between two atoms"
  | unclosedBranch 1 => "1 branch was never closed"
  | unclosedBranch k => s!"{k} branches were never closed"
  | unclosedRing [num] => s!"ring closure {num} was never closed"
  | unclosedRing nums => s!"ring closures {nums} were never closed"
  | selfBond pos a => s!"ring closure at {pos} bonds atom {a} to itself"
  | duplicateBond pos i j => s!"bond at {pos} duplicates the bond between atoms {i} and {j}"
  | conflictingRingBond pos num => s!"ring closure {num} at {pos} has two different bond symbols"
  | internal msg => s!"internal error: {msg}"

instance : ToString ParseError := ⟨toString⟩

/-- Errors that are the OpenSMILES grammar overruling RDKit by decision (see
"What the parser accepts" in the README): RDKit accepts the string, the spec
does not, and LeanSMILES follows the spec.  The tests against RDKit's verdicts
count these separately from parser bugs. -/
def isGrammarDeviation : ParseError → Bool
  | ringAfterBranch _ => true
  | _ => false

end ParseError

/-- What a token is. -/
inductive TokenKind
  /-- A bare or bracket atom, fully decoded. -/
  | atom (a : Atom)
  /-- One of `- = # $ :`. -/
  | bond (k : BondKind)
  /-- `/` or `\`: a single bond with a cis/trans direction mark. -/
  | dirBond (d : BondDir)
  /-- `.`: no bond. -/
  | dot
  | branchOpen
  | branchClose
  /-- A ring-closure label: a digit, or `%` followed by two digits. -/
  | ring (num : ℕ)
  deriving Repr, DecidableEq, Inhabited

/-- A token with its position. -/
structure Token where
  /-- What the token is. -/
  kind : TokenKind
  /-- Offset of the token's first character in the input. -/
  pos : ℕ
  deriving Repr, Inhabited

namespace Tokenizer

/-- Split off a (possibly empty) run of digits. -/
def takeDigits (cs : List Char) : List Char × List Char := cs.span Char.isDigit

/-- The number a run of digits denotes. -/
def digitsToNat (ds : List Char) : ℕ :=
  ds.foldl (fun n d ↦ 10 * n + (d.toNat - '0'.toNat)) 0

/-! ### Bracket atoms

`[` isotope? symbol chirality? hcount? charge? class? `]` -/

/-- A decoded bracket symbol: the element (`none` for `*`), whether it was
lowercase, and the remaining characters. -/
abbrev BracketSymbol := Option Element × Bool × List Char

/-- The element symbol inside brackets, greedy on two-letter symbols (`[Sc]` is scandium,
`[Co]` cobalt); lowercase symbols are aromatic. -/
def bracketSymbol (bracketPos symbolPos : ℕ) : List Char → Except ParseError BracketSymbol
  | '*' :: rest => .ok (none, false, rest)
  | c :: rest =>
    if c.isUpper then
      match rest with
      | d :: rest' =>
        if d.isLower then
          match Element.ofSymbol? (String.ofList [c, d]) with
          | some e => .ok (some e, false, rest')
          | none => oneLetter c rest
        else oneLetter c rest
      | [] => oneLetter c rest
    else if c.isLower then
      match rest with
      | d :: rest' =>
        -- Nothing that may follow a symbol is lowercase, so two lowercase
        -- letters can only be a two-letter aromatic symbol: `[se]`, `[as]`.
        if d.isLower then
          match Element.ofSymbol? (String.ofList [c.toUpper, d]) with
          | some e =>
            if e.aromaticAllowed then .ok (some e, true, rest')
            else .error (.badBracket bracketPos s!"'{c}{d}' may not be written aromatic")
          | none => .error (.unknownElement symbolPos (String.ofList [c, d]))
        else aromaticOne c rest
      | [] => aromaticOne c rest
    else .error (.unexpectedChar symbolPos c)
  | [] => .error (.unexpectedEnd "an element symbol")
where
  /-- A one-letter uppercase symbol. -/
  oneLetter (c : Char) (rest : List Char) : Except ParseError BracketSymbol :=
    match Element.ofSymbol? (String.ofList [c]) with
    | some e => .ok (some e, false, rest)
    | none => .error (.unknownElement symbolPos (String.ofList [c]))
  /-- A one-letter aromatic (lowercase) symbol. -/
  aromaticOne (c : Char) (rest : List Char) : Except ParseError BracketSymbol :=
    match Element.ofSymbol? (String.ofList [c.toUpper]) with
    | some e =>
      if e.aromaticAllowed then .ok (some e, true, rest)
      else .error (.badBracket bracketPos s!"'{c}' may not be written aromatic")
    | none => .error (.unknownElement symbolPos (String.ofList [c]))

/-- The zero-based index of a one-based class number `k` in `1 … n`. -/
def classIndex (n k : ℕ) : Option (Fin n) :=
  if h : 1 ≤ k ∧ k ≤ n then some ⟨k - 1, by omega⟩ else none

/-- `@@`, `@`, a named class `@TH1` … `@OH30` (OpenSMILES §3.7), or nothing.
`pos` is the position of the `[`, for errors. -/
def parseChirality (pos : ℕ) : List Char → Except ParseError (Option Chirality × List Char)
  | '@' :: '@' :: rest => .ok (some .clockwise, rest)
  | '@' :: rest =>
    match rest with
    | c₁ :: c₂ :: rest' =>
      let cls := String.ofList [c₁, c₂]
      if cls ∈ ["TH", "AL", "SP", "TB", "OH"] then
        let (ds, rest'') := takeDigits rest'
        let k := digitsToNat ds
        let mark : Option Chirality :=
          match cls with
          | "TH" => (classIndex 2 k).map .th
          | "AL" => (classIndex 2 k).map .al
          | "SP" => (classIndex 3 k).map .sp
          | "TB" => (classIndex 20 k).map .tb
          | _ => (classIndex 30 k).map .oh
        match mark with
        | some m => .ok (some m, rest'')
        | none => .error (.badBracket pos s!"'@{cls}{String.ofList ds}' is not a chirality class")
      else .ok (some .anticlockwise, rest)
    | _ => .ok (some .anticlockwise, rest)
  | cs => .ok (none, cs)

/-- `H` alone means one hydrogen; `H3` means three; nothing means none.  The
count is one digit (OpenSMILES `hcount ::= 'H' | 'H' DIGIT`): `[CH10]` is an
error.  `pos` is the position of the `[`. -/
def parseHCount (pos : ℕ) : List Char → Except ParseError (ℕ × List Char)
  | 'H' :: rest =>
    let (ds, rest') := takeDigits rest
    match ds with
    | [] => .ok (1, rest')
    | [d] => .ok (d.toNat - '0'.toNat, rest')
    | _ => .error (.badBracket pos s!"hydrogen count 'H{String.ofList ds}' has more than one digit")
  | cs => .ok (0, cs)

/-- `+`, `-`, `++`, `--`, `+2`, `-3`.  A run of signs of any length and a
number of any length are accepted (`[Fe+++]`, `[C+123]`), deliberately looser
than the OpenSMILES grammar: whether the element has the electrons is a
chemistry question, answered after parsing, not a lexical one. -/
def parseCharge : List Char → ℤ × List Char
  | '+' :: rest =>
    let (ds, rest') := takeDigits rest
    if ds.isEmpty then
      let (more, rest'') := rest.span (· == '+')
      ((1 + more.length : ℕ), rest'')
    else ((digitsToNat ds : ℕ), rest')
  | '-' :: rest =>
    let (ds, rest') := takeDigits rest
    if ds.isEmpty then
      let (more, rest'') := rest.span (· == '-')
      (-((1 + more.length : ℕ) : ℤ), rest'')
    else (-((digitsToNat ds : ℕ) : ℤ), rest')
  | cs => (0, cs)

/-- `:n`, or nothing.  The colon needs at least one digit (OpenSMILES
`class ::= ':' NUMBER`): `[C:]` is an error.  `pos` is the position of the `[`. -/
def parseClass (pos : ℕ) : List Char → Except ParseError (Option ℕ × List Char)
  | ':' :: rest =>
    let (ds, rest') := takeDigits rest
    if ds.isEmpty then .error (.badBracket pos "':' is not followed by a class number")
    else .ok (some (digitsToNat ds), rest')
  | cs => .ok (none, cs)

/-- Decode the inside of a bracket atom, given the characters after `[`.
Returns the atom and the characters after the closing `]`. -/
def bracketAtom (pos : ℕ) (cs : List Char) : Except ParseError (Atom × List Char) := do
  let (isoDigits, cs) := takeDigits cs
  let isotope := if isoDigits.isEmpty then none else some (digitsToNat isoDigits)
  let (element, aromatic, cs) ← bracketSymbol pos (pos + 1 + isoDigits.length) cs
  let (chirality, cs) ← parseChirality pos cs
  let (h, cs) ← parseHCount pos cs
  let (charge, cs) := parseCharge cs
  let (atomClass, cs) ← parseClass pos cs
  match cs with
  | ']' :: rest =>
    .ok ({ element, aromatic, isotope, charge, explicitH := some h, chirality, atomClass }, rest)
  | c :: _ => .error (.badBracket pos s!"unexpected '{c}'")
  | [] => .error (.unexpectedEnd "']'")

/-! ### Bare atoms: the organic subset -/

/-- A bare atom: `B C N O P S F Cl Br I *` and aromatic `b c n o p s`. -/
def organicAtom (c : Char) (rest : List Char) : Option (Atom × List Char) :=
  match c, rest with
  | 'C', 'l' :: rest' => some (Atom.ofElement .Cl, rest')
  | 'B', 'r' :: rest' => some (Atom.ofElement .Br, rest')
  | '*', _ => some (Atom.wildcard, rest)
  | 'B', _ => some (Atom.ofElement .B, rest)
  | 'C', _ => some (Atom.ofElement .C, rest)
  | 'N', _ => some (Atom.ofElement .N, rest)
  | 'O', _ => some (Atom.ofElement .O, rest)
  | 'P', _ => some (Atom.ofElement .P, rest)
  | 'S', _ => some (Atom.ofElement .S, rest)
  | 'F', _ => some (Atom.ofElement .F, rest)
  | 'I', _ => some (Atom.ofElement .I, rest)
  | 'b', _ => some ({ element := some .B, aromatic := true }, rest)
  | 'c', _ => some ({ element := some .C, aromatic := true }, rest)
  | 'n', _ => some ({ element := some .N, aromatic := true }, rest)
  | 'o', _ => some ({ element := some .O, aromatic := true }, rest)
  | 'p', _ => some ({ element := some .P, aromatic := true }, rest)
  | 's', _ => some ({ element := some .S, aromatic := true }, rest)
  | _, _ => none

/-! ### The tokenizer -/

/-- Tokenize, with `fuel` bounding the number of tokens (one per character
suffices). -/
def go : ℕ → List Char → ℕ → Array Token → Except ParseError (Array Token)
  | 0, _, _, _ => .error (.internal "tokenizer out of fuel")
  | _, [], _, acc => .ok acc
  | fuel + 1, c :: cs, pos, acc =>
    if c.isWhitespace then .ok acc
    else if c == '[' then do
      let (a, rest) ← bracketAtom pos cs
      go fuel rest (pos + 1 + (cs.length - rest.length)) (acc.push ⟨.atom a, pos⟩)
    else if c == '(' then go fuel cs (pos + 1) (acc.push ⟨.branchOpen, pos⟩)
    else if c == ')' then go fuel cs (pos + 1) (acc.push ⟨.branchClose, pos⟩)
    else if c == '.' then go fuel cs (pos + 1) (acc.push ⟨.dot, pos⟩)
    else if c == '/' then go fuel cs (pos + 1) (acc.push ⟨.dirBond .up, pos⟩)
    else if c == '\\' then go fuel cs (pos + 1) (acc.push ⟨.dirBond .down, pos⟩)
    else if c == '%' then
      match cs with
      | d1 :: d2 :: rest =>
        if !d1.isDigit then .error (.unexpectedChar (pos + 1) d1)
        else if !d2.isDigit then .error (.unexpectedChar (pos + 2) d2)
        else go fuel rest (pos + 3) (acc.push ⟨.ring (digitsToNat [d1, d2]), pos⟩)
      | [d1] => if d1.isDigit then .error (.unexpectedEnd "two digits after '%'")
                else .error (.unexpectedChar (pos + 1) d1)
      | [] => .error (.unexpectedEnd "two digits after '%'")
    else if c.isDigit then go fuel cs (pos + 1) (acc.push ⟨.ring (c.toNat - '0'.toNat), pos⟩)
    else
      match BondKind.ofChar? c with
      | some k => go fuel cs (pos + 1) (acc.push ⟨.bond k, pos⟩)
      | none =>
        match organicAtom c cs with
        | some (a, rest) =>
          go fuel rest (pos + 1 + (cs.length - rest.length)) (acc.push ⟨.atom a, pos⟩)
        | none => .error (.unexpectedChar pos c)

end Tokenizer

/-- Tokenize a SMILES string.  Leading whitespace is skipped; positions still
count from the start of the string. -/
def tokenize (s : String) : Except ParseError (Array Token) :=
  let (lead, cs) := s.toList.span Char.isWhitespace
  Tokenizer.go (cs.length + 1) cs lead.length #[]

end LeanSMILES.SMILES
