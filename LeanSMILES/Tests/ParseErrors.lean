/-
Copyright (c) 2026 Hao Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hao Liu
-/
module

public import LeanSMILES.SMILES.Parse

/-!
# Parse error messages

Run `lake exe parse-errors-test` from the repository root. Each case shows a
small invalid SMILES string, the error constructor it should produce, and the
exact user-facing message. Positions are 0-based character offsets. The
`internal` constructor is checked separately because no input should reach it.

A second list, `accepted`, pins the strings that must parse: the decisions in
the accept direction from "What the parser accepts" in the README, together
with what atom 0 was recorded as.
-/

open LeanSMILES.SMILES

structure ErrorCase where
  name : String
  input : String
  expected : ParseError
  message : String

def cases : List ErrorCase := [
  ⟨"unexpected character", "C?", .unexpectedChar 1 '?',
    "unexpected character '?' at 1"⟩,
  ⟨"unexpected character in bracket", "[13!C]", .unexpectedChar 3 '!',
    "unexpected character '!' at 3"⟩,
  ⟨"invalid second ring digit", "C%1x", .unexpectedChar 3 'x',
    "unexpected character 'x' at 3"⟩,
  ⟨"invalid first ring digit", "C%x1", .unexpectedChar 2 'x',
    "unexpected character 'x' at 2"⟩,
  ⟨"end before bracket symbol", "[", .unexpectedEnd "an element symbol",
    "unexpected end of input, expected an element symbol"⟩,
  ⟨"end before closing bracket", "[C", .unexpectedEnd "']'",
    "unexpected end of input, expected ']'"⟩,
  ⟨"end before two-digit ring label", "C%1", .unexpectedEnd "two digits after '%'",
    "unexpected end of input, expected two digits after '%'"⟩,
  ⟨"end after dot", "C.", .unexpectedEnd "an atom after '.'",
    "unexpected end of input, expected an atom after '.'"⟩,
  ⟨"unknown element", "[X]", .unknownElement 1 "X",
    "unknown element symbol 'X' at 1"⟩,
  ⟨"unknown element after isotope", "[13X]", .unknownElement 3 "X",
    "unknown element symbol 'X' at 3"⟩,
  ⟨"malformed bracket", "[Cx]", .badBracket 0 "unexpected 'x'",
    "malformed bracket atom at 0: unexpected 'x'"⟩,
  ⟨"nonaromatic element written aromatic", "[f]", .badBracket 0 "'f' may not be written aromatic",
    "malformed bracket atom at 0: 'f' may not be written aromatic"⟩,
  ⟨"leading bond", "-C", .bondWithoutAtom 0,
    "bond symbol at 0 cannot connect two atoms"⟩,
  ⟨"consecutive bonds", "C--C", .bondWithoutAtom 1,
    "bond symbol at 1 cannot connect two atoms"⟩,
  ⟨"trailing bond", "C-", .bondWithoutAtom 1,
    "bond symbol at 1 cannot connect two atoms"⟩,
  ⟨"branch before atom", "(C)", .branchWithoutAtom 0,
    "branch opened at 0 without an atom to attach to"⟩,
  ⟨"branch after dot", "C.(O)", .branchWithoutAtom 2,
    "branch opened at 2 without an atom to attach to"⟩,
  ⟨"ring before atom", "1C", .ringWithoutAtom 0,
    "ring-closure label at 0 without an atom to attach to"⟩,
  ⟨"percent ring before atom", "%12C", .ringWithoutAtom 0,
    "ring-closure label at 0 without an atom to attach to"⟩,
  ⟨"ring after dot", "C.1", .ringWithoutAtom 2,
    "ring-closure label at 2 without an atom to attach to"⟩,
  ⟨"unmatched branch close", "C)", .unmatchedBranchClose 1,
    "')' at 1 closes no branch"⟩,
  ⟨"empty branch", "C()", .emptyBranch 2,
    "empty branch '()' closed at 2"⟩,
  ⟨"ring directly after branch open", "C(1C)", .ringAfterBranchOpen 2,
    "ring-closure label at 2 directly after '('"⟩,
  ⟨"percent ring directly after branch open", "C(%12C)", .ringAfterBranchOpen 2,
    "ring-closure label at 2 directly after '('"⟩,
  ⟨"leading dot", ".C", .danglingDot 0,
    "'.' at 0 is not between two atoms"⟩,
  ⟨"dot directly after branch open", "C(.O)", .danglingDot 2,
    "'.' at 2 is not between two atoms"⟩,
  ⟨"dot before branch close", "C(C.)", .danglingDot 3,
    "'.' at 3 is not between two atoms"⟩,
  ⟨"one unclosed branch", "C(C", .unclosedBranch 1,
    "1 branch was never closed"⟩,
  ⟨"unclosed branches", "C(C(C", .unclosedBranch 2,
    "2 branches were never closed"⟩,
  ⟨"one unclosed ring", "C1", .unclosedRing [1],
    "ring closure 1 was never closed"⟩,
  ⟨"unclosed rings in input order", "C12", .unclosedRing [1, 2],
    "ring closures [1, 2] were never closed"⟩,
  ⟨"ring self-bond", "C11", .selfBond 2 0,
    "ring closure at 2 bonds atom 0 to itself"⟩,
  ⟨"duplicate bond", "C1C1", .duplicateBond 3 0 1,
    "bond at 3 duplicates the bond between atoms 0 and 1"⟩,
  ⟨"conflicting ring bond symbols", "C=1CC-1", .conflictingRingBond 6 1,
    "ring closure 1 at 6 has two different bond symbols"⟩,
  -- Decisions in the reject direction (README, "What the parser accepts").
  ⟨"ring label after a branch", "C(C)1CC1", .ringAfterBranch 4,
    "ring-closure label at 4 after a branch: labels must precede branches"⟩,
  ⟨"ring label closing after a branch", "C1CC(C)1", .ringAfterBranch 7,
    "ring-closure label at 7 after a branch: labels must precede branches"⟩,
  ⟨"ring label after a branch and a bond", "C(C)=1CC1", .ringAfterBranch 5,
    "ring-closure label at 5 after a branch: labels must precede branches"⟩,
  ⟨"two-digit hydrogen count", "[CH10]",
    .badBracket 0 "hydrogen count 'H10' has more than one digit",
    "malformed bracket atom at 0: hydrogen count 'H10' has more than one digit"⟩,
  ⟨"class without a number", "[C:]", .badBracket 0 "':' is not followed by a class number",
    "malformed bracket atom at 0: ':' is not followed by a class number"⟩,
  ⟨"chirality class out of range", "[C@TH3]", .badBracket 0 "'@TH3' is not a chirality class",
    "malformed bracket atom at 0: '@TH3' is not a chirality class"⟩,
  ⟨"chirality class without a number", "[Fe@OH]", .badBracket 0 "'@OH' is not a chirality class",
    "malformed bracket atom at 0: '@OH' is not a chirality class"⟩,
  ⟨"two-letter symbol written aromatic", "[te]", .badBracket 0 "'te' may not be written aromatic",
    "malformed bracket atom at 0: 'te' may not be written aromatic"⟩,
  ⟨"unknown two-letter aromatic symbol", "[xy]", .unknownElement 1 "xy",
    "unknown element symbol 'xy' at 1"⟩,
  ⟨"one character after '%'", "C%x", .unexpectedChar 2 'x',
    "unexpected character 'x' at 2"⟩,
  ⟨"RDKit's long ring labels", "C%(123)CC%(123)", .unexpectedChar 2 '(',
    "unexpected character '(' at 2"⟩
]

/-- A string that must parse, with its atom count and what atom 0 was
recorded as (its SMILES form, bare or bracketed). -/
structure AcceptCase where
  name : String
  input : String
  atoms : ℕ
  atom0 : String

def accepted : List AcceptCase := [
  ⟨"leading whitespace is skipped", " C", 1, "C"⟩,
  ⟨"whitespace ends the SMILES; the rest is a title", "C C", 1, "C"⟩,
  ⟨"ring labels before a branch", "C1(C)CC1", 4, "C"⟩,
  ⟨"ring closure across a dot", "C1.C1", 2, "C"⟩,
  ⟨"tetrahedral class", "[C@TH1](F)(Cl)(Br)I", 5, "[C@TH1]"⟩,
  ⟨"allenal class", "[C@AL2](F)(Cl)", 3, "[C@AL2]"⟩,
  ⟨"square-planar class", "[S@SP3](F)(Cl)(Br)I", 5, "[S@SP3]"⟩,
  ⟨"trigonal-bipyramidal class", "[P@TB20](F)(F)(F)(F)F", 6, "[P@TB20]"⟩,
  ⟨"octahedral class, two digits", "[Fe@OH30](C)(C)(C)(C)(C)C", 7, "[Fe@OH30]"⟩,
  ⟨"charge as a run of signs", "[Fe+++]", 1, "[Fe+3]"⟩,
  ⟨"three-digit charge (bounded after parsing, not here)", "[C+123]", 1, "[C+123]"⟩,
  ⟨"isotope with a leading zero", "[02H]", 1, "[2H]"⟩
]

def checkCase (c : ErrorCase) : IO Bool := do
  match parseRaw c.input with
  | .ok _ =>
    IO.eprintln s!"FAIL {c.name} ({c.input.quote}): parser accepted input"
    pure false
  | .error actual =>
    if actual == c.expected && actual.toString == c.message then
      IO.println s!"PASS {c.name} ({c.input.quote}): {actual}"
      pure true
    else
      IO.eprintln s!"FAIL {c.name} ({c.input.quote})"
      IO.eprintln s!"  expected: {repr c.expected} / {c.message}"
      IO.eprintln s!"  got: {repr actual} / {actual}"
      pure false

def checkAccept (c : AcceptCase) : IO Bool := do
  match parseRaw c.input with
  | .error e =>
    IO.eprintln s!"FAIL {c.name} ({c.input.quote}): {e}"
    pure false
  | .ok M =>
    let atom0 := (M.mol.atoms.toList.head?.map toString).getD ""
    if M.n == c.atoms && atom0 == c.atom0 then
      IO.println s!"PASS {c.name} ({c.input.quote}): {M.n} atoms, atom 0 is {atom0}"
      pure true
    else
      IO.eprintln s!"FAIL {c.name} ({c.input.quote})"
      IO.eprintln s!"  expected: {c.atoms} atoms, atom 0 {c.atom0}"
      IO.eprintln s!"  got: {M.n} atoms, atom 0 {atom0}"
      pure false

public def main : IO UInt32 := do
  let results ← cases.mapM checkCase
  let acceptResults ← accepted.mapM checkAccept
  let internalMessage := (ParseError.internal "tokenizer out of fuel").toString
  let internalOk := internalMessage == "internal error: tokenizer out of fuel"
  if internalOk then
    IO.println s!"PASS internal (not reachable from a normal input): {internalMessage}"
  else
    IO.eprintln s!"FAIL internal: {internalMessage}"
  let passed := (results ++ acceptResults).filter id |>.length
  let totalPassed := passed + (if internalOk then 1 else 0)
  let total := cases.length + accepted.length + 1
  IO.println s!"{totalPassed}/{total} parse error message checks passed"
  pure (if results.all id && acceptResults.all id && internalOk then 0 else 1)
