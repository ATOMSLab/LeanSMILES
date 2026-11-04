/-
Copyright (c) 2026 Kevin Ishimwe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Ishimwe, Samiha Sharlin, Tyler Josephson
-/
module

public import Lean.Data.Json

/-!
# CSVparser

Reads a molecule table such as `datasets/delaney-processed.csv`: one row per
molecule, a `smiles` column, and numeric columns. Columns are found by their
header names, so their order and any extra columns do not matter; fields may be
quoted (`"2,2',3,4,6-PCB"`), with `""` for a quote inside a quoted field.
-/

public section

namespace CSVparser

/-- The numeric columns the parser knows, by header name. -/
inductive Feature where
  /-- The measured log solubility (mol/L) column of the Delaney table. -/
  | measuredLogSolubility
  deriving BEq, Inhabited, Repr

/-- Every feature the parser knows: the default column set of `parse` and `load` (pass `[]` to
read only the SMILES). -/
def Feature.all : List Feature := [.measuredLogSolubility]

/-- The column header that holds the feature. -/
def Feature.header : Feature → String
  | .measuredLogSolubility => "measured log solubility in mols per litre"

/-- One row of the table: the SMILES string and the numeric features read from the row. -/
structure Molecule where
  /-- The `smiles` column, trimmed. -/
  smiles : String
  /-- The requested features, in order, each with its value: `0.0` when the column is missing or
  the cell is not a number. -/
  values : List (Feature × Float)
  deriving Inhabited

/-- A single feature value (e.g. `m.get .measuredLogSolubility`); `0.0` if `f` was not read. -/
def Molecule.get (m : Molecule) (f : Feature) : Float :=
  m.values.lookup f |>.getD 0.0

/-- Numeric feature vector in the order requested, ready for ML training. -/
def Molecule.features (m : Molecule) : Array Float :=
  m.values.toArray.map Prod.snd

private def parseFloat (s : String) : Float :=
  match Lean.Json.parse s.trimAscii.toString with
  | .ok (.num n) => n.toFloat
  | _            => 0.0

/-- The fields of one CSV line, with quotes removed. -/
def splitLine (line : String) : List String :=
  let rec go : List Char → Bool → List Char → List String → List String
    | [], _, cur, acc => acc ++ [String.ofList cur.reverse]
    | '"' :: '"' :: cs, true, cur, acc => go cs true ('"' :: cur) acc
    | '"' :: cs, q, cur, acc => go cs (!q) cur acc
    | ',' :: cs, false, cur, acc => go cs false [] (acc ++ [String.ofList cur.reverse])
    | c :: cs, q, cur, acc => go cs q (c :: cur) acc
  go line.toList false [] []

/-- Parse a table: its first line is the header, each later non-blank line becomes a `Molecule`
carrying the given `features` (all of them by default); columns are found by header name. -/
def parse (contents : String) (features := Feature.all) : Array Molecule :=
  let lines := (contents.splitOn "\n").map fun l ↦ (l.dropEndWhile (· == '\r')).toString
  let header := (splitLine (lines.headD "")).map fun h ↦ h.trimAscii.toString
  let column (name : String) : Option Nat := header.idxOf? name
  let smilesCol := (column "smiles").getD header.length
  lines.drop 1 |>.foldl (init := #[]) fun acc line ↦
    if line.trimAscii.isEmpty then acc else
      let cells := splitLine line
      let values := features.map fun f ↦
        (f, match column f.header with
          | some i => parseFloat (cells.getD i "")
          | none => 0.0)
      acc.push { smiles := cells.getD smilesCol "" |>.trimAscii.toString, values }

private unsafe def readFileUnsafe (path : System.FilePath) : String :=
  match unsafeIO (IO.FS.readFile path) with
  | .ok s    => s
  | .error _ => ""

-- A pure view of the file's contents, so that `load` can be used in `def`s and in `#eval`s at
-- elaboration time; an unreadable file reads as the empty string.
@[implemented_by readFileUnsafe]
private opaque readFilePure (path : System.FilePath) : String

/-- `parse` of the file at `path`; an unreadable file gives an empty table. Pure, so it can sit
in a `def` (`def delaney := load "datasets/delaney-processed.csv"`) and run in `#eval`. -/
def load (path : System.FilePath) (features := Feature.all) : Array Molecule :=
  parse (readFilePure path) features

/-- Total indexing `records[i]` with no bounds proof (an out-of-range index reads the default,
empty molecule), so that `#eval records[1]` and `records[start + i]` need no side condition. -/
instance (priority := high) : GetElem (Array Molecule) Nat Molecule (fun _ _ ↦ True) where
  getElem xs i _ := xs.getD i default

/-- Shows a row as `{ smiles := "...", measuredLogSolubility := ... }`: one field per feature
read. -/
instance : Repr Molecule where
  reprPrec m _ :=
    let fields := s!"smiles := \"{m.smiles}\"" :: m.values.map fun (f, x) ↦
      s!"{(reprStr f).splitOn "." |>.getLast!} := {Lean.toJson x}"
    "{ " ++ ", ".intercalate fields ++ " }"

end CSVparser
