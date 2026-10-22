module

public import Lean.Data.Json

public section

namespace CSVparser

/-!
# CSVparser

Reads a molecule table such as `datasets/delaney-processed.csv`: one row per
molecule, a `smiles` column, and numeric columns. Columns are found by their
header names, so their order and any extra columns do not matter; fields may be
quoted (`"2,2',3,4,6-PCB"`), with `""` for a quote inside a quoted field.
-/

/-- The numeric columns the parser knows, by header name. -/
inductive Feature where
  | measuredLogSolubility
  deriving BEq, Inhabited, Repr

def Feature.all : List Feature := [.measuredLogSolubility]

/-- The column header that holds the feature. -/
def Feature.header : Feature → String
  | .measuredLogSolubility => "measured log solubility in mols per litre"

structure Molecule where
  smiles : String
  values : List (Feature × Float)
  deriving Inhabited

/-- Get a single feature value (e.g. `m.get .measuredLogSolubility`). -/
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
    | [], _, cur, acc => (acc ++ [String.ofList cur.reverse])
    | '"' :: '"' :: cs, true, cur, acc => go cs true ('"' :: cur) acc
    | '"' :: cs, q, cur, acc => go cs (!q) cur acc
    | ',' :: cs, false, cur, acc => go cs false [] (acc ++ [String.ofList cur.reverse])
    | c :: cs, q, cur, acc => go cs q (c :: cur) acc
  go line.toList false [] []

def parse (contents : String) (features := Feature.all) : Array Molecule :=
  let lines := (contents.splitOn "\n").map fun l ↦ (l.dropEndWhile (· == '\r')).toString
  let header := (splitLine (lines.headD "")).map fun h ↦ h.trimAscii.toString
  let column (name : String) : Option Nat := header.idxOf? name
  let smilesCol := (column "smiles").getD header.length
  lines.drop 1 |>.foldl (init := #[]) fun acc line =>
    if line.trimAscii.isEmpty then acc else
      let cells := splitLine line
      let values := features.map fun f =>
        (f, match column f.header with
          | some i => parseFloat (cells.getD i "")
          | none => 0.0)
      acc.push { smiles := cells.getD smilesCol "" |>.trimAscii.toString, values }

private unsafe def readFileUnsafe (path : System.FilePath) : String :=
  match unsafeIO (IO.FS.readFile path) with
  | .ok s    => s
  | .error _ => ""

@[implemented_by readFileUnsafe]
private opaque readFilePure (path : System.FilePath) : String

def load (path : System.FilePath) (features := Feature.all) : Array Molecule :=
  parse (readFilePure path) features

instance (priority := high) : GetElem (Array Molecule) Nat Molecule (fun _ _ => True) where
  getElem xs i _ := xs.getD i default

instance : Repr Molecule where
  reprPrec m _ :=
    let fields := s!"smiles := \"{m.smiles}\"" :: m.values.map fun (f, x) =>
      s!"{(reprStr f).splitOn "." |>.getLast!} := {Lean.toJson x}"
    "{ " ++ ", ".intercalate fields ++ " }"

end CSVparser

