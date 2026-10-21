import Lean

namespace CSVparser

inductive Feature where
  | esolPredicted
  | minDegree
  | molecularWeight
  | numHBondDonors
  | numRings
  | numRotatableBonds
  | polarSurfaceArea
  | measuredLogSolubility
  deriving BEq, Inhabited, Repr

def Feature.all : List Feature :=
  [.esolPredicted, .minDegree, .molecularWeight, .numHBondDonors,
   .numRings, .numRotatableBonds, .polarSurfaceArea, .measuredLogSolubility]

structure Molecule where
  smiles : String
  values : List (Feature × Float)
  deriving Inhabited

/-- Get a single feature value (e.g. `m.get .molecularWeight`). -/
def Molecule.get (m : Molecule) (f : Feature) : Float :=
  m.values.lookup f |>.getD 0.0

/-- Numeric feature vector in the order requested, ready for ML training. -/
def Molecule.features (m : Molecule) : Array Float :=
  m.values.toArray.map Prod.snd

private def parseFloat (s : String) : Float :=
  match Lean.Json.parse s.trimAscii.toString with
  | .ok (.num n) => n.toFloat
  | _            => 0.0

def parse (contents : String) (features := Feature.all) : Array Molecule :=
  (contents.splitOn "\n").drop 1 |>.foldl (init := #[]) fun acc line =>
    if line.trimAscii.isEmpty then acc else
      let cells := (line.splitOn ",").reverse.take 9 |>.reverse
      let values := features.map fun f => (f, parseFloat (cells.getD f.ctorIdx ""))
      acc.push { smiles := cells.getD 8 "" |>.trimAscii.toString, values }

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


