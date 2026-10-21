module

public import LeanSMILES.API.CSV
public import LeanSMILES.SMILES.DEFINITIONS

/-!
# Solubility dataset loader

Loads the Delaney (ESOL) dataset and cleans it the way the project notebook does:

1. read the CSV and parse every numeric column exactly (`Decimal`);
2. validate every SMILES with `Chem.SMILES.parse`, dropping the ones that fail;
3. canonicalize and drop duplicate molecules, keeping the first occurrence.

Every record that survives is a `ValidRecord`. It carries proofs that its SMILES parses
to the stored molecule and that the molecule is well-formed with at least one atom. A
`ValidRecord` can only be built by passing those checks.
-/

@[expose] public section

namespace API

open Primitives Chem

/-- Column names of `delaney-processed.csv`. -/
structure DelaneyColumns where
  id : String := "Compound ID"
  smiles : String := "smiles"
  measured : String := "measured log solubility in mols per litre"
  esol : String := "ESOL predicted log solubility in mols per litre"
  descriptors : Vector String 6 := #v["Minimum Degree", "Molecular Weight",
    "Number of H-Bond Donors", "Number of Rings", "Number of Rotatable Bonds",
    "Polar Surface Area"]

/-- One row of the dataset, as read (SMILES not yet validated). -/
structure SolubilityRecord where
  /-- 1-based line number in the CSV file (the header is line 1). -/
  line : Nat
  compoundId : String
  smiles : SMILES
  /-- Measured log solubility, log₁₀(mol/L): the regression target. -/
  logS : Decimal
  /-- The ESOL model's prediction, a published baseline. -/
  esolLogS : Decimal
  /-- The six precomputed descriptors, in `DelaneyColumns.descriptors` order. -/
  descriptors : Vector Decimal 6
  deriving Repr, Inhabited

def parseDecimalField (line : Nat) (column field : String) : Except String Decimal :=
  match Decimal.parse? field with
  | some d => .ok d
  | none => .error s!"line {line}: column '{column}' is not a number: '{field}'"

/-- Read the records out of a parsed CSV. Fails on the first non-numeric numeric field. -/
def parseRecords (csv : CSV) (cols : DelaneyColumns := {}) :
    Except String (Array SolubilityRecord) := do
  let iId ← csv.columnIndex cols.id
  let iSmiles ← csv.columnIndex cols.smiles
  let iMeasured ← csv.columnIndex cols.measured
  let iEsol ← csv.columnIndex cols.esol
  let iDesc ← cols.descriptors.mapM csv.columnIndex
  csv.rows.zipIdx.mapM fun (row, k) => do
    let line := k + 2
    let field := fun i => (row.getD i "").trimAscii.toString
    return {
      line, compoundId := field iId, smiles := ⟨field iSmiles⟩
      logS := ← parseDecimalField line cols.measured (field iMeasured)
      esolLogS := ← parseDecimalField line cols.esol (field iEsol)
      descriptors := ← (iDesc.zip cols.descriptors).mapM fun (i, name) =>
        parseDecimalField line name (field i) }

/-- A record whose SMILES has been checked against the SMILES definitions. -/
structure ValidRecord extends SolubilityRecord where
  molecule : Molecule
  parses : smiles.parse = .ok molecule
  wellFormed : molecule.WellFormed
  nonempty : 0 < molecule.atoms.size

def ValidRecord.canonical (r : ValidRecord) : CanonicalSMILES := r.molecule.canonicalSMILES

/-- Check a record's SMILES: it must parse, give a well-formed molecule, and have at
least one atom. -/
def validate (r : SolubilityRecord) : Except String ValidRecord :=
  match h : r.smiles.parse with
  | .error e => .error e
  | .ok m =>
    if hw : m.WellFormed then
      if hn : 0 < m.atoms.size then
        .ok { toSolubilityRecord := r, molecule := m, parses := h, wellFormed := hw,
              nonempty := hn }
      else .error "empty molecule"
    else .error "bond refers to a missing atom"

/-- What `clean` removed. -/
structure CleaningReport where
  original : Nat
  /-- `(line, SMILES, reason)` for every SMILES that failed validation. -/
  invalid : Array (Nat × String × String)
  /-- `(line, canonical SMILES)` for every later copy of an already-seen molecule. -/
  duplicates : Array (Nat × String)
  unique : Nat
  deriving Repr

/-- Validate, canonicalize and drop duplicates (first occurrence wins), like the
notebook's `canonicalize` + `notna` + `drop_duplicates(subset='canonical_smiles')`. -/
def clean (records : Array SolubilityRecord) : Array ValidRecord × CleaningReport :=
  let (kept, _, invalid, dups) := records.foldl
    (fun (kept, seen, invalid, dups) r =>
      match validate r with
      | .error e => (kept, seen, invalid.push (r.line, r.smiles.str, e), dups)
      | .ok v =>
        let c := v.canonical.smiles.str
        if seen.contains c then (kept, seen, invalid, dups.push (r.line, c))
        else (kept.push v, c :: seen, invalid, dups))
    ((#[] : Array ValidRecord), ([] : List String), #[], #[])
  (kept, { original := records.size, invalid, duplicates := dups, unique := kept.size })

/-- Load and parse the dataset (no cleaning). -/
def loadRecords (path : System.FilePath) (cols : DelaneyColumns := {}) :
    IO (Array SolubilityRecord) := do
  IO.ofExcept (parseRecords (← readCSV path) cols)

/-- Load, validate and deduplicate the dataset. -/
def loadClean (path : System.FilePath) (cols : DelaneyColumns := {}) :
    IO (Array ValidRecord × CleaningReport) := do
  return clean (← loadRecords path cols)

end API

end
