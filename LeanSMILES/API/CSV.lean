module

public import LeanSMILES.Primitives.decimal

/-!
# CSV parsing

`CSV.parse` reads RFC 4180-style CSV: quoted fields may contain commas, newlines and `""`
escapes, and `\r\n` line endings are accepted. Every row must have as many fields as the
header. Numeric fields are read with `Primitives.Decimal.parse?`.
-/

@[expose] public section

namespace API

open Primitives

/-! ## CSV -/

structure CSV where
  header : Array String
  rows : Array (Array String)
  deriving Repr, Inhabited

def fieldOf (rev : List Char) : String := String.ofList rev.reverse

/-- CSV state machine, one character per step (structural recursion). `field` holds the
current field reversed, `quoted` tells whether we are inside quotes. -/
def parseCSVChars : List Char → List Char → Array String → Array (Array String) → Bool →
    Array (Array String)
  | [], field, row, rows, _ =>
    if field.isEmpty && row.isEmpty then rows else rows.push (row.push (fieldOf field))
  | '"' :: '"' :: cs, field, row, rows, true => parseCSVChars cs ('"' :: field) row rows true
  | '"' :: cs, field, row, rows, true => parseCSVChars cs field row rows false
  | c :: cs, field, row, rows, true => parseCSVChars cs (c :: field) row rows true
  | '"' :: cs, field, row, rows, false => parseCSVChars cs field row rows true
  | ',' :: cs, field, row, rows, false =>
    parseCSVChars cs [] (row.push (fieldOf field)) rows false
  | '\r' :: cs, field, row, rows, false => parseCSVChars cs field row rows false
  | '\n' :: cs, field, row, rows, false =>
    parseCSVChars cs [] #[] (rows.push (row.push (fieldOf field))) false
  | c :: cs, field, row, rows, false => parseCSVChars cs (c :: field) row rows false

def CSV.parse (text : String) : Except String CSV :=
  let rows := (parseCSVChars text.toList [] #[] #[] false).filter (· != #[""])
  match rows[0]? with
  | none => .error "empty CSV"
  | some header =>
    let body := rows.extract 1 rows.size
    match body.findIdx? (·.size != header.size) with
    | some i =>
      .error s!"CSV row {i + 2} has {(body.getD i #[]).size} fields, expected {header.size}"
    | none => .ok ⟨header, body⟩

def CSV.columnIndex (csv : CSV) (name : String) : Except String Nat :=
  match csv.header.findIdx? (·.trimAscii.toString == name) with
  | some i => .ok i
  | none => .error s!"no column named '{name}'"

def CSV.column (csv : CSV) (name : String) : Except String (Array String) := do
  let i ← csv.columnIndex name
  return csv.rows.map (·.getD i "")

/-- Number of empty (or all-whitespace) fields in each column, like `df.isnull().sum()`. -/
def CSV.missingCounts (csv : CSV) : Array (String × Nat) :=
  csv.header.mapIdx fun i name =>
    (name, (csv.rows.filter fun r => (r.getD i "").trimAscii.isEmpty).size)

def readCSV (path : System.FilePath) : IO CSV := do
  IO.ofExcept (CSV.parse (← IO.FS.readFile path))

end API

end
