import LeanSMILES.Widgets.Charts
import LeanSMILES.Widgets.Molecule
import LeanSMILES.Widgets.Table
import LeanSMILES.API.Pipeline

/-!
# `#show`: rich notebook output

`#show e` renders `e` as a widget in the infoview, the way Jupyter displays a cell's
value: molecules are drawn, records and metrics become tables, figures are shown as they
are. Any type with a `NotebookDisplay` instance works. `#show` expands to
ProofWidgets' `#html`, which also accepts `IO Html` computations directly.
-/

namespace MetaPrograms

open Lean ProofWidgets Widgets Chem API Primitives

class NotebookDisplay (α : Type) where
  toHtml : α → Html

/-- Display `e` as rich HTML in the infoview. -/
syntax (name := showCmd) "#show " term : command

macro_rules
  | `(#show $t) => `(#html NotebookDisplay.toHtml $t)

instance : NotebookDisplay Html := ⟨id⟩

instance : NotebookDisplay String := ⟨fun s => .element "pre" #[] #[.text s]⟩

instance : NotebookDisplay Molecule := ⟨fun m => moleculeSvg m 300 (Exec.molToSmiles m)⟩

instance [NotebookDisplay α] : NotebookDisplay (Except String α) where
  toHtml
    | .ok a => NotebookDisplay.toHtml a
    | .error e => .element "pre" #[("style", Json.mkObj [("color", toJson "crimson")])]
        #[.text s!"error: {e}"]

instance : NotebookDisplay Descriptors where
  toHtml d := keyValueTable #[("Formula", d.formula),
    ("Molecular weight", d.molecularWeight.toString), ("Heavy atoms", s!"{d.heavyAtoms}"),
    ("H-bond donors", s!"{d.hDonors}"), ("Rings", s!"{d.rings}"),
    ("Rotatable bonds", s!"{d.rotatableBonds}"), ("Minimum degree", s!"{d.minDegree}")]
    "Descriptors"

instance : NotebookDisplay (RegressionMetrics Float) where
  toHtml r := keyValueTable #[("MSE", formatFloat r.mse 4), ("RMSE", formatFloat r.rmse 4),
    ("MAE", formatFloat r.mae 4), ("R²", formatFloat r.r2 4)] "Regression metrics"

instance : NotebookDisplay CleaningReport where
  toHtml r := keyValueTable #[("Original count", s!"{r.original}"),
    ("Invalid SMILES", s!"{r.invalid.size}"), ("Duplicates detected", s!"{r.duplicates.size}"),
    ("Unique molecules", s!"{r.unique}")] "SMILES cleaning"

instance : NotebookDisplay (Summary Float) where
  toHtml s := keyValueTable #[("count", s!"{s.count}"), ("mean", formatFloat s.mean 4),
    ("std", formatFloat s.std 4), ("min", formatFloat s.min 4), ("max", formatFloat s.max 4)]
    "Summary"

/-- The first ten rows, like `df.head(10)`. -/
instance : NotebookDisplay CSV where
  toHtml csv := table (#[""] ++ csv.header)
    ((csv.rows.extract 0 10).mapIdx fun k r => #[s!"{k}"] ++ r)
    s!"{csv.rows.size} rows × {csv.header.size} columns"

instance : NotebookDisplay (Array SolubilityRecord) where
  toHtml rs := table #["", "Compound ID", "smiles", "measured logS", "ESOL logS"]
    ((rs.extract 0 10).mapIdx fun k r =>
      #[s!"{k}", r.compoundId, r.smiles.str, r.logS.toString, r.esolLogS.toString])
    s!"{rs.size} records"

instance : NotebookDisplay (Array ValidRecord) where
  toHtml rs := table #["", "Compound ID", "canonical SMILES", "formula", "measured logS"]
    ((rs.extract 0 10).mapIdx fun k r =>
      #[s!"{k}", r.compoundId, r.canonical.smiles.str, r.molecule.formula, r.logS.toString])
    s!"{rs.size} valid records"

end MetaPrograms
