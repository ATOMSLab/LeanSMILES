# Merge notes: `canonical-smiles` → `main`

What to know when merging this branch into `main`. The branch merged `main` at
`3ede9f6` (PR #13), so it already has the three-library layout and the module
system; what it adds on top is listed here.

## What this branch adds to `main`

| Where | What |
|---|---|
| `LeanLearn/Regression/SparseRidge.lean` | ridge regression (`Ridge(alpha)` objective) on sparse `0/1` features by conjugate gradients |
| `LeanLearn/Regression/Metrics.lean` | `r2`, `rmse`, `mae` |
| `LeanLearn/Plot/Parity.lean` | parity plots as SVG (`paritySvg`), with R², RMSE and MAE per split |
| `Pipelines/Tests/Ridge.lean`, `lake exe ridge-test` | Delaney log solubility on Morgan bits vs scikit-learn; `--svg` writes the plot |
| `tools/sklearn_delaney.py`, `datasets/delaney-ridge.csv` | the scikit-learn answer file |
| `docs/figures/delaney-ridge-parity.svg` | the plot `ridge-test --svg` writes |
| `tools/rdkit_reference/*.py` | the Python reference implementations the RDKit port was written from |
| `datasets/delaney-processed.csv`, `LeanSMILES/Data/CSVparser.lean` | three columns kept; parser reads by header (below) |

`LeanLearn.lean` imports the three new modules; `lakefile.toml` adds `ridge-test`.

## `datasets/delaney-processed.csv` keeps three columns

```
Compound ID,measured log solubility in mols per litre,smiles
```

Removed: `ESOL predicted log solubility in mols per litre`, `Minimum Degree`,
`Molecular Weight`, `Number of H-Bond Donors`, `Number of Rings`,
`Number of Rotatable Bonds`, `Polar Surface Area`. Every remaining value is
unchanged (checked row by row with Python's `csv`).

`LeanSMILES/Data/CSVparser.lean` changed with it:

* **Columns are found by header name**, not by position. The old parser took
  the last 9 cells of each line and assumed their order, so on the slimmed
  file it would have returned empty SMILES without any error.
* **Quoted fields are handled** (`"2,2',3,4,6-PCB"`, `""` inside quotes), via
  `CSVparser.splitLine`.
* **`Feature` has one constructor left, `measuredLogSolubility`**, and names its
  column with `Feature.header`. `esolPredicted`, `minDegree`, `molecularWeight`,
  `numHBondDonors`, `numRings`, `numRotatableBonds` and `polarSurfaceArea` are
  gone.
* `load`, `parse`, `Molecule.get`, `Molecule.features` and `.smiles` keep their
  signatures.

Uses on `main`: `LeanSMILES/Examples/parsercsv.lean` used `.molecularWeight`
(changed here to `.measuredLogSolubility`; `recordsonlymolWeight` is now
`recordsSmilesOnly`); `Pipelines/Data.lean` uses only `.measuredLogSolubility`
and `.smiles` and works unchanged. **Code added to `main` after `3ede9f6` that
uses a removed constructor needs the same change.**

To use a descriptor again, put its column back in the CSV (the full file is in
git history: `git show 422923a:datasets/delaney-processed.csv`) and add a
`Feature` constructor with its header name.

The Python tools read columns by name and are unaffected:
`tools/rdkit_oracle.py` regenerates `datasets/delaney-oracle.csv` byte for
byte, and `tools/sklearn_delaney.py` regenerates `datasets/delaney-ridge.csv`
unchanged.

## The stricter grammar (PR #11)

The parser rejects SMILES with a ring label after a branch; in Delaney that is
chlorothalonil, `c1(C#N)c(Cl)c(C#N)c(Cl)c(Cl)c(Cl)1`. `ridge-test` leaves such
molecules out of its pipeline stage and lists them (its solver stage uses
RDKit's bits and keeps all 1 128). If the grammar decision changes, the
pipeline numbers in the README change with it.

## After merging

```bash
lake build
lake exe validity-test
lake exe oracle-test
lake exe morgan-test
lake exe charge-test
lake exe parse-errors-test
lake exe aromaticity-test
lake exe ols-float-test
lake exe ridge-float-test
lake exe linear-model-test
lake exe logistic-test
lake exe ridge-test
```

All must exit 0.
