# Merge notes: `canonical-smiles` → `main`

What to know when merging this branch into `main` (or another branch). Written
against `main` at `ce30474` (PR #11); the branch last merged `main` at
`649ba82` (PR #7).

## 1. `datasets/delaney-processed.csv` keeps three columns

The Delaney file now has only the columns the code uses:

```
Compound ID,measured log solubility in mols per litre,smiles
```

Removed: `ESOL predicted log solubility in mols per litre`, `Minimum Degree`,
`Molecular Weight`, `Number of H-Bond Donors`, `Number of Rings`,
`Number of Rotatable Bonds`, `Polar Surface Area`. Every remaining value is
unchanged (checked row by row with Python's `csv`).

Because of that, `LeanSMILES/Data/CSVparser.lean` changed:

* **Columns are found by header name**, not by position. The old parser took
  the last 9 cells of each line and assumed their order, so on the slimmed
  file it would have returned empty SMILES without any error.
* **Quoted fields are handled** (`"2,2',3,4,6-PCB"`, `""` inside quotes), via
  the new `CSVparser.splitLine`.
* **`Feature` has one constructor left, `measuredLogSolubility`.** The others
  (`esolPredicted`, `minDegree`, `molecularWeight`, `numHBondDonors`,
  `numRings`, `numRotatableBonds`, `polarSurfaceArea`) are gone, and each
  `Feature` now names its column with `Feature.header`.
* `load`, `parse`, `Molecule.get`, `Molecule.features` and `.smiles` keep their
  signatures.

**When merging:**

* Take this branch's versions of `datasets/delaney-processed.csv`,
  `LeanSMILES/Data/CSVparser.lean` and `LeanSMILES/Examples/parsercsv.lean`.
* Any code that uses a removed `Feature` constructor must change. Known uses:
  `Examples/parsercsv.lean` on `main`, `testing-df` and `algorithms`
  (`records[1].get .molecularWeight`, now `.measuredLogSolubility`; the
  definition `recordsonlymolWeight` is now `recordsSmilesOnly`).
* `testing-df`'s pipeline (`Pipeline/Data.lean`, `Examples/pipeline.lean`) uses
  only `.smiles` and `.measuredLogSolubility`, so it works unchanged.
* To use a descriptor again, put its column back in the CSV (the full file is
  in git history, e.g. `git show 422923a:datasets/delaney-processed.csv`) and
  add a `Feature` constructor with its header name.

The Python tools read columns by name and are unaffected:
`tools/rdkit_oracle.py` regenerates `datasets/delaney-oracle.csv` byte for
byte, and `tools/sklearn_delaney.py` regenerates `datasets/delaney-ridge.csv`
unchanged.

## 2. Files both sides changed

Since `649ba82`, this branch and `main` both changed these files; expect
conflicts:

| File | This branch | `main` |
|---|---|---|
| `LeanSMILES.lean` | imports for `MorganInvariance`, `Aromaticity.Perceive`, `ML.Logistic`, `ML.Ridge`, `Plot.Parity` | imports for `Chem.Charge` |
| `lakefile.toml` | executables `logistic-test`, `aromaticity-test`, `ridge-test` | executables `charge-test`, `parse-errors-test` |
| `LeanSMILES/Tests/Morgan.lean` | must-pass radius-3 counterexample line | skips SMILES rejected as grammar deviations (`ParseError.isGrammarDeviation`) |
| `README.md` | sections on aromatize, classification, ridge, the radius-3 finding | PRs #10–#11 |

Keep both sides in each: they add different imports, executables and sections.

`LeanSMILES/Fingerprint/Morgan.lean` changed only here: its loops were
rewritten as folds and maps (`MorganState`, `growEnv`, `growId`, `dedupStep`,
`roundTriples`, `morganLayer`) so that `Fingerprint/MorganInvariance.lean` can
prove `Molecule.morganBits_relabel`. The output is unchanged (compared with the
original loop code on 13,516 SMILES at radii 0–4). If `main` edits it before
the merge, port the edit onto the new structure rather than reverting it.

## 3. Watch: PR #11's stricter grammar

PR #11 makes the parser follow the OpenSMILES grammar more closely ("ring
labels before branches", H count, class, chirality classes), and `main`'s own
tests now skip SMILES rejected as grammar deviations
(`ParseError.isGrammarDeviation`). Delaney contains such SMILES, e.g.
chlorothalonil, `c1(C#N)c(Cl)c(C#N)c(Cl)c(Cl)c(Cl)1`, with a ring label after
a branch. After merging:

* `aromaticity-test`, `ridge-test` and `logistic-test` call `SMILES.parse`
  directly, so their counts will change, and `ridge-test` stops at the first
  molecule it cannot featurize. Give them the same skip rule as `main`'s tests,
  or decide to accept these SMILES (the acceptance-matrix discussion).
* `CSVparser` is unaffected: it only reads text.

## 4. After merging

```bash
lake build
lake exe validity-test
lake exe oracle-test
lake exe morgan-test
lake exe logistic-test
lake exe aromaticity-test
lake exe ridge-test
```

All must exit 0, along with the tests `main` added (`parse-errors-test`, the
charge test).
