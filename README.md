# LeanSMILES
Formalizing molecular representations in Lean

## Installation

No Lean experience needed. Setup is a one-time job, and most of it is download
time. Two tools do the work: **elan** installs the right Lean version (much as
conda manages Python environments), and **lake** fetches dependencies and builds
the project.

1. **Install the editor and Lean.** Install [Git](https://git-scm.com/downloads)
   and [VS Code](https://code.visualstudio.com/), then add VS Code's **Lean 4**
   extension (search "Lean 4" in the Extensions panel). The first time you open
   a Lean file, the extension offers to install Lean (elan) for you. Accept.

   Prefer the terminal? On macOS or Linux, install elan directly:

   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Download this project:**

   ```bash
   git clone https://github.com/ATOMSLab/LeanSMILES.git
   cd LeanSMILES
   ```

3. **Download the project's dependencies and Mathlib's precompiled cache, then
   check the project:**

   ```bash
   lake exe cache get
   lake build
   ```

   Mathlib is Lean's mathematics library, and it is large. `lake exe cache get`
   downloads it already compiled (several GB of disk). Without it, `lake build`
   compiles Mathlib from scratch, which takes hours. The Lean version this
   project needs (pinned in `lean-toolchain`) installs itself the first time you
   run `lake`.

4. **Try it.** In VS Code, use **File → Open Folder…** and open the whole
   `LeanSMILES` folder, not a single file, so the dataset paths resolve. Then
   open `LeanSMILES/Examples/parsercsv.lean`. The **Lean Infoview** panel on the
   right shows each `#eval` result: the solubility dataset in `datasets/`, read
   in as SMILES strings with their numeric features.

## SMILES → canonical SMILES

`LeanSMILES.Canonical` turns any SMILES into its canonical SMILES, the same
string as RDKit's `Chem.MolToSmiles(Chem.MolFromSmiles(s), isomericSmiles=False)`:

```lean
import LeanSMILES.Canonical
#eval Chem.canonicalSmiles "OCC"            -- Except.ok "CCO"
#eval Chem.canonicalSmiles "C1=CC=CC=C1"    -- Except.ok "c1ccccc1"
```

Open `LeanSMILES/Examples/canonical.lean` for more. The code is in four files
under `LeanSMILES/Canonical/`: `Molecule` (atoms, bonds), `Parse` (SMILES text →
graph), `Sanitize` (RDKit's hydrogens, rings, kekulization, aromaticity) and
`Write` (canonical atom ranking and output).

Tests against RDKit (answers in `datasets/*-oracle.csv`, made by
`tools/rdkit_oracle.py`):

```bash
lake exe canonical-test   # canonical SMILES
lake exe morgan-test      # Morgan fingerprints (bits and unfolded identifiers)
lake exe phase1-test      # every atom and bond of the molecule graph
lake exe validity-test    # invalid SMILES rejected exactly when RDKit rejects them
```

## Morgan fingerprints

`LeanSMILES.Fingerprint.Morgan` computes Morgan (ECFP-like) fingerprints with the
same bits as RDKit's `GetMorganGenerator(radius=2, fpSize=2048)`:

```lean
import LeanSMILES.Fingerprint.Morgan
#eval Chem.morganBits "CCO"                 -- Except.ok [80, 222, 294, 807, 1057, 1410]
```

`LeanSMILES/Examples/morgan.lean` also shows Tanimoto similarity, isotopes and
the bit vector for ML. Test: `lake exe morgan-test` (bits and unfolded
identifiers); `lake exe morgan-test datasets/isotope-cases-oracle.csv` for
isotope-labelled molecules.

Hydrogens written as separate atoms are handled like RDKit: ordinary `[H]`
atoms are folded into their neighbour's H count (`[H]C([H])([H])[H]` → `C`),
while isotopic, charged and stereo-defining ones stay atoms.

Design notes, RDKit references and results: `docs/scope-canonical-smiles-morgan.md`.
