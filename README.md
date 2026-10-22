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

## SMILES → typed molecular graph → canonical SMILES

`LeanSMILES.SMILES.Canon` is the one import for the SMILES toolkit:

```lean
import LeanSMILES.SMILES.Canon
import LeanSMILES.Chem.Graph            -- the Mathlib views
open LeanSMILES LeanSMILES.SMILES

#eval parse "c1cc[nH]c1"                                  -- Except.ok (Molecule 5 ["c","c","c","[nH]","c"] [0:1, 1:2, 2:3, 3:4, 0:4])
#eval (Mol.ofSmiles! "C(O)C").canonicalSmiles             -- "CCO"
#eval (Mol.ofSmiles! "C=CO").mol.adjMatrix                -- !![0, 2, 0; 2, 0, 1; 0, 1, 0]  (over ℚ)
#eval (Mol.ofSmiles! "C=CO").mol.graph.adjMatrix ℚ        -- Mathlib's 0/1 matrix
```

A `Molecule n` is a `Vector Atom n` and a list of `Bond n` between distinct
atoms with no duplicate bonds — the invariants are the type, so
`Molecule.graph : SimpleGraph (Fin n)` and `Molecule.adjMatrix : Matrix (Fin n) (Fin n) ℚ`
come with Mathlib's theorems (`sum_degrees`, `card_edgeFinset`, `relabelIso`,
`canonicalizeIso`).  The matrices also exist as subtypes that say they come
from a molecule — `BondMatrix n` (bond orders, O(1) lookups) and `FlatMatrix n`
(0/1, Mathlib's `IsAdjMatrix`) — with `normalEquiv : {m // m.IsNormal} ≃ Vector Atom n × BondMatrix n`
proving that nothing but bond orientation is lost.  The parser checks syntax, not valence; the only chemistry
applied is the OpenSMILES implicit-hydrogen rule.  Canonical SMILES is
colour refinement plus exhaustive tie-breaking (lexicographically smallest
string), so it is canonical by construction rather than by matching RDKit.

Open `LeanSMILES/Examples/smiles.lean` for more; design and comparison with
the `canonical-smiles` branch in `docs/design-molecular-representation.md`.

### What the parser accepts

The grammar is OpenSMILES's ([opensmiles.org](http://opensmiles.org/opensmiles.html),
§2.2).  RDKit and the specification disagree on a handful of strings; where
they do, LeanSMILES follows the specification, with the decided exceptions
below.  Every row is pinned by `lake exe parse-errors-test`.

| String | RDKit | OpenSMILES | LeanSMILES |
|---|---|---|---|
| `C(C)1CC1` — ring-closure label after a branch | accepts | rejects: `atom ringbond* branch*` | rejects (`ringAfterBranch`).  Chlorothalonil in the Delaney set is written `…c(Cl)1` and is skipped by `oracle-test`. |
| `C(.O)`, `C.(O)`, `C(C.)`, `C.1CC1` — dots next to branches and labels | rejects | allows only the first | rejects all four |
| `" C"` — leading whitespace | methane | empty molecule, then a title | methane |
| `[Fe+++]`, `[C+123]` — charge forms | rejects, accepts | rejects both: `++`/`--` only, two digits | accepts both; whether the element has the electrons is a post-parse chemistry check (follow-up PR), not a lexical one |
| `[CH10]`, `[C:]` — two-digit H count, empty class | accepts, rejects | rejects both | rejects both |
| `[C@TH1]` … `[Fe@OH30]` — named chirality classes | accepts | accepts | accepts, recorded as written (`@` is not rewritten to `@TH1`) |
| `C=1CC-1` — different bond symbols on one ring closure | accepts, opening symbol wins | rejects | rejects (`conflictingRingBond`) |
| `C%(123)CC%(123)` — RDKit's long ring labels | accepts | rejects | rejects |
| `[02H]` — isotope with a leading zero | rejects | accepts | accepts |

Tests against RDKit's answers (oracle files from the `canonical-smiles` branch):

```bash
lake exe parse-errors-test  # every ParseError with its exact message, plus the accept/reject decisions above
lake exe validity-test      # 10 000 broken SMILES: accepts everything RDKit accepts, bar the OpenSMILES rules above (0 parser bugs)
lake exe oracle-test        # 1 128 Delaney molecules: graph = RDKit's, canonical SMILES round-trips and is relabelling-invariant (1 skipped, see above)
lake exe morgan-test        # Morgan fingerprints: ring membership = RDKit's, bits = RDKit's wherever the graph is, relabelling-invariant
```

### Morgan fingerprints

`LeanSMILES.Fingerprint.Morgan` ports RDKit's `GetMorganGenerator(radius=2, fpSize=2048)`
(from the `canonical-smiles` branch's port) onto `Molecule n`: `morganIds` (unfolded
identifiers with counts), `morganBits` (sorted on-bits), `morganVector : Vector Bool 2048`,
`inRingVector`, and an exact `tanimoto : … → ℚ`.  It hashes the graph *as written*, so the
bits equal RDKit's exactly where the as-written bond types and hydrogen counts equal RDKit's
sanitized ones (no aromaticity perception here, by design), and they are always invariant
under relabelling of the atoms.

```lean
#eval (Mol.ofSmiles! "CCO").morganBits        -- [80, 222, 294, 807, 1057, 1410, ...]
#eval tanimoto (Mol.ofSmiles! "CCO").morganBits (Mol.ofSmiles! "CCCO").morganBits
```

## References

LeanSMILES builds on prior work in Lean, cheminformatics, and chemistry
education. [`REFERENCES.md`](REFERENCES.md) credits each source and says what
it is credited for; [`references.bib`](references.bib) has the BibTeX.
