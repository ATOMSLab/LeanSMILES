# LeanSMILES
Formalizing molecular representations in Lean


1. Download the project's dependencies and Mathlib's precompiled cache, then
   check the project:

   ```bash
   lake exe cache get
   lake build
   ```


2. `lake build` also runs the test suite. Each file in `LeanSMILES/Tests/` tests one part
   of the system with `#guard` / `#eval` checks, and a failing check fails the build. To
   run a single test file:

   ```bash
   lake build LeanSMILES.Tests.CanonicalSMILES
   ```

3. Run the example: load the Delaney (ESOL) solubility dataset, clean and validate the
   SMILES, split 80/20, and train and evaluate two linear regression models:

   ```bash
   lake exe linear_regression_example [path/to/delaney-processed.csv]
   ```
