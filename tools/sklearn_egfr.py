"""scikit-learn baseline for the EGFR classification task (ENCH 470 Lecture 21).

Classify ChEMBL molecules as EGFR active (1) or inactive (0) from their Morgan
fingerprints (radius 2, 2048 bits) with L2-regularized logistic regression,
using an 80/20 train/test split, then predict the 5 FDA-approved EGFR drugs.

Writes datasets/egfr-classification.csv, the answer file for `lake exe
logistic-test`, with one row per molecule:
  name, smiles, label (1 active / 0 inactive / empty for FDA drugs),
  split (train / test / fda), sklearn_proba (P(active) from the fully converged
  scikit-learn model), sklearn_pred (0/1), rdkit_bits (RDKit's on-bits,
  space-separated: the exact features scikit-learn was trained on)

The split is scikit-learn's train_test_split(test_size=0.20, random_state=0),
as in the lecture. The model is LogisticRegression(C=1.0) (L2 penalty, intercept
not penalized) solved to tight tolerance, so Lean can be compared with the
exact optimum rather than with wherever lbfgs stops after its default 100 steps.

Usage:  python tools/sklearn_egfr.py
"""
import csv
import warnings

import numpy as np
from rdkit import Chem
from rdkit.Chem import rdFingerprintGenerator
from sklearn.exceptions import ConvergenceWarning
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import accuracy_score, confusion_matrix
from sklearn.model_selection import train_test_split

DATA = "datasets/"
OUT = "datasets/egfr-classification.csv"


def read_chembl(path):
    with open(path, newline="") as f:
        return [(r["molecule_chembl_id"], r["canonical_smiles"]) for r in csv.DictReader(f)]


def main():
    actives = read_chembl(DATA + "Chembl_EGFR_actives_ML.csv")
    inactives = read_chembl(DATA + "Chembl_EGFR_inactives_ML.csv")
    with open(DATA + "EGFR-FDA.csv", newline="") as f:
        fda = [(row[1], row[0]) for row in csv.reader(f) if row]

    gen = rdFingerprintGenerator.GetMorganGenerator(radius=2, fpSize=2048)

    def features(smiles):
        x = np.zeros(2048)
        x[list(gen.GetFingerprint(Chem.MolFromSmiles(smiles)).GetOnBits())] = 1
        return x

    mols = actives + inactives
    X = np.array([features(s) for _, s in mols])
    y = np.array([1] * len(actives) + [0] * len(inactives))
    idx_train, idx_test = train_test_split(np.arange(len(mols)), test_size=0.20, random_state=0)

    # Lecture 21's model (default settings: lbfgs, max_iter=100)
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always", ConvergenceWarning)
        default = LogisticRegression(random_state=0).fit(X[idx_train], y[idx_train])
    # the same objective solved to tight tolerance
    exact = LogisticRegression(random_state=0, max_iter=100000, tol=1e-12).fit(X[idx_train], y[idx_train])

    for name, clf in (("default (as in the lecture)", default), ("converged", exact)):
        pred = clf.predict(X[idx_test])
        print(f"{name}: train acc {clf.score(X[idx_train], y[idx_train]):.4f}, "
              f"test acc {accuracy_score(y[idx_test], pred):.4f}, "
              f"confusion {confusion_matrix(y[idx_test], pred).tolist()}")
    print("default lbfgs hit max_iter:", any(issubclass(w.category, ConvergenceWarning) for w in caught))
    print("default and converged agree on every test prediction:",
          bool((default.predict(X[idx_test]) == exact.predict(X[idx_test])).all()))
    print(f"converged intercept {exact.intercept_[0]:.6f}, n_iter {exact.n_iter_[0]}")

    X_fda = np.array([features(s) for _, s in fda])
    split = {int(i): "train" for i in idx_train} | {int(i): "test" for i in idx_test}
    rows = [(name, s, y[i], split[i], X[i]) for i, (name, s) in enumerate(mols)]
    rows += [(name, s, "", "fda", X_fda[k]) for k, (name, s) in enumerate(fda)]
    with open(OUT, "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["name", "smiles", "label", "split", "sklearn_proba", "sklearn_pred", "rdkit_bits"])
        for name, s, label, sp, x in rows:
            p = exact.predict_proba(x.reshape(1, -1))[0, 1]
            bits = " ".join(str(j) for j in np.flatnonzero(x))
            w.writerow([name, s, label, sp, f"{p:.12f}", int(p >= 0.5), bits])
    for k, (name, _) in enumerate(fda):
        print(f"  {name:12s} P(active) = {exact.predict_proba(X_fda[k:k + 1])[0, 1]:.4f}")
    print(f"wrote {len(rows)} rows to {OUT}")


if __name__ == "__main__":
    main()
