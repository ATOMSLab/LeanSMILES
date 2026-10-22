"""scikit-learn baseline for ridge regression of Delaney log solubility.

Predict the measured log solubility (mol/L) of the 1,128 Delaney molecules from
their Morgan fingerprints (radius 2, 2048 bits) with ridge regression,
Ridge(alpha=1.0) (intercept not penalized), on an 80/20 train/test split made as
in ENCH 470 Lecture 21: train_test_split(test_size=0.20, random_state=0).

Writes datasets/delaney-ridge.csv, the answer file for `lake exe ridge-test`,
with one row per molecule:
  name (commas replaced by ';'), smiles, logS (measured), split (train / test),
  sklearn_pred, rdkit_bits (RDKit's on-bits, space-separated: the exact
  features scikit-learn was trained on)

Usage:  python tools/sklearn_delaney.py
"""
import csv

import numpy as np
from rdkit import Chem
from rdkit.Chem import rdFingerprintGenerator
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_absolute_error, mean_squared_error, r2_score
from sklearn.model_selection import train_test_split

SRC = "datasets/delaney-processed.csv"
OUT = "datasets/delaney-ridge.csv"
TARGET = "measured log solubility in mols per litre"


def main():
    with open(SRC, newline="") as f:
        rows = [(r["Compound ID"], r["smiles"].strip(), float(r[TARGET])) for r in csv.DictReader(f)]

    gen = rdFingerprintGenerator.GetMorganGenerator(radius=2, fpSize=2048)
    X = np.zeros((len(rows), 2048))
    for i, (_, s, _) in enumerate(rows):
        X[i, list(gen.GetFingerprint(Chem.MolFromSmiles(s)).GetOnBits())] = 1
    y = np.array([t for _, _, t in rows])
    idx_train, idx_test = train_test_split(np.arange(len(rows)), test_size=0.20, random_state=0)

    model = Ridge(alpha=1.0).fit(X[idx_train], y[idx_train])
    pred = model.predict(X)
    for name, idx in (("train", idx_train), ("test", idx_test)):
        print(f"{name}: R² {r2_score(y[idx], pred[idx]):.4f}, "
              f"RMSE {np.sqrt(mean_squared_error(y[idx], pred[idx])):.4f}, "
              f"MAE {mean_absolute_error(y[idx], pred[idx]):.4f} log units, n = {len(idx)}")
    print(f"intercept {model.intercept_:.6f}")

    split = {int(i): "train" for i in idx_train} | {int(i): "test" for i in idx_test}
    with open(OUT, "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["name", "smiles", "logS", "split", "sklearn_pred", "rdkit_bits"])
        for i, (name, s, t) in enumerate(rows):
            bits = " ".join(str(j) for j in np.flatnonzero(X[i]))
            w.writerow([name.replace(",", ";"), s, f"{t}", split[i], f"{pred[i]:.12f}", bits])
    print(f"wrote {len(rows)} rows to {OUT}")


if __name__ == "__main__":
    main()
