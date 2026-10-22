#!/usr/bin/env python3
"""Does the drawing carry the stereochemistry? RDKit reads LeanSMILES's mol blocks
(2D coordinates plus wedge/hash flags) and must recover the same canonical
isomeric SMILES as the original string.

    lake exe depict-test                       # writes out/stereo.sdf
    python3 tools/check_depiction.py out/stereo.sdf [n_failures_to_show]

Needs RDKit (`pip install rdkit`). Failures are classified: a tetrahedral
centre read back differently with every bond in a ring (`centre_allring`,
typically a bridged bicyclic where one wedge cannot settle the configuration),
with a chain bond (`centre_chain`), or a double bond whose E/Z was read
differently (`EZ`).
"""
import collections
import signal
import sys

from rdkit import Chem, RDLogger

RDLogger.DisableLog("rdApp.*")


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout()


signal.signal(signal.SIGALRM, _alarm)

blocks = open(sys.argv[1]).read().split("$$$$\n")
show = int(sys.argv[2]) if len(sys.argv) > 2 else 0
cat = collections.Counter()
fails = []
for b in blocks:
    if not b.strip():
        continue
    smi, mb = b.split("\n", 1)
    if mb.startswith("ERROR"):
        cat["lean_reject"] += 1
        continue
    signal.alarm(5)
    try:
        ref = Chem.MolFromSmiles(smi)
        if ref is None:
            cat["rdkit_reject"] += 1
            continue
        m = Chem.MolFromMolBlock(mb)
        if m is None:
            cat["rdkit_read_error"] += 1
            fails.append((0, smi, "READ ERROR"))
            continue
        a, c = Chem.MolToSmiles(ref), Chem.MolToSmiles(m)
        if a == c:
            cat["ok"] += 1
            continue
        ri = ref.GetRingInfo()
        ca = dict(Chem.FindMolChiralCenters(ref, includeUnassigned=True, useLegacyImplementation=False))
        cb = dict(Chem.FindMolChiralCenters(m, includeUnassigned=True, useLegacyImplementation=False))
        kinds = set()
        for i in ca:
            if ca[i] != cb.get(i):
                at = ref.GetAtomWithIdx(i)
                allring = all(ri.NumBondRings(bd.GetIdx()) > 0 for bd in at.GetBonds())
                kinds.add("centre_allring" if allring else "centre_chain")

        def ez(mol):
            return [(bd.GetIdx(), str(bd.GetStereo())) for bd in mol.GetBonds()
                    if str(bd.GetStereo()) != "STEREONONE"]

        if ez(ref) != ez(m):
            kinds.add("EZ")
        if not kinds:
            kinds.add("other")
        for k in kinds:
            cat[k] += 1
        fails.append((ref.GetNumAtoms(), smi, a, c, sorted(kinds)))
    except Timeout:
        cat["timeout"] += 1
        fails.append((0, smi, "TIMEOUT"))
    finally:
        signal.alarm(0)

n = cat["ok"] + len(fails)
print(dict(cat))
print("exact agreement for %d of %d drawings (%.1f%%); a failure may count in several kinds"
      % (cat["ok"], n, 100 * cat["ok"] / max(1, n)))
fails.sort(key=lambda f: f[0])
for f in fails[:show]:
    print("  ", f)
