"""LeanSMILES on the same material.

  lean_check.py keys   <worker>                       # show the worker's answer for one molecule
  lean_check.py cas    <worker> cas.tsv               # does LeanSMILES read CAS's strings?
  lean_check.py stable <worker> work.json [N] [skip]  # N random atom orderings per panel molecule
                                                      # -> how many distinct canonical strings?
`work.json` is the file toolkits.py rd1 writes (RDKit's random SMILES for each molecule).
"""
import csv, json, subprocess, sys
mode, worker = sys.argv[1], sys.argv[2]

def ask(smiles, timeout=600):
    inp = "".join(f"parse\t{s}\n" for s in smiles)
    p = subprocess.run([worker], input=inp, capture_output=True, text=True, timeout=timeout)
    out = []
    for chunk in p.stdout.split("__JSON_START__")[1:]:
        out.append(json.loads(chunk.split("__JSON_END__")[0]))
    return out

if mode == "keys":
    a = ask(["C=1C=CC=CC1", "C[C@H](N)C(O)=O", "O=N(=O)C"])
    for x in a:
        print({k: (v if isinstance(v, (str, int, bool)) or v is None else type(v).__name__) for k, v in x.items()})
        if isinstance(x.get("aromatized"), dict):
            print("   aromatized:", {k: (v if isinstance(v, (str, int, bool)) else type(v).__name__) for k, v in x["aromatized"].items()})

elif mode == "cas":
    rows = [r for r in csv.DictReader(open(sys.argv[3]), delimiter="\t")]
    items = [(r, c, r[c]) for r in rows for c in ("canonical_smiles", "isomeric_smiles") if r[c] and r[c] != "NONE"]
    ans = ask([s for _, _, s in items])
    assert len(ans) == len(items), (len(ans), len(items))
    bad = 0
    for (r, c, s), a in zip(items, ans):
        if a.get("error") or not a.get("canonicalSmiles"):
            bad += 1
            print(f"   rejects {r['rn']:<12} {r['cas_name'][:24]:<24} {s[:40]:<40} {str(a.get('error'))[:90]}")
    print(f"   LeanSMILES rejects {bad} of {len(items)} CAS strings")
    json.dump([{"rn": r["rn"], "col": c, "cas": s, "lean": a.get("canonicalSmiles"),
                "lean_aromatized": (a.get("aromatized") or {}).get("canonicalSmiles") if isinstance(a.get("aromatized"), dict) else None,
                "error": a.get("error")} for (r, c, s), a in zip(items, ans)], open(sys.argv[4], "w"), indent=0)

elif mode == "stable":
    work = json.load(open(sys.argv[3])); N = int(sys.argv[4]) if len(sys.argv) > 4 else 25
    skip = set(sys.argv[5].split(",")) if len(sys.argv) > 5 else set()
    print(f"{'molecule':<30}{'atoms':>6}{'orderings':>10}{'distinct':>9}{'distinct (aromatized)':>23}")
    for e in work:
        if e["name"] in skip or not e["rand"]: continue
        try: ans = ask(e["rand"][:N], timeout=900)
        except subprocess.TimeoutExpired: print(f"{e['name']:<30} timed out"); continue
        errs = [a.get("error") for a in ans if a.get("error")]
        can = {a.get("canonicalSmiles") for a in ans if not a.get("error")}
        aro = {(a.get("aromatized") or {}).get("canonicalSmiles") for a in ans if not a.get("error") and isinstance(a.get("aromatized"), dict)}
        note = f"   {len(errs)} rejected: {errs[0][:60]}" if errs else ""
        print(f"{e['name']:<30}{'':>6}{len(ans):>10}{len(can):>9}{len(aro) if aro else '-':>23}{note}", flush=True)
