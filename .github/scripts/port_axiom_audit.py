#!/usr/bin/env python3
"""Axiom audit for the CoboundaryExpansion port (staging branch only).

`lake build` accepts `sorry` with a warning, and the port imports `Suggested.lean`, whose target
theorems are admitted with `sorry`. A source scan therefore cannot show that the port's theorems
do not depend on an admitted target. This script asks the kernel: it runs `#print axioms` on every
public theorem in `Port/` and `K3/` and fails unless each depends only on
`propext`, `Classical.choice` and `Quot.sound`.
"""
import json, pathlib, re, subprocess, sys, os

ROOT = pathlib.Path(__file__).resolve().parents[2]
BASE = ROOT / "TauCetiRoadmap" / "CoboundaryExpansion"
FILES = sorted(BASE.glob("Port/*.lean")) + sorted(BASE.glob("K3/*.lean"))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
HEADLINE = [
    "TauCetiRoadmap.CoboundaryExpansion.Port.h1_complete_movedNorm_fin_three",
    "TauCetiRoadmap.CoboundaryExpansion.Port.h1Norm_complete_movedNorm_fin_three",
    "CoboundaryK3.h1_eq_all",
]

def strip(s):
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", s, flags=re.S))

THM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+([^\s:({\[]+)", re.M)
NS = re.compile(r"^namespace\s+(\S+)", re.M)
names, imports = [], []
for f in FILES:
    src = strip(f.read_text())
    spaces = NS.findall(src)
    if len(set(spaces)) != 1:
        sys.exit(f"{f}: expected one namespace, found {spaces}")
    names += [f"{spaces[0]}.{n}" for n in THM.findall(src)]
    imports.append("import " + ".".join(f.relative_to(ROOT).with_suffix("").parts))
for h in HEADLINE:
    if h not in names:
        sys.exit(f"headline theorem not found in sources: {h}")

out = pathlib.Path(os.environ.get("RUNNER_TEMP", "/tmp")) / "PortAxiomAudit.lean"
out.write_text("\n".join(imports) + "\n\n" + "\n".join(f"#print axioms {n}" for n in names) + "\n")
p = subprocess.run(["lake", "env", "lean", str(out)], cwd=ROOT, capture_output=True, text=True)
log = p.stdout + p.stderr
(ROOT / "port-axiom-audit.log").write_text(log)
if p.returncode != 0:
    print(log); sys.exit("audit file did not compile")

report, bad = {}, []
for n in names:
    m = re.search(re.escape(f"'{n}' depends on axioms: [") + r"([^\]]*)\]", log, re.S)
    if m:
        used = sorted(a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip())
    elif f"'{n}' does not depend on any axioms" in log:
        used = []
    else:
        sys.exit(f"no axiom report for {n}")
    report[n] = used
    if set(used) - ALLOWED:
        bad.append((n, used))
for h in HEADLINE:
    print(f"{h}: {report[h]}")
if bad:
    for n, u in bad:
        print(f"DISALLOWED: {n} uses {u}")
    sys.exit(f"{len(bad)} theorem(s) depend on disallowed axioms")
print(f"OK: {len(names)} public theorems in Port/ and K3/ use only {sorted(ALLOWED)}")
