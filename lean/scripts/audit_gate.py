#!/usr/bin/env python3
"""Audit gate for the s65 scratch package (S67-08; fail-closed revision S68-04, s66).

Usage: audit_gate.py LOG --required MANIFEST.json [--depchecks-from 'GLOB']

Exit 0 only if ALL hold (otherwise one line per failure and exit 1):
  * MANIFEST is given, readable, and its axiom_roots and depcheck_roots are non-empty;
  * the log contains "Build completed successfully" and no error line; no "declaration uses `sorry`";
  * every "'X' depends on axioms: [..]" report in the log lists only propext, Classical.choice, Quot.sound;
  * every required axiom root appears in EXACTLY ONE axiom report (missing or duplicated -> fail);
  * the log contains no "DEPCHECK FAIL";
  * every required depcheck root appears in EXACTLY ONE "DEPCHECK OK" line (missing or duplicated -> fail);
  * with --depchecks-from: for each required depcheck root, the #dep_check source line exists and its forbid
    list contains the manifest registry (plus the root's extra patterns), so the check cannot be weakened silently.
Counts are printed for information only; they are not the criterion.
Scope: DEPCHECK is a transitive-closure NAME-SUBSTRING check against the registry; it is not a semantic detector.
"""
import glob, json, re, sys
from collections import Counter
STD3 = {"propext", "Classical.choice", "Quot.sound"}
args = sys.argv[1:]
fails = []
def opt(k):
    return args[args.index(k) + 1] if k in args and args.index(k) + 1 < len(args) else None
if not args or args[0].startswith("--"):
    print("GATE FAIL: no log given"); sys.exit(1)
log, man_path, src_glob = args[0], opt("--required"), opt("--depchecks-from")
man = {}
if man_path is None:
    fails.append("no --required manifest (release audit must name its roots)")
else:
    try:
        man = json.load(open(man_path, encoding="utf-8"))
    except Exception as e:
        fails.append(f"manifest unreadable: {e}")
ax_req = man.get("axiom_roots") or []
dc_req = man.get("depcheck_roots") or []
reg = man.get("forbidden_substrings_registry") or []
extra = man.get("forbidden_substrings_extra") or {}
if man_path is not None and not fails:
    if not ax_req: fails.append("manifest axiom_roots empty")
    if not dc_req: fails.append("manifest depcheck_roots empty")
    if dc_req and not reg: fails.append("manifest forbidden_substrings_registry empty")
s = open(log, encoding="utf-8", errors="replace").read()
if "Build completed successfully" not in s:
    fails.append("no 'Build completed successfully'")
for line in s.splitlines():
    if re.search(r"(^|\s)error(\(|:)|: error", line):
        fails.append("error line: " + line[:160])
if "declaration uses `sorry`" in s or "declaration uses 'sorry'" in s:
    fails.append("declaration uses sorry")
reps = re.findall(r"'([^'\n]+(?:'[^'\n]*?)*?)' depends on axioms: \[([^\]]*)\]", s)
rep_count = Counter(n for n, _ in reps)
heads = Counter(re.findall(r"'([^'\n]+(?:'[^'\n]*?)*?)' depends on axioms", s))
if sum(heads.values()) != len(reps):
    fails.append(f"unparsed axiom report(s): {sum(heads.values())} headers vs {len(reps)} parsed")
for name, ax in reps:
    axs = {a.strip() for a in ax.split(",") if a.strip()}
    if not axs <= STD3:
        fails.append(f"non-standard axioms in {name}: {sorted(axs - STD3)}")
for r in ax_req:
    c = max(rep_count.get(r, 0), heads.get(r, 0))
    if c == 0: fails.append(f"required axiom report missing: {r}")
    elif c > 1: fails.append(f"required axiom report duplicated ({c}x): {r}")
for m in re.findall(r"DEPCHECK FAIL [^\n]*", s):
    fails.append(m[:200])
dc_ok = Counter(re.findall(r"DEPCHECK OK (\S+?):", s))
for r in dc_req:
    c = dc_ok.get(r, 0)
    if c == 0: fails.append(f"required DEPCHECK OK missing: {r}")
    elif c > 1: fails.append(f"required DEPCHECK OK duplicated ({c}x): {r}")
if src_glob is not None:
    lines = [l for f in sorted(glob.glob(src_glob)) for l in open(f, encoding="utf-8") if l.startswith("#dep_check ")]
    for r in dc_req:
        short = r.split(".")[-1]
        hits = [l for l in lines if l.split()[1] in (r, short) or r.endswith("." + l.split()[1])]
        if len(hits) != 1:
            fails.append(f"#dep_check source line for {r}: found {len(hits)} (need 1)"); continue
        pats = set(re.findall(r'"([^"]*)"', hits[0]))
        need = set(reg) | set(extra.get(r, []))
        if not need <= pats:
            fails.append(f"#dep_check {r} forbid list lacks {sorted(need - pats)}")
for f in fails:
    print("GATE FAIL:", f)
print(f"GATE SUMMARY: axiom_reports={len(reps)} required_axiom_roots={len(ax_req)} "
      f"depcheck_ok={sum(dc_ok.values())} required_depcheck_roots={len(dc_req)} failures={len(fails)}")
sys.exit(1 if fails else 0)
