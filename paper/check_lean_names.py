r"""List the Lean names cited in main.tex (\leanname{...}) that the library does not declare.

Run from the repository root:  python3 paper/check_lean_names.py
"""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]
tex = (root / "paper" / "main.tex").read_text()
names = set()
for group in re.findall(r"\\leanname\{([^}]*)\}", tex):
    names.add(group.replace(r"\_", "_").strip())

src = "\n".join(p.read_text() for p in (root / "CriticalRadiusFive").glob("*.lean"))
declared = set(re.findall(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+([^\s(:{\[]+)", src, re.M))

missing = []
for n in sorted(names):
    short = n.split(".")[-1]
    if n not in declared and short not in declared:
        missing.append(n)
print(f"{len(names)} names cited, {len(missing)} not found in CriticalRadiusFive/*.lean")
for n in missing:
    print("  missing:", n)
sys.exit(1 if missing else 0)
