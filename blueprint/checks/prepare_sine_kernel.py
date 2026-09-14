"""Prepare the local sine proof closure for a transitive kernel-only audit."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2]
entry = root / "ComputableAnalysis/SineDerivative.lean"
text = entry.read_text()
text = text.replace("(f (x+h)).compute n |>.lo <= a", "((f (x+h)).compute n).lo <= a")
text = text.replace("∀ n c : _,", "∀ (n : Nat) (c : Rat),")
text = text.replace("Rat.mul_one, Rat.natCast_one, step", "Rat.mul_one, step")
text = text.replace(
    "  simpa only [Rat.mul_one, step] using Rat.le_trans hr hm",
    "  have hcast : ((1 : Nat) : Rat) = (1 : Rat) := by decide +kernel\n"
    "  simpa only [Rat.mul_one, step, hcast] using Rat.le_trans hr hm")
entry.write_text(text)

seen = set()
def visit(path):
    if path in seen:
        return
    seen.add(path)
    source = path.read_text()
    for line in source.splitlines():
        if line.startswith("import "):
            for module in line[7:].split():
                dep = root.joinpath(*module.split(".")).with_suffix(".lean")
                if dep.is_file():
                    visit(dep)
    count = len(re.findall(r"\bnative_decide\b", source))
    if count:
        path.write_text(re.sub(r"\bnative_decide\b", "decide +kernel", source))
        print(f"Kernel reduction: {path.relative_to(root)} ({count} occurrences)")

visit(entry)
print(f"Local dependency closure: {len(seen)} modules")

for filename in ['IntegralIdentities.lean', 'ArctanGeometry.lean']:
    lines=(root/'ComputableAnalysis'/filename).read_text().splitlines()
    for i,line in enumerate(lines):
        if re.match(r'^(?:def|structure|theorem) .*?(?:ArctanInverseBisection|arctanInverseBisection|tangentOnUnit|arctanIntegralRectangleCompute.*(?:difference|increment|secant|deriv|strict))',line):
            count=70 if line.startswith('structure ') else 18
            print(f'\nINTERFACE {filename}:{i+1}\n'+'\n'.join(lines[i:i+count]))
