#!/usr/bin/env python3
"""Audit source import boundaries for the modular arithmetic endpoints.

This complements the Lean axiom audit. Imported modules may contain unrelated
native_decide examples; target proof dependencies are checked with #print axioms.
"""
from pathlib import Path
import sys,re
sys.path.insert(0,str(Path(__file__).resolve().parent))
from pde_repo_audit import mask
root=Path(__file__).resolve().parents[1]
pending=['ComputableAnalysis.ModularForms.CMJModularOrbits','ComputableAnalysis.ModularForms.CMExponentialFoundation163','ComputableAnalysis.ModularForms.RamanujanTauIdentities','ComputableAnalysis.ModularForms.CMJEquivalentPoint163','ComputableAnalysis.ModularForms.CMIntegerGrowthDeficit163']
seen=set(); external=set(); failures=[]
while pending:
 name=pending.pop()
 if name in seen:continue
 seen.add(name)
 code=mask(root.joinpath(*name.split('.')).with_suffix('.lean').read_text())
 for line in code.splitlines():
  m=re.match(r'^\s*import\s+(.*)$',line)
  if m:
   for dep in m.group(1).split():
    if dep.startswith('ComputableAnalysis.'):pending.append(dep)
    else:external.add(dep)
 for pattern in [r'\bsorry\b',r'\badmit\b',r'\baxiom\b',r'\bMathlib\b']:
  if re.search(pattern,code):failures.append((name,pattern))
print('External imports:',sorted(external))
print('Project module count:',len(seen))
print('Forbidden source occurrences:',failures)
assert not failures
assert all(x in ['Init','Lean'] or x.startswith(('Init.','Lean.')) for x in external)
print('PASS: only Lean/Init external imports; no Mathlib scalar dependency or unfinished proof declarations. Target axiom audit separately checks proof dependencies.')
