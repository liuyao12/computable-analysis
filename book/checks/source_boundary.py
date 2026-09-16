#!/usr/bin/env python3
"""Inventory migration debt; prevent a silent increase in native noncomputables."""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('boundary',ROOT/'comparison/checks/check_boundary.py')
mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)

def inventory(root=ROOT):
    items=[]
    for f in sorted((root/'ComputableAnalysis').rglob('*.lean')):
        for lineno,line in enumerate(mod.strip_comments(f.read_text()).splitlines(),1):
            if re.search(r'\bnoncomputable\b',line):
                items.append({'file':str(f.relative_to(root)),'line':lineno,'declaration':line.strip()})
    return items

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--freeze',action='store_true');a=ap.parse_args()
    baseline=ROOT/'book/noncomputable-baseline.json';items=inventory()
    if a.freeze:
        baseline.write_text(json.dumps({'scope':'Historical native source inventory, not an approved public API','entries':items},indent=2)+'\n')
    previous=json.loads(baseline.read_text())['entries']
    approved={(i['file'],i['declaration']) for i in previous}
    added=[i for i in items if (i['file'],i['declaration']) not in approved]
    if added:raise SystemExit('New native noncomputable declarations need removal, not automatic approval: '+repr(added))
    preserved=json.loads((ROOT/'book/preserved-chapters.json').read_text())
    for f,sha in preserved['files'].items():
        if hashlib.sha256((ROOT/f).read_bytes()).hexdigest()!=sha:raise SystemExit('Protected chapter changed: '+f)
    result={'nativeSourceNoncomputableCount':len(items),'migrationInventory':items,
       'noNewNativeNoncomputables':True,'chaptersPreserved':True,
       'protectedChapterSources':preserved,'sourceBoundary':mod.check(ROOT),
       'scope':'Source inventory only; Lean declaration flags and execution checked separately.'}
    out=ROOT/'comparison/reports';out.mkdir(exist_ok=True)
    (out/'native-source-boundary.json').write_text(json.dumps(result,indent=2)+'\n')
    print(f'PASS: protected chapters unchanged; native source boundary; {len(items)} historical noncomputable declarations inventoried, no additions')
if __name__=='__main__':main()
