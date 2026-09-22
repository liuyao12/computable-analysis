#!/usr/bin/env python3
"""Publish the pinned PNT+ comparison and audited native square normalization."""
import argparse
import hashlib
import json
import re
from pathlib import Path

PAGE = 'cauchy-arctan.html'
START = '<!-- cauchy-arctan:start -->'
END = '<!-- cauchy-arctan:end -->'
ADDITION = re.compile(re.escape(START) + r'[\s\S]*?' + re.escape(END))
PNT = 'a5154676af9aa3095150ee410cdda80555aa0642'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def install(site, revision, audit, closure):
    assert re.fullmatch('[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'PASS: square-pole normalization, all-tag enclosure, geometry and explicit rate' in log
    assert 'PASS: no Mathlib module in the import closure; no sorryAx' in log
    assert not re.search(r'\berror:|^AUDIT.*sorryAx', log, re.M)
    names = closure.read_text().splitlines()
    for name in ['density_exact', 'raw_equiv_twoPiI', 'taggedSum_enclosed']:
        assert 'ComputableAnalysis.PDE.CauchyContour.' + name in names
    assert 'ComputableAnalysis.piCircleArea' in names
    report_path = site / 'reading/cauchy-arctan-publication.json'
    outputs = [PAGE, 'reading/cauchy-arctan-audit.log', 'reading/cauchy-arctan-closure.txt',
               'reading/cauchy-arctan-publication.json']
    chapter = site / 'ch-complex-paths.html'
    original = ADDITION.sub('', chapter.read_text())
    protected = {str(p.relative_to(site)): digest(p) for p in site.rglob('*')
                 if p.is_file() and p != chapter and str(p.relative_to(site)) not in outputs}
    addition = START + '''<section id="cauchy-arctan"><h2>Arctangent, residues and Cauchy’s formula</h2><p>The square integral of dz/z reduces to 8i times the arctangent area, giving 2πi with our geometric π. This normalization is checked natively. PNT+ supplies the external Mathlib reference for the general rectangle and finite simple-pole residue theorems.</p><p><a href="cauchy-arctan.html">Follow the argument, formal sources and native scope →</a></p><p>The general native residue and Cauchy formulas still require their contour transport and regular-part bridges.</p></section>''' + END
    # Link from the relevant chapter without changing any pre-existing prose.
    assert '</article>' in original
    updated = original.replace('</article>', addition + '</article>', 1)
    assert ADDITION.sub('', updated) == original
    chapter.write_text(updated)
    page = (Path(__file__).with_name('pnt-cauchy') / 'page.html').read_text()
    native = 'https://github.com/liuyao12/computable-analysis/blob/' + revision
    upstream = 'https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/' + PNT + '/PrimeNumberTheoremAnd'
    page = page.replace('__NATIVE__', native).replace('__PNT__', upstream).replace('__REVISION__', revision)
    assert '__NATIVE__' not in page and '__PNT__' not in page
    (site / PAGE).write_text(page)
    (site / outputs[1]).write_text(log)
    (site / outputs[2]).write_text(closure.read_text())
    assert all(digest(site / p) == h for p, h in protected.items())
    report = dict(documentationRevision=revision, nativeProofRevision=revision,
        pntRevision=PNT, nativeScope='square pole normalization',
        upstreamResidueScope='finite simple poles; no boundary poles',
        nativeGeneralResidueTheorem=False, nativeCauchyFormula=False,
        upstreamDerivativeFormulaUsesSeparateMathlibCircleTheorem=True,
        mathlibDependency=False, newPiDefinition=False,
        projectClosureSize=len(names), artifactHashes={p: digest(site / p) for p in outputs[:3]},
        chapterSha256=digest(chapter), chapterBeforeSha256=hashlib.sha256(original.encode()).hexdigest(),
        protectedArtifactHashes=protected,
        checks=dict(pinnedUpstreamSources=True, nativeAuditPassed=True,
            earlierContentPreserved=True, explicitFoundationBoundary=True))
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: PNT+ source comparison and native square-pole normalization; previous artifacts preserved')
    return report

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--site', type=Path, required=True)
    p.add_argument('--revision', required=True)
    p.add_argument('--audit', type=Path, required=True)
    p.add_argument('--closure', type=Path, required=True)
    args = p.parse_args()
    install(args.site, args.revision, args.audit, args.closure)
