#!/usr/bin/env python3
"""Publish audited integer power tests while preserving the existing reader."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    assert 'error:' not in log and 'sorryAx' not in log
    required = re.findall(r'^#print axioms (\S+)', Path('scripts/check_power_improper.lean').read_text(), re.M)
    assert len(required) == 28
    axioms = {}
    for name in required:
        full = 'ComputableAnalysis.' + (name if name.startswith('Integral.') else 'IntegerPowerIntegral.' + name)
        m = re.search("'" + re.escape(full) + r"' depends on axioms: \[([^]]*)\]", log)
        assert m, full
        axioms[full] = re.findall(r'[\w.]+', m[1])
        assert set(axioms[full]) <= {'propext', 'Classical.choice', 'Quot.sound'}, full
    assert 'POWER_TESTS|34|passed' in log
    pending = ['ComputableAnalysis.HarmonicImproperBounds']
    closure = {}
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        data = Path(module.replace('.', '/') + '.lean').read_bytes()
        closure[module] = digest(data)
        for dep in re.findall(r'^import\s+(\S+)', data.decode(), re.M):
            if dep.startswith('ComputableAnalysis.'):
                pending.append(dep)
            else:
                assert dep == 'Init.Grind.Ordered.Rat', dep
    assert len(closure) == 9, closure
    protected = {str(p.relative_to(site)): digest(p.read_bytes()) for p in site.rglob('*') if p.is_file()}
    template = Path(__file__).with_name('power-improper') / 'page.html'
    page = template.read_text().replace('__SOURCE__',
        'https://github.com/liuyao12/computable-analysis/blob/' + revision).replace('__REVISION__', revision[:12])
    assert 'MathJax' in page and '<sup>' not in page and '<sub>' not in page
    assert 'remains unfinished' in page and 'Not yet proved' in page
    assert '__SOURCE__' not in page and '__REVISION__' not in page
    files = {'power-improper.html': page.encode(), 'reading/power-improper-audit.log': audit.read_bytes()}
    for name, data in files.items():
        assert name not in protected, name
        target = site / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    assert all(digest((site / p).read_bytes()) == h for p, h in protected.items())
    report = dict(proofSourceCommit=revision, auditedTheorems=axioms, sourceHashes=closure,
        exponentScope='integer improper integrals; natural exponent series',
        arbitraryRealExponentTestProved=False, nonintegerZeroToOneCaseProved=False,
        compactLogarithmConstructionAdded=False, mathlibDependency=False,
        compactIntegralWitnesses=True, explicitStageBounds=True, finiteIntegralComparison=True,
        naturalSeriesConvergenceClassification=True, regressionGroups=34,
        allPreviousContentPreserved=True, artifactHashes={n:digest(d) for n,d in files.items()})
    (site / 'reading/power-improper.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: 28 theorem audits, 34 regression groups, native import closure, preserved reader')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    parser.add_argument('--audit', type=Path, required=True)
    args = parser.parse_args()
    install(args.site, args.revision, args.audit)
