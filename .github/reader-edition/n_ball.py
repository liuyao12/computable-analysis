#!/usr/bin/env python3
"""Publish the represented ball formula and its independently tested calculator."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def install(site, revision, audit, tests):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    required = ['nBallCoeff_mul_gammaHalfCoeff', 'nBallVolumeModel_gamma',
                'gaussian_square_split', 'gaussian_diagonal_bound',
                'NBallRaw.volume_valid', 'NBallRaw.volume_equiv',
                'nBallVolumeModelInterval_contains']
    assert 'error:' not in log and 'sorryAx' not in log
    axioms = {}
    base = {'propext', 'Classical.choice', 'Quot.sound'}
    # Existing Basic.lean proves the fixed rational fact 0 < 2 by native_decide.
    native = 'RealRaw.mul_valid_of_nonneg_bounded._native.native_decide.ax_1_7'
    for name in required:
        match = re.search(r"'ComputableAnalysis\." + re.escape(name) +
                          r"' depends on axioms: \[([^]]*)\]", log)
        assert match, name
        axioms[name] = re.findall(r'[\w.]+', match[1])
        allowed = base | ({native} if name == 'NBallRaw.volume_valid' else set())
        assert set(axioms[name]) <= allowed, (name, axioms[name])
    runtime = json.loads(tests.read_text())
    assert runtime['passed'] and runtime['leanFixtures'] == 213
    assert runtime['edgeCasesAndOutwardRounding']
    pending = ['ComputableAnalysis.NBallGaussian', 'ComputableAnalysis.Pi']
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
                assert dep.startswith('Init.'), dep
    protected = {str(p.relative_to(site)): digest(p.read_bytes())
                 for p in site.rglob('*') if p.is_file()}
    source = Path(__file__).with_name('n-ball')
    page = (source / 'page.html').read_text().replace('__SOURCE__',
        'https://github.com/liuyao12/computable-analysis/blob/' + revision
    ).replace('__REVISION__', revision[:12])
    assert '__SOURCE__' not in page and '__REVISION__' not in page
    assert 'remain proof targets' in page and 'MathJax' in page
    assert '<sup>' not in page and '<sub>' not in page
    files = {'n-ball-volume.html': page.encode(),
             'reading/n-ball-audit.log': audit.read_bytes(),
             'reading/n-ball-tests.json': tests.read_bytes(),
             'reading/n-ball/calculator.js': (source / 'calculator.js').read_bytes(),
             'reading/n-ball/ui.js': (source / 'ui.js').read_bytes()}
    for name, data in files.items():
        assert name not in protected, name
        target = site / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    assert all(digest((site / p).read_bytes()) == h for p, h in protected.items())
    report = dict(proofSourceCommit=revision, checkedTheorems=required, axioms=axioms,
                  sourceHashes=closure, mathlibDependency=False,
                  representedFormulaValidity=True, representationInvariance=True,
                  nonnegativeInputBoxesRequired=True, geometricVolumeBridgeProved=False,
                  gammaIntegralBridgeProved=False, gaussianNormalizationProved=False,
                  verifiedJavaScript=False, runtimeTests=runtime,
                  allPreviousContentPreserved=True,
                  artifactHashes={n: digest(d) for n, d in files.items()})
    (site / 'reading/n-ball.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: ball formula axioms, native import closure, runtime fixtures and preserved pages')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--site', type=Path, required=True)
    p.add_argument('--revision', required=True)
    p.add_argument('--audit', type=Path, required=True)
    p.add_argument('--tests', type=Path, required=True)
    a = p.parse_args()
    install(a.site, a.revision, a.audit, a.tests)
