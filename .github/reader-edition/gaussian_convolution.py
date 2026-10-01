#!/usr/bin/env python3
"""Add the checked finite convolution page without altering existing pages."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from proof_bundles import attach_links


def digest(data):
    return hashlib.sha256(data).hexdigest()


def install(site, revision, audit):
    assert re.fullmatch(r'[0-9a-f]{40}', revision)
    log = audit.read_text()
    required = [
        'WeightedPoint.action_convolution',
        'WeightedPoint.action_convolution_comm',
        'WeightedPoint.action_convolution_assoc',
        'FiniteProbabilityKernel.variance_convolution',
        'FiniteProbabilityKernel.cubic_replacement_bound',
        'FiniteProbabilityKernel.convolutionPower_replacement_bound',
        'FiniteProbabilityKernel.scaled_convolutionPower_cubic_bound',
    ]
    assert 'error:' not in log and 'sorryAx' not in log
    for name in required:
        match = re.search(r"'ComputableAnalysis\." + re.escape(name) +
                          r"' depends on axioms: \[([^]]*)\]", log)
        assert match, name
        assert set(re.findall(r'[\w.]+', match[1])) <= {
            'propext', 'Classical.choice', 'Quot.sound'}, name
    pending = ['ComputableAnalysis.FiniteConvolution']
    closure = {}
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        source = Path(module.replace('.', '/') + '.lean')
        data = source.read_bytes()
        closure[module] = digest(data)
        imports = re.findall(r'^import\s+(\S+)', data.decode(), re.M)
        for dep in imports:
            if dep.startswith('ComputableAnalysis.'):
                pending.append(dep)
            else:
                assert dep == 'Init.Grind.Ordered.Rat', dep
    assert set(closure) == {
        'ComputableAnalysis.FiniteConvolution',
        'ComputableAnalysis.FiniteApproximateIdentity',
        'ComputableAnalysis.Basic'}, closure
    protected = {str(p.relative_to(site)): digest(p.read_bytes())
                 for p in site.rglob('*') if p.is_file()}
    template = Path(__file__).with_name('gaussian-convolution') / 'page.html'
    page = template.read_text().replace('__SOURCE__',
        'https://github.com/liuyao12/computable-analysis/blob/' + revision
    ).replace('__REVISION__', revision[:12])
    assert 'MathJax' in page and '<sup>' not in page and '<sub>' not in page
    assert '__SOURCE__' not in page and '__REVISION__' not in page
    assert 'Targets' in page and 'continuous central limit theorem remain targets' in page
    files = {'gaussian-convolution.html': page.encode(),
             'reading/gaussian-convolution-audit.log': audit.read_bytes()}
    for name, data in files.items():
        assert name not in protected, name
        target = site / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    attach_links(site,pages={'gaussian-convolution.html'})
    files['gaussian-convolution.html']=(site/'gaussian-convolution.html').read_bytes()
    assert all(digest((site / p).read_bytes()) == h for p, h in protected.items())
    report = dict(proofSourceCommit=revision, checkedTheorems=required,
                  sourceHashes=closure, mathlibDependency=False,
                  finiteRationalScope=True, continuousCLTProved=False,
                  gaussianNormalizationProved=False, allPreviousContentPreserved=True,
                  artifactHashes={n: digest(d) for n, d in files.items()})
    (site / 'reading/gaussian-convolution.json').write_text(
        json.dumps(report, indent=2) + '\n')
    print('PASS: convolution axioms, native import closure and prior page preservation')


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--site', type=Path, required=True)
    p.add_argument('--revision', required=True)
    p.add_argument('--audit', type=Path, required=True)
    a = p.parse_args()
    install(a.site, a.revision, a.audit)
