"""Overlay the requested opening story onto an existing Pages artifact."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]
ASSETS = ROOT / 'book/foundation-story'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def apply(site, require_full=True):
    before = {str(p.relative_to(site)): sha(p) for p in site.rglob('*') if p.is_file()}
    sections = json.loads((ASSETS / 'sections.json').read_text())
    audit = (ASSETS / 'audit.txt').read_text()
    assert 'PASS:' in audit and 'error:' not in audit and 'sorryAx' not in audit
    proof = json.loads((ASSETS / 'proof.json').read_text())
    assert sha(ASSETS / 'proof.tar.gz') == proof['sha256']
    dependencies = json.loads((ASSETS / 'declarations.json').read_text())['declarations']
    for row in json.loads((ASSETS / 'nodes.json').read_text()):
        assert all('ComputableAnalysis.' + n in dependencies for n in row[4]), row[0]
    changed = set()
    # Retain every existing theorem, anchor, proof and worked illustration.
    for name, section in sections.items():
        path = site / name
        text = path.read_text()
        pattern = r'<section class="pedagogical-opening"[^>]*>.*?</section>'
        assert len(re.findall(pattern, text, re.S)) == 1, name
        opening = '<section class="pedagogical-opening" data-pedagogy="opening" id="why-this-page"><p>Start with number computations, then construct rational-input functions and the particular tools needed to compare them. Irrational evaluations are derived add-ons.</p><p><a href="foundation-story/index.html">Explore the construction map and checked proof dependencies.</a></p></section>'
        text = re.sub(pattern, lambda _: opening + '<section class="foundation-story-opening">' + section + '</section>', text, count=1, flags=re.S)
        if name == 'ch-infinite-series.html':
            text = text.replace('CHAPTER 06', 'CHAPTER 05')
            text = re.sub(r'(<h2[^>]*>)6\.', r'\g<1>5.', text)
        if name == 'ch-effective-calculus.html':
            text = text.replace('CHAPTER 05', 'CHAPTER 06')
            text = re.sub(r'(<h2[^>]*>)5\.', r'\g<1>6.', text)
        pair = r'(<a[^>]*href="ch-effective-calculus.html"[^>]*><span>05</span>.*?</a>)(<a[^>]*href="ch-infinite-series.html"[^>]*><span>06</span>.*?</a>)'
        text = re.sub(pair, lambda m: m[2].replace('<span>06</span>', '<span>05</span>') + m[1].replace('<span>05</span>', '<span>06</span>'), text)
        path.write_text(text)
        changed.add(name)
    index = site / 'index.html'
    text = index.read_text()
    pair = r'(<a[^>]*href="ch-effective-calculus.html"[^>]*><span>05</span>.*?</a>)(<a[^>]*href="ch-infinite-series.html"[^>]*><span>06</span>.*?</a>)'
    text = re.sub(pair, lambda m: m[2].replace('<span>06</span>', '<span>05</span>') + m[1].replace('<span>05</span>', '<span>06</span>'), text)
    assert '<h2 id="start">' in text
    intro = '<section id="foundation-story"><h2>From numbers to functions</h2><p>Compute \\(\\sqrt2\\) and \\(\\pi\\), then study rational-input functions, derived irrational evaluations, integrals, power series, and concrete secant proofs of FTC. Explore the square-root interval update and specific arctangent inverse.</p><p>The emphasis is on constructions and exact mathematical identities. Quantitative bounds justify them and remain available for numerical corollaries. When a numerical result is requested, specialize a checked computation, choose a sufficient stage from its error bound, and prove the resulting rational inequalities.</p><p><a href="ch-foundations.html#numbers-to-functions">Read the opening chapter</a> · <a href="foundation-story/index.html">Probe the construction map and checked declarations</a></p></section>'
    index.write_text(text.replace('<h2 id="start">', intro + '<h2 id="start">', 1))
    changed.add('index.html')
    dest = site / 'foundation-story'
    shutil.copytree(ASSETS, dest, dirs_exist_ok=True)
    for name, digest in before.items():
        if name not in changed and not name.startswith('foundation-story/'):
            assert sha(site / name) == digest, name
    report = {'changedExistingPages': sorted(changed), 'preservedFiles': sum(n not in changed for n in before),
              'declarations': len(dependencies), 'proofSha256': proof['sha256'], 'auditSha256': sha(ASSETS / 'audit.txt'),
              'fullRepositoryBuild': 'Build completed successfully' in (ASSETS / 'build.txt').read_text()}
    if require_full:
        assert report['fullRepositoryBuild']
    (dest / 'publication.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: updated opening story and preserved', report['preservedFiles'], 'other existing files')

if __name__ == '__main__':
    apply(Path(sys.argv[1]), require_full='--preview' not in sys.argv[2:])
