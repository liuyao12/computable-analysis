#!/usr/bin/env python3
"""Present the project principle while preserving the earlier proof records."""
import argparse
import hashlib
import json
import re
from pathlib import Path
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parents[2]


def install(site, revision):
    assert re.fullmatch('[0-9a-f]{40}', revision)
    path = site / 'programme.html'
    before = hashlib.sha256(path.read_bytes()).hexdigest()
    doc = BeautifulSoup(path.read_text(), 'html.parser')
    article = doc.article
    assert article and article.select_one('h1') and article.select_one('.lead')
    article.h1.string = 'Construct the objects; prove their laws'
    article.select_one('.lead').string = (
        'Particular computations, justified mathematical objects, and general laws about them.')
    old = article.select_one('#construction-first')
    if old:
        old.decompose()
    repo = f'https://github.com/liuyao12/computable-analysis/blob/{revision}/'
    section = BeautifulSoup((ROOT / 'book/construction-first.html').read_text().replace(
        '__REPO__', repo), 'html.parser')
    article.select_one('.lead').insert_after(section)
    article.select_one('#boundary').find_next_sibling('p').string = (
        'The native route starts with rational arithmetic, finite data and algorithms. '
        'A concrete numerical implementation supplies an executable evaluator with proofs '
        'of its domain, enclosure correctness and arbitrary precision. General laws may '
        'quantify over arbitrary valid representations; their constructions must preserve '
        'executability for executable inputs. Merely defining a function in Lean does not '
        'prove that its numerical witnesses can be computed.')
    article.select_one('#audit').string = 'The earlier published computation audit'
    audit_note = article.select_one('#audit').find_next_sibling('p')
    audit_note.string = (
        'The pinned reader snapshot records 16 historical native noncomputable declarations. '
        'That is a report about its recorded source, not a current count for every development '
        'branch. Its migration policy requires supplying missing numerical witnesses or '
        'algorithms, not merely deleting a keyword. The new contract audit above separately '
        'records the scope of the reviewed native and companion sources.')
    next_note = article.select_one('#next').find_next_sibling('p')
    next_note.string = (
        'Choose a concrete mathematical application, construct the objects it needs, and '
        'prove useful laws from their explicit properties. Record construction, conditional '
        'law, and comparison results separately. Broader existence theorems and sharper '
        'sufficient conditions remain worthwhile when an application or a mathematical '
        'question calls for them; they are not prerequisites for every useful theorem.')
    edition_note = article.select_one('#edition').find_next_sibling('p')
    edition_note.string = (
        'The preservation record below describes the pinned base edition. Later reader '
        'updates, including the integral convention and this project principle, have their '
        'own revision and artifact records. Earlier proof reports retain their original '
        'source provenance. Formal declarations and legacy links remain in the technical reference.')
    meta = doc.select_one('meta[name="documentation-revision"]')
    if meta:
        meta['content'] = revision
    path.write_text(str(doc))
    reading = site / 'reading'
    inventory = json.loads((ROOT / 'docs/CONSTRUCTION_FIRST_INVENTORY.json').read_text())
    (reading / 'construction-first-inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')
    report = {
        'documentationRevision': revision,
        'reviewedSourceRevision': inventory['sourceRevision'],
        'nativeModules': sum(r['scope'] == 'native' for r in inventory['files']),
        'otherSourceFiles': sum(r['scope'] != 'native' for r in inventory['files']),
        'newLeanTheoremsClaimed': False,
        'leanStatementsChanged': False,
        'previousPageSha256': before,
        'artifacts': {name: hashlib.sha256((site / name).read_bytes()).hexdigest()
                      for name in ['programme.html', 'reading/construction-first-inventory.json']},
    }
    (reading / 'construction-first-edition.json').write_text(json.dumps(report, indent=2) + '\n')
    print('Published construction-first principle and source-review scope')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, required=True)
    parser.add_argument('--revision', required=True)
    args = parser.parse_args()
    install(args.site, args.revision)
