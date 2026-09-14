#!/usr/bin/env python3
"""Check graph provenance and metric invariants; optionally check manuscript output."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import re
import unittest
import build_proof_comparison as build

ROOT = Path(__file__).resolve().parents[2]

class CommentTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = 'theorem a := 1 /- outer\n /- inner -/ ignored -/\n"/- string -/" -- ignored\n'
        clean = build.strip_comments(text)
        self.assertEqual(clean.count('\n'), text.count('\n'))
        self.assertNotIn('outer', clean)
        self.assertNotIn('inner', clean)
        self.assertIn('"/- string -/"', clean)
        self.assertNotIn('ignored', clean)

    def test_union_does_not_double_count_ranges(self):
        nodes = [dict(sourcePath='x', sourceRange=dict(start=1,end=3)),
                 dict(sourcePath='x', sourceRange=dict(start=2,end=4))]
        self.assertEqual(build.source_union(nodes, {'x':['a','','b','c']}), 3)

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument('--site', type=Path, default=ROOT/'blueprint/web')
    ap.add_argument('--manuscript', action='store_true')
    args = ap.parse_args()
    result = unittest.TextTestRunner().run(unittest.defaultTestLoader.loadTestsFromTestCase(CommentTests))
    if not result.wasSuccessful(): raise SystemExit(1)
    p = args.site/'proof-comparison'
    data = json.loads((p/'data.json').read_text())
    raw = json.loads((p/'raw.json').read_text())
    assert re.fullmatch('[0-9a-f]{40}', data['sourceCommit'])
    assert all(data['verification'].values())
    nodes = {n['id']: n for n in data['nodes']}
    assert len(nodes) == len(data['nodes'])
    assert len(nodes) == len(raw['nodes'])
    for n in nodes.values():
        assert n['bodyDagNodes'] <= n['bodyTreeNodes']
        assert n['typeDagNodes'] <= n['typeTreeNodes']
        assert all(k in nodes for k in n['bodyRefs'] + n['typeRefs'])
    for graph in ['overview', 'overviewSupplement']:
        g = data[graph]
        assert len(g['nodes']) == (13 if graph == 'overview' else 16)
        for edge in g['edges']:
            assert edge['source'] == edge['witness'][0]
            assert edge['target'] == edge['witness'][-1]
            for dep, consumer in zip(edge['witness'],edge['witness'][1:]):
                assert dep in nodes[consumer]['bodyRefs']+nodes[consumer]['typeRefs']
    for path, digest in data['sourceManifest'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    s=data['summary']
    assert s['direct']['projectDeclarations'] == s['direct']['exclusiveProjectDeclarations']+s['shared']['projectDeclarations']
    assert s['ftc']['projectDeclarations'] == s['ftc']['exclusiveProjectDeclarations']+s['shared']['projectDeclarations']
    for side in ['direct','ftc']:
        assert s[side]['axiomCount'] == len(s[side]['axioms'])
        assert 'sorryAx' not in s[side]['axioms']
    for n in data['supplements']:
        assert not nodes[n]['direct'] and not nodes[n]['ftc']
    if args.manuscript:
        pages = list(args.site.glob('*.html'))
        assert (args.site/'dep_graph_document.html').exists(), 'Native manuscript graph missing'
        text = '\n'.join(p.read_text() for p in pages)
        for label in ['cosine-comparison-direct','cosine-comparison-ftc','cosine-comparison-statement']:
            assert label in text, f'Native blueprint node missing: {label}'
        assert 'proof-comparison/index.html' in (args.site/'index.html').read_text()
    print('PASS: actual reference witnesses, source fingerprints, metric partitions, companion status, and proof checks')

if __name__ == '__main__': main()
