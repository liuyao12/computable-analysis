#!/usr/bin/env python3
"""Grouped checked statements, lossless syntax color, and precise Real shading."""
from __future__ import annotations
import argparse, collections, csv, hashlib, json
from pathlib import Path
import pygraphviz as pgv
from bs4 import BeautifulSoup
from build_three_proof_graph import PICKS, TARGET

ROOT = Path(__file__).resolve().parents[2]
NATIVE, MATHLIB = '#f6fbf5', '#eee1fa'


def real_dependency_paths(nodes):
    assert nodes['Real']['module'].startswith('Mathlib.'), 'Wrong Real type'
    reverse = collections.defaultdict(set)
    for name, node in nodes.items():
        for ref in node['refs']:
            reverse[ref].add(name)
    next_step = {'Real': None}
    todo = collections.deque(['Real'])
    while todo:
        name = todo.popleft()
        for user in sorted(reverse[name]):
            if user not in next_step:
                next_step[user] = name
                todo.append(user)
    def path(name):
        if name not in next_step:
            return []
        result = []
        while name is not None:
            result.append(name)
            name = next_step[name]
        return result
    return path


def classify(flags):
    return 'mixed' if any(flags) and not all(flags) else 'mathlib' if any(flags) else 'native'


def load_groups():
    path = ROOT/'blueprint/three-proofs/node-groups.tsv'
    result = {}
    for row in csv.reader((line for line in path.read_text().splitlines()
                           if line.strip() and not line.startswith('#')), delimiter='\t'):
        assert len(row) == 4, row
        label, title, name, body = row
        assert body in ('yes', 'no')
        sections = result.setdefault(label, {})
        sections.setdefault(title, []).append(name)
    assert set(result) == {label for label, _, _ in PICKS}
    for label, sections in result.items():
        names = [name for group in sections.values() for name in group]
        assert len(names) >= 3 and len(names) == len(set(names)), label
    return result


def enhance(site: Path, report_path: Path, statement_path: Path):
    report = json.loads(report_path.read_text())
    nodes = {n['id']: n for n in report['nodes']}
    statements = {n['name']: n for n in json.loads(statement_path.read_text())['declarations']}
    dependency_path = real_dependency_paths(nodes)
    grouped = load_groups()
    page = site / 'cosine-primitive-graph.html'
    text = page.read_text()
    marker = 'const proofGraphData='
    start = text.index(marker) + len(marker)
    data, consumed = json.JSONDecoder().raw_decode(text[start:])
    old_payload_end = start + consumed
    soup = BeautifulSoup(text, 'html.parser')
    details = {}
    for label, title, anchors in PICKS:
        modal = soup.find(id=label + '_modal')
        assert modal is not None, label
        sections = grouped[label]
        names = [name for group in sections.values() for name in group]
        records = []
        for name in names:
            assert name in statements, f'Unexported grouped declaration: {name}'
            d = dict(statements[name])
            assert name in nodes, name
            node = nodes[name]
            module = node['module']
            path = module.replace('.', '/') + '.lean'
            if module.startswith('MathlibComparison'):
                url = 'https://github.com/liuyao12/computable-analysis/blob/' + data['info']['sourceCommit'] + '/comparison/'
            elif module.startswith('ComputableAnalysis'):
                url = 'https://github.com/liuyao12/computable-analysis/blob/' + data['info']['sourceCommit'] + '/'
            elif module.startswith(('Init.', 'Lean.', 'Std.')):
                url = 'https://github.com/leanprover/lean4/blob/v' + data['info']['leanVersion'] + '/src/'
            else:
                url = 'https://github.com/leanprover-community/mathlib4/blob/' + data['info']['mathlibCommit'] + '/'
            span = node['sourceRange']
            d['sourceUrl'] = url + path + (f"#L{span['start']}-L{span['end']}" if span else '')
            d['realDependencyPath'] = dependency_path(name)
            d['typeUsesReal'] = any(dependency_path(ref) for ref in d['typeRefs'])
            d['routes'] = node['routes']
            d['displayOnly'] = not node['routes']
            records.append(d)
        assert records, f'No elaborated statement for {label}'
        paths = {a: dependency_path(a) for a in anchors}
        details[label] = {'title': title.replace('\n', ' '), 'anchors': anchors,
            'declarations': records, 'groups': [
                {'title': title, 'names': names} for title, names in sections.items()],
            'declarationCount': len(records), 'paths': paths,
            'classification': classify([bool(paths[a]) for a in anchors])}
    for key, dot in data['views'].items():
        g = pgv.AGraph(string=dot)
        for node in g.nodes():
            label = str(node)
            item = details[label]
            anchors = [a for a in item['anchors'] if key not in ['0','1','2']
                or int(key) in nodes[a]['routes']]
            status = classify([bool(item['paths'][a]) for a in anchors])
            node.attr['class'] = 'real-' + status
            node.attr['fillcolor'] = NATIVE + ':' + MATHLIB if status == 'mixed' else MATHLIB if status == 'mathlib' else NATIVE
            node.attr['gradientangle'] = '0'
            node.attr['style'] = 'filled' if label != 'lem:c3-native-exp' else 'dashed,filled'
            node.attr['tooltip'] = {'native': 'No Mathlib Real dependency in this route',
                'mathlib': 'Transitively depends on Mathlib Real',
                'mixed': 'Mathlib Real is used only by the third proof; the statement is native'}[status]
        data['views'][key] = g.string()
    data['nodeDetails'] = details
    data['info']['nodeDisplay'] = {
        'version': 5, 'syntaxHighlighting': 'lossless Lean lexer', 'rationalRoot': 'Rat',
        'separateProofLanes': True, 'groupedStatements': True, 'statementFirst': True,
        'nodeLabelStyle': 'short prose titles; no equations', 'statementSource': 'Lean elaborated types (Meta.ppExpr)',
        'mathlibRealRoot': 'Real',
        'dependencyRule': 'Transitive stored type/body references; proof alternatives classified separately',
        'nativeFill': NATIVE, 'mathlibRealFill': MATHLIB,
        'nodeCount': len(details), 'syntaxSource': 'blueprint/three-proofs/lean-highlight.js',
        'declarationOccurrences': sum(d['declarationCount'] for d in details.values()),
        'uniqueDeclarations': len({r['name'] for d in details.values() for r in d['declarations']}),
        'groupsSha256': hashlib.sha256((ROOT/'blueprint/three-proofs/node-groups.tsv').read_bytes()).hexdigest()}
    data['info']['sourceManifest']['blueprint/three-proofs/node-groups.tsv'] = data['info']['nodeDisplay']['groupsSha256']
    target = details[TARGET]
    assert target['classification'] == 'mixed'
    assert not dependency_path('ComputableAnalysis.CosinePrimitive.Statement')
    assert [bool(target['paths'][a]) for a in target['anchors']] == [False, False, True]
    assert details['def:c3-rationals']['classification'] == 'native'
    assert details['def:c3-mreal']['classification'] == 'mathlib'
    for item in details.values():
        for record in item['declarations']:
            path = record['realDependencyPath']
            if path:
                assert path[0] == record['name'] and path[-1] == 'Real'
                assert all(dep in nodes[user]['refs'] for user, dep in zip(path, path[1:]))
        for anchor, path in item['paths'].items():
            if path:
                assert path[0] == anchor and path[-1] == 'Real'
                assert all(dep in nodes[user]['refs'] for user, dep in zip(path, path[1:]))
    payload = json.dumps(data, separators=(',', ':')).replace('</', '<\\/')
    text = text[:start] + payload + text[old_payload_end:]
    script_end = text.index('</script>', start)
    text = (text[:start+len(payload)] + ';\n' +
            (ROOT/'blueprint/three-proofs/lean-highlight.js').read_text() + '\n' +
            (ROOT/'blueprint/three-proofs/graph.js').read_text() + text[script_end:])
    legend = '''<div class="foundation-legend" aria-label="Node background legend">
      <span><i class="fill-native"></i>No Mathlib ℝ dependency</span>
      <span><i class="fill-mathlib"></i>Depends on Mathlib ℝ</span>
      <span><i class="fill-mixed"></i>Depends on the chosen proof</span>
      <span class="legend-help">Green borders indicate checked statements. Click a broad node for grouped, syntax-highlighted Lean declarations.</span>
    </div>'''
    text = text.replace('<p class="proof-note">', legend + '<p class="proof-note">', 1)
    page.write_text(text)
    assets = site/'three-proofs'
    (assets/'node-details.json').write_text(json.dumps(details, indent=2)+'\n')
    (assets/'blueprint-statements.json').write_text(statement_path.read_text())
    (assets/'summary.json').write_text(json.dumps(data['info'], indent=2)+'\n')
    (assets/'graph.css').write_text((ROOT/'blueprint/three-proofs/graph.css').read_text() +
                                     (ROOT/'blueprint/three-proofs/groups.css').read_text() +
                                     (ROOT/'blueprint/three-proofs/lean-highlight.css').read_text())
    print('PASS: grouped checked Lean declarations, shared rational root, separate proof lanes, and precise Real paths')
    print(json.dumps({k:v['classification'] for k,v in details.items()},indent=2))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--site', type=Path, default=ROOT/'blueprint/web')
    parser.add_argument('--report', type=Path, default=ROOT/'comparison/reports/three-proofs.json')
    parser.add_argument('--statements', type=Path, default=ROOT/'comparison/reports/blueprint-statements.json')
    args = parser.parse_args()
    enhance(args.site, args.report, args.statements)

if __name__ == '__main__': main()
