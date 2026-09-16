"""Separate statement formation from proof use in the mathematical reader.

Statement links unfold definition bodies only, never theorem proofs. They are
not transitively reduced: a name can be part of the statement even when a proof
route also reaches it. Colored links have a witness entered through a stored
proof/certificate body, not just the target declaration's type. This is a
syntactic audit of the chosen bundles, not a claim of minimal logical premises.
"""
from __future__ import annotations
from collections import deque, defaultdict
from pathlib import Path
import json
import pygraphviz as pgv

PREFIX = 'ComputableAnalysis.'
TARGET = 'thm:c3-primitive'
STATEMENT = PREFIX + 'CosinePrimitive.Statement'
COLORS = ['#a45032', '#326493', '#7755a0']
NEUTRAL = '#8b9296'
INPUTS = [
    ('def:c3-trig', 'S', PREFIX + 'CosinePrimitive.S'),
    ('def:c3-trig', 'C', PREFIX + 'CosineFTC.cosine'),
    ('def:c3-pi', 'pi', PREFIX + 'CosinePrimitive.pi'),
    ('def:c3-integral', 'integral', PREFIX + 'CosinePrimitive.integral'),
]


def reference_path(nodes, start, goal, *, definitions_only=False, body_entry=False):
    """Shortest prerequisite-first path; optionally restrict the initial edge."""
    previous = {start: None}
    pending = deque([start])
    while pending:
        current = pending.popleft()
        if current == goal:
            path = []
            while current is not None:
                path.append(current)
                current = previous[current]
            return path
        node = nodes[current]
        if definitions_only and node['kind'] not in ('definition', 'opaque'):
            continue
        fields = ('bodyRefs',) if definitions_only or (body_entry and current == start) else ('bodyRefs', 'typeRefs')
        refs = sorted({name for field in fields for name in node[field]})
        for name in refs:
            if name in previous or (body_entry and name == STATEMENT):
                continue
            previous[name] = current
            pending.append(name)
    return None


def prepare(data, report_path: Path):
    raw = json.loads(report_path.read_text())
    if not all(raw['checks'].values()):
        raise ValueError('Cannot classify unverified proof references')
    nodes = {n['id']: n for n in raw['nodes']}
    details = data['nodeDetails']
    edges = []
    # A genuine declaration-reference witness for every requested statement input.
    for source, name, anchor in INPUTS:
        witness = reference_path(nodes, STATEMENT, anchor, definitions_only=True)
        if not witness:
            raise ValueError('Missing definition-only statement path for ' + name)
        edge = dict(source=source, target=TARGET, route=None, kind='statement',
                    input=name, witness=witness)
        if name == 'C':
            edge['note'] = ('C is the closed wrapper of CosineFTC.cosine with the fixed provider. '
                            'The integral definition calls this underlying cosine evaluator, not the wrapper name C. '
                            'TrigonometricReadback.cosine_stage displays the exact closed computation.')
        edges.append(edge)
    for old in data['witnesses']:
        source, target = old['source'], old['target']
        # Direct statement-formation edges replace proof-colored aliases to data.
        if target == TARGET and source in {s for s, _, _ in INPUTS}:
            continue
        edge = dict(old)
        # Constructing the objects is neutral even when only one route needs them.
        if target.startswith('def:') or target in ('lem:c3-inverse', 'lem:c3-native-exp'):
            edge['kind'] = 'construction'
        else:
            start, goal = old['witness'][-1], old['witness'][0]
            witness = reference_path(nodes, start, goal, body_entry=True)
            if witness:
                edge.update(kind='proof', witness=witness)
            else:
                edge['kind'] = 'type'
        edges.append(edge)
    # Validate the extra distinction, not just existence of an untyped path.
    for edge in edges:
        path = edge['witness']
        if edge['kind'] == 'statement':
            assert path[-1] == STATEMENT
            for dep, user in zip(path, path[1:]):
                assert nodes[user]['kind'] in ('definition', 'opaque')
                assert dep in nodes[user]['bodyRefs']
        if edge['kind'] == 'proof':
            assert path[-2] in nodes[path[-1]]['bodyRefs']
            assert STATEMENT not in path
        for dep, user in zip(path, path[1:]):
            if user in nodes:
                assert dep in nodes[user]['bodyRefs'] + nodes[user]['typeRefs']
    # The S and C declaration paths share one visible bundle edge; the inspector
    # still displays their two different uses. One statement remains one sink.
    for view, dot in data['views'].items():
        graph = pgv.AGraph(string=dot)
        graph.remove_edges_from(list(graph.edges()))
        graph.get_node('def:c3-intervals').attr['label'] = 'Computable number'
        grouped = defaultdict(list)
        for edge in edges:
            if not graph.has_node(edge['source']) or not graph.has_node(edge['target']):
                continue
            if edge['kind'] != 'statement' and view not in ('all', 'companions') and edge['route'] != int(view):
                continue
            grouped[edge['source'], edge['target']].append(edge)
        for (source, target), records in grouped.items():
            kinds = {r['kind'] for r in records}
            attrs = dict(color=NEUTRAL, fontcolor=NEUTRAL, penwidth='1.1', fontsize='9',
                         arrowhead='vee', arrowsize='.7')
            if 'statement' in kinds:
                assert kinds == {'statement'}
                attrs.update(style='dashed', constraint='false', penwidth='1.35',
                             tooltip='Used to state the theorem; no proof is invoked',
                             **{'class': 'statement-edge'})
            elif 'proof' in kinds:
                routes = sorted({r['route'] for r in records if r['kind'] == 'proof'})
                assert routes and None not in routes
                attrs.update(color=':'.join(COLORS[i] for i in routes), penwidth='1.7',
                             tooltip='Used by the selected proof body; click for a checked path',
                             **{'class': 'proof-edge'})
                if target == TARGET:
                    attrs.update(label=' / '.join(['direct', 'native FTC', 'Mathlib'][i] for i in routes),
                                 fontcolor=COLORS[routes[0]], penwidth='2')
            else:
                attrs.update(tooltip='Construction or declaration-type dependency',
                             **{'class': 'construction-edge'})
            graph.add_edge(source, target, **attrs)
        for source in {s for s, _, _ in INPUTS}:
            assert graph.has_edge(source, TARGET), (view, source)
        assert not graph.out_neighbors(TARGET), 'The common theorem must remain a sink'
        indegree = {str(n): graph.in_degree(n) for n in graph.nodes()}
        pending = [n for n, degree in indegree.items() if degree == 0]
        count = 0
        while pending:
            n = pending.pop(); count += 1
            for successor in graph.successors(n):
                key = str(successor); indegree[key] -= 1
                if indegree[key] == 0: pending.append(key)
        assert count == len(indegree), 'Cycle in graph view ' + view
        data['views'][view] = graph.string()
    bundle = details['def:c3-intervals']
    groups = [
        ('Rational intervals', ['QInterval', 'QInterval.Overlaps', 'QInterval.ContainsInterval']),
        ('A computable number', ['RealRaw', 'RealRaw.ValidCompute', 'RealRaw.Valid']),
        ('Equality, order and refinement', ['RealRaw.Equiv', 'RealRaw.Le',
            'RealRaw.allStagesOverlap_of_equiv', 'RealRaw.equiv_trans']),
    ]
    originals = {d['name']: d for d in bundle['declarations']}
    bundle['groups'] = [dict(title=title, names=[PREFIX+n for n in names]) for title,names in groups]
    ordered = [name for group in bundle['groups'] for name in group['names']]
    assert set(ordered) == set(originals), 'The grouping must preserve every original declaration'
    bundle['declarations'] = [originals[name] for name in ordered]
    bundle['strategy']['groups'] = {
        'Rational intervals': 'Start with rational interval data, overlap and containment. A single interval is not yet a computable number.',
        'A computable number': 'The evaluator together with ordered, nested outputs and shrinking widths presents a computable number.',
        'Equality, order and refinement': 'Equality and order compare the represented computations. Validity makes equivalence transitive; arbitrary interval overlap is not transitive.',
    }
    details['def:c3-intervals']['title'] = 'Computable number'
    details['def:c3-intervals']['strategy']['role'] = 'From a rational interval to a computable number'
    details['def:c3-intervals']['strategy']['summary'] = (
        'A rational interval is the first piece of data, not the name of the mathematical object. '
        'A computable number is presented by an evaluator with ordered nested outputs and shrinking widths. '
        'Equality and order then compare such computations.')
    data['witnesses'] = edges
    data['info']['edgeSemantics'] = {
        'version': 1, 'commonStatement': STATEMENT,
        'statementInputs': [name for _, name, _ in INPUTS],
        'statementArrows': 'Gray dashed: definition-only paths to the common statement, never transitively reduced.',
        'constructionArrows': 'Gray solid: constructing objects or forming declaration types.',
        'proofArrows': 'Route-colored: entered through a stored proof/certificate body, not only its type.',
        'colorDoesNotMeanNecessity': True,
        'statementDefinitionsVerified': True, 'proofBodyEntryVerified': True,
        'oneAcyclicSinkInEveryView': True,
        'unchangedProofTermsAndMetrics': True,
    }
    return data
