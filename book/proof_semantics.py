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
NEUTRAL = '#202020'
INTEGRALS = 'def:c3-integrals'
INTEGRAL_RAW = PREFIX + 'Integral.Dovetail.raw'
FTC = 'thm:c3-ftc'
FTC_DECL = PREFIX + 'ConcaveFTC.integral_equiv_endpoint'
INPUTS = [
    ('def:c3-trig', 'S', PREFIX + 'CosinePrimitive.S'),
    ('def:c3-trig', 'C', PREFIX + 'CosineFTC.cosine'),
    ('def:c3-pi', 'pi', PREFIX + 'CosinePrimitive.pi'),
    ('def:c3-integral', 'integral', PREFIX + 'CosinePrimitive.integral'),
    (INTEGRALS, 'integrals', INTEGRAL_RAW),
]


def reference_path(nodes, start, goal, *, definitions_only=False, body_entry=False, type_entry=False):
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
        if definitions_only and not (type_entry and current == start) and node['kind'] not in ('definition', 'opaque'):
            continue
        fields = ('typeRefs',) if type_entry and current == start else (
            ('bodyRefs',) if definitions_only or (body_entry and current == start) else ('bodyRefs', 'typeRefs'))
        refs = sorted({name for field in fields for name in node[field]})
        for name in refs:
            if name in previous or (body_entry and name == STATEMENT):
                continue
            previous[name] = current
            pending.append(name)
    return None


def add_integral_bundle(details):
    """Separate the reusable construction from its cosine instantiation.

    Reuse the exact exported declarations; do not manufacture Lean text or
    count editorial display declarations as extra proof prerequisites.
    """
    from copy import deepcopy
    specific = details['def:c3-integral']
    by_name = {d['name']: d for d in specific['declarations']}
    groups = [
        ('Finite mesh enclosures', ['Integral.Dovetail.intersectMeshes', 'Integral.Dovetail.raw']),
        ('Refinement, validity and identification', ['Integral.Dovetail.raw_contains_mesh',
            'Integral.Dovetail.raw_valid', 'Integral.Dovetail.raw_equiv_endpoint']),
    ]
    groups = [dict(title=title, names=[PREFIX+n for n in names]) for title,names in groups]
    names = [n for g in groups for n in g['names']]
    assert all(n in by_name for n in names)
    bundle = deepcopy(specific)
    bundle.update(title='Integrals', anchors=[INTEGRAL_RAW],
                  declarations=[deepcopy(by_name[n]) for n in names], groups=groups,
                  declarationCount=len(names), paths={INTEGRAL_RAW: []}, classification='native')
    assert all(not d.get('realDependencyPath') for d in bundle['declarations'])
    bundle['mathHtml'] = r"""<p>An integral is constructed from prescribed finite Riemann sums,
    with rational error allowances. Retain earlier meshes while improving the precision
    of their finitely many samples:</p><div class="displaymath">\[
    I_n=\bigcap_{k\le n}\operatorname{expand}(R_{k,n},e_k).
    \]</div><p>Validity requires ordered compatible enclosures, refinement, and widths
    tending to zero. Those conditions must be proved for the given integrand; this
    does not assert that every function has a computable integral.</p>
    <p>The cosine computation instantiates this construction. The native FTC uses
    the same construction in its own statement, then proves its endpoint identity.</p>"""
    bundle['strategy'] = dict(role='Integration before the fundamental theorem',
        summary='The general finite-sum construction is distinct from the cosine example. '
        'Black arrows show its use in defining that example, stating the native FTC, '
        'and stating the common conclusion. A primitive is not used to define the numerical output.',
        groups={
            'Finite mesh enclosures':'These exact definitions intersect prescribed expanded mesh boxes. '
                'The input is the family of independently computed sums and its rational error bound.',
            'Refinement, validity and identification':'The hypotheses expose what makes the resulting '
                'program valid. Comparison with an anchor is a correctness proof, not a runtime input.',
        })
    details[INTEGRALS] = bundle
    # Each declaration is still displayed, but in the mathematically appropriate bundle.
    moved=set(names)
    specific['groups'] = [dict(title=g['title'],names=[n for n in g['names'] if n not in moved])
                          for g in specific['groups']]
    specific['declarations'] = [d for d in specific['declarations'] if d['name'] not in moved]
    specific['declarationCount'] = len(specific['declarations'])
    return bundle


def prepare(data, report_path: Path):
    raw = json.loads(report_path.read_text())
    if not all(raw['checks'].values()):
        raise ValueError('Cannot classify unverified proof references')
    nodes = {n['id']: n for n in raw['nodes']}
    details = data['nodeDetails']
    add_integral_bundle(details)
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
    # The FTC itself mentions the integral constructor in its TYPE. Follow that
    # type, not its proof body, for the black definition arrow.
    ftc_path = reference_path(nodes, FTC_DECL, INTEGRAL_RAW,
                              definitions_only=True, type_entry=True)
    assert ftc_path and ftc_path[-2] in nodes[FTC_DECL]['typeRefs']
    edges.append(dict(source=INTEGRALS, target=FTC, route=1, kind='type',
                      witness=ftc_path, typeEntry=True,
                      note='The integral constructor occurs in the statement of the native FTC; '
                           'this arrow does not assume the FTC conclusion.'))
    for source,target,start,goal in [
        ('def:c3-intervals', INTEGRALS, INTEGRAL_RAW, PREFIX+'RealRaw'),
        (INTEGRALS, 'def:c3-integral', PREFIX+'CosinePrimitive.integral', INTEGRAL_RAW),
    ]:
        witness=reference_path(nodes,start,goal)
        assert witness
        edges.append(dict(source=source,target=target,route=None,kind='construction',
                          globalEdge=True,witness=witness))
    for old in data['witnesses']:
        source, target = old['source'], old['target']
        # Direct statement-formation edges replace proof-colored aliases to data.
        if target == TARGET and source in {s for s, _, _ in INPUTS}:
            continue
        # The new Integrals bundle now explains this former shortcut.
        if source == 'def:c3-intervals' and target == FTC:
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
        if edge.get('typeEntry'):
            assert path[-2] in nodes[path[-1]]['typeRefs']
            assert path[-1] == FTC_DECL and path[0] == INTEGRAL_RAW
        if edge['kind'] == 'proof':
            assert path[-2] in nodes[path[-1]]['bodyRefs']
            assert STATEMENT not in path
        for dep, user in zip(path, path[1:]):
            if user in nodes:
                assert dep in nodes[user]['bodyRefs'] + nodes[user]['typeRefs']
    # The S and C declaration paths share one visible bundle edge; the inspector
    # still displays their two different uses. One statement remains one sink.
    for view, dot in data['views'].items():
        previous_graph = pgv.AGraph(string=dot)
        # Shared-foundation cluster boxes were forcing long definition arrows
        # around the entire drawing. Arrange the same nodes as an ordinary DAG;
        # color and route filters, not bounding boxes, identify the alternatives.
        graph = pgv.AGraph(strict=True, directed=True, rankdir='TB', newrank='true',
                          bgcolor='transparent', splines='spline', compound='false',
                          nodesep='.45', ranksep='.65', outputorder='edgesfirst')
        for old_node in previous_graph.nodes():
            graph.add_node(str(old_node), **dict(old_node.attr))
        graph.add_node(INTEGRALS, label='Integrals', shape='box', group='native')
        graph.add_subgraph([n for n in ['def:c3-intervals', 'def:c3-mreal'] if graph.has_node(n)],
                           name='rank_foundations', rank='same')
        graph.add_subgraph([n for n in [INTEGRALS,'def:c3-arctan','def:c3-mexp'] if graph.has_node(n)],
                           name='rank_general', rank='same')
        graph.add_subgraph([TARGET], name='rank_conclusion', rank='max')
        graph.get_node('def:c3-intervals').attr['label'] = 'Computable number'
        grouped = defaultdict(list)
        for edge in edges:
            if not graph.has_node(edge['source']) or not graph.has_node(edge['target']):
                continue
            if edge['kind'] != 'statement' and not edge.get('globalEdge') and view not in ('all', 'companions') and edge['route'] != int(view):
                continue
            grouped[edge['source'], edge['target']].append(edge)
        for (source, target), records in grouped.items():
            kinds = {r['kind'] for r in records}
            attrs = dict(color=NEUTRAL, fontcolor=NEUTRAL, penwidth='1.1', fontsize='9',
                         arrowhead='vee', arrowsize='.7', style='solid', constraint='true')
            if 'statement' in kinds:
                assert kinds == {'statement'}
                attrs.update(penwidth='1.35', weight='12',
                             tooltip='Used to state the theorem; no proof is invoked',
                             **{'class': 'statement-edge'})
            elif 'proof' in kinds:
                routes = sorted({r['route'] for r in records if r['kind'] == 'proof'})
                assert routes and None not in routes
                attrs.update(color=':'.join(COLORS[i] for i in routes), penwidth='1.7',
                             tooltip='Used by the selected proof body; click for a checked path',
                             **{'class': 'proof-edge'})
                if target == TARGET:
                    attrs.update(fontcolor=COLORS[routes[0]], penwidth='2')
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
        'version': 2, 'commonStatement': STATEMENT,
        'integralsBundle': INTEGRALS, 'integralsUsedInFTCType': True,
        'naturalRankConstrainedLayout': True, 'solidBlackDefinitionArrows': True,
        'statementInputs': [name for _, name, _ in INPUTS],
        'statementArrows': 'Solid black: definition-only paths to the common statement, never transitively reduced.',
        'constructionArrows': 'Solid black: constructing objects or forming declaration types.',
        'proofArrows': 'Route-colored: entered through a stored proof/certificate body, not only its type.',
        'colorDoesNotMeanNecessity': True,
        'statementDefinitionsVerified': True, 'proofBodyEntryVerified': True,
        'oneAcyclicSinkInEveryView': True,
        'unchangedProofTermsAndMetrics': True,
    }
    return data
