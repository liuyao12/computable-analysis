"""Layout only: disjoint proof lanes with their actual, witnessed dependencies.

No visible edge is introduced for alignment. Shared algorithms stay in a
common foundation; the representation bridges stay inside the Mathlib route.
"""
from __future__ import annotations
import collections
import pygraphviz as pgv

Q = 'def:c3-rationals'
REAL = 'def:c3-mreal'
TARGET = 'thm:c3-primitive'
COLORS = ['#a45032', '#326493', '#7755a0']
LANES = [
    ('native', 'Shared native constructions', '#9bb5a2',
     ['def:c3-intervals', 'def:c3-arctan', 'def:c3-pi', 'lem:c3-inverse', 'def:c3-trig', 'def:c3-integral']),
    ('mathlib', 'Mathlib foundation', '#bba4cc',
     [REAL, 'def:c3-mexp', 'def:c3-mpi']),
    ('direct', 'Direct inequalities', COLORS[0], ['lem:c3-direct']),
    ('ftc', 'Native FTC', COLORS[1], ['lem:c3-concavity', 'thm:c3-ftc']),
    ('bridges', 'Mathlib proof and bridges', COLORS[2],
     ['def:c3-real', 'lem:c3-values', 'lem:c3-quadrature', 'lem:c3-mftc']),
    ('companion', 'Separate native computation', '#aa9984', ['lem:c3-native-exp']),
]

def layout_graph(nodes, picks, edges, route=None):
    g = pgv.AGraph(strict=True, directed=True, rankdir='TB', bgcolor='transparent',
                  nodesep='.42', ranksep='.60', newrank='true', compound='true',
                  pad='.2', splines='spline', outputorder='edgesfirst')
    g.node_attr.update(fontname='Arial', fontsize='12', margin='.16,.12',
                       penwidth='1.6', style='filled', fillcolor='#f6fbf5', color='#467552')
    g.edge_attr.update(arrowhead='vee', color='#89968f', arrowsize='.7')
    included = set()
    for label, title, anchors in picks:
        routes = {i for a in anchors for i in nodes[a]['routes']}
        if route is not None and route not in routes:
            continue
        included.add(label)
        attrs = dict(label=title, shape='box' if label.startswith('def:') else 'ellipse')
        if label == Q:
            attrs.update(fontsize='16', penwidth='2.2', fillcolor='#f0f4f9')
        if label == TARGET:
            attrs.update(penwidth='2.7', fillcolor='#d4e9d1', fontsize='15')
        if label == 'lem:c3-native-exp':
            attrs.update(style='dashed,filled', fillcolor='#f7f4ef', color='#85735b')
        g.add_node(label, **attrs)
    for key, title, color, members in LANES:
        current = [n for n in members if n in included]
        if current:
            g.add_subgraph(current, name='cluster_'+key, label=title,
                           style='rounded', color=color, pencolor=color,
                           fontcolor=color, fontname='Arial', fontsize='12',
                           margin='18', penwidth='1.1', labeljust='l')
            for name in current:
                g.get_node(name).attr['group'] = key
    # These are rank constraints, not fabricated mathematical arrows.
    for key, labels, rank in [
        ('top', [Q], 'min'),
        ('foundations', ['def:c3-intervals', REAL], 'same'),
        ('routes', ['lem:c3-direct', 'lem:c3-concavity', 'def:c3-real'], 'same'),
        ('conclusion', [TARGET], 'max')]:
        current = [n for n in labels if n in included]
        if current:
            g.add_subgraph(current, name='rank_'+key, rank=rank)
    grouped = collections.defaultdict(list)
    for edge in edges:
        if edge['source'] in included and edge['target'] in included and (route is None or edge['route'] == route):
            grouped[(edge['source'], edge['target'])].append(edge)
    for (source, target), records in grouped.items():
        routes = {e['route'] for e in records if e['route'] is not None}
        attrs = {'tooltip': 'Click for actual reference-path witnesses'}
        if len(routes) == 1:
            attrs['color'] = COLORS[next(iter(routes))]
        if target == TARGET:
            attrs.update(label=' / '.join(['direct', 'native FTC', 'Mathlib'][i] for i in sorted(routes)),
                         fontsize='10', fontcolor=attrs.get('color', '#47534c'), penwidth='2')
        g.add_edge(source, target, **attrs)
    return g.string()
