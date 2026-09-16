"""Mathematical reading views; checked statements and graph witnesses are retained.
The concave-only construction is explicitly distinguished from the old, more
 general quadrature engine. No claim is made that a renamed bundle changes
Lean theorem hypotheses or proves a new quadrature representation edge.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from copy import deepcopy
import pygraphviz as pgv
INVERSE='lem:c3-inverse'; TRIG='def:c3-trig'; INTEGRALS='def:c3-integrals'


def arctan_text():
    return r'''<p>For a rational parameter \(0\le u\le1\), put</p>
    <div class="displaymath">\[P(u)=\left(\frac{1-u^2}{1+u^2},\frac{2u}{1+u^2}\right).\]</div>
    <p>The shaded sector runs from \((1,0)\) to \(P(u)\), about the origin.
    Its area computation is \(A(u)\). It is defined geometrically, before a
    general integral or trigonometric function.</p>
    <p>For adjacent rational parameters \(v&lt;w\), the chord triangle and
    the tangent quadrilateral have areas</p>
    <div class="displaymath">\[
    L(v,w)=\frac{(w-v)(1+vw)}{(1+v^2)(1+w^2)},\qquad
    U(v,w)=\frac{w-v}{1+vw}.
    \]</div>
    <p>Add these finite areas and refine the rational subdivision. The lower
    sum increases, the upper decreases, and their gap tends to zero. This
    defines the computable number \(A(u)\).</p>
    <p>Only afterwards do rectangle comparisons identify
    \(A(u)\simeq\int_0^u(1+v^2)^{-1}\,dv\). This identity is not its geometric definition.</p>'''


def trig_text():
    return r'''<p>Let \(x\in\mathbb Q\), \(0\le x\le\tfrac12\). First compute
    \(u(x)\in[0,1]\) with</p>
    <div class="displaymath">\[A(u(x))\simeq2xA(1)=\frac{\pi x}{2}.\]</div>
    <p>The inverse step is part of this definition: the certified finite
    search encloses the required slope parameter. It is not a new function
    supplied by the caller.</p>
    <p>Then compute the two coordinates of the same circle point:</p>
    <div class="displaymath">\[
    S(x)=\frac{2u(x)}{1+u(x)^2},\qquad C(x)=\frac{1-u(x)^2}{1+u(x)^2}.
    \]</div>
    <p>If the inverse output is \([u_n^-,u_n^+]\), apply the increasing sine
    coordinate to its endpoints and the decreasing cosine coordinate in
    reverse order. The stage equations below show the exact programs.</p>
    <p>These particular wrappers are restricted to this chart and return zero
    outside it; that totalization is not a global trigonometric definition.</p>'''


def concave_text():
    return r'''<p><strong>Here the integral is introduced only for concave functions.</strong>
    Let \(g\) be a computable concave function on a rational interval
    \([a,b]\), with a supplied rational Lipschitz bound \(K\).
    The estimate is part of the input; it is not obtained by noncomputable choice.</p>
    <p>For a dyadic subdivision with cell width \(h\), define the lower
    chord sum and upper midpoint sum:</p>
    <div class="displaymath">\[
    L_h=\sum_i \frac h2\bigl(g(x_i)+g(x_{i+1})\bigr),\qquad
    U_h=\sum_i h\,g\!\left(\frac{x_i+x_{i+1}}2\right).
    \]</div>
    <p>Concavity orders these finite Riemann sums and gives monotone refinement.
    The Lipschitz estimate bounds their gap by
    \(K(b-a)h/2\). Rational evaluation errors are enclosed separately.
    Intersect the finite output enclosures while reevaluating retained meshes;
    their shrinking widths define \(\int_a^b g\). No primitive is used.</p>
    <p>In the animation, supporting line segments illustrate the upper areas.
    Their areas equal the midpoint rectangles; computing a derivative is not
    required for the midpoint sum.</p>'''


def apply(data):
    details=data['nodeDetails']
    before=Counter((d['name'],d['type'],str(d.get('value'))) for b in details.values() for d in b['declarations'])
    inverse=details.pop(INVERSE);trig=details[TRIG]
    # Keep all declaration cards and their groups, but nest the inverse inside
    # the function construction. Extra internal edges are not drawn as loops.
    trig['groups']=deepcopy(inverse['groups'])+trig['groups']
    trig['declarations']=deepcopy(inverse['declarations'])+trig['declarations']
    trig['anchors']+=inverse['anchors'];trig['paths'].update(inverse['paths'])
    trig['declarationCount']=len(trig['declarations'])
    trig['strategy']['groups']={**inverse['strategy']['groups'],**trig['strategy']['groups']}
    trig['strategy']['role']='Compute a circle point from its sector area'
    trig['strategy']['summary']='Invert the area clock, then apply its rational circle coordinates. Both steps are part of one sine-and-cosine construction.'
    trig['title']='Sine and cosine';trig['mathHtml']=trig_text()
    arctan=details['def:c3-arctan'];arctan['mathHtml']=arctan_text()
    arctan['strategy']['role']='Geometric area before trigonometry'
    arctan['strategy']['summary']='The sector area A(u) is enclosed by finite rational chord and tangent polygons. The GIF fixes u=2/3 rather than illustrating only the special value at one.'
    arctan['illustration']=dict(id='arctan',alt='The circle sector A(u), with u two thirds. Inner chord triangles and outer tangent quadrilaterals refine.',caption='u = 2/3. The shaded sector is A(u); the rational inner and outer bounds refine.')
    pi=details['def:c3-pi'];pi['title']='Pi from the sector area'
    pi['mathHtml']=r'''<p>At \(u=1\), the point is \(P(1)=(0,1)\): the sector is a quarter of the unit disk. Define</p><div class="displaymath">\[\boxed{\pi:=4A(1).}\]</div><p>This is the same arctangent-based computation used in the theorem. It is defined before the cosine integral and does not call that theorem.</p>'''
    integral=details[INTEGRALS];integral['title']='Integrals of concave functions';integral['mathHtml']=concave_text()
    integral['illustration']=dict(id='concave',alt='A concave quadratic enclosed by chord and midpoint-area sums on successively finer dyadic meshes.',caption='A concave example: g(x)=1−x²/2. Chord areas increase and midpoint areas decrease.')
    integral['formalizationBoundary']=(
        'This is the restricted mathematical construction being introduced, not a new claim about the old Lean API. '
        'The exact declarations below implement the more general finite-enclosure engine already used by the three cosine proofs. '
        'They do not require concavity of their integrand. The chord/midpoint constructor and its agreement with the existing cosine quadrature '
        'have not yet been formalized here. Concavity of a primitive in the FTC is a different hypothesis.')
    integral['strategy']['role']='Concavity gives lower and upper area sums'
    integral['strategy']['summary']='The animation concerns the concave integrand g. The existing FTC certificate instead concerns a primitive F; those hypotheses must not be conflated.'
    ftc=details['thm:c3-ftc'];ftc['title']='FTC for a concave primitive'
    ftc['mathHtml']+=r'''<p>Here the concavity hypothesis belongs to the primitive \(F\), not to its derivative \(D\). It must not be read as a certificate that the integrand \(D\) is concave.</p>'''
    after=Counter((d['name'],d['type'],str(d.get('value'))) for b in details.values() for d in b['declarations'])
    assert before==after,'Folding must preserve all exact declaration text'
    edges=[]
    for e0 in data['witnesses']:
        e=deepcopy(e0)
        for end in ['source','target']:
            if e[end]==INVERSE:e[end]=TRIG
        if e['source']==e['target']:continue
        edges.append(e)
    data['witnesses']=edges
    for view,dot in data['views'].items():
        old=pgv.AGraph(string=dot)
        graph=pgv.AGraph(strict=True,directed=True,**dict(old.graph_attr))
        graph.node_attr.update(**dict(old.node_attr));graph.edge_attr.update(**dict(old.edge_attr))
        for n in old.nodes():
            if str(n)==INVERSE:continue
            graph.add_node(str(n),**dict(n.attr))
            title=details.get(str(n),{}).get('title')
            if title:graph.get_node(str(n)).attr['label']=title
        for e in old.edges():
            a,b=map(str,e);a=TRIG if a==INVERSE else a;b=TRIG if b==INVERSE else b
            if a==b:continue
            if graph.has_edge(a,b):
                attrs=graph.get_edge(a,b).attr
                # A collapsed duplicate must keep the proof color if one path
                # uses a proof; retain ALL original witnesses for inspection.
                if 'proof-edge' in str(e.attr.get('class','')):attrs.update(**dict(e.attr))
            else:graph.add_edge(a,b,**dict(e.attr))
        graph.add_subgraph([n for n in ['def:c3-intervals','def:c3-mreal'] if graph.has_node(n)],rank='same')
        graph.add_subgraph([n for n in [INTEGRALS,'def:c3-arctan','def:c3-mexp'] if graph.has_node(n)],rank='same')
        graph.add_subgraph(['thm:c3-primitive'],rank='max')
        assert not graph.has_node(INVERSE)
        indegree={str(n):graph.in_degree(n) for n in graph.nodes()};todo=[n for n,v in indegree.items() if not v];count=0
        while todo:
            n=todo.pop();count+=1
            for next in graph.successors(n):
                next=str(next);indegree[next]-=1
                if not indegree[next]:todo.append(next)
        assert count==len(indegree),'Folding introduced a cycle'
        data['views'][view]=graph.string()
    data['info']['geometricPresentation']={
        'version':1,'inverseFoldedInto':TRIG,'exactDeclarationCardsPreserved':True,
        'arctanParameter':'2/3','piDefinition':'4 A(1)',
        'integralExposition':'Concave integrands with an explicit Lipschitz bound',
        'concaveOnlyLeanConstructorImplemented':False,
        'originalTheoremProgramsAndProofsUnchanged':True}
    return data
