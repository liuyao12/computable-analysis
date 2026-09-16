"""Mathematical reader panels; preserve all checked declarations and witnesses.
Integration uses monotonicity; differentiation uses convexity/concavity and
shrinking secant widths. Illustrations do not replace the Lean programs.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from copy import deepcopy
import pygraphviz as pgv
from numerical_examples import example, table_html
INVERSE='lem:c3-inverse'; TRIG='def:c3-trig'; INTEGRALS='def:c3-integrals'


def arctan_text():
    return r'''<p>For a rational parameter \(0\le u\le1\), put</p>
    <div class="displaymath">\[P(u)=\left(\frac{1-u^2}{1+u^2},\frac{2u}{1+u^2}\right).\]</div>
    <p>Subdivide the vertical segment from \((0,0)\) to \((0,u)\) into
    equal parts \(v_j=ju/n\). Draw each ray from \((-1,0)\) through
    \((0,v_j)\) to the circle: its second intersection is \(P(v_j)\).
    Equal vertical steps generally do not give equal-angle arcs.</p>
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


def monotone_text():
    return r'''<p><strong>For integration, assume the integrand is increasing or decreasing.</strong>
    No concavity, derivative or Lipschitz bound is needed. Let \(f\) be a
    computable monotone function on a rational interval \([a,b]\). For
    \(x_i=a+ih\), \(h=(b-a)/m\), increasing functions give</p>
    <div class="displaymath">\[
      h\sum_{i=0}^{m-1}f(x_i)\ \preceq\ \int_a^b f(x)\,dx
      \ \preceq\ h\sum_{i=1}^{m}f(x_i).
    \]</div>
    <p>For decreasing functions, the right-endpoint sum is the lower bound
    and the left-endpoint sum is the upper bound. In either case the gap
    between exact endpoint sums is \(h\lvert f(b)-f(a)\rvert\).</p>
    <p>In these finite Riemann sums, use lower rational evaluations in the lower sum
    and upper evaluations in the upper sum. Keep both indices: dyadic mesh level
    \(k\), with \(m=2^k\), and evaluation stage \(q\). At output stage \(n\), reevaluate the
    meshes \(k\le n\) at stage \(n\), and intersect the resulting intervals.
    This is a fixed finite schedule, not a search until a tolerance is met.
    Refining samples on a retained mesh controls evaluation error; refining
    the mesh controls the monotone rectangle gap.</p>
    <p>The animation uses the decreasing function \(C\), so it reads right
    endpoints for lower rectangles and left endpoints for upper rectangles.
    It never substitutes the proposed primitive to obtain the integral.</p>'''


def derivative_text():
    return r'''<p><strong>Convexity or concavity belongs to the derivative construction.</strong>
    For a concave function \(f\) and positive rational \(h\), enclose its
    derivative, when it exists, between the right and left secants:</p>
    <div class="displaymath">\[
    \frac{f(x+h)-f(x)}{h}\ \preceq\ f'(x)\ \preceq\
    \frac{f(x)-f(x-h)}{h}.
    \]</div>
    <p>For a convex function, reverse the two bounds. Compute both secants
    using rational enclosures and a predetermined step/evaluation schedule.
    Evaluation uncertainty is divided by \(h\), so its schedule must account
    for this amplification.</p>
    <p>One must also prove that the resulting secant gap shrinks to zero.
    Convexity alone does not remove corners, as \(f(x)=|x|\) at zero shows.
    The quadratic animation illustrates the construction; the exact sine
    declarations below provide the data used in this theorem.</p>'''


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
    arctan['strategy']['summary']='Subdivide the vertical segment 0 to u equally, project every point from (-1,0), then enclose the sector by rational polygons. The GIF uses u=2/3.'
    arctan['illustration']=dict(id='arctan',alt='Equal subdivisions of the vertical segment from zero to u, each projected from minus one onto the circle. Inner and outer polygons enclose A(u).',caption='u = 2/3. Gold marks subdivide the vertical segment; blue rays project each mark to the circle. These are equal parameter steps, not equal angles.')
    pi=details['def:c3-pi'];pi['title']='Pi from the sector area'
    pi['mathHtml']=r'''<p>At \(u=1\), the point is \(P(1)=(0,1)\): the sector is a quarter of the unit disk. Define</p><div class="displaymath">\[\boxed{\pi:=4A(1).}\]</div><p>This is the same arctangent-based computation used in the theorem. It is defined before the cosine integral and does not call that theorem.</p>'''
    integral=details[INTEGRALS];integral['title']='Integrals of monotone functions';integral['mathHtml']=monotone_text()
    cosine_illustration=dict(id='cosine',alt='The decreasing cosine C enclosed by right lower and left upper endpoint rectangles, with separate integral and sine-over-pi bounds.',caption='At t = 1/3, decreasing-function rectangles enclose the integral. A separate circle-coordinate evaluation encloses S(t)/π. Neither numerical side calls the other.')
    integral['illustration']=cosine_illustration
    integral['formalizationBoundary']=(
        'The native library already includes increasing and decreasing Darboux constructions. '
        'The checked declarations in this bundle expose the general finite-enclosure engine used by the existing proofs. '
        'The numerical illustration uses its own rational-polygon evaluation schedule, not the literal output stages of that Lean program. '
        'The three proof terms and the original cosine quadrature definition are unchanged.')
    integral['strategy']['role']='Monotonicity orders the endpoint rectangles'
    integral['strategy']['summary']='Increasing or decreasing integrands give lower and upper rectangle sums. Convexity or concavity is instead used to construct derivatives from secants.'
    derivative=details['lem:c3-concavity'];derivative['mathHtml']=derivative_text()+derivative.get('mathHtml','')
    derivative['illustration']=dict(id='secants',alt='Right and left secants of a concave quadratic converge to its derivative at one half.',caption='Derivative construction for a concave quadratic: right and left secant slopes approach −1/2. This illustration is not a new sine definition.')
    derivative['strategy']['role']='Concavity orders secants; shrinking widths give the derivative'
    ftc=details['thm:c3-ftc'];ftc['title']='FTC for a concave primitive'
    ftc['mathHtml']+=r'''<p>Concavity belongs to the primitive \(F\). Its derivative is decreasing, which is the relevant condition for monotone integration; no concavity of that derivative is required.</p>'''
    theorem=details['thm:c3-primitive'];theorem['illustration']=cosine_illustration
    theorem['mathHtml']+=table_html([example(n)[0] for n in [8,32,128,512]])
    theorem['mathHtml']+='<p>These are independent rational numerical bounds illustrating the theorem, not outputs of its literal Lean stage programs and not a proof by numerical agreement.</p>'
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
        'version':2,'inverseFoldedInto':TRIG,'exactDeclarationCardsPreserved':True,
        'arctanParameter':'2/3','piDefinition':'4 A(1)',
        'integralExposition':'Increasing or decreasing integrands',
        'derivativeExposition':'Convex or concave functions with shrinking secant widths',
        'verticalSubdivisionProjected':True,'independentCosineNumerics':True,
        'numericDriverIsLeanStageExecution':False,
        'originalTheoremProgramsAndProofsUnchanged':True}
    return data
