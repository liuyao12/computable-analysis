#!/usr/bin/env python3
"""Audit a curated graph against the checked declaration graph.

Bundles are UI groupings, not new Lean definitions. Keep the original names,
include underlying definitions as anchors, witness every edge, and check
independent definition closures before claiming an endpoint identity.
"""
from __future__ import annotations
import collections, hashlib, json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
P = 'ComputableAnalysis.'


def closure(nodes, roots):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen: continue
        if n not in nodes: raise ValueError('Missing declaration: '+n)
        seen.add(n); todo.extend(nodes[n]['refs'])
    return seen


def main():
    site=ROOT/'blueprint/web';assets=site/'three-proofs'
    data=json.loads((ROOT/'comparison/reports/three-proofs.json').read_text())
    nodes={n['id']:n for n in data['nodes']}
    details=json.loads((assets/'node-details.json').read_text())
    witnesses=json.loads((assets/'witnesses.json').read_text())
    for item in details.values():
        for d in item['declarations']:
            d['ownerModule']=nodes[d['name']]['module']
            d['namespace']=d['name'].rsplit('.',1)[0] if '.' in d['name'] else ''
    corrections={
        'def:c3-pi': {
            'summary': 'CosinePrimitive is only the namespace containing the data. Its pi is literally 4*A(1), with A the independent geometric arctangent. It is not defined from an integral of C; the definition closure contains neither S nor C nor the endpoint theorem.',
            'groups': {'Validity and identification': 'The stage equality with circle-area pi transports the existing reciprocal facts. The literal readback equation independently verifies 4*A(1); pi_initial gives the initial box [2,4]. This normalization is not a new numerically independent algorithm for pi.'}},
        'def:c3-trig': {
            'summary': 'S and C wrap the same closed inverse-arctangent evaluator used by all three proofs. They are trigonometric functions on rational [0,1/2]. Outside that chart these particular wrappers return zero, not global sine and cosine.',
            'groups': {
                'Closed sine and cosine': 'Domain and OnHalf expose the chart before S and C. CosinePrimitive is a namespace. The defining equations pass the closed provider to CosineFTC.sine/cosine, whose bodies are displayed below.',
                'Underlying inverse-arctangent definitions': 'The wrappers select the certified chart or return zero. tangentRaw/tangentAt expose the inverse call at 2*x. The interval formulas preserve slope endpoint order for sine but reverse it for the decreasing cosine coordinate.',
                'Underlying validity certificates': 'sine_stage and cosine_stage are checked by reduction: both coordinates use exactly ClosedArctanInverse.raw (2*x). The outside-chart equalities document the zero totalization. The integral may use the underlying cosine function without referring to the convenience name C.'}},
        'lem:c3-inverse': {'groups': {'Computation and provider': 'locate bisects the rational lower arctangent rectangle values against t times the lower value at 1. The explicit radius and prefix intersection form raw. The raw search uses no pi evaluator; the provider also carries proofs referring to the earlier normalization identities.'}},
        'def:c3-integral': {'groups': {'Finite-sum and refinement certificates': 'First fix a mesh with small error, then refine its finitely many samples. Each route supplies its own overlap argument for raw_valid. integral_stage exposes the literal program. At t=1/2 the initial integral box is [-1000,2001/2], different from the endpoint box [0,1/2].'}},
        'thm:c3-primitive': {'groups': {'One common proposition': 'Statement compares the fixed cosine-sum program with endpoint, separately defined as inversePi*S(t). Using the same independently defined pi is intentional, not tautological. The readback and initial-box statements expose the difference between the programs. Validity is a separate assertion.'}}
    }
    for label, patch in corrections.items():
        guide=details[label]['strategy']
        if 'summary' in patch: guide['summary']=patch['summary']
        guide['groups'].update(patch.get('groups',{}))
    forbidden={P+'CosinePrimitive.'+x for x in ['Statement','endpoint','viaInequalities','viaFTC','viaMathlib']}
    forbidden |= {P+'CosineFTC.'+x for x in ['fixedMesh_overlaps_endpoint','integral_cosPi_viaInequalities','integral_cosPi_viaFTC']}
    forbidden.add(P+'ConcaveFTC.integral_equiv_endpoint')
    checks=[]
    for short in ['A','pi','S','C','integral']:
        name=P+'CosinePrimitive.'+short;deps=closure(nodes,[name])
        assert not (deps & forbidden), (name,sorted(deps & forbidden))
        assert not any(nodes[n]['module'].startswith('Mathlib') for n in deps), name
        checks.append({'root':name,'declarations':len(deps),'noEndpointTheorem':True,'noMathlib':True})
    piDeps=closure(nodes,[P+'CosinePrimitive.pi'])
    assert P+'ArctanGeometry.arctanGeom' in piDeps
    assert not any(n.startswith((P+'ClosedArctanInverse.',P+'CosineFTC.',P+'SinPiIntegral.')) for n in piDeps)
    rawDeps=closure(nodes,[P+'ClosedArctanInverse.raw'])
    assert P+'ArctanGeometry.arctanIntegralRectangleCompute' in rawDeps
    assert not any(n in rawDeps for n in [P+'piCircleArea',P+'CosinePrimitive.pi',P+'CosinePrimitive.S',P+'CosinePrimitive.C'])
    assert P+'CosineFTC.fixedMesh' in closure(nodes,[P+'CosinePrimitive.integral'])
    # Every broad node has explicit defining anchors in its visible bundle.
    for label,item in details.items():
        names={d['name'] for d in item['declarations']}
        assert set(item['anchors']) <= names,(label,set(item['anchors'])-names)
        assert len(names)==len(item['declarations']),label
        for d in item['declarations']:
            assert d['ownerModule']==nodes[d['name']]['module']
            assert d['namespace']==(d['name'].rsplit('.',1)[0] if '.' in d['name'] else '')
        assert item['strategy']['summary'],label
    # Every edge is a contraction of stored type/body references. The display
    # is not a claim that namespace prefixes are dependencies.
    for e in witnesses:
        assert e['witness'][0] in details[e['source']]['anchors'],e
        assert e['witness'][-1] in details[e['target']]['anchors'],e
        for dep,user in zip(e['witness'],e['witness'][1:]):assert dep in nodes[user]['refs'],(dep,user)
    # In particular, the generic value bridge must visibly depend on native
    # trigonometric definitions, not just bypass them via wrapper naming.
    assert any(e['route']==2 and e['source']=='def:c3-trig' and e['target']=='lem:c3-values' for e in witnesses)
    readback={
        'pi':P+'TrigonometricReadback.pi_definition',
        'sine':P+'TrigonometricReadback.sine_stage',
        'cosine':P+'TrigonometricReadback.cosine_stage',
        'integral':P+'TrigonometricReadback.integral_stage',
        'outsideSine':P+'TrigonometricReadback.sine_outside_chart',
        'outsideCosine':P+'TrigonometricReadback.cosine_outside_chart',
        'distinctIntegralBox':P+'TrigonometricReadback.integral_initial_half',
        'distinctEndpointBox':P+'TrigonometricReadback.endpoint_initial_half'}
    for name in readback.values():
        assert name in nodes
        assert not any(r in closure(nodes,[name]) for r in data['roots'])
    result={'schemaVersion':1,'sourceCommit':json.loads((assets/'summary.json').read_text())['sourceCommit'],
       'passed':True,'nodesAudited':len(details),'edgeWitnessesAudited':len(witnesses),
       'definitions':checks,'piUsesArctanNotCosine':True,'closedInverseRawHasNoPiEvaluator':True,
       'namespaceIsNotDependency':True,'visibleAnchorsCovered':True,
       'stageEquations':readback,
       'notes':['S and C are zero outside the certified chart, not global sine and cosine.',
         'The generic cosine integrand is definitionally the same closed evaluator as C; its spelling need not mention C.',
         'A is geometric arctangent; the rational rectangle evaluator is equivalent, not its literal definition.',
         'Provider certificates reference upstream pi facts; the closed raw search uses only rational arctangent rectangles.',
         'Graph edges include statement/type dependencies and proof/definition dependencies; neither is namespace containment.',
         'Companion declarations are displayed but are not added to measured proof-root closures.']}
    # Update the embedded data only: exact Lean statement text is not rewritten.
    page=site/'cosine-primitive-graph.html';text=page.read_text()
    marker='const proofGraphData=';start=text.index(marker)+len(marker)
    payload,used=json.JSONDecoder().raw_decode(text[start:])
    payload['nodeDetails']=details
    payload['info']['definitionAudit']={'passed':True,'nodeCount':len(details),'report':'three-proofs/definition-audit.json'}
    payload['info']['sourceManifest']['blueprint/checks/audit_blueprint_definitions.py']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    encoded=json.dumps(payload,separators=(',',':')).replace('</','<\\/')
    text=text[:start]+encoded+text[start+used:]
    text=text.replace('</header>','</header><div style="padding:8px 20px"><a href="three-proofs/definition-audit.json">Definition and bundle audit</a> · Namespace prefixes are not mathematical dependencies.</div>',1)
    page.write_text(text)
    (assets/'node-details.json').write_text(json.dumps(details,indent=2)+'\n')
    (assets/'summary.json').write_text(json.dumps(payload['info'],indent=2)+'\n')
    (assets/'definition-audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all bundles/edges audited; pi/S/C/integral definitions have no endpoint-theorem dependency; closed stage equations checked')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
