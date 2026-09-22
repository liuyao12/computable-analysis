#!/usr/bin/env python3
"""Publish the checked historical reconstruction and its geometric illustration."""
import argparse
import hashlib
import json
import re
from fractions import Fraction as Q
from pathlib import Path


def digest(data):
    return hashlib.sha256(data).hexdigest()


def diagram():
    def X(t): return 2*t*t/(1+t*t)
    def Y(t): return 2*t/(1+t*t)
    def point(x,y,offset=0): return f'{70+offset+240*float(x):.4f},{320-240*float(y):.4f}'
    def path(points,offset=0): return 'M'+'L'.join(point(x,y,offset) for x,y in points)
    ts=[Q(k,100) for k in range(101)]
    # Check the exact geometry of every plotted sample before formatting SVG coordinates.
    assert all((X(t)-1)**2+Y(t)**2==1 and Y(t)*t==X(t) for t in ts)
    t=Q(1,2);assert (X(t),Y(t))==(Q(2,5),Q(4,5))
    items=['<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1000 390"><style>text{font-family:Georgia,serif;fill:#294235;font-size:19px}.small{font-family:sans-serif;font-size:14px;fill:#586c5f}</style><rect width="1000" height="390" fill="#f3f5ef"/>']
    for o,title in [(0,'The circle and its tangent'),(500,'The transmuted curve')]:
        items.append(f'<text x="{70+o}" y="36">{title}</text><path d="{path([(0,Q(11,10)),(0,0),(Q(6,5),0)],o)}" stroke="#9aa99d" fill="none"/><text class="small" x="{45+o}" y="340">0</text><text class="small" x="{305+o}" y="340">1</text>')
    items += [f'<path d="{path([(X(a),Y(a)) for a in ts])}" fill="none" stroke="#46785b" stroke-width="3"/>',f'<path d="{path([(0,t),(X(t),Y(t)),(Q(3,5),Q(19,20))])}" stroke="#b27140" fill="none" stroke-width="2"/>',f'<path d="{path([(1,0),(X(t),Y(t))])}" stroke="#8eaa98" stroke-dasharray="5 4" fill="none"/>',f'<circle cx="166" cy="128" r="5" fill="#46785b"/><circle cx="70" cy="200" r="4" fill="#b27140"/><circle cx="310" cy="320" r="4" fill="#46785b"/><text x="177" y="117">(X(t), Y(t))</text><text x="41" y="207">t</text><text class="small" x="285" y="365">centre (1,0)</text>',f'<path d="{path([(0,0)]+[(a,X(a)) for a in ts]+[(1,0)],500)}Z" fill="#dbe8da"/>',f'<path d="{path([(a,X(a)) for a in ts],500)}" fill="none" stroke="#46785b" stroke-width="3"/>','<text x="680" y="283">J</text><text x="810" y="99">X(t)</text><text class="small" x="710" y="365">tangent intercept t →</text>','</svg>']
    return ''.join(items)


def install(site,revision,audit,closure):
    assert re.fullmatch('[0-9a-f]{40}',revision)
    log=audit.read_text();names=closure.read_text().splitlines()
    assert 'PASS: finite transmutation is an actual dependency' in log
    assert 'PASS: geometric transmutation has no calculus certificates' in log
    assert 'error:' not in log and 'sorryAx' not in log
    assert 'ComputableAnalysis.LeibnizTransmutation.sector_cell_transmutation' in names
    protected={str(p.relative_to(site)):digest(p.read_bytes()) for p in site.rglob('*') if p.is_file()}
    out=site/'reading';out.mkdir(exist_ok=True)
    page=Path(__file__).with_name('leibniz-transmutation')/'page.html'
    body=page.read_text().replace('__SOURCE__',f'https://github.com/liuyao12/computable-analysis/blob/{revision}').replace('__REVISION__',revision[:12])
    files={'leibniz-transmutation.html':body.encode(),'reading/leibniz-transmutation.svg':diagram().encode(),'reading/leibniz-transmutation-check.log':audit.read_bytes(),'reading/leibniz-transmutation-closure.txt':closure.read_bytes()}
    for name,data in files.items():
        assert name not in protected, 'Build from the pinned reader artifact'
        (site/name).write_bytes(data)
    assert all(digest((site/p).read_bytes())==h for p,h in protected.items())
    report=dict(proofSourceCommit=revision,theorem='ComputableAnalysis.pi_eq_leibniz_transmutation',canonicalPi='ComputableAnalysis.piCircleArea',projectClosureCount=len(names),mathlibDependency=False,modernReconstruction=True,geometricBridgeUsesCalculus=False,powerQuadratureShared=True,allPreviousContentPreserved=True,artifactHashes={n:digest(d) for n,d in files.items()})
    (out/'leibniz-transmutation.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: checked finite transmutation, exact diagram samples and prior artifacts preserved')


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--site',type=Path,required=True);p.add_argument('--revision',required=True);p.add_argument('--audit',type=Path,required=True);p.add_argument('--closure',type=Path,required=True);a=p.parse_args();install(a.site,a.revision,a.audit,a.closure)
