#!/usr/bin/env python3
"""Attach strategy notes to existing checked blueprint groups, without
rewriting Lean statements or introducing dependency edges."""
from __future__ import annotations
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]

def main():
    site=ROOT/'blueprint/web';page=site/'cosine-primitive-graph.html'
    text=page.read_text();marker='const proofGraphData='
    start=text.index(marker)+len(marker)
    data,used=json.JSONDecoder().raw_decode(text[start:])
    path=ROOT/'blueprint/three-proofs/strategy.json';guides=json.loads(path.read_text())
    assert set(guides)==set(data['nodeDetails'])
    for label,item in data['nodeDetails'].items():
        assert set(guides[label]['groups'])=={g['title'] for g in item['groups']},label
        item['strategy']=guides[label]
    data['info']['nodeDisplay']['strategyGuides']=True
    data['info']['nodeDisplay']['strategyNodes']=len(guides)
    data['info']['sourceManifest']['blueprint/three-proofs/strategy.json']=hashlib.sha256(path.read_bytes()).hexdigest()
    payload=json.dumps(data,separators=(',',':')).replace('</','<\\/')
    text=text[:start]+payload+text[start+used:]
    js=(ROOT/'blueprint/three-proofs/strategy.js').read_text()
    css=(ROOT/'blueprint/three-proofs/strategy.css').read_text()
    text=text.replace('</body>','<style>'+css+'</style><script>'+js+'</script></body>')
    page.write_text(text)
    (site/'three-proofs/node-details.json').write_text(json.dumps(data['nodeDetails'],indent=2)+'\n')
    (site/'three-proofs/summary.json').write_text(json.dumps(data['info'],indent=2)+'\n')
    print('PASS: every broad node has a strategy role and notes matching its exact declaration groups')
if __name__=='__main__':main()
