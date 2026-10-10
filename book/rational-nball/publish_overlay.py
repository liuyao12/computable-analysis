from pathlib import Path
import hashlib,json,os,re,shutil,sys
from apply_chapter_overlay import overlay

def publish(site):
    root=Path(__file__).parent
    manifest=json.loads((root/'manifest.json').read_text())
    assert manifest['fullGeometricLeanProof'] is False
    assert manifest['construction']=='positive_orthant'
    assert manifest['axisTangentsIncluded'] is True
    assert manifest['stageEvaluation']=='incremental'
    assert manifest['wholeBodyVolumeRecomputedDuringRefinement'] is False
    assert manifest['generalCurvedRegionVolumeDefined'] is False
    assert (root/'certificate-check.txt').read_text().startswith('PASS:')
    for name,digest in manifest['sourceHashes'].items():
        assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
    for group in manifest['audits']:
        audit=(root/group['file']).read_text()
        assert 'sorryAx' not in audit and 'error:' not in audit
        for name in group['checkedEndpoints']:
            match=re.search("'"+re.escape(name)+r"' depends on axioms: \[([^]]*)\]",audit)
            assert match,name
            assert set(re.findall(r'[\w.]+',match[1])) <= {'propext','Classical.choice','Quot.sound'},name
        if group.get('declarationDependencyAudit'):
            assert 'PASS:' in audit and 'no Mathlib real/complex scalars, measure or integration' in audit
    before={str(p.relative_to(site)):hashlib.sha256(p.read_bytes()).hexdigest() for p in site.rglob('*') if p.is_file()}
    chapter=site/'ch-circle-sphere.html'
    chapter.write_text(overlay(chapter.read_text()))
    target=site/'rational-nball';target.mkdir(exist_ok=True)
    for name in list(manifest['sourceHashes'])+['manifest.json']:
        if name!='ch-circle-sphere.html':
            (target/name).parent.mkdir(parents=True,exist_ok=True)
            shutil.copy(root/name,target/name)
    changed=lambda name:name=='ch-circle-sphere.html' or name=='rational-nball-publication.json' or name.startswith('rational-nball/')
    for name,digest in before.items():
        if not changed(name):assert hashlib.sha256((site/name).read_bytes()).hexdigest()==digest,name
    metadata={'baseRun':os.environ.get('BASE_RUN'),'chapterSha256':hashlib.sha256(chapter.read_bytes()).hexdigest(),
        'manifestSha256':hashlib.sha256((root/'manifest.json').read_bytes()).hexdigest(),
        'preservedFiles':sum(not changed(n) for n in before),
        'checkedEndpoints':sum(len(g['checkedEndpoints']) for g in manifest['audits']),
        'geometricDimensionRecurrenceLeanChecked':manifest['geometricDimensionRecurrenceLeanChecked'],
        'recurrenceAssumesFiniteShellComparison':False,'fullGeometricLeanProof':False,'volumeConvention':manifest['volumeConvention'],
        'construction':'positive_orthant','stageEvaluation':'incremental','axisTangentsIncluded':True,
        'generalCurvedRegionVolumeDefined':False}
    (site/'rational-nball-publication.json').write_text(json.dumps(metadata,indent=2)+'\n')
    print(json.dumps(metadata))
if __name__=='__main__':publish(Path(sys.argv[1]))
