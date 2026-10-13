"""Publish checked parametrized foundations while preserving existing proof results."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,shutil,sys
from apply_foundation_preface import apply as apply_preface

ROOT=Path(__file__).resolve().parents[1]
ASSETS=ROOT/'book/foundation-story'
MATH=re.compile(r'\\\(.*?\\\)|\\\[.*?\\\]',re.S)
IDS=re.compile(r'\bid=[\"\']([^\"\']+)[\"\']')
def sha(data):return hashlib.sha256(data).hexdigest()

def apply(site):
    before={str(p.relative_to(site)):p.read_bytes() for p in site.rglob('*') if p.is_file()}
    audit=(ASSETS/'bracket-audit.txt').read_text()
    assert 'PASS:' in audit and 'error:' not in audit and 'sorryAx' not in audit
    assert audit.count('AUDIT ')==17
    parametrized_audit=(ASSETS/'parametrized-audit.txt').read_text()
    assert 'PASS:' in parametrized_audit and 'error:' not in parametrized_audit and 'sorryAx' not in parametrized_audit
    assert parametrized_audit.count('AUDIT ')==33
    build=re.search(r'Build completed successfully \((\d+) jobs\)\.', (ASSETS/'build.txt').read_text())
    assert build and int(build.group(1))>=5412
    assert 'Build completed successfully (107 jobs).' in (ASSETS/'snapshot-build.txt').read_text()
    manifest=json.loads((ASSETS/'proof.json').read_text())
    assert sha((ASSETS/'proof.tar.gz').read_bytes())==manifest['sha256']
    declarations=json.loads((ASSETS/'declarations.json').read_text())['declarations']
    for node in json.loads((ASSETS/'nodes.json').read_text()):
        for name in node[4]:assert 'ComputableAnalysis.'+name in declarations,name
    for entry in declarations.values():assert (ASSETS/'sources'/(entry['module']+'.lean')).is_file(),entry['module']
    apply_preface(site)
    path=site/'ch-effective-calculus.html'
    old=path.read_text()
    section=json.loads((ASSETS/'sections.json').read_text())['ch-effective-calculus.html']
    pattern=r'<section class="foundation-story-opening">.*?</section>'
    assert len(re.findall(pattern,old,re.S))==1
    new=re.sub(pattern,lambda _: '<section class="foundation-story-opening">'+section+'</section>',old,count=1,flags=re.S)
    assert not (Counter(MATH.findall(old))-Counter(MATH.findall(new)))
    assert set(IDS.findall(old))<=set(IDS.findall(new))
    path.write_text(new)
    shutil.copytree(ASSETS,site/'foundation-story',dirs_exist_ok=True,
        copy_function=lambda src,dst: Path(dst).write_bytes(Path(src).read_bytes()))
    allowed={'preface.html','ch-effective-calculus.html','foundation-preface/content.html','foundation-preface/00-preface.tex','foundation-preface/publication.json'}
    changed=[]
    for name,data in before.items():
        if name.startswith('foundation-story/') or name in allowed:
            if (site/name).read_bytes()!=data:changed.append(name)
        else:assert (site/name).read_bytes()==data,name
    # Existing modular, trigonometric and exponential result pages remain intact.
    for name in ['modular-proofs.html','modular-dependencies.json','sine-proof-dependencies.json','ch-foundations.html']:
        assert (site/name).read_bytes()==before[name],name
    report={'changedExistingFiles':sorted(changed),'preservedFiles':len(before)-len(changed),
        'declarations':len(declarations),'checkedNewEndpoints':33,'fullRepositoryBuild':True,'buildJobs':int(build.group(1)),'snapshotBuildJobs':107,
        'proofSha256':manifest['sha256'],'bracketAuditSha256':sha((ASSETS/'bracket-audit.txt').read_bytes()),
        'parametrizedAuditSha256':sha((ASSETS/'parametrized-audit.txt').read_bytes()),
        'preservedExistingResults':True,'scope':'Covered cofinal valid diagonals for limits, continuity and derivatives; exact limit compatibility and representation invariance; interval, finite derivative and complex remainder bridges; existing secant, convex, integral and downstream results preserved.'}
    (site/'foundation-story/bracket-publication.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: checked parametrized foundation publication;',report['preservedFiles'],'existing files preserved.')

if __name__=='__main__':apply(Path(sys.argv[1]))
