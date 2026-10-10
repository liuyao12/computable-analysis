"""Apply the reviewed chapter edition to the selected existing Pages artifact."""
from pathlib import Path
import hashlib,json,shutil
ROOT=Path(__file__).parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def apply(site):
 manifest=json.loads((ROOT/'manifest.json').read_text())
 assert not manifest['newLeanProofsClaimed'] and not manifest['leanSourcesModified']
 for name,digest in manifest['artifactHashes'].items():assert sha(ROOT/name)==digest,name
 before={str(p.relative_to(site)):sha(p) for p in site.rglob('*') if p.is_file()}
 # Validate every base page before modifying any one of them.
 for row in manifest['chapters']:
  assert sha(site/row['page'])==row['originalSha256'],row['page']
  assert sha(ROOT/'chapters'/row['page'])==row['pageSha256']
  assert row['mathematicsOutsideOpeningUnchanged']
 for row in manifest['chapters']:shutil.copyfile(ROOT/'chapters'/row['page'],site/row['page'])
 dest=site/'reading/chapter-visuals';dest.mkdir(parents=True,exist_ok=True)
 for name in ['visuals.css','visuals.js']:shutil.copyfile(ROOT/name,dest/name)
 report={k:v for k,v in manifest.items() if k!='artifactHashes'}
 for row in report['chapters']:row.pop('originalOpening',None)
 modified={row['page'] for row in manifest['chapters']}
 for name,digest in before.items():
  if name not in modified and not name.startswith('reading/chapter-visuals/'):
   assert sha(site/name)==digest,name
 report['preservedFiles']=sum(n not in modified and not n.startswith('reading/chapter-visuals/') for n in before)
 report['deployedAssets']={name:sha(dest/name) for name in ['visuals.css','visuals.js']}
 (dest/'publication.json').write_text(json.dumps(report,indent=2)+'\n')
 print('PASS: 15 chapter openings and visuals; preserved',report['preservedFiles'],'other published files')
if __name__=='__main__':
 import sys
 apply(Path(sys.argv[1]))
