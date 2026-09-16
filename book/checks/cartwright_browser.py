#!/usr/bin/env python3
from pathlib import Path
import functools,http.server,json,shutil,threading,sys,mimetypes
from urllib.parse import urlsplit,unquote
from playwright.sync_api import sync_playwright
ROOT=Path(__file__).resolve().parents[2]
def main():
 site=ROOT/'blueprint/web';out=ROOT/'comparison/reports/cartwright-browser';out.mkdir(exist_ok=True,parents=True)
 server=http.server.ThreadingHTTPServer(('127.0.0.1',0),functools.partial(http.server.SimpleHTTPRequestHandler,directory=str(site)))
 threading.Thread(target=server.serve_forever,daemon=True).start();base=f'http://127.0.0.1:{server.server_port}/';errors=[]
 data=json.loads((site/'reading/maps.json').read_text())
 with sync_playwright() as p:
  exe=next((shutil.which(n) for n in ['google-chrome','chromium','chromium-browser'] if shutil.which(n)),None)
  opts={'headless':True,'args':['--no-sandbox']}
  if exe:opts['executable_path']=exe
  browser=p.chromium.launch(**opts);context=browser.new_context(viewport={'width':1520,'height':1100})
  base='https://computable-calculus.test/'
  def serve(route):
   file=(site/unquote(urlsplit(route.request.url).path).lstrip('/')).resolve()
   if file.is_dir():file=file/'index.html'
   if not file.is_relative_to(site.resolve()) or not file.is_file():route.fulfill(status=404,body='Not found');return
   route.fulfill(status=200,body=file.read_bytes(),content_type=mimetypes.guess_type(str(file))[0] or 'application/octet-stream')
  context.route(base+'**',serve)
  page=context.new_page()
  page.on('pageerror',lambda e:errors.append(str(e)))
  page.goto(base+'cartwright.html',wait_until='domcontentloaded')
  if '--offline' not in sys.argv:
   page.wait_for_function('window.MathJax && MathJax.startup && MathJax.startup.promise',timeout=60000)
   page.evaluate('() => MathJax.startup.promise');assert not page.locator('mjx-merror,[data-mjx-error]').count()
  page.locator('[data-proof-map="thm:cartwright-plan"]').click();frame=page.frame_locator('#proof-frame')
  frame.locator('[data-node="thm:cartwright-plan"]').wait_for()
  assert 'not yet implemented' in frame.locator('#cartwright-costs').text_content()
  for route in ['0','1','2','all']:
   frame.locator('[data-route="'+route+'"]').click();frame.locator('#svg-holder[data-view="'+route+'"]').wait_for()
   assert frame.locator('[data-node]').count()==(11 if route=='all' else 9)
  for label in ['cart:denominators','cart:obstruction']:
   frame.locator('[data-node="'+label+'"]').dispatch_event('click');frame.locator('.bundle-lean>summary').click()
   exact=data['bundles'][label]['declarations']
   expected=[d['kind']+' '+d['name']+' : '+d['type']+(' :=\n'+d['value'] if d['value'] is not None else '') for d in exact]
   assert frame.locator('.lean-card code').all_text_contents()==expected
  frame.locator('[data-node="cart:evaluation"]').dispatch_event('click')
  assert 'No Lean proof' in frame.locator('#map-detail').text_content();assert not frame.locator('.bundle-lean').count()
  frame.locator('[data-planned="true"]').first.dispatch_event('click')
  assert 'NOT A CHECKED DEPENDENCY' in frame.locator('#map-detail .role').text_content()
  frame.locator('[data-planned="false"]').first.dispatch_event('click')
  assert frame.locator('.edge-list li').count()>=2
  frame.locator('[data-node="cart:evaluation"]').dispatch_event('click')
  page.screenshot(path=str(out/'arithmetic-calculus-boundary.png'),full_page=True)
  page.locator('#close-proof').click();page.set_viewport_size({'width':390,'height':850})
  assert page.evaluate('document.documentElement.scrollWidth <= innerWidth+2')
  page.screenshot(path=str(out/'arithmetic-mobile.png'),full_page=True)
  page.goto(base+'proof-map.html?theorem=thm:c3-primitive',wait_until='domcontentloaded')
  page.wait_for_selector('[data-node="thm:c3-primitive"]');assert not page.locator('#cartwright-costs').count()
  page.wait_for_selector('#proof-comparison .pm-card');assert page.locator('#proof-comparison .pm-card').count()==3
  assert not errors,errors;browser.close()
 server.shutdown();(out/'results.json').write_text(json.dumps({'passed':True,'offline':('--offline' in sys.argv),'noFakeProofScores':True,'exactCheckedArithmetic':True,'existingComparisonPreserved':True,'errors':errors},indent=2)+'\n')
 print('PASS: proposed routes visibly pending, checked arithmetic text, edge provenance, true arithmetic costs and existing comparison')
if __name__=='__main__':main()
