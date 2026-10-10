from pathlib import Path
import json,re,hashlib,html
ROOT=Path(__file__).parent
# name, renderer, title, opening, caption, control, min, max, initial, construction fragment, legend
ROWS=[
('rational-circle-trigonometry','angles','Sector area becomes an angle coordinate',
'A point on the circle has two coordinates. Sector area tells us how far it has turned, even when its slope becomes vertical.',
 r'The sector grows through a quarter-turn. Its area supplies the input; the horizontal and vertical projections supply \(C\) and \(S\). A full turn has input length \(2\).','Quarter-turn stage',0,16,8,'a0000000011','Orange horizontal projection · Blue vertical projection'),
('integrals','rectangles','Enclose every cell, then refine',
'Bound the rate throughout each small interval. Multiplying those bounds by its length gives lower and upper contributions to the total.',
 r'For \(f(t)=t^2\) on \([0,1]\), green rectangles lie below the curve and orange rectangles lie above it. Their exact rational totals approach one another.','Refinement',0,6,2,'a0000000016','Green lower rectangles · Orange upper rectangles'),
('effective-calculus','secants','Two secants squeeze one derivative',
'Neighboring secants of a convex function give lower and upper slopes. Shrinking the increment brings those bounds together.',
 r'Here \(f(t)=t^2\), at \(t=1\). The green and blue secant slopes are \(2-h\) and \(2+h\); the dashed orange tangent has slope \(2\). The general construction also controls errors in the function evaluations.','Refinement',0,6,2,'a0000000022','Green left secant · Blue right secant · Dashed orange tangent'),
('infinite-series','series','A prefix needs a remainder bound',
'Adding terms gives a prefix. Bounding all omitted terms turns that prefix into a computation of the sum.',
 r'The lengths are \(1,1/2,1/4,\ldots\). Green includes the selected prefix; orange is the entire remaining tail. A finite geometric identity computes both exactly.','Included terms',1,8,4,'a0000000032','Green included prefix · Orange omitted tail'),
('exponential-logarithm','growth','More compounding periods, the same growth law',
'Repeated multiplication and a power series give two computations of exponential. Their agreement lets later chapters use either one.',
 r'Divide a unit time interval into \(N\) periods, each with growth factor \(1+1/N\). The green vertices show compound growth; the gray curve sketches \(E(t)\). The chapter proves their agreement, with errors that also cover represented inputs.','Refinement',0,3,2,'a0000000038','Green compound growth · Gray exponential'),
('algebra-fta','root','Select a branch and keep its bracket',
'An equation does not choose a root. A selected branch and a separating interval make it a function computation.',
 r'Bisection selects the positive root of \(w^2=2\). The green strip records every possible value still allowed by the exact square comparisons. Complex branches require analogous separation data.','Bisections',0,8,3,'a0000000043','Green root bracket · Dashed orange target value'),
('local-models','charts','Moving the centre spends radius',
'A local model carries coefficients and an error bound. Moving its centre changes the region where that same evidence remains valid.',
 r'The original disk has radius \(1\). A centre displacement bounded by \(d_0\) leaves a certified radius \(1-d_0\). The new disk stays inside the original; further continuation needs new evidence.','Centre displacement',0,8,4,'a0000000048','Gray original disk · Green recentered disk'),
('complex-paths','path','A continued value remembers the path',
'Complex accumulation follows a specified path. Returning to the same input need not return the same continued branch.',
 r'Follow a logarithm from \(1\) around the origin. After one turn the input returns to \(1\), while the continued logarithm has gained \(2\pi i\). The path and its local branch evidence are part of the construction.','Path stage',0,24,12,'a0000000057','Green traversed path · Blue current point · Orange excluded origin'),
('improper-parameters','tails','Compute the middle; budget both ends',
'A cutoff makes an integral finite. Bounds on both omitted ends make it an approximation to the desired improper computation.',
 r'For the example \(t e^{-t}\), compute on \([\varepsilon,T]\). The missing near part is at most \(\varepsilon^2/2\); the far part is \((T+1)e^{-T}\le(T+1)/2^T\) for integer \(T\). Both allowances shrink as the cutoffs move.','Cutoff stage',1,8,3,'a0000000058','Green computed middle · Blue near tail · Orange far tail'),
('fourier','fourier','A positive kernel concentrates its weight',
'Finite oscillations build a positive averaging kernel. Its near part uses continuity; a tail bound controls the distant part.',
 r'The period is \(2\). As \(N\) grows, the kernel narrows around zero while its normalized total stays \(1\). Dashed lines mark \(|t|=1/4\), separating the near and far estimates.','Kernel stage',1,5,3,'a0000000063','Green kernel · Dashed orange near-region boundary'),
('impulses','pulse','A narrower pulse keeps the same total effect',
'A pulse can shrink in duration and grow in height without losing its total effect. Test functions record that effect.',
 r'The rectangle has width \(\varepsilon\) and height \(1/\varepsilon\). Its area is always \(1\). Against \(\phi(t)=1+t\), its value tends to \(\phi(0)=1\): this is convergence on tests.','Pulse refinement',0,4,2,'a0000000071','Green unit-area pulse'),
('differential-equations','evolution','Two basic responses propagate every initial state',
'A linear equation needs only its responses to the basic initial states. Their combinations give the response to any other state.',
 r'For \(y^{\prime\prime}+\pi^2y=0\), the two responses are \(C(t)\) and \(S(t)\). Their initial velocities are \(0\) and \(\pi\). Selecting their sum illustrates the linear reuse encoded by the fundamental matrix.','Time stage',0,32,8,'a0000000079','Green first response · Dashed blue second response · Orange selected value'),
('special-equations','bessel','A recurrence produces values and controls the tail',
'A special function becomes usable once its chosen local data generate coefficients and a bound for the missing terms.',
 r'The green polynomial retains terms of the \(J_0\) series through the selected degree index. Gray sketches a longer prefix. On \(|z|\le4\), the first omitted term and the decreasing ratio \(4/(N+2)^2\) give the displayed error bound.','Last term index',2,8,3,'a0000000083','Green selected prefix · Gray longer prefix'),
('transforms-zeta','zeta','Choose a tail bound from the convergence mechanism',
'Damping, cancellation and decreasing terms need different tail estimates. The reciprocal-square sum gives a concrete decreasing-term example.',
 r'Green includes the first \(N\) terms. Comparing the decreasing curve with adjacent unit-width rectangles bounds the remaining reciprocal-square tail between \(1/(N+1)\) and \(1/N\). Later endpoint corrections sharpen this idea.','Included terms',1,10,4,'a0000000090','Green included terms · Gray reciprocal-square curve'),
('elliptic','elliptic','Change the coordinate before computing',
'The original integrand rises without bound at an endpoint. The rational circle coordinate cancels that singular factor and gives a bounded integrand.',
 r'Dashed orange shows the original height; green shows the transformed height in its own sampling coordinate. The horizontal coordinates differ, so equal integrals come from the substitution identity, not equal areas under these two plotted heights. Keep \(m<1\).','Parameter stage',0,9,5,'a0000000093','Dashed orange original integrand · Green transformed integrand')
]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def build(site):
 report={'baseRun':38054353598,'newLeanProofsClaimed':False,'leanSourcesModified':False,'chapters':[],'artifactHashes':{}}
 for name,kind,title,opening,caption,label,mn,mx,initial,anchor,legend in ROWS:
  filename='ch-'+name+'.html';path=site/filename;s=path.read_text();before=s
  # Link to an actual construction fragment, rather than trusting old generated numbering.
  if 'id="'+anchor+'"' not in s:
   headings=re.findall(r'<h2[^>]*id="([^"]+)"',s)
   assert headings,filename;anchor=headings[0]
  original=re.search(r'<section class="pedagogical-opening".*?</section>',s,re.S)
  if original:
   context=re.search(r'<p class="pedagogical-context">.*?</p>',original[0],re.S)
   replacement='<section class="pedagogical-opening" data-pedagogy="opening" id="why-this-page"><p>'+opening+'</p>'+(context[0] if context else '')+'</section>'
   s=s[:original.start()]+replacement+s[original.end():]
  values=None
  if kind in ['rectangles','growth','fourier']:values=[str(2**j) for j in range(mx+1)];label={'rectangles':'Number of cells','growth':'Compounding periods','fourier':'Kernel order'}[kind]
  if kind=='charts':values=[str(j/10) for j in range(mx+1)]
  if kind=='elliptic':values=[str(j/10) for j in range(mx+1)]
  extra=''
  if kind=='evolution':extra='<label>Initial response <select aria-label="Initial response"><option value="first">First response</option><option value="second">Second response</option><option value="sum" selected>Sum of both</option></select></label>'
  attrs=' data-values="'+html.escape(json.dumps(values),quote=True)+'"' if values else ''
  accessible=html.escape(title+'. '+re.sub(r'\\\(.*?\\\)', '',caption),quote=True)
  figure=f'''<!-- chapter-visual:start -->
<figure class="chapter-visual" data-visual="{kind}" id="visual-construction">
<h2>{title}</h2>
<canvas role="img" aria-label="{accessible}">{html.escape(title)}</canvas>
<div class="visual-legend">{legend}</div>
<div class="visual-controls"><label>{label}: <span data-stage-value>{values[initial] if values else initial}</span><input type="range" min="{mn}" max="{mx}" value="{initial}" step="1" aria-label="{label}"{attrs}></label>{extra}<button type="button" data-visual-reset>Reset</button></div>
<div class="visual-output" aria-live="polite"></div>
<figcaption>{caption} <a href="#{anchor}">Follow the construction.</a></figcaption>
<noscript><p>{caption}</p></noscript>
</figure>
<!-- chapter-visual:end -->
'''
  if original:
   match=re.search(r'<section class="pedagogical-opening".*?</section>',s,re.S);s=s[:match.end()]+figure+s[match.end():]
  else:
   match=re.search(r'<h2[^>]*>7\.1 ',s);assert match;s=s[:match.start()]+figure+s[match.start():]
  s=s.replace('</head>','<link rel="stylesheet" href="reading/chapter-visuals/visuals.css"><script defer src="reading/chapter-visuals/visuals.js"></script></head>',1)
  assert s.count('id="visual-construction"')==1
  # Existing mathematical statements, proof bodies, anchors and proof links must be unchanged.
  strip=lambda x:re.sub(r'<section class="pedagogical-opening".*?</section>','',x,flags=re.S)
  stripped=s.replace(figure,'').replace('<link rel="stylesheet" href="reading/chapter-visuals/visuals.css"><script defer src="reading/chapter-visuals/visuals.js"></script>','')
  assert strip(stripped)==strip(before),filename
  (ROOT/'chapters'/filename).write_text(s)
  report['chapters'].append({'page':filename,'visual':kind,'title':title,'originalSha256':digest(path),'pageSha256':digest(ROOT/'chapters'/filename),'originalOpening':original[0] if original else None,'mathematicsOutsideOpeningUnchanged':True,'control':{'min':mn,'max':mx,'initial':initial}})
 for p in [*ROOT.glob('*.css'),*ROOT.glob('*.js'),*ROOT.glob('*.py'),*ROOT.glob('chapters/*.html')]:report['artifactHashes'][str(p.relative_to(ROOT))]=digest(p)
 (ROOT/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');return report
if __name__=='__main__':
 import sys
 build(Path(sys.argv[1]));print('Built 15 chapter visuals; original mathematical bodies and anchors preserved.')
