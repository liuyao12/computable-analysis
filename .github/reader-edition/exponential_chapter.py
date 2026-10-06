#!/usr/bin/env python3
"""Render the exponential chapter and package its checked native source closure.

Only the chapter page and its proof bundle are overlaid on the existing reader.
"""
import argparse
import hashlib
import html
import json
import re
import shutil
import zipfile
from pathlib import Path

CORE = 'ComputableAnalysis.ExponentialComputations.API'
NAMESPACE = 'ComputableAnalysis.ExponentialComputations.'
ENDPOINTS = [
    'compoundValue_equiv_powerSeries', 'Implementation.equivalent',
    'representedTaylor_agrees', 'exp_positive', 'exp_injective', 'log_exp',
    'exp_log', 'logChart_derivative', 'integralLog_hasIntegral',
    'integralLog_equiv_log', 'integralLog_exp', 'exp_integralLog',
    'integralLog_congr', 'real_computation_agrees_of_integral_inverse',
]
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def closure(roots):
    pending = list(roots)
    result, external = {}, set()
    while pending:
        module = pending.pop()
        if module in result:
            continue
        source = Path(module.replace('.', '/') + '.lean')
        data = source.read_bytes()
        result[module] = data
        for dep in re.findall(r'^import\s+(\S+)', data.decode(), re.M):
            if dep.startswith('ComputableAnalysis.'):
                pending.append(dep)
            else:
                external.add(dep)
    assert external <= {'Init', 'Init.Grind.Ordered.Rat'}, external
    return result, sorted(external)


def audit_core(audit):
    text = audit.read_text()
    assert 'error:' not in text and 'sorryAx' not in text
    for endpoint in ENDPOINTS:
        match = re.search("'" + re.escape(NAMESPACE + endpoint) +
                          r"' depends on axioms: \[([^]]*)\]", text)
        assert match, endpoint
        assert set(re.findall(r'[\w.]+', match[1])) <= STANDARD_AXIOMS, endpoint
    return text


def inline(text):
    parts = re.split(r'(\$[^$]*\$|\\\([^)]*\\\))', text, flags=re.S)
    output = []
    for part in parts:
        if part.startswith('$') and part.endswith('$'):
            output.append('\\(' + html.escape(part[1:-1]) + '\\)')
        elif part.startswith('\\('):
            output.append(html.escape(part))
        else:
            part = html.escape(part)
            part = re.sub(r'\\texttt\{([^{}]+)\}', r'<code>\1</code>', part)
            output.append(part)
    return ''.join(output)


def source_link(name, sources):
    hits = []
    for module, data in sources.items():
        namespace, scopes = '', []
        for line_number, line in enumerate(data.decode().splitlines(), 1):
            ns = re.match(r'namespace\s+(\S+)', line)
            section = re.match(r'(?:noncomputable\s+)?section(?:\s+\S+)?\s*$', line)
            if ns:
                scopes.append(namespace)
                namespace = namespace+'.'+ns[1] if namespace else ns[1]
            elif section:
                scopes.append(namespace)
            elif re.match(r'end(?:\s+\S+)?\s*$', line):
                if scopes:
                    namespace = scopes.pop()
            decl = re.match(r'(?:theorem|def|abbrev|structure)\s+(\w+)', line)
            if decl and namespace+'.'+decl[1] == name:
                hits.append((module,line_number))
    assert len(hits) == 1, (name,hits)
    module, line = hits[0]
    return f'exponential-chapter/source-view/{module}.html#L{line}'


def render_tex(tex, sources):
    tex = re.sub(r'\\chapter\{[^}]+\}\\label\{[^}]+\}', '', tex, count=1).strip()
    tex = re.sub(r'\\label\{[^}]+\}', '', tex)
    tokens = re.split(r'(\\section\{[^}]+\}|\\\[.*?\\\]|'
                      r'\\begin\{theorem\}\[[^]]+\]|\\end\{theorem\}|'
                      r'(?:\\lean\{[^}]+\}\s*)+\\leanok)', tex, flags=re.S)
    result, navigation, section = [], [], 0
    for token in tokens:
        token = token.strip()
        if not token:
            continue
        if token.startswith('\\section'):
            section += 1
            title = re.fullmatch(r'\\section\{([^}]+)\}', token)[1]
            ident = f'section-{section}'
            result.append(f'<h2 id="{ident}">7.{section} {inline(title)}</h2>')
            navigation.append(f'<a href="#{ident}">7.{section} {inline(title)}</a>')
        elif token.startswith('\\['):
            result.append('<div class="displaymath">' + html.escape(token) + '</div>')
        elif token.startswith('\\begin{theorem}'):
            title = re.search(r'\[([^]]+)\]', token)[1]
            result.append('<section class="exp-theorem"><h3>' + html.escape(title) + '</h3>')
        elif token == '\\end{theorem}':
            result.append('</section>')
        elif token.startswith('\\lean{'):
            names = re.findall(r'\\lean\{([^}]+)\}', token)
            items = ''.join(f'<li><a href="{source_link(n, sources)}"><code>{html.escape(n)}</code></a></li>'
                            for n in names)
            result.append(f'<details class="exp-proof"><summary>Lean proof · {len(names)} declarations</summary><ul>{items}</ul></details>')
        else:
            for paragraph in re.split(r'\n\s*\n', token):
                result.append('<p>' + inline(re.sub(r'\s+', ' ', paragraph)) + '</p>')
    rendered = '\n'.join(result)
    assert not re.search(r'\\(?:lean|leanok|section|label|begin|end)\b', rendered)
    assert section == 7
    return rendered, ''.join(navigation)


def install(site, output, audit, declarations, runtime, build, constants_audit):
    log = audit_core(audit)
    core, external = closure([CORE])
    sources, _ = closure([CORE, 'ComputableAnalysis.ExponentialComputations.Constants',
                          'ComputableAnalysis.FiniteExponentialTaylor'])
    assert len(core) >= 14
    for module, data in sources.items():
        if module.startswith('ComputableAnalysis.ExponentialComputations.') or module.endswith('.RealExponentialCore'):
            assert not re.search(r'\b(?:sorry|admit|native_decide)\b|^axiom\s', data.decode(), re.M), module
    tex = Path('blueprint/src/05-exponential-logarithm.tex').read_text()
    names = re.findall(r'\\lean\{([^}]+)\}', tex)
    decl_log = declarations.read_text()
    assert 'error:' not in decl_log and all(n in decl_log for n in names)
    assert runtime.read_text().splitlines() == ['true','true'], runtime.read_text()
    template = (site / 'ch-exponential-logarithm.html').read_text()
    body, navigation = render_tex(tex, sources)
    main_start = template.index('<div class="main-text">') + len('<div class="main-text">')
    main_end = template.index('</div></article>', main_start)
    opening = '''<h1 id="ch:exponential-logarithm">Exponential and Logarithm</h1>
<p class="exp-status">Checked global identities on represented inputs · 6 October 2026</p>'''
    template = template[:main_start] + opening + body + template[main_end:]
    template = re.sub(r'(<aside class="on-this-page">).*?(</aside>)',
                      r'\1<span>On this page</span>' + navigation + r'\2', template, flags=re.S)
    template = re.sub(r'<footer class="chapter-footer">.*?</footer>',
        '<footer class="chapter-footer"><span>Checked chapter core · native computable foundation</span>'
        '<a href="exponential-chapter/index.html">Proof sources and audit ↗</a></footer>', template, flags=re.S)
    template = re.sub(r'<meta[^>]+name="documentation-revision"[^>]*?/>', '', template)
    css = '''<style>.exp-status{font:12px/1.6 system-ui;color:var(--muted);border-left:3px solid #71856b;padding-left:12px}
.exp-theorem{margin:28px 0;padding:18px 22px;background:#f1f4ed;border-left:3px solid #71856b}
.exp-theorem h3{margin-top:0}.exp-proof{font:12px/1.6 system-ui;margin:15px 0;color:var(--muted)}
.exp-proof summary{cursor:pointer}.exp-proof li{margin:7px 0;overflow-wrap:anywhere}
.exp-proof code{font-size:11px}.exp-theorem .exp-proof{margin:10px 0}
@media(max-width:720px){.exp-theorem{padding:14px}.exp-proof code{font-size:10px}}</style>'''
    template = template.replace('</head>', css + '</head>')
    assert 'MathJax' in template and '<sup>' not in template and '<sub>' not in template
    assert 'Factorial prefixes' not in template
    output.mkdir(parents=True, exist_ok=True)
    (output / 'ch-exponential-logarithm.html').write_text(template)
    bundle = output / 'exponential-chapter';bundle.mkdir(exist_ok=True)
    for module, data in sources.items():
        target = bundle / 'sources' / (module.replace('.', '/') + '.lean')
        target.parent.mkdir(parents=True, exist_ok=True);target.write_bytes(data)
    for name in names:
        link = source_link(name,sources)
        module = link.split('/source-view/')[1].split('.html')[0]
        view = bundle/'source-view'/(module+'.html')
        if view.exists():
            continue
        view.parent.mkdir(parents=True,exist_ok=True)
        rows = ''.join(f'<span id="L{i}"><a href="#L{i}">{i:4}</a> {html.escape(line)}</span>\n'
                       for i,line in enumerate(sources[module].decode().splitlines(),1))
        view.write_text('<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>'+module+'</title><style>body{margin:24px;background:#fbfaf6;color:#252b27}pre{font:12px/1.65 monospace;white-space:pre;overflow-x:auto}pre span{display:block}pre span:target{background:#fff2b8}a{color:#466442}pre a{color:#999;text-decoration:none}</style></head><body><a href="../index.html">Proof bundle</a><h1 style="font:18px system-ui">'+module+'</h1><pre>'+rows+'</pre></body></html>')
    shutil.copy(audit, bundle/'core-audit.log')
    assert 'Build completed successfully' in build.read_text()
    shutil.copy(build,bundle/'focused-build.log')
    assert 'error:' not in constants_audit.read_text()
    shutil.copy(constants_audit,bundle/'legacy-constants-audit.log')
    shutil.copy(declarations, bundle/'chapter-declarations.log')
    shutil.copy(runtime, bundle/'runtime.log')
    shutil.copy('scripts/check_exponential_computations.lean', bundle/'check_exponential_computations.lean')
    shutil.copy('scripts/check_exponential_computations_runtime.lean', bundle/'check_exponential_computations_runtime.lean')
    shutil.copy('blueprint/src/05-exponential-logarithm.tex', bundle/'chapter.tex')
    shutil.copy('lean-toolchain', bundle/'lean-toolchain')
    shutil.copy('lakefile.toml', bundle/'lakefile.toml')
    shutil.copy('lake-manifest.json', bundle/'lake-manifest.json')
    new_modules = sorted(m for m in sources if m.startswith('ComputableAnalysis.ExponentialComputations.'))
    links = ''.join('<li><a href="sources/'+m.replace('.', '/')+'.lean"><code>'+m+'</code></a></li>' for m in new_modules)
    bundle_page = '''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Exponential chapter · proof audit</title><link rel="stylesheet" href="../reading/book.css"></head><body>
<main style="max-width:900px;margin:40px auto;padding:0 24px"><a href="../ch-exponential-logarithm.html">← Exponential and logarithm</a>
<h1>Proof sources and audit</h1><p>The chapter core has checked global agreement, representation invariance,
reciprocal integral evidence, and both inverse laws. Its 14 audited endpoints use only
<code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code>.
The source import closure uses Lean's native foundation and no Mathlib.</p>
<p>The separate legacy constant compatibility module inherits older native arithmetic proof dependencies.
The chapter does not claim an independent exponential evaluator based on integral-only bisection,
or an agreement theorem for the older named <code>logTwoSeries</code>.</p>
<p>These are content-hashed snapshots of the exact local proof sources used for this chapter,
including their transitive imports. They preserve the source scope independently of unrelated repository work.</p>
<ul><li><a href="core-audit.log">Core theorem types and axiom audit</a></li>
<li><a href="chapter-declarations.log">Every chapter declaration checked by Lean</a></li>
<li><a href="runtime.log">Reciprocal quadrature runtime checks</a></li>
<li><a href="focused-build.log">Successful focused Lake build</a></li>
<li><a href="legacy-constants-audit.log">Separate legacy constant axiom audit</a></li>
<li><a href="manifest.json">Source hashes and verification manifest</a></li>
<li><a href="chapter.tex">Chapter manuscript</a></li>
<li><a href="sources.zip">Complete Lean source snapshot (ZIP)</a></li></ul>
<h2>Chapter modules</h2><ul>'''+links+'''</ul>
<p>To replay the core audit, extract the source archive into a separate directory, install the
version in <code>lean-toolchain</code>, and run <code>lake build ComputableAnalysis.ExponentialComputations.API</code>,
then <code>lake env lean check_exponential_computations.lean</code>.
The snapshot has no umbrella import: only this chapter's dependency closure is included.
The full repository build encountered errors in the unrelated <code>FiniteQuarticQuadraticSplit</code> module;
the focused chapter build completed successfully.</p></main></body></html>'''
    (bundle/'index.html').write_text(bundle_page)
    report = dict(checkedEndpoints=[NAMESPACE+n for n in ENDPOINTS],
                  coreAxioms=sorted(STANDARD_AXIOMS), coreImportModules=len(core),
                  focusedLakeBuildPassed=True, fullRepositoryBuildPassed=False,
                  fullRepositoryBuildFailure='FiniteQuarticQuadraticSplit: unknown qcomplexQuadraticPolynomial',
                  snapshotModules=len(sources), externalImports=external,
                  mathlibDependency=False, representedInputDomain='all valid real/complex; logarithm strictly positive real',
                  independentReciprocalQuadrature=True, independentIntegralOnlyExponentialBackend=False,
                  legacyConstantCompatibilityHasNativeArithmeticDependencies=True,
                  namedLegacyLogTwoSeriesAgreement=False,
                  manuscriptSha256=digest(tex.encode()),
                  sourceHashes={m:digest(d) for m,d in sorted(sources.items())},
                  coreAuditSha256=digest(log.encode()),
                  chapterHtmlSha256=digest(template.encode()))
    (bundle/'manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    with zipfile.ZipFile(bundle/'sources.zip','w',compression=zipfile.ZIP_DEFLATED) as archive:
        for module,data in sorted(sources.items()):
            archive.writestr(module.replace('.','/')+'.lean',data)
        for name in ['lean-toolchain','lakefile.toml','lake-manifest.json',
                     'check_exponential_computations.lean','check_exponential_computations_runtime.lean',
                     'manifest.json','core-audit.log','chapter-declarations.log','runtime.log',
                     'focused-build.log','legacy-constants-audit.log']:
            archive.writestr(name,(bundle/name).read_bytes())
    print(f'PASS: {len(ENDPOINTS)} core audits, {len(names)} chapter declarations, {len(core)} native core imports; {len(sources)} source snapshots')


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    for name in ['site','output','audit','declarations','runtime','build','constants-audit']:
        p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();install(a.site,a.output,a.audit,a.declarations,a.runtime,a.build,a.constants_audit)
