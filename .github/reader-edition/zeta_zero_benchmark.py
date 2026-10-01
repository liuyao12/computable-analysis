#!/usr/bin/env python3
"""Reproducible source inventory; pending zero certificates have no score."""
import argparse
import hashlib
import json
import re
from pathlib import Path


def uncomment(source):
    """Remove nested Lean comments, preserving strings and physical newlines."""
    out = []
    i = depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith('/-', i):
                depth += 1; i += 2
            elif source.startswith('-/', i):
                depth -= 1; i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(source[i])
            if source[i] == '\\' and i + 1 < len(source):
                i += 1; out.append(source[i])
            elif source[i] == '"':
                quoted = False
            i += 1
        elif source.startswith('/-', i):
            depth = 1; out.extend('  '); i += 2
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end == -1: break
            out.extend(' ' * (end - i)); i = end
        else:
            char = re.match(r"'(?:\\.|[^'\\\n])'", source[i:]) if source[i] == "'" else None
            if char:
                out.extend(char[0]); i += len(char[0])
            else:
                quoted = source[i] == '"'
                out.append(source[i]); i += 1
    if depth: raise ValueError('Unclosed Lean block comment')
    return ''.join(out)


def inventory(root, module):
    files = {}
    external = set()
    def visit(name):
        path = root / (name.replace('.', '/') + '.lean')
        if not path.is_file():
            if name.startswith('ComputableAnalysis'):
                raise FileNotFoundError(path)
            external.add(name); return
        relative = path.relative_to(root).as_posix()
        if relative in files: return
        data = path.read_bytes()
        code = uncomment(data.decode())
        files[relative] = dict(physicalLines=len(data.decode().splitlines()),
            codeLines=sum(bool(line.strip()) for line in code.splitlines()),
            bytes=len(data), sha256=hashlib.sha256(data).hexdigest())
        for imports in re.findall(r'^\s*import\s+([^\n]+)', code, re.M):
            for dependency in imports.split(): visit(dependency)
    visit(module)
    return dict(files=dict(sorted(files.items())), externalImports=sorted(external),
        projectClosureCodeLines=sum(f['codeLines'] for f in files.values()))


def build_report(root, revision):
    module = 'ComputableAnalysis.ZeroIsolation'
    measured = inventory(root, module)
    return dict(schemaVersion=2, documentationRevision=revision,
        metric='Nonblank physical Lean source lines after removing nested comments; includes imports and namespaces.',
        closureScope='All declarations in project-local transitive import files, not a minimized theorem dependency slice. External library sources are excluded and listed.',
        sourceInventoryIsProofVerification=False, concreteZetaZerosCertified=0,
        comparison=dict(metric='Additional Lean code lines for each zero, excluding the shared baseline for every ordinal, including the first.',
            sharedBaselineExcluded=True, generatedCertificateDataCountedAsCode=False),
        shared=dict(baselineProofCodeLines=None, baselineStatus='Complete shared zeta-certification machinery not yet implemented.',
            module=module, theorem='ComputableAnalysis.FunctionTheory.ZeroIsolation.unique_zero_on_line',
            status='Checked conditional reflection-and-uniqueness implication; no concrete zeta certificate.',
            direct=measured['files']['ComputableAnalysis/ZeroIsolation.lean'], **measured),
        targets=[dict(ordinal=k, status='Not yet implemented', additionalProofCodeLines=None,
            sharedBaselineExcluded=True, certificateBytes=None, kernelCheckSeconds=None,
            ordinalCompletenessProved=False) for k in [1, 2]])


def render_table(report):
    direct = report['shared']['direct']['codeLines']
    closure = report['shared']['projectClosureCodeLines']
    return f'''<div class="numeric-scroll"><table id="zeta-zero-shared-table">
<thead><tr><th>Shared setup</th><th>Lean code lines</th><th>Status</th></tr></thead>
<tbody><tr><td>Complete shared zeta-certification machinery</td><td>Pending</td><td>Not yet constructed</td></tr>
<tr><td>Existing conditional reflection module</td><td>{direct}</td><td>Conditional law checked; one component of the setup</td></tr></tbody></table></div>
<p>The conditional module's project-local import closure contains {closure:,} code lines. This conservative file-level inventory includes every declaration in those import files; it is not the size of a minimal proof or the complete shared zeta-certification setup. External library source is excluded and listed in the report. Source counting itself does not verify a theorem.</p>
<div class="numeric-scroll"><table id="zeta-zero-benchmark-table">
<caption>Per-zero comparison: additional code only, excluding the shared setup for both zeros.</caption>
<thead><tr><th>Zero certification</th><th>Additional Lean code lines</th><th>Certificate bytes</th><th>Kernel-check time</th><th>Status</th></tr></thead>
<tbody><tr><td>First positive-height zero</td><td>Pending</td><td>Pending</td><td>Pending</td><td>Not yet certified here</td></tr>
<tr><td>Second positive-height zero</td><td>Pending</td><td>Pending</td><td>Pending</td><td>Pending</td><td>Not yet certified here</td></tr></tbody></table></div>'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--revision', default='working-tree')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    encoded = json.dumps(build_report(args.root.resolve(), args.revision), indent=2) + '\n'
    if args.output: args.output.write_text(encoded)
    else: print(encoded, end='')
