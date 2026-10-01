#!/usr/bin/env python3
"""Reproducible source inventory; pending zero certificates have no score."""
import argparse
import hashlib
from html import escape
from urllib.parse import urlsplit
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


def load_targets(path):
    """Load reference metadata only; it cannot assert a proved certificate."""
    data = json.loads(path.read_text())
    if not isinstance(data, dict) or data.get('schemaVersion') != 1 or not isinstance(data.get('targets'), list):
        raise ValueError('Expected target registry schema 1 with a targets list')
    targets = []
    seen = set()
    for row in data['targets']:
        if not isinstance(row, dict):
            raise ValueError('Registry entries must be objects')
        if set(row) - {'ordinal', 'approximateImaginaryPart', 'numericalReference'}:
            raise ValueError('Registry entries may contain only numerical target metadata')
        ordinal = row.get('ordinal')
        if type(ordinal) is not int or ordinal < 1 or ordinal in seen:
            raise ValueError('Target ordinals must be distinct positive integers')
        seen.add(ordinal)
        height = row.get('approximateImaginaryPart')
        if height is not None and (not isinstance(height, str) or
                not re.fullmatch(r'(?:0|[1-9][0-9]*)\.[0-9]+', height) or
                not any(c in '123456789' for c in height)):
            raise ValueError('Approximate heights must be positive decimal strings or null')
        reference = row.get('numericalReference')
        if height is not None and not reference:
            raise ValueError('A numerical height requires a reference URL')
        if reference is not None and (not isinstance(reference, str) or
                urlsplit(reference).scheme != 'https' or not urlsplit(reference).netloc):
            raise ValueError('Numerical references must be HTTPS URLs or null')
        targets.append(dict(ordinal=ordinal, approximateImaginaryPart=height,
            numericalReference=reference))
    return sorted(targets, key=lambda row: row['ordinal'])


def build_report(root, revision, targets_path=None):
    targets_path = targets_path or root / 'book/zeta-zeros/benchmark-targets.json'
    targets = load_targets(targets_path)
    module = 'ComputableAnalysis.ZeroIsolation'
    measured = inventory(root, module)
    root_law = inventory(root, 'ComputableAnalysis.ZeroFromEnclosures')
    return dict(schemaVersion=3, documentationRevision=revision,
        metric='Nonblank physical Lean source lines after removing nested comments; includes imports and namespaces.',
        closureScope='All declarations in project-local transitive import files, not a minimized theorem dependency slice. External library sources are excluded and listed.',
        sourceInventoryIsProofVerification=False, concreteZetaZerosCertified=0,
        targetRegistrySha256=hashlib.sha256(targets_path.read_bytes()).hexdigest(),
        scope=dict(ordinalUpperLimit=None, registryEntriesAreCertificates=False,
            finiteHeightCompletenessProved=False,
            completenessStatus='Individual targets do not establish a complete ordinal prefix or exclude omitted zeros below a height.'),
        comparison=dict(metric='Additional Lean code lines for each zero, excluding the shared baseline for every ordinal, including the first.',
            sharedBaselineExcluded=True, generatedCertificateDataCountedAsCode=False),
        shared=dict(baselineProofCodeLines=None, baselineStatus='Complete shared zeta-certification machinery not yet implemented.',
            module=module, theorem='ComputableAnalysis.FunctionTheory.ZeroIsolation.unique_zero_on_line',
            status='Checked conditional reflection-and-uniqueness implication; no concrete zeta certificate.',
            direct=measured['files']['ComputableAnalysis/ZeroIsolation.lean'],
            rootConstruction=dict(module='ComputableAnalysis.ZeroFromEnclosures',
                status='Checked conditional enclosure-to-root and line-location laws; concrete zeta bounds not supplied.',
                direct=root_law['files']['ComputableAnalysis/ZeroFromEnclosures.lean'], **root_law), **measured),
        targets=[dict(**target, numericalReferenceIsRepositoryCertificate=False,
            status='Formal certificate not yet implemented', additionalProofCodeLines=None,
            sharedBaselineExcluded=True, certificateBytes=None, kernelCheckSeconds=None,
            exactLineLocationProved=False, simplicityProved=False,
            ordinalCompletenessProved=False) for target in targets])


def render_table(report):
    direct = report['shared']['direct']['codeLines']
    closure = report['shared']['projectClosureCodeLines']
    root_loc = report['shared']['rootConstruction']['direct']['codeLines']
    rows = ''
    for row in report['targets']:
        height = (rf'\({escape(row["approximateImaginaryPart"])}\)'
            if row['approximateImaginaryPart'] is not None else 'Not supplied')
        rows += (rf'<tr><td>Zero \(n={row["ordinal"]}\)</td><td>{height}</td>'
            '<td>Pending</td><td>Pending</td><td>Pending</td>'
            '<td>Formal certificate pending</td></tr>')
    return f'''<div class="numeric-scroll"><table id="zeta-zero-shared-table">
<thead><tr><th>Shared setup</th><th>Lean code lines</th><th>Status</th></tr></thead>
<tbody><tr><td>Complete shared zeta-certification machinery</td><td>Pending</td><td>Not yet constructed</td></tr>
<tr><td>Existing conditional reflection module</td><td>{direct}</td><td>Conditional law checked; one component of the setup</td></tr>
<tr><td>Enclosure-to-root construction laws</td><td>{root_loc}</td><td>Conditional laws checked; actual zeta enclosures pending</td></tr></tbody></table></div>
<p>The conditional module's project-local import closure contains {closure:,} code lines. This conservative file-level inventory includes every declaration in those import files; it is not the size of a minimal proof or the complete shared zeta-certification setup. External library source is excluded and listed in the report. Source counting itself does not verify a theorem.</p>
<div class="numeric-scroll"><table id="zeta-zero-benchmark-table">
<caption>Per-zero comparison: additional code only, excluding the shared setup for every zero.</caption>
<thead><tr><th>Zero certification</th><th>Imaginary part (approx.)</th><th>Additional Lean code lines</th><th>Certificate bytes</th><th>Kernel-check time</th><th>Status</th></tr></thead>
<tbody>{rows}</tbody></table></div>
<p>The imaginary parts are rounded numerical reference values from <a href="https://www.lmfdb.org/zeros/zeta/">LMFDB's zero table</a>. They identify the targets; they are not repository proof certificates. “Pending” refers to the formal certification and its code-size, certificate-size and timing measurements.</p>'''


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--revision', default='working-tree')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--targets', type=Path, help='Reference target registry; accepts any positive ordinal, with no fixed upper limit')
    args = parser.parse_args()
    encoded = json.dumps(build_report(args.root.resolve(), args.revision, args.targets), indent=2) + '\n'
    if args.output: args.output.write_text(encoded)
    else: print(encoded, end='')
