#!/usr/bin/env python3
"""Cold-check the finite rational area model and audit its theorem axioms."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

SOURCE = 'ComputableAnalysis/RationalAreaFoundation.lean'
CHECK = 'scripts/check_rational_area_foundation.lean'
EXPECTED = {
    'area_pythagoras_of_bilinear', 'pythagoras_square_areas',
    'four_triangle_dissection_content', 'similarity_square_content',
    'circle_point_square_content', 'tangent_intersection_supporting_lines',
    'outer_wedge_quadrilateral_content', 'unit_disk_support',
    'wedge_gap_bounds', 'uniform_fan_gap_bound', 'unit_chart_increment_bounds',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--lean', default=shutil.which('lean'))
    args = parser.parse_args()
    root, build = args.source_root.resolve(), args.build_dir.resolve()
    build.mkdir(parents=True, exist_ok=True)
    imports = re.findall(r'^import\s+([^\n]+)', (root/SOURCE).read_text(), re.M)
    assert imports == ['Init.Grind.Ordered.Rat'], imports
    env = dict(os.environ, LEAN_PATH=str(build))
    version = subprocess.check_output([args.lean, '--version'], text=True).strip()
    output = build / 'ComputableAnalysis/RationalAreaFoundation.olean'
    output.parent.mkdir(exist_ok=True)
    for name, command in [
        ('build', [args.lean, '-o', str(output), SOURCE]),
        ('check', [args.lean, CHECK]),
    ]:
        result = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
        (build/(name+'.log')).write_text(result.stdout+result.stderr)
        if result.returncode:
            raise RuntimeError(result.stdout+result.stderr)
    text = (build/'check.log').read_text()
    matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S)
    assert {n.rsplit('.',1)[-1] for n,_ in matches} == EXPECTED, matches
    for name, axioms in matches:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
            'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
    report = {'leanVersion': version, 'coldBuild': True,
              'imports': imports, 'auditedTheorems': [n for n,_ in matches],
              'sourceSha256': {p: hashlib.sha256((root/p).read_bytes()).hexdigest()
                               for p in [SOURCE,CHECK]},
              'scope': 'Finite rational area algebra and sector-fan estimates; no complete polygon-dissection or curved-area-role formalization claimed.'}
    (build/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('PASS: cold rational-only build and eleven theorem-axiom audits.')


if __name__ == '__main__':
    main()
