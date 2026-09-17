"""Validate transported source bytes, then commit the readable sources on the feature branch."""
import bz2
import hashlib
import os
import pathlib
import subprocess

BASE = 'f7f132a3e6637d778db537e1503f5106bdcc1a31'
subprocess.run(['git', 'merge-base', '--is-ancestor', BASE, 'HEAD'], check=True)
EXPECTED = [
    'ea08443579b0cbe0eef19ea5d8493b0743986e66',
    '81f0617335f1d74a364c77b7de25a80b36a51ed2',
    '0956940fc05a8c9a2b080b6593bf1c0819440dff',
    '9d1eaac3d1c9419d01bec3046eeaac6dfeb14c97',
    '93ab9689b5b8920b6e4a1cf46c1cfb12b544e9e1',
    'f6bcb8c9416b63bd717ca48165d27d021ce8c30e',
    'e5ea5f0a7d611c83c4d8c612bbb05439e4e0b2f3',
    '338c292e9ad95da3b2b0edfb365934acde397d10',
]
parts = []
for i, expected in enumerate(EXPECTED):
    b = bytearray(pathlib.Path(f'.github/payloads/integral-portfolio.{i}.bzpart').read_bytes())
    if i == 3:
        # Restore one known base64 transcription error, then check the ORIGINAL hash.
        assert b[7483] == 93
        b[7483] = 94
    assert hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest() == expected, i
    parts.append(bytes(b))
packed = b''.join(parts)
assert len(packed) == 71588
assert hashlib.sha256(packed).hexdigest() == '7dfada4a8846f78858c6b892d41dee817c45662deb20e758cad93147d4aa216f'
patch = bz2.decompress(packed)
assert len(patch) == 387570
assert hashlib.sha256(patch).hexdigest() == 'd523a869e2655cb14b210e24d56faa3dc5dd245968a4179b94929b820b184fa4'
text = patch.decode('utf-8')
paths = []
for line in text.splitlines():
    if not line.startswith('diff --git '):
        continue
    left, right = line[len('diff --git '):].split(' ')
    assert left.startswith('a/') and right.startswith('b/')
    path = right[2:]
    assert path == left[2:] and '..' not in pathlib.PurePosixPath(path).parts
    assert path in ['.gitignore', 'FORMALIZATION_GUIDE.md', 'GOALS.md'] or path.startswith((
        'ComputableAnalysis/', 'book/', 'comparison/MathlibComparison/', 'comparison/checks/')), path
    paths.append(path)
assert len(paths) == 58, len(paths)
assert 'new file mode 120000' not in text and 'new file mode 160000' not in text
p = pathlib.Path('/tmp/integral-portfolio.patch')
p.write_bytes(patch)
check = subprocess.run(['git', 'apply', '--check', str(p)], capture_output=True)
if check.returncode == 0:
    subprocess.run(['git', 'apply', str(p)], check=True)
    subprocess.run(['git', 'add', '--', *paths], check=True)
    subprocess.run(['git', 'config', 'user.name', 'github-actions[bot]'], check=True)
    subprocess.run(['git', 'config', 'user.email', '41898282+github-actions[bot]@users.noreply.github.com'], check=True)
    subprocess.run(['git', 'commit', '-m', 'Add checked Cartwright proofs and paired Wallis/beta integral applications'], check=True)
    subprocess.run(['git', 'push', 'origin', 'HEAD:refs/heads/work/integral-portfolio'], check=True)
else:
    # A rerun may encounter the already materialized source, but not a conflict.
    subprocess.run(['git', 'apply', '--reverse', '--check', str(p)], check=True)
subprocess.run(['git', 'diff', '--check'], check=True)
sha = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
with open(os.environ['GITHUB_ENV'], 'a') as f:
    f.write('SOURCE_SHA=' + sha + '\n')
print('Readable source snapshot:', sha, '; validated files:', len(paths))
