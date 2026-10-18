"""Preserve the public reader, then overlay only the hydrogen showpiece.

The old Pages artifact can expire. Seed a live snapshot from the existing
site backup's complete file inventory, then follow same-site static references.
Never rebuild or copy unrelated working-tree mathematics into the publication.
"""
from concurrent.futures import ThreadPoolExecutor, as_completed
from hashlib import sha256
from html.parser import HTMLParser
from pathlib import Path, PurePosixPath
from urllib.error import HTTPError
from urllib.parse import unquote, urljoin, urlsplit
from urllib.request import Request, urlopen
import json
import re
import shutil
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
BASE = 'https://liuyao12.github.io/computable-analysis/'
ASSETS = ROOT / 'book/hydrogen-showpiece'


class References(HTMLParser):
    def __init__(self):
        super().__init__()
        self.urls = []

    def handle_starttag(self, tag, attrs):
        for key, value in attrs:
            if key in ('href', 'src', 'data-src') and value:
                self.urls.append(value)


def name_for(url, current=BASE):
    target = urlsplit(urljoin(current, url))
    base = urlsplit(BASE)
    if target.netloc != base.netloc or not target.path.startswith(base.path):
        return None
    name = unquote(target.path[len(base.path):])
    if not name or name.endswith('/'):
        name += 'index.html'
    if '..' in PurePosixPath(name).parts or name.startswith('/'):
        return None
    return name


def download(name):
    from urllib.parse import quote
    url = BASE + quote(name, safe='/')
    for attempt in range(3):
        try:
            with urlopen(Request(url, headers={'User-Agent': 'ComputableAnalysis-SitePreservation/1.0'}), timeout=45) as response:
                return name, response.read()
        except HTTPError as error:
            if error.code == 404:
                return name, None
            if attempt == 2:
                raise
        except OSError:
            if attempt == 2:
                raise
        time.sleep(attempt + 1)


def json_paths(value):
    # Source inventories describe repository paths, not deployed URLs.
    # Follow explicitly designated links, rather than interpreting every file
    # in a proof archive's hash manifest as a separate public URL.
    if isinstance(value, list):
        for item in value:
            yield from json_paths(item)
    elif isinstance(value, dict):
        for key, item in value.items():
            if key.lower() in ('url', 'href', 'src', 'downloadurl', 'sourceurl') and isinstance(item, str):
                yield item
            elif isinstance(item, (dict, list)):
                yield from json_paths(item)


def modules_in(value):
    if isinstance(value, dict):
        if isinstance(value.get('module'), str):
            yield value['module']
        for item in value.values():
            yield from modules_in(item)
    elif isinstance(value, list):
        for item in value:
            yield from modules_in(item)


def snapshot(site, inventory=None, resume=False):
    inventory = inventory or ROOT / 'book/modular-dependencies/pages-base.json'
    metadata = json.loads(Path(inventory).read_text())
    pending = set(metadata['preservedCriticalHashes']) | {'index.html', 'reading/book.css', 'reading/book.js'}
    seen, hashes, missing = set(), {}, []
    site.mkdir(parents=True, exist_ok=True)
    while pending:
        batch = sorted(pending - seen)
        if not batch:
            break
        seen.update(batch)
        pending = set()
        with ThreadPoolExecutor(max_workers=32) as pool:
            def retrieve(name):
                cached = site / name
                return (name, cached.read_bytes()) if resume and cached.is_file() else download(name)
            futures = [pool.submit(retrieve, name) for name in batch]
            for future in as_completed(futures):
                name, body = future.result()
                if body is None:
                    missing.append(name)
                    continue
                target = site / name
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(body)
                hashes[name] = sha256(body).hexdigest()
                urls = []
                if name.endswith('.html'):
                    parser = References()
                    parser.feed(body.decode('utf-8'))
                    urls = parser.urls
                elif name.endswith('.json'):
                    data = json.loads(body)
                    urls = list(json_paths(data))
                    if name == 'foundation-story/declarations.json':
                        urls += ['sources/' + module + '.lean' for module in modules_in(data)]
                elif name.endswith('.js'):
                    urls = re.findall(r'''["']([^"'\s<>]+\.(?:html|css|js|json|lean|wasm|svg|png|jpg|pdf|gz|txt|log))["']''', body.decode('utf-8'))
                elif name.endswith('.css'):
                    text = body.decode('utf-8')
                    # Follow actual static loads, not file names inside embedded proof text.
                    urls = re.findall(r'''(?:url\(|fetch\(|import\()[\s"']*([^"'()\s<>]+\.(?:html|css|js|json|wasm|svg|png|jpg|pdf|gz))''', text)
                for url in urls:
                    linked = name_for(url, BASE + name)
                    if linked and linked not in seen:
                        pending.add(linked)
        print('Preserved', len(hashes), 'live files; next references', len(pending), flush=True)
    assert all(name in hashes for name in ('index.html', 'reading/book.css', 'reading/book.js'))
    # Reject a mixed snapshot if a concurrent publication changed the reader.
    assert sha256(download('index.html')[1]).hexdigest() == hashes['index.html'], 'Live index changed during snapshot'
    return hashes, missing


def overlay(site, before):
    manifest = json.loads((ASSETS / 'source-manifest.json').read_text())
    for source in manifest['sources']:
        assert sha256((ASSETS / source['snapshot']).read_bytes()).hexdigest() == source['sha256']
    shutil.copytree(ASSETS, site / 'hydrogen', dirs_exist_ok=True)
    index = site / 'index.html'
    text = index.read_text()
    section = '''<section id="hydrogen-showpiece"><h2>Hydrogen fine structure with explicit errors</h2><p>Exact dimensionless energy gaps for constructed regular Dirac states, with symbolic coupling and proved remainder bounds. Read the model, the inequalities and the precise formal scope.</p><p><a href="hydrogen/">Explore the hydrogen showpiece →</a></p></section>'''
    if 'id="hydrogen-showpiece"' in text:
        text, count = re.subn(r'<section id="hydrogen-showpiece">.*?</section>', section, text, count=1, flags=re.S)
        assert count == 1
    else:
        anchor = '<h2 id="start">'
        assert text.count(anchor) == 1, 'Expected reader insertion point'
        text = text.replace(anchor, section + anchor, 1)
    index.write_text(text)
    for name, digest in before.items():
        if name != 'index.html' and not name.startswith('hydrogen/'):
            assert sha256((site / name).read_bytes()).hexdigest() == digest, name
    report = {'preservedLiveFiles': len(before), 'changedExistingPages': ['index.html'],
              'addedDestination': 'hydrogen/', 'liveBaseHashes': before}
    (site / 'hydrogen/publication.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: only the home page link and hydrogen destination changed', flush=True)


if __name__ == '__main__':
    output = Path(sys.argv[1])
    hashes, missing = snapshot(output, sys.argv[2] if len(sys.argv) > 2 else None, '--resume' in sys.argv)
    overlay(output, hashes)
    (output / 'hydrogen/snapshot-missing.json').write_text(json.dumps(missing, indent=2) + '\n')
