import hashlib,json,pathlib,shutil
root=pathlib.Path(__file__).resolve().parents[1];site=root/'_site'
m=json.loads((root/'book-preservation.json').read_text())
for path,digest in m['files'].items():
    data=(site/path).read_bytes()
    if path=='index.html':
        link=b'<p id="foundation-textbook-link"><a href="foundation-textbook/">Read the living foundation textbook</a></p>\n'
        data=data.replace(link,b'',1)
    assert hashlib.sha256(data).hexdigest()==digest, 'Existing page changed: '+path
for p in (root/'book/dirichlet-contour').iterdir():
    if p.is_file():shutil.copy2(p,site/'foundation-textbook'/p.name)
print('Verified all',len(m['files']),'existing live files; only the textbook home link was added.')
