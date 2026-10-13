"""Keep the manuscript preface aligned with the published reader text."""
from html.parser import HTMLParser
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]

def escape(text):
    parts = re.split(r'(\\\(.*?\\\)|\\\[.*?\\\])', text, flags=re.S)
    return ''.join(part if part.startswith(('\\(', '\\[')) else re.sub(r'([&%$#_{}])', r'\\\1', part) for part in parts)

class Latex(HTMLParser):
    def __init__(self):
        super().__init__()
        self.output = []
        self.section = ''

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'h1': self.output.append('\\chapter*{')
        elif tag == 'h2':
            self.output.append('\n\\section*{')
            self.section = attrs['id']
        elif tag == 'p': self.output.append('\n')
        elif tag in ['code', 'strong', 'em']:
            self.output.append({'code': '\\texttt{', 'strong': '\\textbf{', 'em': '\\emph{'}[tag])
        elif tag == 'a':
            url = attrs['href']
            if not url.startswith('https:'):
                url = 'https://liuyao12.github.io/computable-analysis/' + url
            self.output.append('\\href{' + url.replace('#', '\\#') + '}{')
        else: raise ValueError('Unsupported preface element: ' + tag)

    def handle_endtag(self, tag):
        if tag == 'h1': self.output.append('}\n\\addcontentsline{toc}{chapter}{Preface}\n\\label{ch:preface}\n')
        elif tag == 'h2': self.output.append('}\n\\label{preface:' + self.section + '}\n')
        elif tag in ['code', 'strong', 'em', 'a']: self.output.append('}')
        elif tag == 'p': self.output.append('\n')

    def handle_data(self, text): self.output.append(escape(text))

parser = Latex()
parser.feed((ROOT / 'book/foundation-preface/content.html').read_text())
text = ''.join(parser.output)
assert text.count('\\(') == text.count('\\)')
assert text.count('\\[') == text.count('\\]')
assert text.count('{') == text.count('}')
(ROOT / 'blueprint/src/00-preface.tex').write_text(text)
print('PASS: preface manuscript generated with balanced LaTeX delimiters and braces')
