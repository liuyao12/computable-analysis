"""Keep the manuscript preface aligned with the published reader text."""
from html.parser import HTMLParser
from pathlib import Path
import argparse
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
        self.pre = False
        self.column = 0
        self.bold_cell = False

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'h1':
            self.output.append('\\chapter*{')
        elif tag == 'h2':
            self.output.append('\n\\section*{')
            self.section = attrs['id']
        elif tag == 'p':
            self.output.append('\n')
        elif tag == 'pre':
            self.pre = True
            self.output.append('\n\\begin{verbatim}\n')
        elif tag == 'code' and self.pre:
            pass
        elif tag in ['code', 'strong', 'em']:
            self.output.append({'code': '\\texttt{', 'strong': '\\textbf{', 'em': '\\emph{'}[tag])
        elif tag == 'a':
            url = attrs['href']
            if not url.startswith('https:'):
                url = 'https://liuyao12.github.io/computable-analysis/' + url
            self.output.append('\\href{' + url.replace('#', '\\#') + '}{')
        elif tag == 'table':
            self.output.append('\n\\begin{center}\n\\small\n\\begin{tabular}{rll}\n\\hline\n')
        elif tag == 'tr':
            self.column = 0
        elif tag in ['th', 'td']:
            if self.column:
                self.output.append(' & ')
            self.column += 1
            self.bold_cell = tag == 'th' and attrs.get('scope') == 'col'
            if self.bold_cell:
                self.output.append('\\textbf{')
        elif tag == 'mark':
            self.output.append('\\fbox{')
        elif tag == 'span':
            if 'id' in attrs:
                self.output.append('\\label{preface:' + attrs['id'] + '}')
        elif tag in ['div', 'thead', 'tbody']:
            pass
        else:
            raise ValueError('Unsupported preface element: ' + tag)

    def handle_endtag(self, tag):
        if tag == 'h1':
            self.output.append('}\n\\addcontentsline{toc}{chapter}{Preface}\n\\label{ch:preface}\n')
        elif tag == 'h2':
            self.output.append('}\n\\label{preface:' + self.section + '}\n')
        elif tag == 'code' and self.pre:
            pass
        elif tag in ['code', 'strong', 'em', 'a', 'mark']:
            self.output.append('}')
        elif tag == 'p':
            self.output.append('\n')
        elif tag == 'pre':
            self.output.append('\n\\end{verbatim}\n')
            self.pre = False
        elif tag in ['th', 'td']:
            if self.bold_cell:
                self.output.append('}')
            self.bold_cell = False
        elif tag == 'tr':
            self.output.append(' \\\\\n')
        elif tag == 'thead':
            self.output.append('\\hline\n')
        elif tag == 'table':
            self.output.append('\\hline\n\\end{tabular}\n\\end{center}\n')

    def handle_data(self, text):
        self.output.append(text if self.pre else escape(text))


def render(source):
    parser = Latex()
    parser.feed(source)
    text = ''.join(parser.output)
    assert text.count('\\(') == text.count('\\)')
    assert text.count('\\[') == text.count('\\]')
    assert text.count('{') == text.count('}')
    assert text.count('\\begin{tabular}') == text.count('\\end{tabular}')
    assert text.count('\\begin{verbatim}') == text.count('\\end{verbatim}')
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    target = ROOT / 'blueprint/src/00-preface.tex'
    text = render((ROOT / 'book/foundation-preface/content.html').read_text())
    if args.check:
        assert target.read_text() == text, 'Regenerate the manuscript before publishing'
    else:
        target.write_text(text)
    print('PASS: preface manuscript matches the reader, with balanced math, tables, and pseudocode')


if __name__ == '__main__':
    main()
