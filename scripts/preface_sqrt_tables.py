"""Generate abbreviated decimal displays of the preface's exact rational bounds."""
from fractions import Fraction
from pathlib import Path
import argparse
import html
import re

ROOT = Path(__file__).resolve().parents[1]
CONTENT = ROOT / 'book/foundation-preface/content.html'


def decimal(q, places, upper=False):
    scale = 10 ** places
    units = (q.numerator * scale + (q.denominator - 1 if upper else 0)) // q.denominator
    if not places:
        return str(units)
    return f'{units // scale}.{units % scale:0{places}d}'


def display(value, highlighted):
    prefix, suffix = value[:highlighted], value[highlighted:highlighted + 1]
    parts = []
    if prefix:
        parts.append(r'\mathbf{' + prefix + '}')
    if suffix:
        parts.append(r'\mathrm{' + suffix + r'}\ldots')
    label = prefix + suffix + ('...' if suffix else '')
    return '<span class="decimal-number" aria-label="' + html.escape(label) + '">\\(' + ''.join(parts) + '\\)</span>'


def rows():
    l, u = Fraction(1), Fraction(2)
    previous = None
    result = []
    for n in range(6):
        assert 1 <= l <= u <= 2 and l * u == 2
        assert l * l <= 2 <= u * u
        assert u - l <= Fraction(1, 4 ** n)
        if previous:
            a, b = previous
            assert a <= l <= u <= b
            assert u - l == (b - a) ** 2 / (4 * u)
        result.append((n, l, u))
        previous = l, u
        l = (2 + l * u) / (l + u)
        u = (u + 2 / u) / 2
    return result


def table(product=False):
    lines = ['<div class="preface-table"><table>',
             '<thead><tr><th scope="col">Stage \\(n\\)</th><th scope="col">Lower bound</th><th scope="col">Upper bound</th></tr></thead>',
             '<tbody>']
    for n, l, u in rows():
        if product and n < 2:
            continue
        places = 40
        if product:
            l, u = l * l, u * u
        if n == 0:
            lines.append(f'<tr><th scope="row">\\({n}\\)</th><td>\\({l}\\)</td><td>\\({u}\\)</td></tr>')
            continue
        lo, hi = decimal(l, places), decimal(u, places)
        for value, exact in [(lo, l), (hi, u)]:
            assert Fraction(value) <= exact < Fraction(value) + Fraction(1, 10 ** places)
        if product:
            nines = len(lo.split('.')[1]) - len(lo.split('.')[1].lstrip('9'))
            zeros = len(hi.split('.')[1]) - len(hi.split('.')[1].lstrip('0'))
            length = 2 + min(nines, zeros)
            assert lo.startswith('1.' + '9' * (length - 2))
            assert hi.startswith('2.' + '0' * (length - 2))
        else:
            length = next((i for i, (a, b) in enumerate(zip(lo, hi)) if a != b), min(len(lo), len(hi)))
        lines.append(f'<tr><th scope="row">\\({n}\\)</th><td>{display(lo, length)}</td><td>{display(hi, length)}</td></tr>')
    lines.extend(['</tbody>', '</table></div>'])
    return '\n'.join(lines)


def render(source):
    for name, product in [('sqrt', False), ('product', True)]:
        pattern = re.compile(r'(<!-- ' + name + r'-table:start -->).*?(<!-- ' + name + r'-table:end -->)', re.S)
        assert len(pattern.findall(source)) == 1, name
        source = pattern.sub(lambda m: m[1] + '\n' + table(product) + '\n' + m[2], source)
    return source


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = CONTENT.read_text()
    expected = render(source)
    if args.check:
        assert source == expected, 'Regenerate the preface tables before publishing'
    else:
        CONTENT.write_text(expected)
    print('PASS: secant–tangent updates, nesting, squared bounds, shrinking, abbreviated digits, and matched bold prefixes')


if __name__ == '__main__':
    main()
