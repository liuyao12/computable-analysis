from pathlib import Path
import re,sys

def overlay(original):
    root=Path(__file__).parent
    section=(root/'chapter-section.html').read_text()
    text=re.sub(r'<!-- rational-nball:start -->.*?<!-- rational-nball:end -->\s*','',original,flags=re.S)
    marker='<h2 id="a0000000009">2.12 What precedes calculus</h2>'
    if marker not in text:marker=marker.replace('2.12','2.13')
    assert marker in text
    text=text.replace(marker,section+'\n'+marker.replace('2.12','2.13'),1)
    if 'href="rational-nball/chapter.css"' not in text:
        text=text.replace('</head>','<link rel="stylesheet" href="rational-nball/chapter.css"><script defer src="rational-nball/polyhedra-data.js"></script><script defer src="rational-nball/polyhedra-view.js"></script></head>',1)
    nav='<a href="#sec:rational-nball">2.12 Volume in every dimension</a><a href="#nball-volume-axioms">Volume axioms</a><a href="#nball-simplex-volume">Simplex determinant formula</a><a href="#nball-3d-illustration">Rational polyhedra in 3D</a><a href="#nball-general-formula">General formula</a><a href="#nball-recurrence-proof">Finite recurrence proof</a>'
    old='<a href="#a0000000009">2.12 What precedes calculus</a>'
    if 'href="#sec:rational-nball"' not in text:
        text=text.replace(old,nav+old.replace('2.12','2.13'))
    text=text.replace('<span>Original chapter preserved</span>','<span>Chapter 2 · rational polytope exhaustion</span>')
    assert text.count('id="sec:rational-nball"')==1
    return text

if __name__=='__main__':
    original=Path(sys.argv[1]);target=Path(sys.argv[2]);target.write_text(overlay(original.read_text()))
