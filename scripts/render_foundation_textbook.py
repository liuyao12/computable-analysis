#!/usr/bin/env python3
"""Render the living Markdown textbook without third-party build dependencies.

Supports the deliberately small Markdown vocabulary used in textbook/: headings,
paragraphs, lists, tables, fenced code, links, emphasis, and LaTeX math. Rejects
unclosed code/math blocks. Math is left intact for the site's KaTeX reader.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import re
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "textbook"
OUTPUT = ROOT / "book" / "foundation-textbook"
KATEX = "https://cdn.jsdelivr.net/npm/katex@0.16.22/dist/"
TAYLOR_SKILL = ROOT / "skills" / "taylor-from-ftc" / "SKILL.md"
SKILL_LINK = "../skills/taylor-from-ftc/SKILL.md"
SKILL_DOWNLOAD = "skills/taylor-from-ftc/SKILL.md"
MISSION_DOWNLOAD = "downloads/foundation-mission.md"
APPLICATION_SOURCE = ROOT / "subprojects" / "special-topics" / "textbook" / "euler-applications.md"
CONTOUR_DOWNLOADS = ROOT / "book" / "dirichlet-contour"

STYLE = """:root{color-scheme:light;--ink:#242f32;--muted:#52676b;--paper:#faf9f5;--line:#d9dfda;--accent:#155e63}
*{box-sizing:border-box}body{margin:0;background:var(--paper);color:var(--ink);font:19px/1.75 Georgia,serif}
a{color:var(--accent);text-underline-offset:3px}a:hover{text-decoration-thickness:2px}
.shell{display:grid;grid-template-columns:270px minmax(0,820px);gap:64px;max-width:1240px;margin:auto;padding:48px 32px}
aside{font:14px/1.6 system-ui,sans-serif;align-self:start;position:sticky;top:28px;max-height:calc(100vh - 56px);overflow-y:auto}
.brand{display:block;color:var(--ink);font-size:20px;font-weight:700;text-decoration:none;margin-bottom:8px}
.label{color:var(--muted);margin:0 0 24px}nav a{display:block;padding:9px 12px;border-left:2px solid var(--line);text-decoration:none}
nav a[aria-current=page]{border-color:var(--accent);background:#eaf0eb;font-weight:650}
main{min-width:0} main img{display:block;max-width:100%;height:auto;margin:24px auto} h1{font-size:2.1em;line-height:1.2;letter-spacing:-.025em;margin:0 0 30px}h2{font-size:1.35em;line-height:1.3;margin:42px 0 16px}
p{margin:0 0 20px}li{margin-bottom:10px}code{font: .8em/1.5 ui-monospace,SFMono-Regular,Consolas,monospace;background:#edf0eb;padding:2px 4px;border-radius:3px;overflow-wrap:anywhere}
pre{background:#edf0eb;padding:20px;overflow:auto;border-radius:6px}pre code{padding:0;white-space:pre;overflow-wrap:normal}
.table-wrap{overflow-x:auto;margin:24px 0}table{border-collapse:collapse;font-size:.84em;width:100%}th,td{text-align:left;vertical-align:top;border-bottom:1px solid var(--line);padding:12px 10px}th{font-family:system-ui,sans-serif;font-size:.9em}
.math{overflow-x:auto}.katex-display{overflow-x:auto;overflow-y:hidden;padding:8px 0}.katex{font-size:1.05em}
.source,footer{font:13px/1.6 system-ui,sans-serif;color:var(--muted)}.source{border-top:1px solid var(--line);margin-top:44px;padding-top:18px}footer{margin-top:36px}
.skip{position:absolute;left:-10000px}.skip:focus{left:12px;top:8px;padding:8px;background:white}
@media(max-width:900px){.shell{grid-template-columns:1fr;gap:32px;padding:28px 22px}aside{position:static;max-height:none;overflow-y:visible}nav{display:flex;flex-wrap:wrap;gap:4px}nav a{font-size:12px;padding:5px 8px}h1{font-size:1.8em}body{font-size:18px}}
"""


def destination(name: str) -> str:
    return "index.html" if name == "README.md" else Path(name).with_suffix(".html").name


def inline(text: str) -> str:
    tokens = re.split(r"(\$[^$\n]+\$|`[^`]+`|!?\[[^\]]+\]\([^)]+\)|\*\*.+?\*\*)", text)
    out = []
    for token in tokens:
        if token.startswith("`") and token.endswith("`"):
            out.append("<code>" + html.escape(token[1:-1]) + "</code>")
        elif token.startswith("$") and token.endswith("$"):
            out.append(html.escape(token))
        elif token.startswith("**") and token.endswith("**"):
            out.append("<strong>" + inline(token[2:-2]) + "</strong>")
        elif (image := re.fullmatch(r"!\[([^\]]+)\]\((assets/[a-z0-9.-]+)\)", token)):
            out.append(f'<img src="{image[2]}" alt="{html.escape(image[1], quote=True)}" loading="lazy">')
        elif (match := re.fullmatch(r"\[([^\]]+)\]\(([^)]+)\)", token)):
            url = match[2]
            if ":" in url and not url.startswith(("https://", "http://")):
                raise ValueError("Unsupported link scheme: " + url)
            if url.endswith(".md") and "/" not in url:
                url = destination(url)
            elif url == SKILL_LINK:
                url = SKILL_DOWNLOAD
            out.append(f'<a href="{html.escape(url, quote=True)}">{inline(match[1])}</a>')
        else:
            out.append(html.escape(token))
    return "".join(out)


def markdown(text: str) -> str:
    lines = text.splitlines()
    out, i = [], 0
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1
            continue
        if line.startswith("```") or line == "$$":
            delimiter = "```" if line.startswith("```") else "$$"
            block = []
            i += 1
            while i < len(lines) and lines[i].strip() != delimiter:
                block.append(lines[i])
                i += 1
            if i == len(lines):
                raise ValueError("Unclosed block: " + delimiter)
            value = html.escape("\n".join(block))
            out.append("<pre><code>" + value + "</code></pre>" if delimiter == "```" else '<div class="math">$$\n' + value + '\n$$</div>')
        elif line.startswith("#"):
            match = re.fullmatch(r"(#{1,6})\s+(.+)", line)
            if not match:
                raise ValueError("Invalid heading: " + line)
            level = len(match[1])
            out.append(f"<h{level}>" + inline(match[2]) + f"</h{level}>")
        elif line.startswith("|"):
            rows = []
            while i < len(lines) and lines[i].strip().startswith("|"):
                cells = [s.strip() for s in lines[i].strip().strip("|").split("|")]
                if not all(re.fullmatch(r":?-+:?", c.replace(" ", "")) for c in cells):
                    tag = "th" if not rows else "td"
                    rows.append("<tr>" + "".join(f"<{tag}>" + inline(c) + f"</{tag}>" for c in cells) + "</tr>")
                i += 1
            out.append('<div class="table-wrap"><table>' + "".join(rows) + "</table></div>")
            continue
        elif re.match(r"(?:- |\d+\. )", line):
            ordered = not line.startswith("- ")
            tag = "ol" if ordered else "ul"
            items = []
            while i < len(lines):
                match = re.match(r"(?:- |\d+\. )(.+)", lines[i].strip())
                if not match:
                    break
                item = [match[1]]
                i += 1
                while i < len(lines) and lines[i].startswith("  ") and lines[i].strip():
                    item.append(lines[i].strip())
                    i += 1
                items.append("<li>" + inline(" ".join(item)) + "</li>")
            out.append(f"<{tag}>" + "".join(items) + f"</{tag}>")
            continue
        else:
            paragraph = [line]
            i += 1
            while i < len(lines) and lines[i].strip():
                if re.match(r"(?:#|\||```|\$\$|- |\d+\. )", lines[i].strip()):
                    break
                paragraph.append(lines[i].strip())
                i += 1
            out.append("<p>" + inline(" ".join(paragraph)) + "</p>")
            continue
        i += 1
    return "\n".join(out)


def render(source: Path, chapters: list[Path]) -> str:
    text = source.read_text()
    title = text.splitlines()[0].removeprefix("# ")
    nav = "".join(f'<a href="{destination(p.name)}"' + (' aria-current="page"' if p == source else '') + '>' + html.escape("Contents" if p.name == "README.md" else p.read_text().splitlines()[0].removeprefix("# ")) + '</a>' for p in chapters)
    digest = hashlib.sha256(text.encode()).hexdigest()
    return f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="source-sha256" content="{digest}"><title>{html.escape(title)} · Computable Analysis</title>
<style>{STYLE}</style><link rel="stylesheet" href="{KATEX}katex.min.css">
<script defer src="{KATEX}katex.min.js"></script><script defer src="{KATEX}contrib/auto-render.min.js"></script>
</head><body><a class="skip" href="#content">Skip to content</a><div class="shell"><aside>
<a class="brand" href="index.html">Computable Analysis</a><p class="label">The living foundation textbook</p><nav aria-label="Chapters">{nav}</nav>
<p><a href="../index.html">Project website</a></p></aside><main id="content">{markdown(text)}
<div class="source"><a href="{source.name}" download>Download this chapter as Markdown</a> · <a href="{MISSION_DOWNLOAD}" download>Complete mission Markdown with skill</a> · <a href="{SKILL_DOWNLOAD}" download>Taylor from FTC skill</a> · Editable source · Revision {digest[:12]}</div>
<footer>Definitions, proposition statements, and proofs develop together. Open targets are labelled explicitly.</footer>
</main></div><script>document.addEventListener('DOMContentLoaded',function(){{renderMathInElement(document.getElementById('content'),{{delimiters:[{{left:'$$',right:'$$',display:true}},{{left:'$',right:'$',display:false}}],throwOnError:true}});}});</script></body></html>
'''


def skill_body() -> str:
    text = TAYLOR_SKILL.read_text()
    match = re.match(r"\A---\n.*?\n---\n", text, re.DOTALL)
    if not match:
        raise ValueError("Taylor skill must have YAML frontmatter")
    return text[match.end():].lstrip()


def mission_markdown(chapters: list[Path]) -> str:
    """Make one portable manuscript; contributors receive the skill itself."""
    targets = {source.name: "#chapter-" + source.stem for source in chapters}
    targets[SKILL_LINK] = "#skill-taylor-from-ftc"

    def link(match: re.Match) -> str:
        return match[1] + targets.get(match[2], match[2]) + match[3]

    parts = [
        "# Computable Analysis: mission manuscript\n\n"
        "Editable foundation text, including the reusable Taylor-from-FTC "
        "construction skill. Open targets retain their chapter status labels. "
        "This manuscript does not itself submit a mission or publish formal declarations.\n"
    ]
    for source in chapters:
        text = re.sub(r"(\[[^\]]+\]\()([^)]+)(\))", link, source.read_text())
        parts.append(f'<a id="chapter-{source.stem}"></a>\n\n' + text.rstrip() + "\n")
    parts.append('<a id="skill-taylor-from-ftc"></a>\n\n' + skill_body())
    return "\n\n".join(parts)


def generated_files(chapters: list[Path]) -> dict[str, bytes]:
    expected = {}
    for source in chapters:
        expected[destination(source.name)] = render(source, chapters).encode()
        # Chapter downloads live beside the HTML, so adapt repository-relative
        # skill links to their packaged location without changing the source.
        expected[source.name] = source.read_text().replace(
            "](" + SKILL_LINK + ")", "](" + SKILL_DOWNLOAD + ")"
        ).encode()
    # An optional companion lesson is a separate page/download, not part of
    # the foundation's mission or its mathematical source ownership.
    if APPLICATION_SOURCE.is_file():
        expected[destination(APPLICATION_SOURCE.name)] = render(APPLICATION_SOURCE, chapters + [APPLICATION_SOURCE]).encode()
        expected[APPLICATION_SOURCE.name] = APPLICATION_SOURCE.read_bytes()
    expected[SKILL_DOWNLOAD] = TAYLOR_SKILL.read_bytes()
    expected[MISSION_DOWNLOAD] = mission_markdown(chapters).encode()
    # The Dirichlet contour chapter links to these standalone companion files.
    # Ship copies beside the rendered chapters and in the mission download
    # directory so both web links and the portable manuscript resolve.
    for name in ("dirichlet-contour-proof.tar.gz", "dirichlet-contour-verification.json"):
        source = CONTOUR_DOWNLOADS / name
        if source.is_file():
            expected[name] = source.read_bytes()
            expected[f"downloads/{name}"] = source.read_bytes()
    # Preserve the textbook's small explanatory animations in both reader
    # pages and the portable mission manuscript.
    assets = SOURCE / "assets"
    if assets.is_dir():
        for source in assets.rglob("*"):
            if source.is_file():
                relative = source.relative_to(SOURCE).as_posix()
                contents = source.read_bytes()
                expected[relative] = contents
                expected[f"downloads/{relative}"] = contents
    return expected


def write_files(output: Path, files: dict[str, bytes]) -> None:
    for name, value in files.items():
        target = output / name
        target.parent.mkdir(parents=True, exist_ok=True)
        # Replace a fresh file rather than truncating a cloud-backed download.
        with tempfile.NamedTemporaryFile(dir=target.parent, delete=False) as stream:
            temporary = Path(stream.name)
            try:
                stream.write(value)
                stream.flush()
                temporary.replace(target)
            finally:
                temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    chapters = [SOURCE / "README.md"] + sorted(p for p in SOURCE.glob("*.md") if p.name != "README.md")
    expected = generated_files(chapters)
    if args.check:
        stale = [name for name, value in expected.items() if not (args.output / name).is_file() or (args.output / name).read_bytes() != value]
        if stale:
            raise SystemExit("Stale generated textbook files: " + ", ".join(stale))
    else:
        write_files(args.output, expected)
    print(f"{'Checked' if args.check else 'Rendered'} {len(chapters)} chapters, portable mission Markdown, and Taylor skill.")


if __name__ == "__main__":
    main()
