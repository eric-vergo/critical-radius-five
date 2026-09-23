#!/usr/bin/env python3
"""Draw the dependency graph of the blueprint as a poster.

The nodes and `uses` edges come from the blueprint build
(`blueprint/_out/site/html-multi/-verso-data/blueprint-manifest.json`, written by
`lake exe vbp build`). If that file is missing, or with `--from-source`, they are read
directly from the chapter files instead. Short node titles always come from the chapter
files: the first `*bold*` phrase of each statement.

Outputs, next to this script:
  proof-graph.dot   the graph, for graphviz
  proof-graph.svg   the poster (landscape A1)
  proof-graph.pdf   the same, converted with rsvg-convert

Requires `dot` (graphviz) and `rsvg-convert` (librsvg) on PATH, and the fonts Avenir Next,
Menlo and STIX Two Text (all shipped with macOS); other systems fall back to similar fonts.
"""

from __future__ import annotations

import argparse
import html
import json
import math
import os
import re
import subprocess
import sys
import textwrap
from dataclasses import dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
CHAPTER_DIR = ROOT / "blueprint" / "CriticalRadiusFiveBlueprint" / "Chapters"
CHAPTERS = ["Setup", "UpperBound", "LowerBound", "MainTheorem"]
MANIFEST = ROOT / "blueprint" / "_out" / "site" / "html-multi" / "-verso-data" / "blueprint-manifest.json"
NAMESPACE = "CriticalRadiusFive."
MAIN = "thm:main"

# ---------------------------------------------------------------------------
# Visual design

# Graphviz font names, and how they are written in the SVG (CSS family stack, weight).
SANS = "Avenir Next"
SANS_BOLD = "Avenir Next Demi-Bold"  # a Pango font description: family "Avenir Next", weight 600
MONO = "Menlo"
MATH = "STIX Two Text"
SANS_STACK = "'Avenir Next', Avenir, 'Helvetica Neue', Helvetica, Arial, sans-serif"
MONO_STACK = "Menlo, 'SF Mono', Consolas, 'DejaVu Sans Mono', monospace"
MATH_STACK = "'STIX Two Text', 'STIX Two Math', 'Times New Roman', serif"
SVG_FONTS = {
    SANS_BOLD: (SANS_STACK, "600"),
    SANS: (SANS_STACK, "400"),
    MONO: (MONO_STACK, "400"),
    MATH: (MATH_STACK, "400"),
}

INK = "#0f172a"
MUTED = "#475569"
FAINT = "#94a3b8"
RULE = "#e2e8f0"

# One colour family per part of the proof: node border, header text, Lean names, edges into
# the family, cluster background and outline.
FAMILIES = {
    "setup": dict(name="Setup and general facts",
                  border="#64748b", header="#475569", lean="#475569", edge="#94a3b8",
                  cluster="#f8fafc", outline="#cbd5e1", swatch="#f1f5f9"),
    "upper-bound": dict(name="Upper bound",
                        border="#1d4ed8", header="#1d4ed8", lean="#1e40af", edge="#7fa6ec",
                        cluster="#eff6ff", outline="#93c5fd", swatch="#dbeafe"),
    "lower-bound": dict(name="Lower bound",
                        border="#c2410c", header="#c2410c", lean="#9a3412", edge="#f0a070",
                        cluster="#fff7ed", outline="#fdba74", swatch="#ffedd5"),
    "main": dict(name="Main theorem",
                 border="#0f172a", header="#fcd34d", lean="#fde68a", edge="#1e293b",
                 cluster="#ffffff", outline="#ffffff", swatch="#0f172a"),
}

# Cluster titles; `_c` marks a subscript c.
CLUSTER_TITLES = {
    "upper-bound": "Upper bound:  r_c(5) ≤ √(3 + φ)",
    "setup": "Setup",
    "lower-bound": "Lower bound:  √(3 + φ) ≤ r_c(5)",
}
CLUSTER_ORDER = ["upper-bound", "setup", "lower-bound"]
# Where each cluster title sits, clear of the edges that leave the cluster at the top.
CLUSTER_LABEL_SIDE = {"upper-bound": "l", "setup": "c", "lower-bound": "r"}

KIND_NAMES = {"definition": "Definition", "lemma": "Lemma", "theorem": "Theorem",
              "proposition": "Proposition", "corollary": "Corollary"}

NODE_WIDTH = 214  # minimum width of a node's table, in points
HEADER_SPLIT = 100  # of which the kind and number take at least this much; the label the rest

# The formula in the main node, in the notation of m() below.
MAIN_FORMULA = "_r_<tspan baseline-shift=\"sub\" font-size=\"17\">_c_</tspan>(5) = √(3 + _φ_) = 2.14896…"

# A1 landscape, in points (1 mm = 72/25.4 pt).
PAGE_W_MM, PAGE_H_MM = 841, 594
PT_PER_MM = 72 / 25.4
PAGE_W, PAGE_H = PAGE_W_MM * PT_PER_MM, PAGE_H_MM * PT_PER_MM
MARGIN = 64.0
HEADER_H = 214.0
FOOTER_H = 92.0


# ---------------------------------------------------------------------------
# Data


@dataclass
class Node:
    label: str
    kind: str
    number: str = ""
    title: str = ""
    parent: str = ""
    lean: list[str] = field(default_factory=list)
    chapter: int = 0
    order: int = 0


@dataclass
class Graph:
    nodes: dict[str, Node]
    edges: list[tuple[str, str]]  # (dependency, dependent): the dependent uses the dependency
    source: str


DIRECTIVE = re.compile(r'^:::(definition|lemma_|theorem|proposition|corollary|proof)\s+"([^"]+)"(.*)$')
OPTION = re.compile(r'\((\w+)\s*:=\s*"([^"]*)"\)')
USES = re.compile(r'\{uses\s+"([^"]+)"')
BOLD = re.compile(r'\*([^*\n]+)\*')


def strip_quotes(name: str) -> str:
    """Manifest labels are Lean names, quoted with « » when needed."""
    return name.replace("«", "").replace("»", "")


def parse_chapters() -> Graph:
    """Read nodes, uses edges, Lean names and short titles from the chapter files."""
    nodes: dict[str, Node] = {}
    edges: list[tuple[str, str]] = []
    order = 0
    for chapter_index, chapter in enumerate(CHAPTERS, start=1):
        lines = (CHAPTER_DIR / f"{chapter}.lean").read_text(encoding="utf-8").splitlines()
        counter = 0
        i = 0
        while i < len(lines):
            match = DIRECTIVE.match(lines[i])
            if not match:
                i += 1
                continue
            directive, label, rest = match.groups()
            options = dict(OPTION.findall(rest))
            body = []
            i += 1
            while i < len(lines) and lines[i].strip() != ":::":
                body.append(lines[i])
                i += 1
            text = "\n".join(body)
            uses = USES.findall(text)
            uses += [u.strip() for u in options.get("uses", "").split(",") if u.strip()]
            if directive != "proof":
                counter += 1
                order += 1
                kind = "lemma" if directive == "lemma_" else directive
                title = BOLD.search(text)
                nodes[label] = Node(
                    label=label, kind=kind,
                    number=f"{KIND_NAMES[kind]} {chapter_index}.{counter}",
                    title=title.group(1).strip().rstrip(".") if title else label,
                    parent=options.get("parent", ""),
                    lean=[n.strip() for n in options.get("lean", "").split(",") if n.strip()],
                    chapter=chapter_index, order=order)
            edges += [(dep, label) for dep in uses]
    edges = list(dict.fromkeys(edges))
    return Graph(nodes, edges, "chapter sources")


def read_manifest(path: Path, source: Graph) -> Graph:
    """Nodes, numbers, groups, edges and Lean names from the blueprint build."""
    data = json.loads(path.read_text(encoding="utf-8"))
    graph = data["graphs"][0]
    previews = {p.get("key"): p for p in data.get("previews", [])}
    nodes: dict[str, Node] = {}
    edges: list[tuple[str, str]] = []
    missing: list[str] = []
    for raw in graph["nodes"]:
        label = strip_quotes(raw["label"])
        preview = previews.get(f"{raw['label']}--statement") or {}
        decls = (preview.get("codeData") or {}).get("externalDecls") or []
        missing += [f"{label}: {d.get('written')}" for d in decls if not d.get("present")]
        lean = [d.get("written") or d.get("canonical") for d in decls]
        from_source = source.nodes.get(label)
        nodes[label] = Node(
            label=label, kind=raw.get("kind", "lemma"), number=raw.get("title", ""),
            title=from_source.title if from_source else label,
            parent=strip_quotes(raw.get("parent") or ""),
            lean=[n for n in lean if n] or (from_source.lean if from_source else []),
            chapter=from_source.chapter if from_source else 0,
            order=from_source.order if from_source else 0)
    for edge in graph["edges"]:
        edges.append((strip_quotes(edge["source"]), strip_quotes(edge["target"])))
    edges = list(dict.fromkeys(edges))
    if missing:
        print(f"note: {len(missing)} Lean name(s) were not found when the blueprint was built:")
        for item in missing:
            print(f"  {item}")
    # The manifest and the chapter files should describe the same graph.
    if set(nodes) != set(source.nodes):
        print("warning: nodes differ between the manifest and the chapter files:",
              sorted(set(nodes) ^ set(source.nodes)))
    if set(edges) != set(source.edges):
        print("warning: edges differ between the manifest and the chapter files (rebuild the blueprint?):",
              sorted(set(edges) ^ set(source.edges)))
    try:
        shown = path.resolve().relative_to(ROOT)
    except ValueError:
        shown = path
    return Graph(nodes, edges, f"the blueprint manifest ({shown})")


# ---------------------------------------------------------------------------
# Graphviz


def family_of(node: Node) -> str:
    if node.label == MAIN:
        return "main"
    return node.parent if node.parent in FAMILIES else "setup"


def esc(text: str) -> str:
    return html.escape(text, quote=False)


def font(face: str, size: int, color: str, text: str) -> str:
    return f'<FONT FACE="{face}" POINT-SIZE="{size}" COLOR="{color}">{text}</FONT>'


def rich(text: str, size: int) -> str:
    """Escape text for an HTML-like label, typesetting GG₅ and r_c with real subscripts."""
    sub = int(round(size * 0.68))
    out = esc(text)
    out = out.replace("GG₅", f'GG<SUB><FONT POINT-SIZE="{sub}">5</FONT></SUB>')
    out = out.replace("r_c", f'r<SUB><FONT POINT-SIZE="{sub}">c</FONT></SUB>')
    return out


def short_lean(name: str) -> str:
    return name[len(NAMESPACE):] if name.startswith(NAMESPACE) else name


def node_label(node: Node) -> str:
    fam = FAMILIES[family_of(node)]
    is_main = node.label == MAIN
    title_size = 21 if is_main else 15
    title_lines = textwrap.wrap(node.title, width=32 if is_main else 26) or [node.label]
    title = "<BR/>".join(rich(line, title_size) for line in title_lines)
    rows = [
        "<TR>"
        f'<TD ALIGN="LEFT" VALIGN="BOTTOM" WIDTH="{HEADER_SPLIT}">'
        f'{font(SANS_BOLD, 10, fam["header"], esc(node.number.upper()))}</TD>'
        f'<TD ALIGN="RIGHT" VALIGN="BOTTOM" WIDTH="{NODE_WIDTH - HEADER_SPLIT}">'
        f'{font(MONO, 8, "#cbd5e1" if is_main else FAINT, esc(node.label))}</TD>'
        "</TR>",
        "<HR/>",
        f'<TR><TD COLSPAN="2" ALIGN="LEFT" BALIGN="LEFT">'
        f'{font(SANS_BOLD, title_size, "#ffffff" if is_main else INK, title)}</TD></TR>',
    ]
    if is_main:
        # Laid out by graphviz for its size only; graph_svg() replaces it by MAIN_FORMULA.
        formula = ('<I>r</I><SUB><FONT POINT-SIZE="17"><I>c</I></FONT></SUB>(5) = '
                   '√(3 + <I>φ</I>) = 2.14896…')
        rows.append(f'<TR><TD COLSPAN="2" ALIGN="LEFT">{font(MATH, 26, fam["lean"], formula)}</TD></TR>')
    if node.lean:
        names = "<BR/>".join(esc(short_lean(n)) for n in node.lean)
        rows.append(f'<TR><TD COLSPAN="2" ALIGN="LEFT" BALIGN="LEFT">'
                    f'{font(MONO, 11 if is_main else 10, fam["lean"], names)}</TD></TR>')
    rule = "#475569" if is_main else RULE
    return (f'<<TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0" CELLPADDING="3" '
            f'COLOR="{rule}" WIDTH="{NODE_WIDTH}">' + "".join(rows) + "</TABLE>>")


def node_attrs(node: Node) -> str:
    fam = FAMILIES[family_of(node)]
    if node.label == MAIN:
        style, pen, fill = "rounded,filled", 3.0, fam["swatch"]
    elif node.kind == "definition":
        style, pen, fill = "filled", 1.4, "#ffffff"
    elif node.kind == "theorem":
        style, pen, fill = "rounded,filled", 2.8, "#ffffff"
    else:
        style, pen, fill = "rounded,filled", 1.4, "#ffffff"
    return (f'shape=box, style="{style}", color="{fam["border"]}", fillcolor="{fill}", '
            f'penwidth={pen}, margin="0.10,0.07", label={node_label(node)}')


def cluster_label(parent: str) -> str:
    fam = FAMILIES[parent]
    return "<" + font(SANS_BOLD, 21, fam["header"], rich(CLUSTER_TITLES[parent], 21)) + ">"


def to_dot(graph: Graph) -> str:
    out = [
        "digraph proof {",
        "  rankdir=BT;",
        '  bgcolor="transparent";',
        "  newrank=true;",
        "  nodesep=0.30;",
        "  ranksep=0.95;",
        "  splines=spline;",
        '  outputorder="edgesfirst";',
        f'  fontname="{SANS}";',
        f'  node [fontname="{SANS}"];',
        '  edge [penwidth=1.5, arrowsize=0.8, arrowhead=vee];',
    ]
    by_family: dict[str, list[Node]] = {}
    for node in sorted(graph.nodes.values(), key=lambda n: n.order):
        by_family.setdefault(family_of(node), []).append(node)
    for parent in CLUSTER_ORDER:
        fam = FAMILIES[parent]
        out += [
            f'  subgraph "cluster_{parent}" {{',
            f"    label={cluster_label(parent)};",
            f'    labeljust="{CLUSTER_LABEL_SIDE[parent]}"; labelloc="b";',  # with rankdir=BT, "b" is the top
            f'    style="rounded,filled"; fillcolor="{fam["cluster"]}"; color="{fam["outline"]}"; penwidth=1.5;',
            "    margin=20;",
        ]
        for node in by_family.get(parent, []):
            out.append(f'    "{node.label}" [{node_attrs(node)}];')
        out.append("  }")
    for node in by_family.get("main", []):
        out.append(f'  "{node.label}" [{node_attrs(node)}];')
    for dep, user in graph.edges:
        if dep not in graph.nodes or user not in graph.nodes:
            print(f"warning: edge {dep} -> {user} mentions an unknown node")
            continue
        fam = FAMILIES[family_of(graph.nodes[user])]
        extra = ", penwidth=2.4, arrowsize=0.9" if user == MAIN else ""
        # Keep each part of the proof compact; edges between parts may stretch.
        if family_of(graph.nodes[dep]) == family_of(graph.nodes[user]):
            extra += ", weight=3"
        out.append(f'  "{dep}" -> "{user}" [color="{fam["edge"]}"{extra}];')
    out.append("}")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# The poster page


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    # A fixed timestamp makes the PDF byte-for-byte reproducible (cairo honours SOURCE_DATE_EPOCH).
    env = {**os.environ, "SOURCE_DATE_EPOCH": os.environ.get("SOURCE_DATE_EPOCH", "0")}
    try:
        return subprocess.run(cmd, check=True, capture_output=True, env=env, **kw)
    except FileNotFoundError:
        sys.exit(f"error: `{cmd[0]}` not found on PATH")
    except subprocess.CalledProcessError as err:
        sys.exit(f"error: {' '.join(cmd)} failed:\n{err.stderr.decode(errors='replace')}")


def graph_svg(dot_source: str) -> tuple[str, float, float]:
    """Lay out with graphviz; return the inner SVG markup and its size in points."""
    svg = run(["dot", "-Tsvg"], input=dot_source.encode()).stdout.decode()
    match = re.search(r'<svg[^>]*viewBox="([^"]+)"[^>]*>(.*)</svg>', svg, re.S)
    if not match:
        sys.exit("error: unexpected SVG from graphviz")
    _, _, w, h = (float(v) for v in match.group(1).split())
    inner = match.group(2)
    inner = re.sub(r"<!--.*?-->", "", inner, flags=re.S)
    inner = re.sub(r"<title>.*?</title>", "", inner, flags=re.S)
    # Graphviz writes its font names verbatim; spell them as CSS family stacks and weights.
    for face, (stack, weight) in SVG_FONTS.items():
        inner = inner.replace(f'font-family="{face}"', f'font-family="{stack}" font-weight="{weight}"')
    # Graphviz places the italic and subscript pieces of the formula in the main node as separate,
    # absolutely positioned texts, which drift apart; set the formula as one text instead.
    pieces = list(re.finditer(rf'<text[^>]*font-family="{re.escape(MATH_STACK)}"[^>]*>.*?</text>', inner, re.S))
    if pieces:
        xs = [float(re.search(r' x="([^"]+)"', p.group(0)).group(1)) for p in pieces]
        y = float(re.search(r' y="([^"]+)"', pieces[0].group(0)).group(1))
        formula = text(min(xs), y, m(MAIN_FORMULA), 25, family=MATH_STACK, fill=FAMILIES["main"]["lean"])
        for p in reversed(pieces):
            inner = inner[:p.start()] + inner[p.end():]
        end = inner.rindex("</g>")  # inside the outermost group, which carries graphviz's transform
        inner = inner[:end] + formula + "\n" + inner[end:]
    return inner, w, h


def text(x, y, content, size, *, family=SANS_STACK, weight=400, fill=INK, anchor="start", style="normal"):
    return (f'<text x="{x:.1f}" y="{y:.1f}" font-family="{family}" font-size="{size}" '
            f'font-weight="{weight}" font-style="{style}" fill="{fill}" text-anchor="{anchor}">{content}</text>')


def m(content: str) -> str:
    """Inline mathematics: STIX Two Text; letters in italic are marked with _..._ ."""
    content = re.sub(r"_([^_]+)_", r'<tspan font-style="italic">\1</tspan>', content)
    return f'<tspan font-family="{MATH_STACK}">{content}</tspan>'


def sub(content: str, size: float) -> str:
    return f'<tspan baseline-shift="sub" font-size="{size}">{content}</tspan>'


def sup(content: str, size: float) -> str:
    return f'<tspan baseline-shift="super" font-size="{size}">{content}</tspan>'


def lens_figure(cx: float, cy: float, scale: float) -> str:
    """The two disks of radius r_c about -1 and +1, their lens, and the chord E'E."""
    r = math.sqrt(3 + (1 + math.sqrt(5)) / 2)
    zeta = complex(math.cos(2 * math.pi / 5), math.sin(2 * math.pi / 5))
    e = zeta - zeta ** 2

    def p(z: complex) -> tuple[float, float]:
        return cx + scale * z.real, cy - scale * z.imag

    rad = scale * r
    h = math.sqrt(r * r - 1)
    top, bottom = p(complex(0, h)), p(complex(0, -h))
    lens = (f"M {top[0]:.2f} {top[1]:.2f} A {rad:.2f} {rad:.2f} 0 0 1 {bottom[0]:.2f} {bottom[1]:.2f} "
            f"A {rad:.2f} {rad:.2f} 0 0 1 {top[0]:.2f} {top[1]:.2f} Z")
    blue = FAMILIES["upper-bound"]["border"]
    (lx, ly), (rx, ry), (ex, ey), (fx, fy) = p(-1), p(1), p(e), p(-e)
    return "\n".join([
        f'<path d="{lens}" fill="{FAMILIES["upper-bound"]["cluster"]}" stroke="none"/>',
        f'<circle cx="{lx:.2f}" cy="{ly:.2f}" r="{rad:.2f}" fill="none" stroke="#64748b" stroke-width="1.5"/>',
        f'<circle cx="{rx:.2f}" cy="{ry:.2f}" r="{rad:.2f}" fill="none" stroke="#64748b" stroke-width="1.5"/>',
        f'<line x1="{fx:.2f}" y1="{fy:.2f}" x2="{ex:.2f}" y2="{ey:.2f}" stroke="{blue}" stroke-width="3" '
        'stroke-linecap="round"/>',
        f'<circle cx="{lx:.2f}" cy="{ly:.2f}" r="3" fill="#475569"/>',
        f'<circle cx="{rx:.2f}" cy="{ry:.2f}" r="3" fill="#475569"/>',
        f'<circle cx="{ex:.2f}" cy="{ey:.2f}" r="4.5" fill="{blue}"/>',
        f'<circle cx="{fx:.2f}" cy="{fy:.2f}" r="4.5" fill="{blue}"/>',
        text(lx - 6, ly - 10, m("−1"), 15, fill=MUTED, anchor="end"),
        text(rx + 6, ry + 22, m("+1"), 15, fill=MUTED),
        text(ex + 10, ey - 6, m("_E_"), 18, fill=blue),
        text(fx - 10, fy + 20, m("_E_′"), 18, fill=blue, anchor="end"),
    ])


def legend(x: float, y: float, example: str) -> str:
    """One line: the colour families, the node kinds, the meaning of an edge, and how Lean names
    are shown (`example` is a fully qualified declaration name)."""
    parts = []
    cx = x

    def swatch(fill: str, stroke: str, pen: float, rx: float) -> None:
        parts.append(f'<rect x="{cx:.1f}" y="{y - 14:.1f}" width="30" height="19" rx="{rx}" '
                     f'fill="{fill}" stroke="{stroke}" stroke-width="{pen}"/>')

    for key in ["setup", "upper-bound", "lower-bound", "main"]:
        fam = FAMILIES[key]
        swatch(fam["swatch"], fam["border"], 1.6, 5)
        parts.append(text(cx + 40, y, esc(fam["name"]), 15))
        cx += 40 + 8.3 * len(fam["name"]) + 34
    cx += 18
    for name, pen, rx in [("Definition", 1.4, 0), ("Lemma", 1.4, 6), ("Theorem", 2.8, 6)]:
        swatch("#ffffff", "#334155", pen, rx)
        parts.append(text(cx + 40, y, name, 15))
        cx += 40 + 8.3 * len(name) + 34
    cx += 18
    parts.append(text(cx, y, m("_A_"), 17))
    parts.append(f'<line x1="{cx + 18:.1f}" y1="{y - 5:.1f}" x2="{cx + 52:.1f}" y2="{y - 5:.1f}" '
                 f'stroke="#64748b" stroke-width="1.6"/>')
    parts.append(f'<path d="M {cx + 58:.1f} {y - 5:.1f} l -11 -5.5 l 3.5 5.5 l -3.5 5.5 Z" fill="#64748b"/>')
    parts.append(text(cx + 64, y, m("_B_"), 17))
    parts.append(text(cx + 88, y, "means  " + m("_B_") + "  uses  " + m("_A_"), 15))
    parts.append(text(PAGE_W - MARGIN, y,
                      f'<tspan font-family="{MONO_STACK}" font-size="14" fill="{INK}">{esc(short_lean(example))}</tspan>'
                      '  is the Lean declaration  '
                      f'<tspan font-family="{MONO_STACK}" font-size="14" fill="{INK}">{esc(example)}</tspan>',
                      15, fill=MUTED, anchor="end"))
    return "\n".join(parts)


def poster(graph: Graph, inner: str, gw: float, gh: float) -> tuple[str, float]:
    area_x, area_y = MARGIN, MARGIN + HEADER_H
    area_w, area_h = PAGE_W - 2 * MARGIN, PAGE_H - area_y - MARGIN - FOOTER_H
    scale = min(area_w / gw, area_h / gh)
    draw_w, draw_h = gw * scale, gh * scale
    gx = area_x + (area_w - draw_w) / 2
    gy = area_y + (area_h - draw_h) / 2

    title = text(MARGIN, MARGIN + 46, "The critical radius of GG" + sub("5", 32), 52, weight=600)
    formula = text(MARGIN, MARGIN + 112,
                   m("_r_" + sub("_c_", 30) + "(5) = √(3 + _φ_) = 2.1489611417…")
                   + f'<tspan dx="26" font-family="{SANS_STACK}" font-size="24" fill="{MUTED}">a root of</tspan>'
                   + f'<tspan dx="10" font-size="30" fill="{MUTED}">'
                   + m("_x_" + sup("4", 19) + " − 7_x_" + sup("2", 19) + " + 11") + "</tspan>", 46)
    statement = text(
        MARGIN, MARGIN + 160,
        f'<tspan font-weight="600" fill="{INK}">Theorem.</tspan>  The group generated by the clockwise 72° '
        "turns of two closed disks of radius " + m("_r_") + " about " + m("±1") + " is finite for "
        + m("_r_ &lt; √(3 + _φ_)") + " and infinite for " + m("_r_ ≥ √(3 + _φ_)")
        + ", where " + m("_φ_") + " is the golden ratio.",
        19, fill=MUTED)
    subline = text(MARGIN, MARGIN + 192,
                   "The dependency graph of the machine-checked proof in Lean 4 and Mathlib, "
                   "drawn from its Verso blueprint. Every box is a blueprint node.",
                   15, fill=FAINT)
    rule_y = MARGIN + HEADER_H - 4
    rule = (f'<line x1="{MARGIN:.1f}" y1="{rule_y:.1f}" x2="{PAGE_W - MARGIN:.1f}" y2="{rule_y:.1f}" '
            f'stroke="{RULE}" stroke-width="1.5"/>')
    figure = lens_figure(PAGE_W - MARGIN - 150, MARGIN + 82, 36)
    caption = text(PAGE_W - MARGIN - 150, MARGIN + 192,
                   "The chord " + m("_E_′_E_") + " in the lens at " + m("_r_ = _r_" + sub("_c_", 10) + "(5)"),
                   13, fill=FAINT, anchor="middle")

    legend_y = PAGE_H - MARGIN - 38
    main = graph.nodes.get(MAIN)
    example = main.lean[0] if main and main.lean else NAMESPACE + "criticalRadius_five"
    legend_rule = (f'<line x1="{MARGIN:.1f}" y1="{legend_y - 34:.1f}" x2="{PAGE_W - MARGIN:.1f}" '
                   f'y2="{legend_y - 34:.1f}" stroke="{RULE}" stroke-width="1.5"/>')
    footer_y = PAGE_H - MARGIN + 2
    footer = text(MARGIN, footer_y,
                  "The formal proof uses only the axioms propext, Classical.choice and Quot.sound.   "
                  "The value was conjectured by R. Hearn, W. Kretschmer, T. Rokicki, B. Streeter and E. Vergo, "
                  "“Two-Disk Compound Symmetry Groups”, arXiv:2302.12950.",
                  13, fill=FAINT)
    count = text(PAGE_W - MARGIN, footer_y,
                 f"critical-radius-five · {len(graph.nodes)} nodes · {len(graph.edges)} edges",
                 13, fill=FAINT, anchor="end")

    body = (f'<svg x="{gx:.2f}" y="{gy:.2f}" width="{draw_w:.2f}" height="{draw_h:.2f}" '
            f'viewBox="0 0 {gw:.2f} {gh:.2f}" overflow="visible">{inner}</svg>')
    svg = "\n".join([
        '<?xml version="1.0" encoding="UTF-8" standalone="no"?>',
        '<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
        f'width="{PAGE_W_MM}mm" height="{PAGE_H_MM}mm" viewBox="0 0 {PAGE_W:.2f} {PAGE_H:.2f}">',
        "<title>The critical radius of GG5: dependency graph of the proof</title>",
        f'<rect width="{PAGE_W:.2f}" height="{PAGE_H:.2f}" fill="#ffffff"/>',
        title, formula, statement, subline, figure, caption, rule,
        body,
        legend_rule, legend(MARGIN, legend_y, example),
        footer, count,
        "</svg>",
    ]) + "\n"
    return svg, scale


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--manifest", type=Path, default=MANIFEST, help="blueprint-manifest.json of a blueprint build")
    parser.add_argument("--from-source", action="store_true", help="ignore the manifest; parse the chapter files")
    parser.add_argument("--out", type=Path, default=HERE, help="output directory (default: this directory)")
    args = parser.parse_args()

    source = parse_chapters()
    if not args.from_source and args.manifest.exists():
        graph = read_manifest(args.manifest, source)
    else:
        if not args.from_source:
            print(f"note: {args.manifest} not found; reading the chapter files instead")
        graph = source
    print(f"graph from {graph.source}: {len(graph.nodes)} nodes, {len(graph.edges)} edges")

    dot_source = to_dot(graph)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "proof-graph.dot").write_text(dot_source, encoding="utf-8")
    inner, gw, gh = graph_svg(dot_source)
    svg, scale = poster(graph, inner, gw, gh)
    svg_path = args.out / "proof-graph.svg"
    svg_path.write_text(svg, encoding="utf-8")
    run(["rsvg-convert", "-f", "pdf", "-o", str(args.out / "proof-graph.pdf"), str(svg_path)])
    print(f"graph scaled by {scale:.2f} onto an A1 landscape page")
    print(f"wrote proof-graph.dot, proof-graph.svg, proof-graph.pdf in {args.out}")


if __name__ == "__main__":
    main()
