#!/usr/bin/env python3
"""Render a finite rational endpoint comparison for the FTC.

The primitive is `F(t) = t^2` and its candidate derivative is `2t` on
`[0, 1]`.  For each dyadic cell `[p, r]`, exactly

    2p (r-p) <= F(r)-F(p) <= 2r (r-p).

The frames draw the endpoint rise on the left and those lower/right rectangle
sums on the right for 1, 2, 4, and 8 cells.  All mesh coordinates and all
rectangle heights are rational.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "ftc-endpoint-comparison.gif"
PNG_PATH = ASSET_DIR / "ftc-endpoint-comparison.png"

WIDTH, HEIGHT = 760, 470
P_LEFT, P_RIGHT = 74, 314
D_LEFT, D_RIGHT = 446, 686
TOP, BASELINE = 58, 368
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
PRIMITIVE = (126, 34, 206, 255)
DERIVATIVE = (30, 64, 175, 255)
LOWER_FILL = (176, 227, 219, 255)
LOWER_EDGE = (13, 148, 136, 255)
UPPER_FILL = (254, 215, 170, 255)
UPPER_EDGE = (234, 88, 12, 255)


def font(size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    for name in (
        "/System/Library/Fonts/Supplemental/Arial.ttf",
        "/Library/Fonts/Arial.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ):
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            continue
    return ImageFont.load_default()


SMALL = font(16)
LABEL = font(18)


def px(t: Fraction) -> float:
    return P_LEFT + float(t) * (P_RIGHT - P_LEFT)


def dx(t: Fraction) -> float:
    return D_LEFT + float(t) * (D_RIGHT - D_LEFT)


def primitive_y(value: Fraction) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


def derivative_y(value: Fraction) -> float:
    return BASELINE - float(value / 2) * (BASELINE - (TOP + 16))


def axes(draw: ImageDraw.ImageDraw, left: int, right: int, label: str, y_top: int) -> None:
    draw.line((left - 22, BASELINE, right + 22, BASELINE), fill=AXIS, width=3)
    draw.line((left, BASELINE + 18, left, y_top - 18), fill=AXIS, width=3)
    for half in range(1, 2):
        x = left + half * (right - left) / 2
        draw.line((x, y_top, x, BASELINE), fill=GRID, width=1)
    draw.text((left, BASELINE + 30), "0", font=SMALL, fill=INK, anchor="mm")
    draw.text((right, BASELINE + 30), "1", font=SMALL, fill=INK, anchor="mm")
    draw.text((right + 18, BASELINE + 4), "t", font=LABEL, fill=INK, anchor="lm")
    draw.text((left - 2, y_top - 20), label, font=LABEL, fill=INK, anchor="mm")


def frame(subdivisions: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    axes(draw, P_LEFT, P_RIGHT, "F", TOP)
    axes(draw, D_LEFT, D_RIGHT, "F'", TOP + 16)

    # Endpoint rise F(1)-F(0), drawn as the exact vertical primitive span.
    draw.line((px(Fraction(1)), primitive_y(Fraction(0)),
               px(Fraction(1)), primitive_y(Fraction(1))), fill=PRIMITIVE, width=7)
    primitive_points = []
    for index in range(241):
        t = Fraction(index, 240)
        primitive_points.append((px(t), primitive_y(t * t)))
    draw.line(primitive_points, fill=PRIMITIVE, width=4, joint="curve")

    cells = [Fraction(index, subdivisions) for index in range(subdivisions + 1)]
    for left, right in zip(cells, cells[1:]):
        # For the increasing candidate derivative, right endpoints give the
        # upper rectangle.  Paint it first so the orange finite gap remains.
        draw.rectangle(
            (dx(left), derivative_y(2 * right), dx(right), BASELINE),
            fill=UPPER_FILL,
            outline=UPPER_EDGE,
            width=2,
        )
        draw.rectangle(
            (dx(left), derivative_y(2 * left), dx(right), BASELINE),
            fill=LOWER_FILL,
            outline=LOWER_EDGE,
            width=2,
        )
        x = dx(left)
        draw.line((x, BASELINE - 5, x, BASELINE + 5), fill=AXIS, width=1)
    draw.line((dx(Fraction(1)), BASELINE - 5, dx(Fraction(1)), BASELINE + 5), fill=AXIS, width=1)

    derivative_points = []
    for index in range(121):
        t = Fraction(index, 120)
        derivative_points.append((dx(t), derivative_y(2 * t)))
    draw.line(derivative_points, fill=DERIVATIVE, width=4)
    draw.text((P_RIGHT - 13, primitive_y(Fraction(1)) - 18), "F(1)-F(0)",
              font=SMALL, fill=PRIMITIVE, anchor="rm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(subdivisions) for subdivisions in (1, 2, 4, 8)]
    # Four cells make the lower/upper endpoint comparison readable on paper.
    frames[2].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1200, 1200, 1200, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
