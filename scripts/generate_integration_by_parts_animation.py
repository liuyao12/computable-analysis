#!/usr/bin/env python3
"""Render exact product-rectangle cells for finite integration by parts.

For each rational state `(u, v, u_next, v_next)`, the coloured rectangles
are the literal disjoint tiling

    [0, u] × [v, v_next]  union  [u, u_next] × [0, v_next]

of `[0, u_next] × [0, v_next]` minus `[0, u] × [0, v]`.  Their areas are
`u * (v_next - v)` and `v_next * (u_next - u)`, respectively.  Thus every
frame is the finite one-cell identity behind the project’s integration by
parts theorem, with no completed integral drawn as an input.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "integration-by-parts-cell.gif"
PNG_PATH = ASSET_DIR / "integration-by-parts-cell.png"

WIDTH, HEIGHT = 620, 500
LEFT, RIGHT = 110, 500
TOP, BASELINE = 38, 428
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
OLD_FILL = (226, 232, 240, 255)
OLD_EDGE = (148, 163, 184, 255)
VERTICAL_FILL = (176, 227, 219, 255)
VERTICAL_EDGE = (13, 148, 136, 255)
HORIZONTAL_FILL = (254, 215, 170, 255)
HORIZONTAL_EDGE = (234, 88, 12, 255)
OUTLINE = (71, 85, 105, 255)


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


def x_screen(value: Fraction) -> float:
    return LEFT + float(value) * (RIGHT - LEFT)


def y_screen(value: Fraction) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


def rect(
    draw: ImageDraw.ImageDraw,
    x0: Fraction,
    y0: Fraction,
    x1: Fraction,
    y1: Fraction,
    fill: tuple[int, int, int, int],
    outline: tuple[int, int, int, int],
) -> None:
    draw.rectangle(
        (x_screen(x0), y_screen(y1), x_screen(x1), y_screen(y0)),
        fill=fill,
        outline=outline,
        width=3,
    )


def frame(u: Fraction, v: Fraction, u_next: Fraction, v_next: Fraction) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    for quarter in range(1, 5):
        x = x_screen(Fraction(quarter, 4))
        y = y_screen(Fraction(quarter, 4))
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
        draw.line((LEFT, y, RIGHT, y), fill=GRID, width=1)

    draw.line((LEFT - 25, BASELINE, RIGHT + 28, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 20, LEFT, TOP - 18), fill=AXIS, width=3)

    # The old product rectangle, then its two exact increment strips.
    rect(draw, Fraction(0), Fraction(0), u_next, v_next, WHITE, OUTLINE)
    rect(draw, Fraction(0), Fraction(0), u, v, OLD_FILL, OLD_EDGE)
    rect(draw, Fraction(0), v, u, v_next, VERTICAL_FILL, VERTICAL_EDGE)
    rect(draw, u, Fraction(0), u_next, v_next, HORIZONTAL_FILL, HORIZONTAL_EDGE)

    for value, label in ((u, "u_i"), (u_next, "u_{i+1}")):
        x = x_screen(value)
        draw.line((x, BASELINE - 7, x, BASELINE + 7), fill=AXIS, width=2)
        draw.text((x, BASELINE + 32), label, font=SMALL, fill=INK, anchor="mm")
    for value, label in ((v, "v_i"), (v_next, "v_{i+1}")):
        y = y_screen(value)
        draw.line((LEFT - 7, y, LEFT + 7, y), fill=AXIS, width=2)
        draw.text((LEFT - 16, y), label, font=SMALL, fill=INK, anchor="rm")
    draw.text((RIGHT + 25, BASELINE + 4), "u", font=LABEL, fill=INK, anchor="lm")
    draw.text((LEFT - 4, TOP - 20), "v", font=LABEL, fill=INK, anchor="mm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    states = [
        (Fraction(1, 4), Fraction(1, 3), Fraction(1, 2), Fraction(1, 2)),
        (Fraction(1, 2), Fraction(1, 2), Fraction(3, 4), Fraction(2, 3)),
        (Fraction(3, 4), Fraction(2, 3), Fraction(1), Fraction(1)),
    ]
    frames = [frame(*state) for state in states]
    # A middle cell keeps both strips clearly visible in print.
    frames[1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1450, 1450, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
