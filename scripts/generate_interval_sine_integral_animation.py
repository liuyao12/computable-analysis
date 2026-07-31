#!/usr/bin/env python3
"""Render interval-valued Darboux stages for sin(pi*t) on [0, 1/2].

Every coloured rectangle height comes from a rational interval.  The bounds
use the rational pi enclosure 333/106 < pi < 355/113 and alternating Taylor
partial sums on [0, 2].  The thin blue vertical segments are the actual finite
value boxes used by the rectangles; the smooth black curve is only a visual
reference shape.
"""

from __future__ import annotations

from fractions import Fraction
from math import factorial, sin, pi
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "interval-sine-integral-stage.gif"
PNG_PATH = ASSET_DIR / "interval-sine-integral-stage.png"

WIDTH, HEIGHT = 700, 500
LEFT, RIGHT = 82, 642
TOP, BASELINE = 58, 398
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
CURVE = (28, 41, 56, 255)
BOX = (30, 64, 175, 255)
LOWER_FILL = (176, 227, 219, 255)
LOWER_EDGE = (13, 148, 136, 255)
UPPER_FILL = (254, 215, 170, 255)
UPPER_EDGE = (234, 88, 12, 255)

PI_LOWER = Fraction(333, 106)
PI_UPPER = Fraction(355, 113)


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


def x_screen(t: Fraction) -> float:
    return LEFT + float(2 * t) * (RIGHT - LEFT)


def y_screen(value: Fraction | float) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


def partial_sine(x: Fraction, last: int) -> Fraction:
    return sum(
        (
            Fraction(1 if k % 2 == 0 else -1, factorial(2 * k + 1))
            * x ** (2 * k + 1)
        )
        for k in range(last + 1)
    )


def sine_box(t: Fraction, lower_last: int) -> tuple[Fraction, Fraction]:
    """A rational Taylor enclosure for sin(pi*t), where 0 <= t <= 1/2.

    Odd final indices are alternating lower sums; even final indices are
    upper sums.  Both arguments stay in [0, 2], where the alternating-term
    bound applies.
    """

    lower = partial_sine(PI_LOWER * t, lower_last)
    upper = partial_sine(PI_UPPER * t, lower_last + 1)
    return lower, upper


def rectangle(
    draw: ImageDraw.ImageDraw,
    left: Fraction,
    right: Fraction,
    height: Fraction,
    fill: tuple[int, int, int, int],
    outline: tuple[int, int, int, int],
) -> None:
    draw.rectangle(
        (x_screen(left), y_screen(height), x_screen(right), BASELINE),
        fill=fill,
        outline=outline,
        width=2,
    )


def value_bracket(
    draw: ImageDraw.ImageDraw,
    t: Fraction,
    bounds: tuple[Fraction, Fraction],
) -> None:
    x = x_screen(t)
    lo, hi = bounds
    draw.line((x, y_screen(lo), x, y_screen(hi)), fill=BOX, width=3)
    draw.line((x - 5, y_screen(lo), x + 5, y_screen(lo)), fill=BOX, width=2)
    draw.line((x - 5, y_screen(hi), x + 5, y_screen(hi)), fill=BOX, width=2)


def frame(subdivisions: int, lower_last: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    draw.line((LEFT - 25, BASELINE, RIGHT + 26, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 18), fill=AXIS, width=3)

    cells = [Fraction(index, 2 * subdivisions) for index in range(subdivisions + 1)]
    boxes = {t: sine_box(t, lower_last) for t in cells}
    for t in cells:
        x = x_screen(t)
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
        draw.line((x, BASELINE - 6, x, BASELINE + 6), fill=AXIS, width=2)

    # sin(pi*t) is increasing on this interval: left lower boxes and right
    # upper boxes are the finite Darboux bounds.
    for left, right in zip(cells, cells[1:]):
        rectangle(draw, left, right, boxes[right][1], UPPER_FILL, UPPER_EDGE)
    for left, right in zip(cells, cells[1:]):
        rectangle(draw, left, right, boxes[left][0], LOWER_FILL, LOWER_EDGE)

    curve = []
    for index in range(241):
        t = Fraction(index, 480)
        curve.append((x_screen(t), y_screen(sin(pi * float(t)))))
    draw.line(curve, fill=CURVE, width=4, joint="curve")

    for t in cells:
        value_bracket(draw, t, boxes[t])
    for t, label in ((Fraction(0), "0"), (Fraction(1, 2), "1/2")):
        draw.text((x_screen(t), BASELINE + 29), label, font=SMALL, fill=INK, anchor="mm")
    draw.text((LEFT - 26, TOP + 2), "1", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT - 58, y_screen(Fraction(3, 4)) - 20), "sin(πt)",
              font=LABEL, fill=CURVE, anchor="mm")
    draw.text((RIGHT + 22, BASELINE + 4), "t", font=LABEL, fill=INK, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [
        frame(subdivisions, lower_last)
        for subdivisions, lower_last in ((1, 1), (2, 3), (4, 5), (8, 7))
    ]
    # Keep the broad first Taylor brackets in print: later frames make their
    # certified value intervals too narrow to see at page scale.
    frames[0].save(PNG_PATH, format="PNG", optimize=True)
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
