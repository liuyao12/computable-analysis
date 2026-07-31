#!/usr/bin/env python3
"""Render lower and upper Darboux stages for an exact rational example.

The frames use the decreasing rational function ``f(t) = 1 / (1 + t^2)`` on
``[0, 1]``.  Every endpoint value and every rectangle height is a rational
number.  Green right-endpoint rectangles are the lower sum and orange
left-endpoint rectangles are the upper sum.  This exact case contrasts with
the interval-valued sine stage rendered by the companion script.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "monotone-integral-stage.gif"
PNG_PATH = ASSET_DIR / "monotone-integral-stage.png"

WIDTH, HEIGHT = 700, 500
LEFT, RIGHT = 82, 642
TOP, BASELINE = 58, 398
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
CURVE = (30, 64, 175, 255)
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


def x_screen(t: Fraction) -> float:
    return LEFT + float(t) * (RIGHT - LEFT)


def y_screen(value: Fraction) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


def value(t: Fraction) -> Fraction:
    return Fraction(1, 1) / (Fraction(1, 1) + t * t)


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


def frame(subdivisions: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    draw.line((LEFT - 25, BASELINE, RIGHT + 26, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 18), fill=AXIS, width=3)

    cells = [Fraction(index, subdivisions) for index in range(subdivisions + 1)]
    for t in cells:
        x = x_screen(t)
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
        draw.line((x, BASELINE - 6, x, BASELINE + 6), fill=AXIS, width=2)

    # This function is decreasing: left endpoints give the upper bracket.
    # Paint it first so the orange finite gap remains visible.
    for left, right in zip(cells, cells[1:]):
        rectangle(draw, left, right, value(left), UPPER_FILL, UPPER_EDGE)
    for left, right in zip(cells, cells[1:]):
        rectangle(draw, left, right, value(right), LOWER_FILL, LOWER_EDGE)

    points = []
    for index in range(241):
        t = Fraction(index, 240)
        points.append((x_screen(t), y_screen(value(t))))
    draw.line(points, fill=CURVE, width=4, joint="curve")

    for t, label in ((Fraction(0), "0"), (Fraction(1), "1")):
        draw.text((x_screen(t), BASELINE + 29), label, font=SMALL, fill=INK, anchor="mm")
    draw.text((LEFT - 26, TOP + 2), "1", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT - 72, y_screen(Fraction(3, 5)) - 20), "1/(1+t²)", font=LABEL,
              fill=CURVE, anchor="mm")
    draw.text((RIGHT + 22, BASELINE + 4), "t", font=LABEL, fill=INK, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(subdivisions) for subdivisions in (1, 2, 4, 8)]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
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
