#!/usr/bin/env python3
"""Render finite rational secant--tangent brackets for `sqrt(2)`.

For a bracket `a^2 <= 2 <= b^2`, the secant through `(a, a^2)` and
`(b, b^2)` meets `y = 2` at `(2 + a*b) / (a + b)`.  The tangent at
`(b, b^2)` meets the same line at `(b + 2/b) / 2`.  The frames use those
literal `Fraction` updates; no floating-point state selects an endpoint.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "sqrt-secant-tangent.gif"
PNG_PATH = ASSET_DIR / "sqrt-secant-tangent.png"

TARGET = Fraction(2)
WIDTH, HEIGHT = 430, 700
# The data rectangle is 300 by 600 pixels for `[0, 9/4] × [0, 9/2]`.
# Thus one unit on either coordinate axis occupies the same 400/3 pixels.
LEFT, RIGHT = 70, 370
TOP, BASELINE = 25, 625
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
CURVE = (30, 64, 175, 255)
SECANT = (234, 88, 12, 255)
TANGENT = (13, 148, 136, 255)
NEXT = (126, 34, 206, 255)
GRID = (203, 213, 225, 255)


def font(size: int) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    """Load a compact readable font, retaining a portable fallback."""

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
    return LEFT + float(value / Fraction(9, 4)) * (RIGHT - LEFT)


def y_screen(value: Fraction) -> float:
    return BASELINE - float(value / Fraction(9, 2)) * (BASELINE - TOP)


def next_bracket(a: Fraction, b: Fraction) -> tuple[Fraction, Fraction]:
    """The exact rational secant and tangent intersections with `y = 2`."""

    return (TARGET + a * b) / (a + b), (b + TARGET / b) / 2


def stages() -> list[tuple[Fraction, Fraction]]:
    """Return three exact rational enclosure states."""

    a, b = Fraction(1), Fraction(2)
    result = []
    for _ in range(3):
        result.append((a, b))
        a, b = next_bracket(a, b)
    return result


def dot(draw: ImageDraw.ImageDraw, x: float, y: float, color: tuple[int, int, int, int]) -> None:
    draw.ellipse((x - 6, y - 6, x + 6, y + 6), fill=color, outline=WHITE, width=2)


def frame(a: Fraction, b: Fraction) -> Image.Image:
    """Draw one secant--tangent construction and its next bracket."""

    a_next, b_next = next_bracket(a, b)
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    # Half-unit rational grid cells are square because `x_screen` and
    # `y_screen` use the same pixels-per-unit scale.
    for half in range(1, 5):
        x = x_screen(Fraction(half, 2))
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
    for half in range(1, 10):
        y = y_screen(Fraction(half, 2))
        draw.line((LEFT, y, RIGHT, y), fill=GRID, width=1)

    draw.line((LEFT - 24, BASELINE, RIGHT + 22, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 10), fill=AXIS, width=3)
    for value, label in ((Fraction(0), "0"), (Fraction(1), "1"),
                         (Fraction(2), "2")):
        x = x_screen(value)
        draw.line((x, BASELINE - 6, x, BASELINE + 6), fill=AXIS, width=2)
        draw.text((x, BASELINE + 28), label, font=SMALL, fill=INK, anchor="mm")
    for value, label in ((Fraction(2), "2"), (Fraction(4), "4")):
        y = y_screen(value)
        draw.line((LEFT - 6, y, LEFT + 6, y), fill=AXIS, width=2)
        draw.text((LEFT - 18, y), label, font=SMALL, fill=INK, anchor="rm")

    points = []
    samples = 270
    for index in range(samples + 1):
        x = Fraction(9 * index, 4 * samples)
        points.append((x_screen(x), y_screen(x * x)))
    draw.line(points, fill=CURVE, width=4, joint="curve")

    target_y = y_screen(TARGET)

    ax, ay = x_screen(a), y_screen(a * a)
    bx, by = x_screen(b), y_screen(b * b)
    an_x, bn_x = x_screen(a_next), x_screen(b_next)

    # The secant and tangent meet the target level at the next two endpoints.
    draw.line((ax, ay, bx, by), fill=SECANT, width=3)
    tangent_left = x_screen(b_next)
    draw.line((tangent_left, target_y, bx, by), fill=TANGENT, width=3)
    dot(draw, ax, ay, SECANT)
    dot(draw, bx, by, TANGENT)
    dot(draw, an_x, target_y, SECANT)
    dot(draw, bn_x, target_y, TANGENT)

    # The small purple bracket is the next exact rational enclosure.
    draw.line((an_x, BASELINE, bn_x, BASELINE), fill=NEXT, width=7)
    draw.line((an_x, BASELINE - 16, an_x, BASELINE + 16), fill=NEXT, width=3)
    draw.line((bn_x, BASELINE - 16, bn_x, BASELINE + 16), fill=NEXT, width=3)
    draw.line((an_x, target_y, an_x, BASELINE - 17), fill=SECANT, width=2)
    draw.line((bn_x, target_y, bn_x, BASELINE - 17), fill=TANGENT, width=2)

    # Keep the labels distinct even once the rational endpoints are sub-pixel close.
    draw.text((ax - 12, BASELINE + 54), "a", font=SMALL, fill=SECANT, anchor="rm")
    draw.text((bx + 12, BASELINE + 54), "b", font=SMALL, fill=TANGENT, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(a, b) for a, b in stages()]
    # The first frame preserves the visibly distinct secant and tangent for print.
    frames[0].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1500, 1250, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
