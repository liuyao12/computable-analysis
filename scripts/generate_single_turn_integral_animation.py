#!/usr/bin/env python3
"""Render finite stages around the first normalized-sinc turning point.

The illustration uses s(t) = sin(pi*t)/(pi*t) on [0, 2].  Its first nonzero
turn is the irrational solution of tan(pi*t) = pi*t.  Each frame uses a
nested rational bracket for that point, draws finite endpoint rectangles for
the decreasing left and increasing right tails, and encloses the unknown
middle contribution by (right-left) * [-1/4, 0].

The plotted curve is numerical artwork only.  The rational brackets and the
three-part layout show the exact certificate shape that a future formal sinc
instance must obtain from certified sine/tangent sign boxes.
"""

from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "single-turn-integral.gif"
PNG_PATH = ASSET_DIR / "single-turn-integral.png"

WIDTH, HEIGHT = 620, 400
# The sinc input is the normalized angle t in sin(pi*t)/(pi*t).  Map t to its
# actual angle pi*t, using the same pixels per radian and per function-value
# unit.  This deliberately differs from square Cartesian scaling: it gives
# the underlying trigonometric oscillation its natural visual aspect.
TRIG_SCALE = 82
LEFT = 74
RIGHT = LEFT + round(2 * math.pi * TRIG_SCALE)
TOP, BASELINE = 170, 270
Y_MIN, Y_MAX = -0.28, 1.04
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
CURVE = (30, 41, 59, 255)
LOWER_FILL = (176, 227, 219, 255)
LOWER_EDGE = (13, 148, 136, 255)
UPPER_FILL = (254, 215, 170, 255)
UPPER_EDGE = (234, 88, 12, 255)
MIDDLE_FILL = (253, 230, 138, 255)
MIDDLE_EDGE = (202, 138, 4, 255)


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


def x_screen(t: Fraction | float) -> float:
    return LEFT + float(t) * math.pi * TRIG_SCALE


def y_screen(value: float) -> float:
    return BASELINE - value * TRIG_SCALE


def sinc(t: Fraction | float) -> float:
    t_float = float(t)
    if t_float == 0:
        return 1.0
    return math.sin(math.pi * t_float) / (math.pi * t_float)


def bracket_states() -> list[tuple[Fraction, Fraction]]:
    # Every pair contains the first positive root 1.430296653... of
    # tan(pi*t) = pi*t.  Their endpoints are deliberately rational.
    return [
        (Fraction(1), Fraction(3, 2)),
        (Fraction(7, 5), Fraction(29, 20)),
        (Fraction(143, 100), Fraction(287, 200)),
        (Fraction(7151, 5000), Fraction(3576, 2500)),
    ]


def area_rectangle(
    draw: ImageDraw.ImageDraw,
    left: Fraction,
    right: Fraction,
    height: float,
    fill: tuple[int, int, int, int],
    edge: tuple[int, int, int, int],
) -> None:
    y_zero = y_screen(0)
    y_height = y_screen(height)
    draw.rectangle(
        (x_screen(left), min(y_zero, y_height), x_screen(right), max(y_zero, y_height)),
        fill=fill,
        outline=edge,
        width=1,
    )


def monotone_rectangles(
    draw: ImageDraw.ImageDraw,
    start: Fraction,
    stop: Fraction,
    subdivisions: int,
) -> None:
    """Draw finite lower and upper endpoint sums on one monotone tail."""

    if start == stop:
        return
    cells = [
        start + (stop - start) * Fraction(index, subdivisions)
        for index in range(subdivisions + 1)
    ]
    for cell_left, cell_right in zip(cells, cells[1:]):
        left_value, right_value = sinc(cell_left), sinc(cell_right)
        lower, upper = min(left_value, right_value), max(left_value, right_value)
        area_rectangle(draw, cell_left, cell_right, upper, UPPER_FILL, UPPER_EDGE)
        area_rectangle(draw, cell_left, cell_right, lower, LOWER_FILL, LOWER_EDGE)


def frame(left: Fraction, right: Fraction, subdivisions: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    for half in range(1, 4):
        x = x_screen(Fraction(half, 2))
        draw.line((x, TOP, x, y_screen(Y_MIN)), fill=GRID, width=1)
    for value in (-0.25, 0.25, 0.5, 0.75, 1.0):
        y = y_screen(value)
        draw.line((LEFT, y, RIGHT, y), fill=GRID, width=1)

    draw.line((LEFT - 20, y_screen(0), RIGHT + 25, y_screen(0)), fill=AXIS, width=3)
    draw.line((LEFT, y_screen(Y_MIN) + 18, LEFT, TOP - 18), fill=AXIS, width=3)

    monotone_rectangles(draw, Fraction(0), left, subdivisions)
    monotone_rectangles(draw, right, Fraction(2), subdivisions)
    draw.rectangle(
        (x_screen(left), y_screen(0), x_screen(right), y_screen(-0.25)),
        fill=MIDDLE_FILL,
        outline=MIDDLE_EDGE,
        width=2,
    )

    points = [(x_screen(index / 600), y_screen(sinc(index / 600)))
              for index in range(1201)]
    draw.line(points, fill=CURVE, width=4, joint="curve")

    for tick, label in ((0, "0"), (1, "1"), (2, "2")):
        x = x_screen(tick)
        draw.line((x, y_screen(0) - 7, x, y_screen(0) + 7), fill=AXIS, width=2)
        draw.text((x, y_screen(0) + 28), label, font=SMALL, fill=INK, anchor="mm")
    for tick, label in ((-0.25, "−¼"), (0, "0"), (1, "1")):
        y = y_screen(tick)
        draw.line((LEFT - 7, y, LEFT + 7, y), fill=AXIS, width=2)
        draw.text((LEFT - 14, y), label, font=SMALL, fill=INK, anchor="rm")

    left_x, right_x = x_screen(left), x_screen(right)
    draw.line((left_x, TOP, left_x, y_screen(-0.25)), fill=MIDDLE_EDGE, width=2)
    draw.line((right_x, TOP, right_x, y_screen(-0.25)), fill=MIDDLE_EDGE, width=2)
    draw.text((left_x - 8, y_screen(0) + 52), "l", font=SMALL,
              fill=MIDDLE_EDGE, anchor="rm")
    draw.text((right_x + 8, y_screen(0) + 52), "r", font=SMALL,
              fill=MIDDLE_EDGE, anchor="lm")
    draw.text((RIGHT + 20, y_screen(0) + 4), "t", font=LABEL, fill=INK, anchor="lm")
    draw.text((LEFT - 2, TOP - 20), "s", font=LABEL, fill=INK, anchor="mm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [
        frame(left, right, 2 ** stage)
        for stage, (left, right) in enumerate(bracket_states())
    ]
    frames[1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1250, 1250, 1250, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
