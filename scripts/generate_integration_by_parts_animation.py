#!/usr/bin/env python3
"""Render paired finite subdivisions for integration by parts.

The parameter interval is the fixed rational interval [t0, t1].  An affine
f and a quadratic g make the common equal t-subdivision visible as equal
f(t)-steps and unequal g(t)-steps.  The orange horizontal-first and teal
vertical-first staircases pass through precisely the same samples
(f(t_i), g(t_i)).  Their pale corner rectangles shrink under refinement;
every displayed datum is rational.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "integration-by-parts-cell.gif"
PNG_PATH = ASSET_DIR / "integration-by-parts-cell.png"

WIDTH, HEIGHT = 600, 530
# Both displayed coordinate ranges are [0, 1], so the f and g units are
# square.  The nonuniformity in the picture comes only from g(t)=t^2.
LEFT, RIGHT = 120, 480
TOP, BASELINE = 38, 398
PARAMETER_LINE = 464
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
CURVE = (38, 50, 68, 255)
ORANGE = (234, 88, 12, 255)
TEAL = (13, 148, 136, 255)
CORNER = (254, 243, 199, 255)


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
LABEL = font(19)


T0 = Fraction(0)
T1 = Fraction(1)


def normalized_parameter(t: Fraction) -> Fraction:
    """The affine demonstrator on the fixed interval [t0, t1]."""
    return (t - T0) / (T1 - T0)


def f(t: Fraction) -> Fraction:
    return normalized_parameter(t)


def g(t: Fraction) -> Fraction:
    return normalized_parameter(t) ** 2


def x_screen(value: Fraction | float) -> float:
    return LEFT + float(value) * (RIGHT - LEFT)


def y_screen(value: Fraction | float) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


def draw_path(
    draw: ImageDraw.ImageDraw,
    points: list[tuple[float, float]],
    colour: tuple[int, int, int, int],
) -> None:
    for left, right in zip(points, points[1:]):
        draw.line((*left, *right), fill=colour, width=4)


def frame(subdivisions: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    parameters = [
        T0 + Fraction(index, subdivisions) * (T1 - T0)
        for index in range(subdivisions + 1)
    ]
    f_values = [f(t) for t in parameters]
    g_values = [g(t) for t in parameters]

    # Equal f(t)-divisions are vertical; their g(t)-images are intentionally
    # uneven horizontal levels.  Both are the image of the same equal t_i mesh.
    for value in f_values:
        x = x_screen(value)
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
    for value in g_values[1:]:
        y = y_screen(value)
        draw.line((LEFT, y, RIGHT, y), fill=GRID, width=1)

    draw.line((LEFT - 22, BASELINE, RIGHT + 28, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 18), fill=AXIS, width=3)

    # This ruler is the source subdivision.  The plot itself is in the
    # (f(t), g(t)) plane, so t is deliberately shown as a separate fixed
    # interval rather than mislabeled as a coordinate axis.
    draw.line((LEFT, PARAMETER_LINE, RIGHT, PARAMETER_LINE), fill=AXIS, width=3)
    for t in parameters:
        x = x_screen(normalized_parameter(t))
        draw.line((x, PARAMETER_LINE - 8, x, PARAMETER_LINE + 8), fill=AXIS, width=2)

    curve = []
    for index in range(241):
        t = T0 + Fraction(index, 240) * (T1 - T0)
        curve.append((x_screen(f(t)), y_screen(g(t))))
    draw.line(curve, fill=CURVE, width=3, joint="curve")

    # The rectangle between a horizontal-first and vertical-first step is the
    # finite corner discrepancy.  It becomes small because both subdivisions
    # are driven by the same increasingly fine parameter mesh.
    for left_f, right_f, left_g, right_g in zip(
        f_values, f_values[1:], g_values, g_values[1:]
    ):
        draw.rectangle(
            (x_screen(left_f), y_screen(right_g),
             x_screen(right_f), y_screen(left_g)),
            fill=CORNER,
        )

    lower = [(x_screen(f_values[0]), y_screen(g_values[0]))]
    upper = [(x_screen(f_values[0]), y_screen(g_values[0]))]
    for left_f, right_f, left_g, right_g in zip(
        f_values, f_values[1:], g_values, g_values[1:]
    ):
        # Horizontal-first uses the old g endpoint; vertical-first uses the
        # old f endpoint.  These are the two finite integration-by-parts
        # zigzags whose common refinement is the parameter partition.
        lower.extend([(x_screen(right_f), y_screen(left_g)),
                      (x_screen(right_f), y_screen(right_g))])
        upper.extend([(x_screen(left_f), y_screen(right_g)),
                      (x_screen(right_f), y_screen(right_g))])
    draw_path(draw, lower, ORANGE)
    draw_path(draw, upper, TEAL)

    for fv, gv in zip(f_values, g_values):
        x, y = x_screen(fv), y_screen(gv)
        draw.ellipse((x - 4, y - 4, x + 4, y + 4), fill=CURVE)

    draw.text((LEFT - 3, PARAMETER_LINE + 30), "t0", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT + 3, PARAMETER_LINE + 30), "t1", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT + 25, PARAMETER_LINE + 3), "t", font=LABEL, fill=INK, anchor="lm")
    draw.text((RIGHT + 26, BASELINE + 4), "f(t)", font=LABEL, fill=INK, anchor="lm")
    draw.text((LEFT - 4, TOP - 22), "g(t)", font=LABEL, fill=INK, anchor="mm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(subdivisions) for subdivisions in (1, 2, 4, 8, 16)]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1050, 1050, 1050, 1050, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
