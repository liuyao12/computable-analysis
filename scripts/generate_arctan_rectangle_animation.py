#!/usr/bin/env python3
"""Render the finite rectangle enclosures for the arctangent kernel.

The frames are the same midpoint partitions used by
`ArctanGeometry.arctanAreaLoopState 1 n`: 1, 2, 4, and 8 cells of `[0, 1]`.
On a cell `[p, r]`, the decreasing rational kernel `1 / (1 + t^2)` has the
exact lower and upper rectangles respectively at `r` and `p`.  Thus the GIF
shows a finite certified enclosure rather than a picture of a completed
integral.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "arctan-rectangle-enclosure.gif"
PNG_PATH = ASSET_DIR / "arctan-rectangle-enclosure.png"

WIDTH, HEIGHT = 720, 500
# The kernel is drawn on [0, 1] x [0, 1].  Keep Cartesian units square so the
# decreasing rational graph is not widened merely to fill the canvas.
LEFT, RIGHT = 196, 524
TOP, BASELINE = 70, 398
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
CURVE = (30, 64, 175, 255)
UPPER_FILL = (254, 215, 170, 255)
UPPER_EDGE = (234, 88, 12, 255)
LOWER_FILL = (176, 227, 219, 255)
LOWER_EDGE = (13, 148, 136, 255)
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


LABEL = font(18)
SMALL = font(16)


def kernel(t: Fraction) -> Fraction:
    return Fraction(1, 1) / (Fraction(1, 1) + t * t)


def x_screen(t: Fraction) -> float:
    return LEFT + float(t) * (RIGHT - LEFT)


def y_screen(value: Fraction) -> float:
    return BASELINE - float(value) * (BASELINE - TOP)


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


def stage_frame(subdivisions: int) -> Image.Image:
    """Render lower/right and upper/left rectangles at one exact stage."""

    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    # Axes and dyadic cell boundaries precede the coloured finite enclosures.
    draw.line((LEFT - 28, BASELINE, RIGHT + 22, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 18), fill=AXIS, width=3)
    values = [Fraction(index, subdivisions) for index in range(subdivisions + 1)]
    for value in values:
        x = x_screen(value)
        draw.line((x, BASELINE, x, TOP + 5), fill=GRID, width=1)
        draw.line((x, BASELINE - 6, x, BASELINE + 6), fill=AXIS, width=2)

    # For a decreasing kernel, left endpoints give the outer (upper) sum and
    # right endpoints give the inner (lower) sum.  Painting the latter last
    # leaves precisely the certified gap visible in orange.
    for left, right in zip(values, values[1:]):
        rectangle(draw, left, right, kernel(left), UPPER_FILL, UPPER_EDGE)
    for left, right in zip(values, values[1:]):
        rectangle(draw, left, right, kernel(right), LOWER_FILL, LOWER_EDGE)

    curve_points = []
    samples = 240
    for index in range(samples + 1):
        t = Fraction(index, samples)
        curve_points.append((x_screen(t), y_screen(kernel(t))))
    draw.line(curve_points, fill=CURVE, width=4, joint="curve")

    draw.text((LEFT - 1, BASELINE + 28), "0", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT, BASELINE + 28), "1", font=SMALL, fill=INK, anchor="mm")
    draw.text((LEFT - 28, TOP + 3), "1", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT - 42, y_screen(kernel(Fraction(15, 16))) - 25),
              "1/(1+t²)", font=LABEL, fill=CURVE, anchor="mm")
    draw.text((RIGHT + 8, BASELINE + 4), "t", font=LABEL, fill=INK, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [stage_frame(subdivisions) for subdivisions in (1, 2, 4, 8)]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1200, 1200, 1200, 1800],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
