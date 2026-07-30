#!/usr/bin/env python3
"""Render finite rational brackets of Lean's `piLeibniz` evaluator.

The state transition is copied directly from `ComputableAnalysis.Pi.leibnizSeries`:
at iteration `i` it subtracts `1 / (4*i + 3)` from the previous upper endpoint
and then adds `1 / (4*i + 5)`.  `piLeibniz` multiplies the resulting bracket
by four.  Every plotted coordinate is converted from an exact `Fraction`.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "leibniz-interval.gif"
PNG_PATH = ASSET_DIR / "leibniz-interval.png"

WIDTH, HEIGHT = 720, 360
LEFT, RIGHT = 86, 650
TOP, AXIS_Y = 50, 226
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
BRACKET = (13, 148, 136, 255)
BRACKET_FILL = (204, 251, 241, 255)
ENDPOINT = (234, 88, 12, 255)
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


LABEL = font(19)
SMALL = font(16)


def x_screen(value: Fraction) -> float:
    """Place exact values on the fixed rational axis [5/2, 7/2]."""

    return LEFT + float(value - Fraction(5, 2)) * (RIGHT - LEFT)


def leibniz_bracket(stage: int) -> tuple[Fraction, Fraction]:
    """Return the exact endpoints of `piLeibniz.compute stage`."""

    upper, lower = Fraction(1), Fraction(0)
    for index in range(stage):
        lower = upper - Fraction(1, 4 * index + 3)
        upper = lower + Fraction(1, 4 * index + 5)
    return 4 * lower, 4 * upper


def stage_frame(stage: int) -> Image.Image:
    """Render one finite `4[S_{2n}, S_{2n+1}]` bracket."""

    lo, hi = leibniz_bracket(stage)
    width = hi - lo
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    draw.text((LEFT, TOP), "Leibniz finite bracket", font=LABEL,
              fill=INK, anchor="la")
    draw.text((LEFT, TOP + 32),
              f"stage n = {stage}:  I(n) = 4[S(2n), S(2n+1)]", font=SMALL,
              fill=INK, anchor="la")
    draw.text((LEFT, TOP + 57),
              f"exact width = 4/{4 * stage + 1}", font=SMALL,
              fill=INK, anchor="la")

    draw.line((LEFT - 18, AXIS_Y, RIGHT + 18, AXIS_Y), fill=AXIS, width=3)
    for tick, label in ((Fraction(5, 2), "5/2"), (Fraction(3), "3"),
                        (Fraction(7, 2), "7/2")):
        x = x_screen(tick)
        draw.line((x, AXIS_Y - 7, x, AXIS_Y + 7), fill=AXIS, width=2)
        draw.line((x, AXIS_Y - 54, x, AXIS_Y - 10), fill=GRID, width=1)
        draw.text((x, AXIS_Y + 29), label, font=SMALL, fill=INK, anchor="mm")

    left_x, right_x = x_screen(lo), x_screen(hi)
    draw.rounded_rectangle((left_x, AXIS_Y - 22, right_x, AXIS_Y + 22),
                           radius=10, fill=BRACKET_FILL)
    draw.line((left_x, AXIS_Y, right_x, AXIS_Y), fill=BRACKET, width=7)
    for x in (left_x, right_x):
        draw.line((x, AXIS_Y - 30, x, AXIS_Y + 30), fill=ENDPOINT, width=3)

    draw.text(((left_x + right_x) / 2, AXIS_Y - 48), "certified rational interval",
              font=SMALL, fill=BRACKET, anchor="mm")
    draw.text((LEFT, HEIGHT - 42),
              "All positions are rendered from exact rational endpoints.",
              font=SMALL, fill=AXIS, anchor="la")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [stage_frame(stage) for stage in (1, 2, 4, 8)]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1350, 1350, 1350, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
