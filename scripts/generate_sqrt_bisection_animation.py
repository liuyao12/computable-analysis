#!/usr/bin/env python3
"""Render finite stages of Lean's rational square-root bisection algorithm.

The computation is `sqrtBisect 2 k { lo := 0, hi := sqrtUpperBound 2 }` from
`ComputableAnalysis.AlgebraicFunctions`.  At each finite stage the midpoint
is rational and its square is compared with the rational target 2; the GIF
therefore depicts the actual bracket update, not an appeal to a completed
square root.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "sqrt-bisection.gif"
PNG_PATH = ASSET_DIR / "sqrt-bisection.png"

TARGET = Fraction(2)
WIDTH, HEIGHT = 720, 500
LEFT, RIGHT = 92, 646
TOP, BASELINE = 54, 400
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
CURVE = (30, 64, 175, 255)
TARGET_LINE = (234, 88, 12, 255)
BRACKET = (13, 148, 136, 255)
BRACKET_FILL = (204, 251, 241, 255)
MIDPOINT = (126, 34, 206, 255)
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


def fraction_text(value: Fraction) -> str:
    """Print a rational in the same elementary form used in the algorithm."""

    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def x_screen(value: Fraction) -> float:
    return LEFT + float(value / 2) * (RIGHT - LEFT)


def y_screen(value: Fraction) -> float:
    return BASELINE - float(value / Fraction(9, 2)) * (BASELINE - TOP)


def bisection_stages() -> list[tuple[Fraction, Fraction]]:
    """Return `sqrtBisect 2 k [0, 2]` for the displayed finite stages."""

    lo, hi = Fraction(0), Fraction(2)
    stages = [(lo, hi)]
    for _ in range(5):
        midpoint = (lo + hi) / 2
        if midpoint * midpoint <= TARGET:
            lo = midpoint
        else:
            hi = midpoint
        stages.append((lo, hi))
    return stages


def stage_frame(stage: int, interval: tuple[Fraction, Fraction]) -> Image.Image:
    """Render one certified bracket and the next rational midpoint test."""

    lo, hi = interval
    midpoint = (lo + hi) / 2
    midpoint_square = midpoint * midpoint
    keep_right = midpoint_square <= TARGET

    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    # Rational-coordinate axes and the polynomial graph x^2.
    draw.line((LEFT - 25, BASELINE, RIGHT + 22, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 12), fill=AXIS, width=3)
    for tick in range(3):
        x = x_screen(Fraction(tick))
        draw.line((x, BASELINE - 6, x, BASELINE + 6), fill=AXIS, width=2)
        draw.text((x, BASELINE + 28), str(tick), font=SMALL, fill=INK, anchor="mm")
    for tick in (2, 4):
        y = y_screen(Fraction(tick))
        draw.line((LEFT - 6, y, LEFT + 6, y), fill=AXIS, width=2)
        draw.text((LEFT - 17, y), str(tick), font=SMALL, fill=INK, anchor="rm")

    curve_points = []
    samples = 240
    for index in range(samples + 1):
        x = Fraction(2 * index, samples)
        curve_points.append((x_screen(x), y_screen(x * x)))
    draw.line(curve_points, fill=CURVE, width=4, joint="curve")

    target_y = y_screen(TARGET)
    draw.line((LEFT, target_y, RIGHT, target_y), fill=TARGET_LINE, width=3)
    draw.text((RIGHT - 4, target_y - 14), "q = 2", font=LABEL,
              fill=TARGET_LINE, anchor="rm")
    draw.text((RIGHT - 12, y_screen(Fraction(15, 4)) - 18), "x²", font=LABEL,
              fill=CURVE, anchor="mm")

    # The teal segment is the current `QInterval`; it is wholly rational.
    left_x, right_x = x_screen(lo), x_screen(hi)
    draw.rounded_rectangle((left_x, BASELINE - 17, right_x, BASELINE + 17),
                           radius=8, fill=BRACKET_FILL)
    draw.line((left_x, BASELINE, right_x, BASELINE), fill=BRACKET, width=6)
    draw.line((left_x, BASELINE - 23, left_x, BASELINE + 23), fill=BRACKET, width=3)
    draw.line((right_x, BASELINE - 23, right_x, BASELINE + 23), fill=BRACKET, width=3)

    midpoint_x, midpoint_y = x_screen(midpoint), y_screen(midpoint_square)
    draw.line((midpoint_x, BASELINE, midpoint_x, midpoint_y), fill=GRID, width=2)
    draw.ellipse((midpoint_x - 6, midpoint_y - 6, midpoint_x + 6, midpoint_y + 6),
                 fill=MIDPOINT, outline=WHITE, width=2)
    draw.text((midpoint_x, BASELINE + 55), f"m = {fraction_text(midpoint)}",
              font=SMALL, fill=MIDPOINT, anchor="mm")

    relation = "≤" if keep_right else ">"
    retained = f"[{fraction_text(midpoint)}, {fraction_text(hi)}]" if keep_right else \
        f"[{fraction_text(lo)}, {fraction_text(midpoint)}]"
    draw.text((LEFT, TOP - 1),
              f"{stage} bisections: I = [{fraction_text(lo)}, {fraction_text(hi)}]",
              font=LABEL, fill=INK, anchor="la")
    draw.text((LEFT, TOP + 27),
              f"m² = {fraction_text(midpoint_square)} {relation} 2; retain {retained}",
              font=SMALL, fill=INK, anchor="la")
    draw.text((RIGHT + 8, BASELINE + 4), "x", font=LABEL, fill=INK, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [stage_frame(stage, interval) for stage, interval in enumerate(bisection_stages())]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1300, 1300, 1300, 1300, 1300, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
