#!/usr/bin/env python3
"""Render equal parameter divisions transported to unequal image divisions.

The finite substitution picture uses x = phi(t) = t^2 on a fixed parameter
interval [t0, t1].  At each stage the t line is divided equally; the exact
rational images phi(t_i) form an unequal x subdivision.  The connecting
segments expose the finite data behind a change of variables rather than
suggesting a completed-real substitution rule.
"""

from __future__ import annotations

from fractions import Fraction
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "substitution-partition.gif"
PNG_PATH = ASSET_DIR / "substitution-partition.png"

WIDTH, HEIGHT = 620, 330
LEFT, RIGHT = 96, 524
T_AXIS, X_AXIS = 92, 222
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
MAP = (30, 64, 175, 255)


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


def screen(value: Fraction) -> float:
    return LEFT + float(value) * (RIGHT - LEFT)


def phi(t: Fraction) -> Fraction:
    return t * t


def frame(subdivisions: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    values = [Fraction(index, subdivisions) for index in range(subdivisions + 1)]

    draw.line((LEFT - 20, T_AXIS, RIGHT + 24, T_AXIS), fill=AXIS, width=3)
    draw.line((LEFT - 20, X_AXIS, RIGHT + 24, X_AXIS), fill=AXIS, width=3)
    for t in values:
        t_x, x_x = screen(t), screen(phi(t))
        draw.line((t_x, T_AXIS + 8, x_x, X_AXIS - 8), fill=GRID, width=2)
        draw.line((t_x, T_AXIS - 7, t_x, T_AXIS + 7), fill=AXIS, width=2)
        draw.line((x_x, X_AXIS - 7, x_x, X_AXIS + 7), fill=MAP, width=2)
        draw.ellipse((t_x - 4, T_AXIS - 4, t_x + 4, T_AXIS + 4), fill=AXIS)
        draw.ellipse((x_x - 4, X_AXIS - 4, x_x + 4, X_AXIS + 4), fill=MAP)

    draw.text((LEFT - 11, T_AXIS + 30), "t0", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT + 9, T_AXIS + 30), "t1", font=SMALL, fill=INK, anchor="mm")
    draw.text((RIGHT + 26, T_AXIS + 3), "t", font=LABEL, fill=INK, anchor="lm")
    draw.text((RIGHT + 26, X_AXIS + 3), "x=phi(t)", font=LABEL, fill=INK, anchor="lm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(subdivisions) for subdivisions in (1, 2, 4, 8)]
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
