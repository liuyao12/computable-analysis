#!/usr/bin/env python3
"""Render the Figure 2.1 rational-circle subdivision animation.

The diagram is deliberately derived from the same rational chart used in the
blueprint: P(t) = ((1 - t^2)/(1 + t^2), 2t/(1 + t^2)).  Keeping this small
generator in the repository makes the GIF reproducible and lets the static
PDF fallback use the exact final GIF frame.
"""

from __future__ import annotations

from math import ceil
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "rational-circle-subdivision.gif"
PNG_PATH = ASSET_DIR / "rational-circle-subdivision.png"

WIDTH, HEIGHT = 1400, 900
CENTER = (480, 650)
RADIUS = 380
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (111, 126, 140, 255)
BLUE = (37, 99, 235, 255)
BLUE_FAINT = (37, 99, 235, 76)
TEAL = (13, 148, 136, 255)
TEAL_FILL = (225, 247, 243, 255)
CORAL = (234, 88, 12, 255)
ARC = (52, 64, 76, 255)
GRID = (148, 163, 184, 255)


def font(size: int, bold: bool = False) -> ImageFont.FreeTypeFont | ImageFont.ImageFont:
    """Load a readable system font, while retaining a portable fallback."""

    names = (
        [
            "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
            "/Library/Fonts/Arial Bold.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        ]
        if bold
        else [
            "/System/Library/Fonts/Supplemental/Arial.ttf",
            "/Library/Fonts/Arial.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        ]
    )
    for name in names:
        try:
            return ImageFont.truetype(name, size)
        except OSError:
            continue
    return ImageFont.load_default()


TITLE_FONT = font(38, bold=True)
LABEL_FONT = font(25)
SMALL_FONT = font(21)


def point(t: float) -> tuple[float, float]:
    """The first-quadrant rational circle point P(t), in Euclidean coordinates."""

    denominator = 1 + t * t
    return ((1 - t * t) / denominator, (2 * t) / denominator)


def screen(p: tuple[float, float]) -> tuple[float, float]:
    """Map a mathematical point to the raster canvas."""

    return (CENTER[0] + RADIUS * p[0], CENTER[1] - RADIUS * p[1])


def tangent_intersection(
    p: tuple[float, float], q: tuple[float, float]
) -> tuple[float, float]:
    """Intersection of the unit-circle tangents at distinct points p and q."""

    determinant = p[0] * q[1] - p[1] * q[0]
    return ((q[1] - p[1]) / determinant, (p[0] - q[0]) / determinant)


def draw_dashed_line(
    draw: ImageDraw.ImageDraw,
    start: tuple[float, float],
    end: tuple[float, float],
    fill: tuple[int, int, int, int],
    width: int,
    dash: int = 16,
    gap: int = 11,
) -> None:
    """Draw a crisp dashed segment without a graphics-library dependency."""

    dx, dy = end[0] - start[0], end[1] - start[1]
    length = (dx * dx + dy * dy) ** 0.5
    if length == 0:
        return
    position = 0.0
    while position < length:
        finish = min(position + dash, length)
        draw.line(
            (
                start[0] + dx * position / length,
                start[1] + dy * position / length,
                start[0] + dx * finish / length,
                start[1] + dy * finish / length,
            ),
            fill=fill,
            width=width,
        )
        position += dash + gap


def dot(draw: ImageDraw.ImageDraw, p: tuple[float, float], radius: int, fill: tuple[int, int, int, int]) -> None:
    draw.ellipse((p[0] - radius, p[1] - radius, p[0] + radius, p[1] + radius), fill=fill)


def text_centered(
    draw: ImageDraw.ImageDraw,
    xy: tuple[float, float],
    text: str,
    fill: tuple[int, int, int, int],
    used_font: ImageFont.FreeTypeFont | ImageFont.ImageFont,
) -> None:
    draw.text(xy, text, font=used_font, fill=fill, anchor="mm")


def stage_frame(subdivisions: int, iteration: int) -> Image.Image:
    """Render one rational parameter subdivision stage."""

    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    origin = screen((0, 0))
    west = screen((-1, 0))
    top = screen((0, 1))
    right = screen((1, 0))

    # Quiet axes and the exact unit arc give the fixed geometry for every frame.
    draw.line((west[0] - 28, origin[1], right[0] + 42, origin[1]), fill=AXIS, width=3)
    draw.line((origin[0], origin[1] + 30, origin[0], top[1] - 34), fill=AXIS, width=3)
    draw.arc(
        (CENTER[0] - RADIUS, CENTER[1] - RADIUS, CENTER[0] + RADIUS, CENTER[1] + RADIUS),
        start=270,
        end=360,
        fill=ARC,
        width=6,
    )

    values = [index / subdivisions for index in range(subdivisions + 1)]
    circle_points = [point(value) for value in values]
    raster_points = [screen(p) for p in circle_points]

    # Equal vertical marks and their rays are the main visual explanation.
    draw.line((origin, top), fill=(100, 116, 139, 255), width=5)
    for value, endpoint in zip(values, raster_points):
        height = screen((0, value))
        draw.line((west, height, endpoint), fill=BLUE_FAINT, width=3)
        draw.line((height[0] - 9, height[1], height[0] + 9, height[1]), fill=GRID, width=3)
        dot(draw, height, 6, BLUE)

    # The visible wedge is the inscribed polygon, not an arbitrary shaded arc.
    draw.polygon([origin, *raster_points], fill=TEAL_FILL)
    draw.line(raster_points, fill=TEAL, width=8, joint="curve")

    # The tangent-intersection chain is the circumscribed polygon.
    tangent_points = [
        screen(tangent_intersection(left, right_point))
        for left, right_point in zip(circle_points, circle_points[1:])
    ]
    outer_chain = [raster_points[0], *tangent_points, raster_points[-1]]
    for left, right_point in zip(outer_chain, outer_chain[1:]):
        draw_dashed_line(draw, left, right_point, CORAL, width=6)

    # Points are drawn last so the rational samples remain unmistakable.
    for sample in raster_points:
        dot(draw, sample, 8, INK)
    dot(draw, origin, 8, INK)
    dot(draw, west, 8, INK)

    # A compact visual legend replaces paragraph-level prose in the original figure.
    text_centered(draw, (1050, 128), "rational-circle refinement", INK, TITLE_FONT)
    text_centered(
        draw,
        (1050, 182),
        f"iteration {iteration}:  {subdivisions} equal vertical pieces",
        INK,
        LABEL_FONT,
    )
    legend_x, legend_y = 970, 275
    draw.line((legend_x, legend_y, legend_x + 86, legend_y), fill=BLUE, width=5)
    draw.text((legend_x + 108, legend_y), "projection rays", font=LABEL_FONT, fill=INK, anchor="lm")
    draw.line((legend_x, legend_y + 57, legend_x + 86, legend_y + 57), fill=TEAL, width=8)
    draw.text((legend_x + 108, legend_y + 57), "inscribed polygon", font=LABEL_FONT, fill=INK, anchor="lm")
    draw_dashed_line(draw, (legend_x, legend_y + 114), (legend_x + 86, legend_y + 114), CORAL, width=6)
    draw.text((legend_x + 108, legend_y + 114), "circumscribed polygon", font=LABEL_FONT, fill=INK, anchor="lm")

    draw.text((west[0] - 10, west[1] + 39), "(-1, 0)", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((origin[0] + 1, origin[1] + 39), "0", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((top[0] - 25, top[1] - 8), "1", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((right[0] + 22, right[1] + 36), "P(0)", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((top[0] + 48, top[1] - 20), "P(1)", font=SMALL_FONT, fill=INK, anchor="mm")

    # A short progress indicator makes the loop readable even when viewed once.
    bar_x, bar_y, bar_width = 980, 770, 300
    draw.rounded_rectangle((bar_x, bar_y, bar_x + bar_width, bar_y + 12), radius=6, fill=(226, 232, 240, 255))
    completed = iteration / 4
    draw.rounded_rectangle((bar_x, bar_y, bar_x + ceil(bar_width * completed), bar_y + 12), radius=6, fill=BLUE)
    draw.text((1130, 814), "vertical marks → rational arc points", font=SMALL_FONT, fill=INK, anchor="mm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    stages = [1, 2, 4, 8]
    frames = [stage_frame(subdivisions, index) for index, subdivisions in enumerate(stages, start=1)]
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
