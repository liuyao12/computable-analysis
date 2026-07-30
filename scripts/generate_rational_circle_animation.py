#!/usr/bin/env python3
"""Render the Figure 2.1 rational-circle subdivision animation.

The diagram is deliberately derived from the same rational chart used in the
blueprint: P(t) = ((1 - t^2)/(1 + t^2), 2t/(1 + t^2)).  Keeping this small
generator in the repository makes the GIF reproducible and lets the static
PDF fallback use the exact final GIF frame.
"""

from __future__ import annotations

from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "rational-circle-subdivision.gif"
PNG_PATH = ASSET_DIR / "rational-circle-subdivision.png"

# Keep the source itself narrower than a typical reading column.  The web
# renderer preserves the GIF's intrinsic size if it cannot interpret a TeX
# relative width, so a compact canvas also prevents horizontal scrolling.
WIDTH, HEIGHT = 720, 580
CENTER = (330, 430)
RADIUS = 250
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (111, 126, 140, 255)
PROJECTION = (148, 163, 184, 255)
TEAL = (13, 148, 136, 255)
TEAL_FILL = (176, 227, 219, 255)
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


SMALL_FONT = font(17)


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


def dot(draw: ImageDraw.ImageDraw, p: tuple[float, float], radius: int, fill: tuple[int, int, int, int]) -> None:
    draw.ellipse((p[0] - radius, p[1] - radius, p[0] + radius, p[1] + radius), fill=fill)


def stage_frame(subdivisions: int) -> Image.Image:
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

    # The coloured wedge is precisely the inscribed polygon whose area is the
    # lower certificate.  Draw it before the construction rays so both remain
    # visible in every GIF frame.
    draw.polygon([origin, *raster_points], fill=TEAL_FILL)

    # Equal vertical marks and the straight projection segments encode the
    # rational parametrisation.  Each segment from (-1, 0) reaches its point
    # on the arc; the thin neutral grey keeps it subordinate to the area data.
    draw.line((origin, top), fill=(100, 116, 139, 255), width=4)
    for value, endpoint in zip(values, raster_points):
        height = screen((0, value))
        draw.line((west, endpoint), fill=PROJECTION, width=2)
        draw.line((height[0] - 7, height[1], height[0] + 7, height[1]), fill=GRID, width=2)
        dot(draw, height, 4, AXIS)

    draw.line(raster_points, fill=TEAL, width=6, joint="curve")

    # The tangent-intersection chain is the circumscribed polygon.
    tangent_points = [
        screen(tangent_intersection(left, right_point))
        for left, right_point in zip(circle_points, circle_points[1:])
    ]
    outer_chain = [raster_points[0], *tangent_points, raster_points[-1]]
    for left, right_point in zip(outer_chain, outer_chain[1:]):
        draw.line((left, right_point), fill=CORAL, width=4)

    # Points are drawn last so the rational samples remain unmistakable.
    for sample in raster_points:
        dot(draw, sample, 6, INK)
    dot(draw, origin, 6, INK)
    dot(draw, west, 6, INK)

    draw.text((west[0] - 10, west[1] + 39), "(-1, 0)", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((origin[0] + 1, origin[1] + 39), "0", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((top[0] - 25, top[1] - 8), "1", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((right[0] + 22, right[1] + 36), "P(0)", font=SMALL_FONT, fill=INK, anchor="mm")
    draw.text((top[0] + 48, top[1] - 20), "P(1)", font=SMALL_FONT, fill=INK, anchor="mm")

    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    stages = [1, 2, 4, 8]
    frames = [stage_frame(subdivisions) for subdivisions in stages]
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
