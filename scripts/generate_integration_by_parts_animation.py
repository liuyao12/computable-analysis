#!/usr/bin/env python3
"""Render the continuous geometric picture for integration by parts.

The increasing rational parametrization ``U(t)=t, V(t)=t^2`` traces the
curve ``V=U^2`` from ``(0,0)`` to ``(1,1)``.  Within the product rectangle up
to the current parameter, the area below the curve is ``∫ V dU`` and the
area above it is ``∫ U dV``.  The two coloured regions therefore tile the
rectangle ``[0,U(t)] × [0,V(t)]``.  The GIF is intentionally continuous and
nearly wordless; the Lean theorem below it supplies the synchronized finite
rational partition calculation that certifies this picture.
"""

from __future__ import annotations

from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "integration-by-parts-cell.gif"
PNG_PATH = ASSET_DIR / "integration-by-parts-cell.png"

WIDTH, HEIGHT = 560, 480
LEFT, RIGHT = 92, 468
TOP, BASELINE = 38, 414
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
GRID = (203, 213, 225, 255)
TEAL_FILL = (176, 227, 219, 255)
TEAL_EDGE = (13, 148, 136, 255)
ORANGE_FILL = (254, 215, 170, 255)
ORANGE_EDGE = (234, 88, 12, 255)
CURVE = (51, 65, 85, 255)


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


SMALL = font(17)
LABEL = font(19)


def x_screen(value: float) -> float:
    return LEFT + value * (RIGHT - LEFT)


def y_screen(value: float) -> float:
    return BASELINE - value * (BASELINE - TOP)


def curve_points(stop: float, count: int = 160) -> list[tuple[float, float]]:
    return [(x_screen(stop * i / count), y_screen((stop * i / count) ** 2))
            for i in range(count + 1)]


def frame(stop: float) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)

    for quarter in range(1, 5):
        x = x_screen(quarter / 4)
        y = y_screen(quarter / 4)
        draw.line((x, TOP, x, BASELINE), fill=GRID, width=1)
        draw.line((LEFT, y, RIGHT, y), fill=GRID, width=1)

    draw.line((LEFT - 20, BASELINE, RIGHT + 25, BASELINE), fill=AXIS, width=3)
    draw.line((LEFT, BASELINE + 18, LEFT, TOP - 18), fill=AXIS, width=3)

    top = stop * stop
    # Below V=U²: ∫ V dU.  Above it in the current product rectangle:
    # ∫ U dV.  The polygons meet exactly along the parametrized curve.
    lower = [(x_screen(0), y_screen(0))] + curve_points(stop) + [
        (x_screen(stop), y_screen(0))]
    upper = [(x_screen(0), y_screen(top)), (x_screen(stop), y_screen(top))]
    upper += list(reversed(curve_points(stop)))
    draw.polygon(lower, fill=ORANGE_FILL)
    draw.polygon(upper, fill=TEAL_FILL)

    draw.line(curve_points(stop), fill=CURVE, width=3, joint="curve")
    draw.rectangle(
        (x_screen(0), y_screen(top), x_screen(stop), y_screen(0)),
        outline=CURVE,
        width=2,
    )

    x = x_screen(stop)
    y = y_screen(top)
    draw.ellipse((x - 5, y - 5, x + 5, y + 5), fill=CURVE)
    draw.text((RIGHT + 23, BASELINE + 4), "U", font=LABEL, fill=INK, anchor="lm")
    draw.text((LEFT - 4, TOP - 20), "V", font=LABEL, fill=INK, anchor="mm")
    draw.text((x, BASELINE + 30), "U(t)", font=SMALL, fill=INK, anchor="mm")
    draw.text((LEFT - 14, y), "V(t)", font=SMALL, fill=INK, anchor="rm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    states = [1 / 8, 2 / 8, 3 / 8, 4 / 8, 5 / 8, 6 / 8, 7 / 8, 1]
    frames = [frame(stop) for stop in states]
    frames[-1].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[500] * (len(frames) - 1) + [1800],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
