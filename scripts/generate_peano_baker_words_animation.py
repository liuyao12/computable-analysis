#!/usr/bin/env python3
"""Render finite chronological-word states for Peano--Baker expansion.

`ordered_words(n)` is exactly the recursion in `LinearODE.orderedIndexWords`:
retain every old word, then prepend the newest index to every old word.  A
coloured tile denotes one rational-matrix factor `B_i`; tiles run newest to
oldest from left to right.  Thus the final frame visibly includes `B_2 B_1
B_0`, never the reversed product.
"""

from __future__ import annotations

from pathlib import Path

from PIL import Image, ImageDraw, ImageFont


ROOT = Path(__file__).resolve().parents[1]
ASSET_DIR = ROOT / "blueprint" / "src" / "assets"
GIF_PATH = ASSET_DIR / "peano-baker-words.gif"
PNG_PATH = ASSET_DIR / "peano-baker-words.png"

WIDTH, HEIGHT = 640, 470
WHITE = (255, 255, 255, 255)
INK = (28, 41, 56, 255)
AXIS = (100, 116, 139, 255)
EMPTY = (226, 232, 240, 255)
COLORS = (
    (13, 148, 136, 255),
    (234, 88, 12, 255),
    (126, 34, 206, 255),
)
TILE = 56
LEFT, TOP = 192, 36
ROW = 48


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
LABEL = font(20)


def ordered_words(steps: int) -> list[list[int]]:
    if steps == 0:
        return [[]]
    old = ordered_words(steps - 1)
    return old + [[steps - 1, *word] for word in old]


def frame(steps: int) -> Image.Image:
    image = Image.new("RGBA", (WIDTH, HEIGHT), WHITE)
    draw = ImageDraw.Draw(image)
    words = ordered_words(steps)

    for row, word in enumerate(words):
        y = TOP + row * ROW
        if not word:
            draw.rectangle((LEFT, y, LEFT + TILE, y + TILE - 8), fill=EMPTY, outline=AXIS, width=2)
            draw.text((LEFT + TILE / 2, y + (TILE - 8) / 2), "I", font=SMALL, fill=INK, anchor="mm")
            continue
        for col, index in enumerate(word):
            x = LEFT + col * (TILE + 8)
            draw.rectangle((x, y, x + TILE, y + TILE - 8), fill=COLORS[index], outline=WHITE, width=2)
            draw.text((x + TILE / 2, y + (TILE - 8) / 2), f"B{index}", font=SMALL, fill=WHITE, anchor="mm")

    timeline_y = 430
    draw.line((LEFT - 80, timeline_y, LEFT + 3 * (TILE + 8) + 24, timeline_y), fill=AXIS, width=2)
    for index in range(3):
        x = LEFT + index * (TILE + 8) + TILE / 2
        draw.line((x, timeline_y - 7, x, timeline_y + 7), fill=AXIS, width=2)
        draw.text((x, timeline_y + 24), str(index), font=SMALL, fill=INK, anchor="mm")
    draw.text((LEFT - 98, timeline_y), "t", font=LABEL, fill=INK, anchor="mm")
    return image


def main() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    frames = [frame(steps) for steps in range(4)]
    # Three samples show all eight chronological terms without becoming dense.
    frames[3].save(PNG_PATH, format="PNG", optimize=True)
    frames[0].save(
        GIF_PATH,
        format="GIF",
        save_all=True,
        append_images=frames[1:],
        duration=[1050, 1050, 1250, 1900],
        loop=0,
        disposal=2,
        optimize=True,
    )
    print(f"wrote {GIF_PATH.relative_to(ROOT)}")
    print(f"wrote {PNG_PATH.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
