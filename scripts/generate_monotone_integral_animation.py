#!/usr/bin/env python3
"""Compatibility entry point for the TikZ animation renderer."""

from generate_tikz_animations import all_animations, render


if __name__ == "__main__":
    render(next(animation for animation in all_animations() if animation.name == "monotone-integral-stage"))
