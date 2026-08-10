# TikZ animation sources

Each GIF in the blueprint is assembled from the corresponding TikZ frame
sources in this directory. The source of truth for their rational meshes,
stages, and rendering pipeline is scripts/generate_tikz_animations.py.

Regenerate every animated and print fallback asset with:

    python3 scripts/generate_tikz_animations.py

To regenerate one animation while revising it:

    python3 scripts/generate_tikz_animations.py --only integration-by-parts-cell

The renderer invokes pdflatex and pdftoppm. It writes TeX-native labels and
formulas in every frame, then uses Pillow solely to assemble the rendered
pages into the checked-in GIF and PNG assets.
