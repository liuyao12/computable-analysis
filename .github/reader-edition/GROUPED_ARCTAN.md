# Grouped arctangent flashcard

The final reader pass groups five former cards under **Arctangent**, headed
`pi = 4 arctan(1)`, just as the complex logarithm has one card with several
computations. The expanded group contains geometric area, rational-kernel
quadrature, Leibniz, Brouncker, and Machin. Machin remains in arctangent notation,
with no expanded series. All previous formula text is retained.

There are now seven top-level flashcards for the eleven previously listed
representations. Newton, logarithm and the other ungrouped cards are unchanged.
The final edition and placement metadata record this distinction. The earlier
`pi-patterns.json` remains the unchanged numerical record of its build stage;
`arctan-group.json` records the final arrangement and preservation checks.

Old fragments such as `#pi-machin` automatically open the group. The old
`#pi-arctan` fragment leads to its new common card; the kernel integral has
`#pi-arctan-integral`. The canonical location remains Chapter 1, Other examples,
after sqrt(2). Cosine quadrature is not added back to the gallery.

Run `group_arctan.py` and `test_arctan_group.py` after the existing reader and
pattern passes and tests. The new final pass changes only Chapter 1 HTML and
reader-arrangement metadata. Numerical algorithms and records, Lean sources,
proof graphs, comparisons, worked examples and animations are not changed.
No new formalization or equivalence proof is claimed.
