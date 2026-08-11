import ComputableAnalysis.Algebraic
import ComputableAnalysis.ComplexPathIntegral
import ComputableAnalysis.Pi

/-!
# ComputableAnalysis playground

This file is meant to be opened in VS Code and edited casually.  Put the
cursor on a `#eval!` command and the InfoView will show the result.  Try
changing the numeric stage arguments, or replace the rational inputs in the
examples below.

## Project scope

This project is not trying to become a floating-point library, or a general
library of numerical implementations for numbers and functions that existing
systems already handle well.  The computational layer is here because it gives
proofs something concrete to certify: rational enclosures, validity proofs,
equivalence bridges, and reusable certificates for later mathematics, science,
and engineering applications.  The algorithms should be transparent and good
enough to evaluate, but proof clarity and certifiability matter more than raw
speed.

## Background

The central object in this repository is not Lean/mathlib's classical
`Real`.  A raw computable real is an algorithm

```
Nat -> QInterval
```

where stage `n` returns a rational interval enclosing the number.  A proof of
validity, when we need one, says these intervals are ordered, nested, and
shrink to zero.  Complex numbers are treated similarly, except the output is a
rational rectangle in the complex plane.

This is intentionally close to what one would write in a programming language:
run the algorithm longer, get a sharper rational enclosure.  Equality is not
decimal equality; it is eventual overlap of certified interval algorithms.

## How this differs from mathlib

mathlib develops analysis over completed real and complex number types, with
topology, filters, measure theory, and a very large theorem library.  This
project is exploring a more concrete constructive layer.  We mostly compute
with `Nat`, `Rat`, rational intervals, and rational complex boxes, and we avoid
importing the usual mathlib real-analysis machinery.  The payoff is that many
definitions can be inspected by evaluation: the same object used in a theorem
can also print a rational enclosure.

The examples below are not proofs by themselves.  They are executable
sanity checks for the raw algorithms that theorems can later certify.
-/

namespace ComputableAnalysis
namespace Playground

/-!
## Square Root Of Two

The first thing to try is `sqrt 2`.  It is a `RealRaw`, so evaluation means
calling its `compute` field at a natural-number stage and displaying the
rational interval returned at that stage.

For intuition, `sqrt 2` is the positive root of `x^2 - 2`; the familiar
mental model is Newton's tangent method, or the tangent-secant method.
Here `sqrt 2` elaborates to the square-root raw algorithm defined in
`AlgebraicFunctions.lean`.  In this project the important extra step is
certification: the computation returns rational enclosures, not just a
floating-point approximation.
-/

#eval! ((sqrt 2).compute 5).display
#eval! ((sqrt 2).compute 20).display
#eval! ((sqrt 2).compute 100).display

/-!
## Raw arithmetic

Raw arithmetic builds new interval algorithms from old ones.  Complex numerals,
the constant `I`, division by a raw real denominator, and powers are ordinary
notation here, so the familiar unit complex number can be written directly.
-/

#eval! ((((1 + 1 * I) / sqrt 2) ^ 4).compute 2).display
#eval! ((((1 + 1 * I) / sqrt 2) ^ 4).compute 3).display

/-!
## Pi

The pi file contains several raw algorithms: the slow Leibniz series, the
faster Machin formula, and geometric interval constructions from the unit
circle.  Here we keep only a few live examples; see
`ComputableAnalysis/Pi.lean` for the definitions and more detailed examples.
-/

#eval! (piLeibniz.compute 10).display
#eval! (piMachin.compute 10).display
#eval! (piCircleArea.compute 10).display

/-!
## Comparing `sqrt 2 + sqrt 3` With Pi

The executable order test we have at this level is `RealRaw.compareAt`.
With one stage, `RealRaw.compareAt x y n` compares `x.compute n` and
`y.compute n`; with two stages, `RealRaw.compareAt x y nx ny` compares
`x.compute nx` and `y.compute ny`.  The result `.less` means the stage
certifies `x < y`, `.greater` means it certifies `y < x`, and `.overlap`
means the intervals still overlap.

The sum `sqrt 2 + sqrt 3` is numerically close to pi.  Machin's formula is
already sharp enough to separate them by stage `1`; only the deliberately
coarse stage `0` still overlaps.
-/

#eval! ((sqrt 2 + sqrt 3).compute 1).display
#eval! (piMachin.compute 1).display
#eval! (RealRaw.compareAt (sqrt 2 + sqrt 3) piMachin 0).display
#eval! (RealRaw.compareAt (sqrt 2 + sqrt 3) piMachin 1).display
#eval! (RealRaw.compareAt piMachin (sqrt 2 + sqrt 3) 1).display
#eval! (RealRaw.compareAt (sqrt 2 + sqrt 3) piMachin 1 10).display

end Playground
end ComputableAnalysis
