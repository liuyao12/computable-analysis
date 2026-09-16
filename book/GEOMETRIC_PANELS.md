# Geometric panels and independently evaluated numerical bounds

`illustrations.py` produces three reproducible GIFs and reduced-motion posters.
The arctan sector uses u=2/3. Every frame subdivides the vertical segment from
(0,0) to (0,u) into equal parts and draws every projection ray from (-1,0)
through a subdivision point to its rational circle point. The resulting arcs
are not equal-angle subdivisions. Inner chord and outer tangent polygons
give exact rational area bounds. Pi remains **4 A(1)**.

## Integration and differentiation are different constructions

Integration is introduced for increasing or decreasing functions. Endpoint
rectangles give lower and upper sums, with exact gap h |f(b)-f(a)|. No
concavity, derivative or Lipschitz bound is needed. Keep a fixed finite
schedule of retained meshes and increasingly precise sample evaluations.
The native library already has increasing and decreasing Darboux constructions;
the existing three cosine proofs and their general quadrature program remain
unchanged. The map retains all its original checked declarations and witnesses.

Convexity or concavity instead orders the secants used to construct a derivative.
For concave functions, right secants are lower and left secants upper. For
convex functions, reverse those roles. A shrinking-gap condition is necessary:
convexity alone allows corners. The separate secant animation uses the quadratic
f(x)=1-x²/2 at x=1/2, not a new sine definition.

## The cosine numerical driver

The main theorem and the monotone integral panel now show the decreasing C
on [0,1/3], using right lower and left upper rectangles. The second numerical
readout independently evaluates S(1/3)/pi; it does not define the first readout.
The chapter includes four rows through 512 cells. All displayed interval
endpoints round OUTWARDS, not to the nearest decimal.

`numerical_examples.py` uses exact rational chord/tangent bounds on an area-clock
grid and outward rounding to a 60-bit dyadic grid (to keep denominators small).
The target clock value is 2 x A(1). An ordered table first brackets the slope;
the geometric bounds

    (v-a)/(1+b²) <= A(v)-A(a) <= (v-a)/(1+a²),  a <= v <= b,

then tighten that bracket. These follow by bounding each chord/tangent increment
and refining. Cosine and sine are rational coordinates of the enclosed slope.
The integral routine consumes only cosine boxes; the endpoint routine consumes
only sine and pi boxes. They do not call each other. Ordinary floating-point
trigonometry occurs only in regression sanity checks, never in the driver.

These are independently computed illustrative rational enclosures, **not
executions of the literal Lean stage programs**, and their agreement is not a
replacement for the theorem. No new Lean theorem or equivalence of output
schedules is claimed. The inverse declarations remain folded into Sine and
cosine, with all exact declaration cards preserved.
