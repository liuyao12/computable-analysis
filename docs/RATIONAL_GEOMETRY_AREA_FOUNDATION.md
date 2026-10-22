# Rational geometry, Pythagoras, and trigonometry by sector area

This is a small sufficient foundation proposal, with explicit proofs and a checked finite algebra model. “Minimal” here means that unnecessary existence and analytic axioms have been removed. Independence of every remaining axiom is not claimed. No completed real field, numerical distance formula, square-root existence, integral, derivative, or trigonometric addition formula is assumed.

## The obstruction that determines the scope

The rational plane contains the unit square and its diagonal. It cannot also satisfy the unrestricted axiom “copy any segment onto any ray.” Copying that diagonal onto the horizontal axis, after Pythagoras, would produce a rational $c$ with $c^2=2$. Thus even some ordinary segment-construction axioms are too strong; excluding circle intersections alone is insufficient.

Likewise, a right angle can be bisected as a pair of rational rays, but its diagonal ray contains no rational unit-circle point. Numerical sine and cosine cannot both be rational-valued functions of all rational angle coordinates. The rational geometry and the subsequent constructions of particular represented numbers must remain distinct.

This is consistent with the distinction between ordered fields, Pythagorean fields, and Euclidean fields in the foundations literature. Full straightedge-and-compass existence has stronger field requirements than our rational substrate. See [Beeson, Constructive Geometry and the Parallel Postulate](https://arxiv.org/abs/1407.4398) and [Baldwin, sections 4.2–4.4](https://homepages.math.uic.edu/~jbaldwin/pub/axconIfeb29.pdf). These references motivate the scope; the proposal below is our particular weaker rational system.

## A small geometric base

**G1. Ordered rational affine plane.** Points admit rational affine combinations. Choose an origin and two independent unit-frame vectors. Lines, betweenness, parallelism, rational subdivision, and intersections of supplied nonparallel lines are the ordinary rational affine constructions. A concrete model is $\mathbb Q^2$. This is incidence and order, without a metric.

**G2. A compatible quarter-turn.** Supply an additive, rational-linear map $J$ on displacements, with

$$
J^2v=-v.
$$

Choose the positive unit frame $(e,Je)$. Coordinates in this frame make $J(x,y)=(-y,x)$. A square erected on a displacement $v$ is the parallelogram with vertices

$$
0,\quad v,\quad v+Jv,\quad Jv.
$$

This is the explicit Euclidean geometric input: perpendicular directions and equal quarter-turned sides are encoded by the square construction. Affine incidence and area alone cannot distinguish a square from a sheared parallelogram. We are not deriving right angles from pure affine geometry, or pretending that an unspecified notion of “square” needs no axioms.

G2 requires no numerical angle, length, arbitrary rotation, or angle-bisection existence. It has the literal rational model above. The formulation is a convenient small algebraic presentation of the geometric structure, rather than a claim to have reconstructed all synthetic Euclidean geometry.

## Four polygon-area laws

For finite rational polygonal regions, use a rational-valued content $a(P)$. Regions may be represented by certified finite triangulations, with common edges treated as boundaries.

**P1. Unit normalization.** The square on $e$ has area $1$.

**P2. Finite dissection additivity and zero boundaries.** For a certified finite partition with disjoint interiors, the whole area is the sum of the piece areas. Segments and points have area zero. We use only rational vertices and rational cuts.

**P3. Nonnegativity.** Polygonal areas are nonnegative. Monotonicity follows when the rational polygonal difference is decomposed into pieces. Strict positivity for nondegenerate triangles follows from the area formula below, rather than being another axiom.

**P4. Translation invariance.** Translating a polygon by a rational displacement preserves area.

Quarter-turn, reflection, shear, similarity, and arbitrary available rational rigid-motion area laws can be derived after identifying polygon content. They need not all be independent area axioms.

Here is why these laws determine the familiar polygon areas. Tile the unit square into $N^2$ translated small squares. P1, P2 and P4 fix each small square's area as $1/N^2$. Tiling then determines every axis-aligned rational rectangle. For any fixed rational polygon, the small grid cells meeting its finitely many edges have total area tending to zero: each edge meets at most a computable linear number of cells as $N$ grows, while a cell has area $1/N^2$. P3 squeezes its content between the interior-cell and covering-cell sums. All comparisons and errors are rational. No unknown supremum is introduced.

Alternatively, finite rational dissections give the determinant formulas directly. The rational triangulation/shoelace computation supplies a model of P1–P4. In particular, the oriented parallelogram content is

$$
\omega((x,y),(z,w))=xw-yz,
$$

and a positively oriented triangle on displacements $u,v$ has area $\omega(u,v)/2$. Bilinearity and reversal of sign are derived area identities, not a distance formula. The general polygon-law-to-formula proof is given here mathematically; its complete polygon partition formalization remains to be added.

## Pythagoras before distance

Let $Q(v)$ denote the area of the square erected on $v$. Then

$$
Q(v)=\omega(v,Jv).
$$

For a right triangle with legs $v$ and $kJv$, the erected squares satisfy

$$
Q(v+kJv)=Q(v)+Q(kJv).
$$

To see the geometric dissection, place four congruent right triangles with rational axis legs $a,b$ inside the square of side $a+b$. Their remaining central square has successive side displacements $(b,a)$, $J(b,a)$, $- (b,a)$, and $-J(b,a)$. Additivity gives

$$
Q((b,a))=(a+b)^2-4\frac{ab}{2}=a^2+b^2.
$$

The placements use translations and quarter-turns, with no copying of a hypotenuse onto an axis. In a coordinate proof, bilinearity of $\omega$ and $J^2=-I$ give the same square-area identity. This is Pythagoras as an identity between areas, before numerical lengths are assigned.

Only now define the squared size of a displacement as its erected-square area. Its coordinate theorem is

$$
Q((x,y))=x^2+y^2.
$$

Thus the coordinate squared-distance formula is a proved consequence of square area. The diagonal of the unit square has square area $2$; a numerical length for it still requires constructing a positive represented value whose square is $2$.

In this area-based presentation, segment congruence can now mean equality of erected-square contents, and a rigid motion is an affine map preserving that content. This is an explicit foundational choice. A presentation with primitive segment congruence would need its own compatibility axioms and is not being silently assumed here.

For a rational linear map $M$, polygon area scales by $|\det M|$. The rational direct similarity $M=aI+bJ$ consequently satisfies

$$
Q(Mv)=(a^2+b^2)Q(v),\qquad
a(MP)=(a^2+b^2)a(P).
$$

When $a^2+b^2=1$, it is an available rational rigid motion. General nonzero similarities transport rational rays without requiring unit normalization. Ratios of sector area to the corresponding disk area are invariant under the same scaling. This supplies angle transport even when the required unit-radius rotation is absent over $\mathbb Q$.

There is a necessary radius-independence bridge here. A similarity with squared scale $\kappa$ sends the unit disk to $D_\kappa=\{v:Q(v)\leq\kappa\}$, rather than back to the unit disk. First prove area scaling under positive rational homotheties. For a fixed ray cone and any positive rational $R$, construct rational brackets $\ell^2\leq R\leq h^2$ with $h^2-\ell^2$ arbitrarily small. Inclusion puts the sector in $D_R$ between the corresponding rationally dilated unit sectors. If $B$ is the unit-sector area, both its proposed area and $RB$ are between $\ell^2B$ and $h^2B$. Since $0\leq B\leq4$, their difference is at most $4(h^2-\ell^2)$. This proves the exact radius law by rational squeezing, without assuming a number $\sqrt R$ or a rational normalization motion. The same argument applies to the disk. Thus normalized sector area is independent of radius, which is what makes similarity-based angle transport well-defined. This bridge is a mathematical derivation here, not one of the finite Lean results below.

A rational oriented geometric angle can therefore be presented as an ordered pair of rational rays, with congruence given by a translation and one rational direct similarity applied to both rays. This definition of congruence precedes numerical angle measure. Area covariance and radius independence then prove that congruent angles have equivalent normalized sector measures. A chosen counterclockwise sweep handles the orientation; coincident rays and additional whole turns require a separate zero/winding convention. The numerical specification below begins with one first-quadrant sweep.

## An area specification with no existence axiom

For a particular additional region $E$, ask whether a supplied valid represented value $A$ can serve as its area. The mathematical laws are:

- Agreement with rational polygon content wherever both are supplied.
- Order under justified inclusions.
- Finite additivity for supplied regions with justified boundary treatment and decomposition.

These are conditional laws. They do not assert that every region has an area, that every area is rational, or that every desired decomposition already has area witnesses. Rational motion invariance for the disk and sectors will follow from their polygon comparisons; it need not be assumed for all subsets.

For uniqueness at one particular region, construct rational polygons

$$
P_n\subseteq E\subseteq T_n,\qquad
a(T_n)-a(P_n)\longrightarrow0.
$$

Any supplied area obeying polygon agreement and order lies between the same rational numbers, so two such areas are equivalent. This proves uniqueness independently of constructing an area value. Polygon exhaustion is a sufficient proof method for these regions, not an additional definition or universal class of admissible regions.

## Circle and sector areas from rational polygons

Define the unit disk geometrically by erected-square size:

$$
D=\{v\in\mathbb Q^2:Q(v)\leq1\}.
$$

After Pythagoras this has the familiar coordinate inequality. A sector is the intersection with the appropriate oriented cone of rays. This is a predicate on rational points, even when the bounding ray has no rational unit-circle point.

There is a particularly simple rational chart for the first-quadrant boundary:

$$
p(u)=\left(\frac{1-u^2}{1+u^2},\frac{2u}{1+u^2}\right),
\qquad0\leq u\leq1.
$$

Rational algebra proves $Q(p(u))=1$. This chart is construction data; it is not the definition of sine or cosine. For $0\leq u\leq v\leq1$, let the inner wedge be the triangle on $0,p(u),p(v)$. The outer wedge is the quadrilateral formed using the intersection of the two supporting tangents. That intersection is the rational point

$$
t(u,v)=\left(\frac{1-uv}{1+uv},\frac{u+v}{1+uv}\right).
$$

Their areas are

$$
L(u,v)=\frac{(v-u)(1+uv)}{(1+u^2)(1+v^2)},\qquad
U(u,v)=\frac{v-u}{1+uv}.
$$

The support and containment statements use square-area positivity and rational half-plane inequalities. Their exact area difference is

$$
U(u,v)-L(u,v)
=\frac{(v-u)^3}{(1+uv)(1+u^2)(1+v^2)}
\leq(v-u)^3.
$$

Subdivide the parameter interval $[0,r]$ into $N$ equal pieces, for any rational $r\in[0,1]$. Add the inner and outer wedge areas. Their total difference is at most

$$
N(r/N)^3=\frac{r^3}{N^2}\leq\frac1{N^2}.
$$

With $N=2^n$, refining inserts chords and tangent constraints: the inner polygon grows, and the outer polygon shrinks. The area intervals are nested and their widths shrink to zero. They therefore construct a valid represented area $A(r)$ of the sector ending at $p(r)$. The same finite geometric comparisons establish its area role. Four copies construct the unit-disk area $\Pi$, with $\Pi\simeq4A(1)$ and width at most $4/N^2$. This is where particular represented area values are constructed; they were not assumed at the geometric layer.

For $N=2$ and $N=4$, the resulting whole-disk bounds are respectively $[14/5,10/3]$ and $[6486/2125,2209/693]$. These exactly match the first two existing `FiniteCircleAreaExample` certificates. This is a useful finite regression; it is not an all-stage comparison theorem or a substitute for the geometric area-role proof.

## The sector description of sine and cosine

Measure angles first by rational quarter-turn coordinates $t\in[0,1]$. The intended pair $(C(t),S(t))$ has nonnegative coordinates, satisfies the unit-circle equation, and bounds a sector with area

$$
\operatorname{Area}(\operatorname{Sector}((1,0),(C(t),S(t))))
\simeq tA(1)\simeq\frac{t\Pi}{4}.
$$

This specification uses area, quadrant, and normalization. No addition formula or differential equation is an axiom.

Existence requires a construction, because this point usually is not rational. The polygon bounds give a calculus-free quantitative route. For rational $0\leq u\leq v\leq1$,

$$
\frac{v-u}{4}\leq L(u,v)
\leq A(v)-A(u)\leq U(u,v)\leq v-u.
$$

The finite wedge inequalities are checked in the companion Lean file; the inequalities for actual sector areas follow after their geometric containment and area-role proofs. These estimates give strict order and an effective continuity bound. Invert $A$ at target $tA(1)$ using rational brackets and adequately precise area enclosures. Separated midpoint/target intervals select a half. Overlapping intervals permit a middle-half step because the lower increment bound turns area uncertainty into a controlled slope uncertainty. Equality never needs to be decided.

The brackets stay nested, halve in width, and retain the forward-target inequalities. Their endpoint images shrink together by the upper increment bound, proving the inverse's forward area law. Transport the brackets through $p$, with the sine endpoint order increasing and the cosine endpoint order reversed. This constructs the coordinate computations and identifies their sector area.

For uniqueness, the sector area is strictly increasing with the boundary direction. More quantitatively, every first-quadrant represented unit point has half-angle coordinate $u=S/(1+C)$; the positive denominator is bounded below by $1$. The circle equation recovers the chart coordinates. The lower increment bound forces any two such coordinates with the same sector area to agree. This argument needs the derived represented-coordinate and area-continuity bridges, not an assumption that the desired point was rational.

Ordinary radians then have $\theta\simeq2\operatorname{Area}(\operatorname{Sector})$. Hence the quarter-turn coordinate represents $\theta\simeq\Pi t/2$; the project's primary convention $\sin(\pi x)$ uses $t=2x$ in the first quadrant. Other quadrants, signs, and whole turns need the explicit geometric transformations and winding convention.

## Addition laws are consequences, with a genuine extension bridge

For an available rational unit-circle point, its rational rotation matrix preserves erected-square size, the disk, and polygon areas. The polygon bounds therefore prove sector-area invariance. Adjoining suitably oriented sectors adds their areas. Matrix multiplication supplies the sine/cosine coordinate addition formulas at these geometric points.

The constructed point at a rational quarter-turn coordinate generally has represented coordinates. Its rotation does not map $\mathbb Q^2$ into itself. To transfer the geometric argument to every such input, approximate its half-angle coordinate by rational brackets and prove the resulting image and sector-area errors shrink. This derived transport bridge is essential. Rational rigid motions alone do not already prove the full addition formulas. No completed plane or unrestricted rotation existence is needed if this approximation argument is carried out.

## What is checked now, and what remains

`ComputableAnalysis/RationalAreaFoundation.lean` imports only Lean's rational ordered-ring support. Its conditional `area_pythagoras_of_bilinear` derives Pythagoras for any supplied alternating bilinear parallelogram content, without assuming its coordinate formula. The file also checks the concrete quarter-turn and content identities, Pythagoras in square contents, the four-triangle area arithmetic, rational similarity laws, the rational circle chart, both wedge-area formulas, the tangent supporting-line equations, the unit-disk support inequality, the exact wedge gap and cubic bound, the summed $r^3/N^2$ bound, and the finite unit-chart increment bounds. These are conditional area-algebra and finite model theorems; they do not assume a numerical distance formula.

The general derivation from P1–P4 to polygon content, complete polygon containment/partition certificates, actual nested sector-area evaluator and its role theorem, radius-independence argument, and the new area-specification-to-trigonometry/represented-motion bridges are not formalized by those finite checks. The mathematical derivations above specify the route and quantitative obligations. Existing geometric arctangent and inverse-circle modules supply related constructions; a checked comparison at the geometric specification is required before treating them as this implementation. The new checked module is currently published in the companion proof bundle, rather than as an export of the main library root.

The next formalization milestone should therefore be the rational polygon dissection and sector-containment layer, followed by the explicit sector evaluator and its area-role theorem. Adding an abstract record whose fields assume the sector identification would not complete that work.
