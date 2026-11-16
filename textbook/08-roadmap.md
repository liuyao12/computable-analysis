# Proposition ledger and contribution roadmap

## What the initial release establishes

The first boundary is an explicit, dependency-closed selection of source
modules. It is not a claim of complete coverage of analysis or a semantic
audit of every selected declaration. The named definitions and proposition
entry points below are checked by
`scripts/check_foundation_statements.lean`.

| ID | Mathematical contract | Existing source entry points | Status |
| --- | --- | --- | --- |
| N-01 | Ordered nested intervals with shrinking width represent a real value. | `RealCompute.Valid`, `RealCompute.ValidCompute` | Existing definitions |
| N-02 | Equality of values is an equivalence relation on valid representatives. | `RealCompute.Equiv`, `RealCompute.equiv_trans` | Existing theorem with validity hypotheses |
| N-03 | Complex coordinate projections preserve validity and equivalence. | `ComplexCompute.realPart_valid`, `ComplexCompute.realPart_equiv` | Existing theorems |
| N-Q | Real and complex values are quotients of valid names, with exact equality bridges and an injective real inclusion. | `ComputableAnalysis.Real`, `ComputableAnalysis.Complex`, `Real.ofRaw_eq_iff`, `Complex.ofRaw_eq_iff`, `Complex.ofReal_injective` | Checked quotient values and equality laws |
| F-D | A domain-dependent represented evaluator descends to a function on quotient complex values. | `DomainFunctions.Map`, `RiemannHilbert.DomainFunctions.Map.value_ofRaw` | Checked foundation interface; historical namespaces retained |
| F-E | Restrictions preserve validity, extensions compose, and overlap agreement generates a broader equivalence between presentations. | `FunctionRaw.extends_trans`, `FunctionRaw.sameFunction_trans`, `FunctionRaw.overlapEquivalent_minimal` | Checked raw laws; an analytic continuation class additionally requires admissible holomorphic charts |
| A-01 | Addition and subtraction preserve validity. | `RealCompute.add_valid`, `RealCompute.sub_valid` | Existing theorems |
| F-01 | Sampler agreement composes when the intermediate domain covers the comparison. | `PartialRealFunRaw.agreeOnOverlap_trans_of_cover` | Existing conditional law |
| C-01 | Function-specific covered bracket constructions yield a common extension value. | `BracketContinuity.exists_continuousAt_of_enclosures` | Existing conditional law |
| C-E | A monotone rational sampler is continuous when every valid input name eventually contained in its interval admits valid scheduled endpoint bounds; any two valid constructions agree. | `EndpointContinuity.ContinuousOn`, `bounds_equiv`, `bounds_value_eq`, `rational_agreement` | Definition, comparison laws, and strict polynomial/rational interval bridges checked; no interior-point condition or automatic turning-point selection |
| C-02 | A general represented real function preserves validity and value equivalence, and each output interval uses finite input information; these laws imply enclosure of compatible primary rational samples. | `FunctionContinuity.Continuous`, `Continuous.covers_rational` | Checked sufficient computational certificate and enclosure bridge; finite observation is not the primary endpoint definition |
| C-03 | Every real polynomial is continuous for arbitrary valid represented coefficients and inputs. | `FunctionContinuity.polynomial_continuous`, `polynomial_congr` | Checked under `FunctionContinuity.Continuous` and the endpoint criterion on supplied strict monotonicity intervals |
| C-04 | Every real rational expression is continuous on its full nonzero-denominator domain, with internally searched reciprocal separation. | `FunctionContinuity.rationalFunction_continuous`, `rationalFunction_domain`, `CertifiedReciprocal.mul_reciprocal` | Checked sufficient certificate, genuine non-pole domain, reciprocal identity, and strict interval endpoint bridges; complex counterpart remains open |
| F-I | Strict rational increase and a justified validity-preserving extension construct the unique preimage of every valid target in the endpoint range. | `StrictMonotoneInverse.inverse_target`, `inverse_unique`, `inverse_evalOn`, `inverse_congr`, `inverseValue` | Checked for the covered extension and directly for valid endpoint schedules through `EndpointInverse`; executable quotient inverse |
| D-01 | A bracket derivative is unique and invariant under equivalent input and function representations. | `BracketDerivative.unique`, `BracketDerivative.congr_point`, `BracketDerivative.congr_function` | Existing conditional laws |
| I-01 | The current rectangle relation has uniqueness and representation invariance. | `Integral.HasIntegral.unique`, `Integral.HasIntegral.congrFunction` | Existing conditional laws, rectangle scope |
| I-02 | An actual integral witness and local derivative-order evidence imply FTC. | `Integral.HasIntegral.ftc` | Existing conditional law |
| I-03 | A constant with arbitrary valid represented value has an integral on an ordered rational interval. | `Integral.constant_hasIntegral` | Existing construction theorem |
| D-02 | Valid shrinking convex/concave outer secants define a covered secant derivative at represented inputs, independently of valid schedules and input names. | `ConvexFTC.OuterSecants.hasDerivative`, `ConvexFTC.OuterSecants.equiv` | Checked construction and comparison laws |
| D-03 | Constructed convex/concave derivatives are nondecreasing/nonincreasing. | `ConvexFTC.derivative_monotone` | Checked conditional law |
| I-04 | Signed monotone represented samplers have arbitrarily tight rectangle bounds with internal width searches. | `ConvexFTC.boundsAtTolerance_gap`, `ConvexFTC.tight` | Checked finite construction |
| I-05 | Independent quadrature of a constructed convex/concave derivative is a certified integral and equals the endpoint difference. | `ConvexFTC.integral_hasIntegral`, `ConvexFTC.integral_ftc` | Checked construction and exact FTC; ordered rational endpoints |
| I-06 | Finitely many compatible convex/concave supporting-slope pieces yield a global certified integral and FTC, independently of the supplied decomposition. | `PiecewiseFTC.Pieces.hasIntegral`, `PiecewiseFTC.Pieces.ftc`, `PiecewiseFTC.Pieces.integral_equiv` | Checked construction and exact comparison; rational breakpoints |
| I-11 | An accumulated continuous monotone integral has the integrand extension as its covered derivative at every represented closed-domain point. | `MonotoneFTC.accumulated`, `curved`, `closed_hasDerivativeAt`, `exists_closed_derivative`, `closed_value_congr` | Checked independent quadrature, closed endpoint support, and name invariance; rational primary integral sampler |
| I-12 | Convex/concave relative closed derivatives imply supporting slopes and exact recovery by independent signed quadrature. | `ConvexFTC.closed_supports`, `closedIntegral_hasIntegral`, `closedIntegral_ftc`, `oriented_ftc`, `PiecewiseFTC.Pieces.ofClosed` | Checked on the actual closed curvature domain; no outside endpoint secants; proper bounds rational |
| I-13 | Actual compact FTC witnesses and endpoint-value convergence identify a supplied integral limit with the limiting endpoint difference. | `ConvexFTC.limit_hasIntegral`, `limit_ftc` | Checked conditional exhaustion law, with arbitrary represented limiting values |
| S-01 | Actual rational finite sums and shrinking certified tail errors define a valid represented series sum. | `ErrorSeries.Series.sum_valid`, `ErrorSeries.Series.hasSum` | Checked construction and summation role |
| S-02 | The summation claim has a unique value independently of a chosen error schedule. | `ErrorSeries.HasSum.unique` | Checked conditional law |
| P-01 | A factorial majorant gives a represented power-series sum and finite remainder bounds. | `ErrorPowerSeries.factorialSum_hasSum`, `ErrorPowerSeries.factorialSum_identify` | Checked construction and identification law |
| P-02 | Radian sine/cosine coefficient streams have valid sums with shrinking factorial remainders. | `ErrorPowerSeries.sine_hasSum`, `ErrorPowerSeries.cosine_hasSum`, `ErrorPowerSeries.sine_remainder`, `ErrorPowerSeries.cosine_remainder` | Checked independent series results; unused in the geometric FTC derivation |
| G-01 | Midpoint refinement gives an exact dyadic squared-mesh budget. | `ArctanGeometry.arctanIntegralRectangle_dyadicSquareMesh` | Existing finite identity |
| G-02 | The geometric sector normalization agrees with circle area. | `ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea` | Existing value comparison |
| G-03 | The dyadic rectangle value agrees with geometric arctangent. | `ArctanGeometry.arctanIntegralRectangleRaw_equiv_arctanGeom` | Existing raw comparison; use the separate validity hypotheses |
| G-04 | The odd Taylor series converges to geometric arctangent for every represented input in $[-1,1]$. | `ArctanTaylorFTC.hasIntegral`, `ArctanTaylorSeries.rational_geometric`, `remainder_bound`, `hasSum`, `series_valid`, `series_exact`, `series_congr` | Checked signed geometric extension, finite monomial FTC bound, both endpoints, exact equality and name invariance |
| T-01 | The arctangent inverse gives valid first-quadrant circle computations with a justified target. | `ArctanInverseCircle.sineQuarter_valid`, `ArctanInverseCircle.quarterSlope_target` | Existing branch-specific construction results |
| T-02 | The geometric rational samplers extend to every represented real, independently of its name, and have period two. | `GeometricTrig.sinAt_valid`, `sinAt_rational`, `sinAt_congr`, `sinAt_period` and cosine counterparts | Checked construction and exact comparison laws |
| T-03 | Both geometric normalized derivatives hold at every valid represented real, including quadrant joins. | `GeometricTrig.sin_derivative`, `cos_derivative`, `full_firstOrder_small` | Checked covered real derivative laws from geometric finite estimates |
| T-04 | The geometric derivative cycle iterates at arbitrary represented inputs, with geometric initial coefficients and uniform rational bounds. | `GeometricTrig.jet_derivative`, `jet_zero`, `jetAt_small`, `jetAt_congr` | Checked successive derivatives and quantitative Taylor input |
| T-05 | Repeated FTC on the actual geometric derivative family produces certified integral remainders and shrinking factorial bounds. | `GeometricTaylorFTC.integral_remainder`, `RepeatedFTC.remainder_bound`, `GeometricTaylorReal.remainder_bound` | Checked finite FTC derivation, including negative rational angles and arbitrary represented inputs |
| T-06 | The odd/even Taylor series converge exactly to geometric normalized sine/cosine on the full represented real domain. | `GeometricTaylorSeries.sin_taylor_converges`, `cos_taylor_converges`, `sin_taylor`, `cos_taylor`, `series_valid`, `sinTaylorAt_congr`, `cosTaylorAt_congr` | Checked convergence, valid sum computations, exact equality and name invariance |

| E-01 | Finite Euler growth bounds yield a valid positive function, initial value one, and its own derivative at every represented real. | `EulerReal.eval_valid`, `eval_congr`, `sample_zero`, `eval_positive`, `derivative`, `value` | Checked finite-algebra construction and full-domain derivative; no exponential series |
| E-02 | Imaginary-coefficient Euler steps yield a valid complex computation agreeing exactly with geometric normalized sine/cosine at every represented real. | `EulerImaginary.sample_valid`, `eval_valid`, `eval_congr`, `euler_identity`, `solves_rotation`, `value_agrees_circle` | Checked finite ODE error comparison and normalized component derivative laws; no power series |
| E-03 | A certified reciprocal of pi converts radian input to the normalized primary coordinate. | `EulerImaginary.radian_on_normalized`, `radian_euler_identity` | Checked all-real coordinate identities; radian derivative chain-rule bridge remains separate |

| E-04 | The full integer-step Euler powers converge to the ODE function at every valid represented real; each finite power preserves equivalent names. | `EulerPowerLimit.powers_tend_to`, `approximation_error`, `approximation_congr` | Checked full-domain convergence and quantitative comparison; no series premise |
| E-05 | The factorial exponential series converges exactly to the ODE Euler function at every valid represented real. | `EulerSeriesFinite.euler_factorial_error`, `EulerSeriesIdentity.exponential_hasSum`, `seriesAt_equiv_euler`, `seriesAt_congr` | Checked finite binomial comparison, represented series construction, equality and name invariance |
| E-06 | The existing adaptive rational factorial-series evaluator is valid and agrees with the Euler ODE computation and its represented-input series extension. | `EulerLegacySeries.adaptive_valid`, `adaptive_equiv_euler`, `seriesAt_rational` | Checked original program and exact comparison; the separate `expEuler` display candidate is invalid in general |
| E-07 | Full imaginary Euler powers, the normalized imaginary factorial series, and the geometric circle functions agree at every valid represented real input. | `EulerImaginaryPowerLimit.powers_tend_to_euler`, `approximation_congr`, `EulerImaginarySeries.seriesAt_equiv_euler`, `EulerExponentialAgreement.imaginary_three_way` | Checked coordinate convergence, exact complex agreement, and input-name invariance |
| E-08 | The real and imaginary power-series computations yield the same mathematical quotient functions as the Euler computations. | `EulerExponentialAgreement.real_values_three_way`, `powerLimitAt_equiv_series`, `imaginarySeriesValue_eq_eulerValue`, `adaptive_value_eq` | Checked equality of quotient values through ordinary executable definitions |

| E-09 | Negating an arbitrary represented input conjugates the imaginary Euler exponential. | `EulerRotationReflection.conjugation` | Checked finite Euler reflection and limit uniqueness; downstream negative-angle identities use this law and Euler's formula |
| E-10 | Repeated FTC on the actual Euler solution gives the factorial Taylor series at every valid represented real. | `EulerTaylorFTC.remainder_integral`, `EulerTaylorSeries.remainder_bound`, `hasSum`, `series_valid`, `series_exact`, `series_congr` | Checked derivative-family integral remainders, factorial decay, all-real transport and exact equality; independent of the earlier binomial convergence proof |
| I-07 | A supplied justified FTC step yields independent rectangle quadrature with its mathematical integral role and exact endpoint identity. | `FTCStepQuadrature.integral_valid`, `hasIntegral`, `integral_equiv_endpoint` | Checked conditional construction; the companion instantiates it for geometric trigonometric integrands |

| A-02 | Quotient real arithmetic satisfies the ring and order laws, with a reciprocal on the genuine nonzero domain. | `RealValueArithmetic.mul_add`, `le_total`, `mul_reciprocal`, `reciprocal_unique`, `divide_mul` | Checked laws and ordinary quotient definitions; complete complex-field/Archimedean API audit remains separate |
| C-05 | Strict rational order and finite sample tests construct nested endpoint schedules; finite-observation coverage proves validity. | `StrictEndpointContinuity.precision`, `EndpointContinuityBridge.evaluation_valid`, `EndpointContinuityDecreasing.decreasing_continuous` | Checked constructors and bridges; no automatic turning-point selection |
| D-04 | Addition, subtraction, products, and supplied reciprocals preserve full covered secant derivatives; polynomial differentiation holds at every valid represented input. | `RealSecantDerivative.HasDerivativeAt.add`, `HasDerivativeAt.mul`, `HasDerivativeAt.reciprocal`, `valueLimit_of_realizer`, `polynomial` | Checked with actual independent value/domain evidence and arbitrary represented coefficients |
| I-08 | Supplied actual integrals satisfy linearity, rational scaling, order, and adjacent-interval additivity. | `Integral.linear`, `compatibleWithScaleRat`, `orderPreserving`, `additiveOnAdjacentIntervals` | Checked at current rectangle-based sufficient scope, using independent partitions |
| I-09 | Shrinking actual rectangle bounds construct an integral without a pre-existing witness. | `BoundsQuadrature.valid`, `hasIntegral`, `MonotoneQuadrature.hasIntegral` | Checked existence construction, separately from uniqueness and conditional laws |
| I-10 | Piecewise supporting slopes for a product, and actual integrals of its two derivative terms, imply integration by parts. | `Integral.integrationByParts` | Checked conditional law with rational interval endpoints; no universal curvature constructor |
| L-01 | Fixed dyadic reciprocal quadrature defines a strictly increasing rational logarithm with integral increments. | `DyadicReciprocalIntegral.hasIntegral`, `MonotoneLogarithm.increment`, `strictly_increasing` | Checked independent construction; no pre-existing logarithm or exponential |
| L-02 | The logarithm extends to positive represented inputs, reflects order, has full real range, and admits a constructive inverse. | `MonotoneLogarithm.eval_valid`, `eval_congr`, `eval_reflects_order`, `inverseLog_target`, `inverseLog_eval`, `value_inverseValue`, `inverseValue_value` | Checked full-domain raw and quotient inverse laws |
| L-03 | The quadrature logarithm has full covered secant derivative \(1/x\) at every valid positive represented input. | `MonotoneLogarithm.secant_bounds`, `derivative` | Checked from integral increments and shrinking reciprocal endpoint computations |
| L-04 | The Taylor series for $\log(1+x)$ converges to the quadrature logarithm for $-1<x\le1$, with represented inputs and a certified denominator budget. | `LogTaylorFTC.hasIntegral`, `LogTaylorSeries.remainder_bound`, `hasSum`, `series_valid`, `series_exact`, `series_congr` | Checked finite reciprocal division integrated by monomial FTC; positive endpoint included, pole excluded |
| L-05 | Ordinary dyadic quadrature of the reciprocal between positive represented endpoints gives the difference of logarithms constructed by inverting Euler's exponential. | `DyadicGridIntegral.representedReciprocalIntegral_eq_inverseEulerLog`, `inverseEulerLog_agrees` | Checked via the nonuniform exponential grid and comparison of integral enclosures |
| F-01 | The dyadic Gaussian improper integral equals \(\sqrt{\pi}\). The normalized cosine transform leaves inversion factor \(1\). | `FourierQuadrature.gaussianDyadic_equiv_sqrt_pi`, `gaussianUnit_cosine_transform_exact`, `melroseGaussianFactor_eq_one` | Checked one-dimensional Gaussian normalization |
| F-02 | Fourier inversion reconstructs a real-valued sampler at every valid represented point. | `FourierQuadrature.inverseLineAt_eq`, `inverseLineAt_congr` | Checked with the stated derivative, moment, and decay certificates |
| C-01 | Holomorphic functions agreeing locally agree throughout their shared connected domain. | `FunctionTheory.Holomorphic.identityOnConnected` | Checked with local Taylor evidence constructed through rectangular Cauchy integrals |

Every declaration is in the `ComputableAnalysis` namespace; the table omits
that prefix for readability. A declaration check establishes availability
and type checking. It does not certify this inventory as an independent
mathematical audit.

## Open work, in dependency order

The opening chapter targets are: complete the public ordered-field contract
on represented values; expose circle area/circumference comparisons without
specialized imports; construct and identify the actual three-dimensional
sphere bounds; and certify the geometric arctangent quadrature in the intended integral
relation. Raw comparison, semantic integral identification, and a full-domain
derivative theorem are separate obligations. Higher dimensions belong to later propositions. The later Euler ODE
construction and geometric rotation comparison are now checked as E-01–E-03.

The intended integral contract now explicitly includes constant/simple-function
values, adjacent-interval addition, and comparison with simple lower and upper
bounds. Audit and prove the bridges from the present rectangle route. The
course's calculus constructions remain function-specific: use proved
monotonicity and curvature pieces, together with explicit bounds on any
remaining pieces. Comparing the punctured-quotient and admissible-secant
derivative interfaces is useful support work, but it is not a prerequisite for
constructing the derivatives and integrals of particular course functions.

The first constructed convex/concave recovery theorem is now checked in
`ConvexFTC`: it derives monotonicity from actual valid outer secants and
identifies independently evaluated signed quadrature with the endpoint
difference. The companion `ConvexFTCExamples` supplies square, negative square,
and represented-coefficient affine regressions. Convexity alone does not
provide a shrinking derivative at corners. The quotient-extension comparison,
pointwise quotient-extension bridge and function-specific represented-endpoint
constructions remain separate work. The relative one-sided endpoint bridge,
differentiation of accumulated continuous monotone integrals, and supplied-
exhaustion recovery laws are now checked as I-11–I-13.

`PiecewiseFTC` now joins compatible supplied pieces and certifies their global
integral, with a cubic regression that changes curvature at zero. `ErrorSeries`
and `ErrorPowerSeries` provide sums whose definitions include proved error
bounds. Chapters 4 and 5 cover those constructions before Chapter 6's Taylor
theorem. The geometric derivative cycle and period-two real extension are now
proved, including all quadrant joins. Repeated FTC applied to those actual
geometric functions now produces the finite factorial remainder, and its
vanishing proves the normalized Taylor expansions at arbitrary represented
inputs. The proof does not use the older independent radian series candidates. The
Euler exponential now has an additional repeated-FTC Taylor derivation on all
represented reals. Integrating finite reciprocal-kernel identities also gives
the quadrature logarithm series on $-1<x\le1$ and geometric arctangent series
on $[-1,1]$, including their convergent endpoints. All three have certified
error-padded sums, exact identities, and representation invariance.
Separate geometric curvature certificates, expansion centers beyond zero, and
faster proved-equivalent evaluators remain useful contribution areas.

1. **Review the public number and arithmetic contracts.** Split oversized
   modules when useful; retain exact laws and executable algorithms. Check
   the scope and representation invariance of each exported operation.
2. **Promote general support.** The manifest explicitly distinguishes
   specialized topics, examples, legacy models, and support awaiting
   decoupling or a source audit. Promote the general pieces with closed
   imports and checked statements, rather than importing a topic catalogue.
3. **Complete function-specific extension and identity bridges.** Start from
   rational-input functions; construct the needed represented-input
   extensions and prove agreement, including coordinate and domain changes.
4. **Separate general integration laws from the rectangle route.** Preserve
   the existing route and its theorems. Justify the new bridges and any wider
   uniqueness claim without assuming the conclusion.
5. **Finish function-specific calculus constructions and elementary
   functions.** Prove the evaluation, normalization, global-domain, and
   comparison bridges needed for exact represented-input identities when an
   application needs them. General derivative algebra and universal
   continuity/derivative theories are supporting work, not course
   prerequisites. Both convex/concave
   FTC directions are now checked at their stated scope, including relative
   closed endpoints, without requiring a universal derivative constructor.
   The rational logarithm from fixed dyadic reciprocal quadrature, its positive
   represented extension, full real range, constructive inverse, both inverse
   laws, and derivative are now checked as L-01–L-03. Identify its inverse with
   the existing Euler exponential; the checked Euler/series comparison will
   then identify the factorial-series computation as well. The companion's
   other reciprocal-integral inverse laws do not replace this obligation.
6. **Promote general complex and ODE APIs.** Keep actual analytic equation,
   domain, and initial-value evidence; separate finite algebra from analytic
   existence. The ODE capstone is a local Lipschitz existence-and-uniqueness
   theorem for an effectively evaluated rational vector field on a bounded
   rational box, with a pointwise rational solution computation and explicit
   error bounds. State the differential equation through its derivative or
   equivalent integral identity, prove uniqueness for actual solutions with
   matching data, and require the local step-size conditions that keep the
   solution in the box. Do not assume global existence; continuation requires
   fresh bounds, and polynomial vector fields are a key instantiation. Keep
   the proof computable and pointwise, without abstract function-space
   completeness. `ScalarODEUniqueness` and `PeanoBaker` are supporting results,
   not this existence theorem. Specialized applications stay downstream.
7. **Publish stable Prove2Me units.** Export reviewed definitions and
   meaningful theorem targets in manageable groups with a pinned source
   revision. Existing checked results are dependencies, not falsely open
   problems. The living source remains editable.

Continued fractions are a further open chapter target. CF-01 in Chapter 8
asks for rational convergent recurrences with explicit error schedules for
Brouncker's and Euler's pi fractions, then exact identification of Brouncker's
value with $4/\pi_{\rm circle}$ and Euler's with $\pi_{\rm circle}$. The
reciprocal of Brouncker's value and Euler's value then give two computations
of the same pi. The generic rational recurrence, adjacent-convergent
determinant identity, and certificate-to-`RealCompute` interface are checked in
`ContinuedFraction.lean`. The finite Brouncker convergent has also been
proved to be the reciprocal of its corresponding Leibniz partial sum. The
remaining work is to certify the reciprocal limit and to prove the separate
finite transformation and tail estimate for Euler's fraction, then connect
both limits to `piCircleArea`. The textbook presents those infinite
identities as open targets, not as existing Lean theorems.

These are contribution areas, not completed Lean propositions with invented
placeholder proofs. Before a target becomes a platform theorem, write its
precise domain, hypotheses, and conclusion here, compile its formal
statement locally, and independently review its faithfulness.

## Far-out lighthouse: distributions and PDE fundamental solutions

The long-range goal is a computable distribution calculus for physics and
engineering, developed without Lebesgue integration or abstract functional
analysis. A distribution begins as a sequence of ordinary computable
functions with certified Riemann pairings against smooth compactly supported
tests and an effective convergence schedule. Two sequences represent the
same distribution when their actions agree on every test function. Different
sequences, including suitable holomorphic boundary-value sequences, remain
available as computations of the same mathematical object.

The first substantial application is to define the Dirac distribution and
prove explicit fundamental-solution identities for the Laplace, heat and
wave equations on $\mathbb R^n$ for every positive dimension $n$. The public
identity is stated by action on arbitrary valid represented test functions;
the source normalization at the singularity is proved with explicit
small-region or initial-trace estimates. The heat and wave solutions carry
the retarded support condition. Exact kernel formulas, the wave dimension
recurrence, multivariable calculus prerequisites, and contributor milestones
are laid out in `docs/COMPUTABLE_DISTRIBUTIONS_ROADMAP.md`.

The first Prove2Me contribution should be a `Textbook` mission for the
sequence-based distribution quotient and Dirac identity. Laplace, heat and
wave results then become later missions in the same series, building to the
all-dimensions target. The repository roadmap and textbook remain editable;
only declarations exported to Prove2Me become immutable after proposal
submission. This programme is independent of the first single-variable
foundation mission. The initial action-level Lean statements now live in the
separate `subprojects/computable-distributions` package; their missing
concrete Riemann-pairing bridge is recorded there.

Existing heat-kernel and holomorphic-boundary work supplies candidate
computations and partial estimates, not this sequence-based definition or
the requested general fundamental-solution theorems. Those connections must
be proved before any existing result is counted as a milestone completion.

## Choosing a first contribution

Prefer a missing bridge needed by a real downstream construction. An issue
should state the mathematical result, the current evidence, the missing
step, and an appropriate verification command. A complete conditional law
counts as complete at its stated scope. A concrete requested construction
still requires its actual evidence.
