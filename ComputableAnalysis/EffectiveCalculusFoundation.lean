import ComputableAnalysis.IntegralFoundation
import ComputableAnalysis.FiniteTaylorFTCInterface
import ComputableAnalysis.FiniteMonotoneSequenceInterface
import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.PolynomialMeanValue
import ComputableAnalysis.FiniteQuadratureMeanValue
import ComputableAnalysis.FiniteLHopitalCertificate
import ComputableAnalysis.FiniteGapAwareInverseSearch
import ComputableAnalysis.EffectiveFTCPortfolio
import ComputableAnalysis.FinitePiecewiseAbsoluteValue

/-!
# Effective calculus foundation

This scoped entry point collects the finite secant, derivative-bound,
curvature, stabilization, inverse-search, and L'Hôpital contracts that turn
an explicit interval evaluator into an effective FTC certificate.

It is a proof interface, not a general completeness theorem: each special
function supplies its own domain, schedule, and finite overlap data.  Routine
scalar, signed, and piecewise variants are transported or assembled from the
representative certificates.
-/

namespace ComputableAnalysis.Integral

/-! Curvature is the intended provider-facing route to the effective FTC:
convex and concave functions supply monotone derivative bounds, while this
wrapper closes the same finite endpoint certificate. -/
theorem effectiveCurvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact curvatureFTC h

/-- Convex providers can close the effective FTC directly. -/
theorem effectiveConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact convexFTC h

/-- Concave providers can close the effective FTC directly. -/
theorem effectiveConcaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw := by
  exact concaveFTC h

/-- The square function is the first complete concrete curvature client: its
finite convexity bounds feed the effective FTC and close at the endpoint
difference. -/
theorem effectiveSquareCurvatureFTC :
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      squareCurvatureFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact squareCurvatureFTC_equiv_endpoint

/-- The curvature certificate's bounded integral is the normalized square
integral, whose finite endpoint value is one. -/
theorem effectiveSquareCurvatureFTC_value_one :
    squareCurvatureFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat 1) := by
  exact effectiveFTCPortfolio.square_effective_value

/-! The polynomial regression ladder is part of the public FTC interface too.
    These aliases keep the finite budgets and endpoint computations in their
    detailed module while giving downstream proof authors one stable place to
    discover the nonlinear examples. -/
theorem effectiveCubeFTC_equiv_endpoint :
    cubeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      cubeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact cubeEffectiveFTC_equiv_endpoint

theorem effectiveQuarticFTC_equiv_endpoint :
    quarticEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      quarticEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact quarticEffectiveFTC_equiv_endpoint

theorem effectiveQuarticIntegralFTC_equiv_one_fifth :
    quarticIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 5)) := by
  exact quarticIntegralEffectiveFTC_equiv_one_fifth

theorem effectiveFifthIntegralFTC_equiv_one_sixth :
    fifthIntegralEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (1 / 6)) := by
  exact fifthIntegralEffectiveFTC_equiv_one_sixth

/-! The scoped entry point gives the finite-piece FTC its project-facing name.
The partition, cell endpoint certificates, and endpoint transport remain
explicit inputs; this wrapper adds no completeness or general continuity
assumption. -/
theorem effectiveGeneralIntegralFor_equiv_totalEndpointDifference_of_telescope
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F)
    (h : PiecewiseMonotoneEndpointFTCFor F c)
    {first : RealRaw} {rest : List RealRaw}
    (hvalues : forall x, x ∈ first :: rest -> x.Valid)
    (htransport :
      FiniteRawListEquiv
        (piecewiseMonotoneEndpointDifferenceList F c)
        (rawAdjacentDifferenceList (first :: rest)))
    (htotal : (rawLast first rest - first).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c)) :
    (generalIntegralFor F c).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c) := by
  exact generalIntegralFor_equiv_totalEndpointDifference_of_telescope
    F c h hvalues htransport htotal

/-! The canonical finite-piece endpoint theorem is the common multi-turn
closure.  When each certified cell already uses the adjacent endpoint
representative, the finite telescope is discharged internally; only the
piecewise endpoint-FTC certificates remain as inputs. -/
theorem effectiveGeneralIntegralFor_equiv_totalEndpointDifference_of_canonical_values
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F)
    (h : PiecewiseMonotoneEndpointFTCFor F c) :
    (generalIntegralFor F c).Equiv
      (piecewiseMonotoneTotalEndpointDifference F c) := by
  exact generalIntegralFor_equiv_totalEndpointDifference_of_canonical_values
    F c h

/-! The focused entry point also exposes the nonuniform finite-piece error
budget.  This is the preferred interface for clients whose cells have
different evaluator costs: only the finite sum of their rational budgets is
charged against the requested tolerance. -/
theorem effectiveGeneralIntegralFor_precision_witness_of_cell_budgets
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) (eps : QPos)
    (bound : Nat -> Rat)
    (hcell : ∃ N : Nat, ∀ n, N <= n ->
      ∀ k (hk : k < c.pieces),
        ((piecewiseMonotoneCellIntegral F c k hk).compute n).width <=
          bound k)
    (hsum : (List.range c.pieces).foldl
      (fun total k => total + bound k) 0 <= eps.val) :
    ∃ N : Nat, ∀ n, N <= n ->
      ((generalIntegralFor F c).compute n).width <= eps.val := by
  exact piecewiseMonotoneIntegralFor_precision_witness_of_cell_budgets
    F c eps bound hcell hsum

/-! Uniform allocation is the convenient entry point when all cells use the
same evaluator schedule. -/
theorem effectiveGeneralIntegralFor_precision_witness_of_common_cell_budget
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) (eps : QPos)
    (hcell : ∃ N : Nat, ∀ n, N <= n ->
      ∀ k (hk : k < c.pieces),
        ((piecewiseMonotoneCellIntegral F c k hk).compute n).width <=
          eps.val / (c.pieces : Rat)) :
    ∃ N : Nat, ∀ n, N <= n ->
      ((generalIntegralFor F c).compute n).width <= eps.val := by
  exact piecewiseMonotoneIntegralFor_precision_witness_of_common_cell_budget
    F c eps hcell

/-! Representation changes are explicit: an alternative finite list of cell
evaluators can be used once its entries are proved equivalent to the
canonical list. -/
theorem effectiveGeneralIntegralFor_equiv_of_finiteRawListEquiv
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F)
    (xs : List RealRaw)
    (hxs : ∀ x, x ∈ xs -> x.Valid)
    (hlist : FiniteRawListEquiv
      (piecewiseMonotoneCellList F c) xs) :
    (generalIntegralFor F c).Equiv (finiteRawSum xs) := by
  exact piecewiseMonotoneIntegralFor_equiv_of_finiteRawListEquiv
    F c xs hxs hlist

/-! The canonical representation is available without unfolding the general
integral alias: it is the finite sum of the certified cell raws. -/
theorem effectiveGeneralIntegralFor_equiv_finiteRawSum
    (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) :
    (generalIntegralFor F c).Equiv
      (finiteRawSum (piecewiseMonotoneCellList F c)) := by
  exact piecewiseMonotoneIntegralFor_equiv_finiteRawSum F c

/-! Publicly expose the finite mean-value conclusion through the effective
calculus entry point.  The conclusion is an overlap of rational boxes, so it
does not select an attained intermediate real number. -/
theorem effectiveMeanValueBracket
    {F dF : RealFunRaw} {a b : Rat}
    {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C)
    (hF : F.Valid) (hwidth : 0 < C.width) (n : Nat) :
    QInterval.Overlaps
      (H.bound n)
      (QInterval.divByRat
        (endpointDifferenceInterval F C.lower C.upper
          (H.endpointPrecision n))
        C.width) := by
  exact CandidateDerivativeCellControl.endpoint_average_overlaps_bound
    H hF hwidth n

/-! Affine cells provide the first completely closed adjacent-interval
    additivity instances.  The endpoint formula is rational, so these are
    finite raw-overlap proofs in either orientation. -/
theorem effectiveAffineMonotoneIntegralFor_adjacent_additive
    {r c a b d : Rat} (hr : 0 <= r) :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneConstructionFor (r := r) (c := c) (a := a) (b := d) hr)).Equiv
      { compute := RealRaw.addCompute
          (monotoneIntegralFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
            (affineMonotoneConstructionFor (r := r) (c := c) (a := a) (b := b) hr))
          (monotoneIntegralFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
            (affineMonotoneConstructionFor (r := r) (c := c) (a := b) (b := d) hr)) } := by
  exact affineMonotoneIntegralFor_adjacent_additive hr

theorem effectiveAffineMonotoneIntegralFor_of_nonpos_adjacent_additive
    {r c a b d : Rat} (hr : r <= 0) :
    (monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a d)
      (affineMonotoneConstructionFor_of_nonpos
        (r := r) (c := c) (a := a) (b := d) hr)).Equiv
      { compute := RealRaw.addCompute
          (monotoneIntegralFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
            (affineMonotoneConstructionFor_of_nonpos
              (r := r) (c := c) (a := a) (b := b) hr))
          (monotoneIntegralFor
            (FunctionOnInterval.exactRat (fun x => r * x + c) b d)
            (affineMonotoneConstructionFor_of_nonpos
              (r := r) (c := c) (a := b) (b := d) hr)) } := by
  exact affineMonotoneIntegralFor_of_nonpos_adjacent_additive hr

theorem effectiveAffineMonotoneIntegralFor_eq_ofRat
    {r c a b : Rat} (hr : 0 <= r) :
    monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (affineMonotoneConstructionFor hr) =
      RealRaw.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  exact affineMonotoneIntegralFor_eq_ofRat hr

theorem effectiveAffineMonotoneIntegralFor_of_nonpos_eq_ofRat
    {r c a b : Rat} (hr : r <= 0) :
    monotoneIntegralFor
      (FunctionOnInterval.exactRat (fun x => r * x + c) a b)
      (affineMonotoneConstructionFor_of_nonpos hr) =
      RealRaw.ofRat ((b - a) * (r * (a + b) / 2 + c)) := by
  exact affineMonotoneIntegralFor_of_nonpos_eq_ofRat hr

end ComputableAnalysis.Integral

namespace ComputableAnalysis.FinitePolynomial

/-! Public focused-entry-point name for the parametric finite power rule. -/
def effectiveMonomialPowerRule
    (a b C : Rat) (n : Nat)
    (hleft : -C <= a) (hright : b <= C) (hC1 : 1 <= C) :
    HasDerivativeOnInterval
      (normalizedMonomialOnInterval a b n)
      (monomialOnInterval a b n) :=
  normalizedMonomial_hasDerivativeOnInterval a b C n hleft hright hC1

end ComputableAnalysis.FinitePolynomial

namespace ComputableAnalysis

/-! Public nonlinear seed cases.  These concrete rational finite-difference
    certificates are the first clients of the general product/FTC interfaces. -/
theorem effectiveSquareDerivative_nonempty :
    Nonempty (EffectiveDerivativeExact
      ExactFunction.square ExactFunction.doubleId) :=
  ExactFunction.square_derivative_effective

theorem effectiveSquareFTCExactUnit_nonempty :
    Nonempty (EffectiveFTCExact
      ExactFunction.square ExactFunction.doubleId 0 1) :=
  ⟨ExactFunction.squareFTCExactUnit⟩

/-! Composition closure for effective derivatives.  The caller supplies the
inner positivity, radius transports, and weighted error budget; all remaining
work is finite rational error arithmetic. -/
def effectiveDerivativeCompositionOfBudget
    {f df g dg : Rat -> Rat}
    (outer : EffectiveDerivativeExact f df)
    (inner : EffectiveDerivativeExact g dg)
    (outerTol innerTol : QPos -> QPos)
    (stepRadius : QPos -> QPos)
    (hinner_pos : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        0 < g (x + h) - g x)
    (hinner_radius : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        h <= (inner.stepRadius (innerTol eps)).val)
    (houter_radius : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
        g (x + h) - g x <=
          (outer.stepRadius (outerTol eps)).val)
    (hbudget : forall (eps : QPos) (x h : Rat),
      0 < h -> h <= (stepRadius eps).val ->
      qabs (ExactFunction.differenceQuotient f (g x)
        (g (x + h) - g x)) *
          (innerTol eps).val +
        qabs (dg x) * (outerTol eps).val <= eps.val) :
    EffectiveDerivativeExact (fun x => f (g x))
      (fun x => df (g x) * dg x) :=
  ExactFunction.EffectiveDerivativeExact.compOfBudget
    outer inner outerTol innerTol stepRadius hinner_pos hinner_radius
    houter_radius hbudget

/-! Product closure has the same provider-facing shape.  The finite budget
    explicitly accounts for both factor secant errors and the quadratic corner
    term; no general product theorem over a completed real space is assumed. -/
def effectiveDerivativeProductOfBudget
    {u du v dv : Rat -> Rat}
    (stepRadius : QPos -> QPos)
    (hbudget : forall eps x h,
      0 < h -> h <= (stepRadius eps).val ->
      qabs (u x) * qabs (ExactFunction.differenceQuotient v x h - dv x) +
        qabs (v x) * qabs (ExactFunction.differenceQuotient u x h - du x) +
          qabs h * qabs (ExactFunction.differenceQuotient u x h) *
            qabs (ExactFunction.differenceQuotient v x h) <= eps.val) :
    EffectiveDerivativeExact (fun x => u x * v x)
      (fun x => u x * dv x + v x * du x) :=
  ExactFunction.EffectiveDerivativeExact.mulOfBudget
    u du v dv stepRadius hbudget

/-! The square specialization is the common nonlinear observable in the
    calculus examples.  It keeps the product-rule corner term explicit while
    presenting the familiar derivative `2*u*du` to downstream certificates. -/
def effectiveDerivativeSquareOfBudget
    {u du : Rat -> Rat}
    (stepRadius : QPos -> QPos)
    (hbudget : forall eps x h,
      0 < h -> h <= (stepRadius eps).val ->
      qabs (u x) * qabs (ExactFunction.differenceQuotient u x h - du x) +
        qabs (u x) * qabs (ExactFunction.differenceQuotient u x h - du x) +
          qabs h * qabs (ExactFunction.differenceQuotient u x h) *
            qabs (ExactFunction.differenceQuotient u x h) <= eps.val) :
    EffectiveDerivativeExact (fun x => u x * u x)
      (fun x => 2 * u x * du x) := by
  have hproduct := effectiveDerivativeProductOfBudget
    (u := u) (du := du) (v := u) (dv := du) stepRadius hbudget
  have hderiv : (fun x => u x * du x + u x * du x) =
      (fun x => 2 * u x * du x) := by
    funext x
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.add_comm]
  rw [hderiv] at hproduct
  exact hproduct

end ComputableAnalysis
