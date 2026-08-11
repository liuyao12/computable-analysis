import ComputableAnalysis.Elementary
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.FTC
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.Taylor

/-!
# First-year calculus catalogue

This file is intentionally concrete.  It does not state IVT, MVT, or a general
integrability theorem.  Instead it records the elementary functions and
derivative identities that a first calculus course actually uses, with proofs
where the current constructive machinery is ready.
-/

namespace ComputableAnalysis

namespace FirstYearCalculus

abbrev Coeffs := FormalPowerSeries.Coeffs

/-- A checked coefficient-shift table entry.

The proof says that the listed coefficient stream has the displayed next
Taylor-coefficient stream.  Analytic convergence and interval evaluation are
handled separately by the concrete raw algorithms. -/
structure PowerSeriesDerivativeEntry where
  functionName : String
  derivativeName : String
  function : Coeffs
  derivative : Coeffs
  checked : FormalPowerSeries.HasCoefficientShift function derivative

namespace PowerSeriesDerivativeEntry

def monomial (k : Nat) : PowerSeriesDerivativeEntry where
  functionName := "x^(n+1)/(n+1)"
  derivativeName := "x^n"
  function := FormalPowerSeries.monomialShiftedCoeff k
  derivative := FormalPowerSeries.monomialCoeff k
  checked := FormalPowerSeries.monomialShiftedCoeff_hasCoefficientShift k

def exp : PowerSeriesDerivativeEntry where
  functionName := "exp x"
  derivativeName := "exp x"
  function := FormalPowerSeries.expCoeff
  derivative := FormalPowerSeries.expCoeff
  checked := FormalPowerSeries.expCoeff_hasCoefficientShift

def sin : PowerSeriesDerivativeEntry where
  functionName := "sin x"
  derivativeName := "cos x"
  function := FormalPowerSeries.sinCoeff
  derivative := FormalPowerSeries.cosCoeff
  checked := FormalPowerSeries.sinCoeff_hasCoefficientShift

def negCos : PowerSeriesDerivativeEntry where
  functionName := "-cos x"
  derivativeName := "sin x"
  function := FormalPowerSeries.neg FormalPowerSeries.cosCoeff
  derivative := FormalPowerSeries.sinCoeff
  checked := FormalPowerSeries.neg_cosCoeff_hasCoefficientShift

def cosh : PowerSeriesDerivativeEntry where
  functionName := "cosh x"
  derivativeName := "sinh x"
  function := FormalPowerSeries.coshCoeff
  derivative := FormalPowerSeries.sinhCoeff
  checked := FormalPowerSeries.coshCoeff_hasCoefficientShift

def sinh : PowerSeriesDerivativeEntry where
  functionName := "sinh x"
  derivativeName := "cosh x"
  function := FormalPowerSeries.sinhCoeff
  derivative := FormalPowerSeries.coshCoeff
  checked := FormalPowerSeries.sinhCoeff_hasCoefficientShift

def hasCheckedProof (entry : PowerSeriesDerivativeEntry) : Prop :=
  FormalPowerSeries.HasCoefficientShift entry.function entry.derivative

end PowerSeriesDerivativeEntry

/- Real-axis versions of the power-series elementary functions. -/
namespace RealElementary

def expPS : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ComputableAnalysis.exp.ps

def sinPS : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ComputableAnalysis.sin.ps

def cosPS : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ComputableAnalysis.cos.ps

def sinhFromExp : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ComputableAnalysis.sinh.fromExp

def coshFromExp : PartialRealFunRaw :=
  FunctionRaw.realPartOnRealAxis ComputableAnalysis.cosh.fromExp

def sqrtRat : PartialRealFunRaw :=
  sqrtPartialRaw

def invX : PartialRealFunRaw :=
  RatFun.asPartialRealFunRaw RatFun.oneOverX

def invOnePlusSquare : PartialRealFunRaw :=
  RatFun.asPartialRealFunRaw RatFun.oneOverOnePlusSquare

def invOnePlusSquareOnInterval (a b : Rat) : FunctionOnInterval :=
  RatFun.oneOverOnePlusSquareOnInterval a b

end RealElementary

/- Concrete integration targets that remain after the current checked table:
these are not general theorems, but named first-year formulas whose individual
constructive proofs should be supplied one by one. -/
namespace IntegralTargets

def log_from_invX : Prop :=
  Nonempty Elementary.LogFromIntegralInv

def arctan_from_invOnePlusSquare : Prop :=
  Elementary.Arctan.PowerSeriesSpec

def asin_from_sqrt_kernel : Prop :=
  Nonempty Elementary.ArcsinFromMonotoneSin

def exp_integral_inverse_consistency
    (inverse : ComputableAnalysis.exp.InverseLogIntegral) : Prop :=
  ComputableAnalysis.exp.agreesWithInverseLogIntegral inverse

end IntegralTargets

/-- The currently checked power-series portion of the first-year
derivative table. -/
theorem checked_power_series_table :
    PowerSeriesDerivativeEntry.hasCheckedProof PowerSeriesDerivativeEntry.exp /\
    PowerSeriesDerivativeEntry.hasCheckedProof PowerSeriesDerivativeEntry.sin /\
    PowerSeriesDerivativeEntry.hasCheckedProof PowerSeriesDerivativeEntry.negCos /\
    PowerSeriesDerivativeEntry.hasCheckedProof PowerSeriesDerivativeEntry.sinh /\
    PowerSeriesDerivativeEntry.hasCheckedProof PowerSeriesDerivativeEntry.cosh := by
  exact ⟨PowerSeriesDerivativeEntry.exp.checked,
    PowerSeriesDerivativeEntry.sin.checked,
    PowerSeriesDerivativeEntry.negCos.checked,
    PowerSeriesDerivativeEntry.sinh.checked,
    PowerSeriesDerivativeEntry.cosh.checked⟩

/- A finite constructive-IVT refinement of the unit square-root search.  The
   endpoint statements are rational square certificates, and the requested
   stage is accompanied by its literal dyadic error budget. -/
theorem sqrtOnUnitBisectionSearch_stage_certificate
    (q : Rat) (hq : inDomainInterval 0 1 q) (n : Nat) (hn : n ≠ 0)
    (eps : Rat)
    (hbudget : 1 / (((2 ^ (n + 9) : Nat) : Rat)) <= eps) :
    let I := (sqrtOnUnitBisectionSearch q hq).compute_preimage n
    subintervalOf I 0 1 /\
      I.lo * I.lo <= q /\
      q <= I.hi * I.hi /\
      I.width <= eps := by
  have hdomain : sqrtDomain q := by
    unfold sqrtDomain
    grind [hq.1]
  have hsub := sqrtApproxOnUnit_subinterval q hq n
  have hspec := sqrtApproxOnDomain_spec q hdomain n
  have hwidth := sqrtApproxOnDomain_width_eq_unit hdomain hq.2 n hn
  dsimp [sqrtOnUnitBisectionSearch]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hsub
  · simpa [sq] using hspec.2.2.1
  · simpa [sq] using hspec.2.2.2
  · rw [hwidth]
    exact hbudget

/- A finite stage-to-stage certificate for the unit square-root search.

The later box is contained in the earlier box, both endpoint squares bracket
the rational target, and the later width is no larger.  For positive stages
the two widths are also exposed as their exact dyadic rational values.  This
is a statement about the executable bisection trace only; it invokes no
completed real, completeness, or general intermediate-value principle. -/
theorem sqrtOnUnitBisectionSearch_nested_stage_certificate
    (q : Rat) (hq : inDomainInterval 0 1 q)
    {n m : Nat} (hnm : n <= m) (hn : n ≠ 0) (hm : m ≠ 0) :
    let I := (sqrtOnUnitBisectionSearch q hq).compute_preimage n
    let J := (sqrtOnUnitBisectionSearch q hq).compute_preimage m
    I.lo <= J.lo /\
      J.lo <= J.hi /\
      J.hi <= I.hi /\
      I.lo * I.lo <= q /\
      q <= I.hi * I.hi /\
      J.lo * J.lo <= q /\
      q <= J.hi * J.hi /\
      J.width <= I.width /\
      I.width = 1 / (((2 ^ (n + 9) : Nat) : Rat)) /\
      J.width = 1 / (((2 ^ (m + 9) : Nat) : Rat)) := by
  have hdomain : sqrtDomain q := by
    unfold sqrtDomain
    grind [hq.1]
  have hnest := sqrtApproxOnDomain_nested q hdomain n m hnm
  have hspecN := sqrtApproxOnDomain_spec q hdomain n
  have hspecM := sqrtApproxOnDomain_spec q hdomain m
  have hwidthN := sqrtApproxOnDomain_width_eq_unit hdomain hq.2 n hn
  have hwidthM := sqrtApproxOnDomain_width_eq_unit hdomain hq.2 m hm
  have hwidthMono :
      (sqrtApproxOnDomain q hdomain m).width <=
        (sqrtApproxOnDomain q hdomain n).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  dsimp [sqrtOnUnitBisectionSearch]
  refine ⟨hnest.1, hnest.2.1, hnest.2.2, ?_, ?_, ?_, ?_, hwidthMono, ?_, ?_⟩
  · exact hspecN.2.2.1
  · exact hspecN.2.2.2
  · exact hspecM.2.2.1
  · exact hspecM.2.2.2
  · exact hwidthN
  · exact hwidthM

/-- A finite Taylor-style enclosure for the rational arctangent kernel.

The omitted term is controlled by an explicit rational power budget.  Thus
this is an executable finite certificate for every rational input, rather
than a statement about a completed limit or an infinite series. -/
theorem arctanKernel_error_box
    (x eps : Rat) (n : Nat)
    (hbudget : (x * x) ^ (n + 1) <= eps) :
    Taylor.ArctanKernel.kernelPartial x n - eps <= 1 / (1 + x * x) /\
      1 / (1 + x * x) <= Taylor.ArctanKernel.kernelPartial x n + eps := by
  have hcertificate :=
    Taylor.ArctanKernel.finite_remainder_error_budget x eps n hbudget
  have hremLower : -eps <= Taylor.ArctanKernel.kernelRemainder x n := by
    have hself :=
      self_le_qabs (-(Taylor.ArctanKernel.kernelRemainder x n))
    have habs : qabs (Taylor.ArctanKernel.kernelRemainder x n) <= eps :=
      hcertificate.2
    rw [qabs_neg] at hself
    have hneg : -(Taylor.ArctanKernel.kernelRemainder x n) <= eps :=
      Rat.le_trans hself habs
    grind
  have hremUpper : Taylor.ArctanKernel.kernelRemainder x n <= eps := by
    exact Rat.le_trans (self_le_qabs _) hcertificate.2
  constructor
  · rw [hcertificate.1]
    grind
  · rw [hcertificate.1]
    grind
end FirstYearCalculus

end ComputableAnalysis
