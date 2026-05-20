import ComputableAnalysis.Elementary
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.FTC
import ComputableAnalysis.FunctionDomains

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

/-- A checked formal derivative table entry.

The proof says that differentiating the listed coefficient stream gives the
listed derivative coefficient stream.  Analytic convergence and interval
evaluation are handled separately by the concrete raw algorithms. -/
structure PowerSeriesDerivativeEntry where
  functionName : String
  derivativeName : String
  function : Coeffs
  derivative : Coeffs
  checked : FormalPowerSeries.HasFormalDerivative function derivative

namespace PowerSeriesDerivativeEntry

def monomial (k : Nat) : PowerSeriesDerivativeEntry where
  functionName := "x^(n+1)/(n+1)"
  derivativeName := "x^n"
  function := FormalPowerSeries.monomialShiftedCoeff k
  derivative := FormalPowerSeries.monomialCoeff k
  checked := FormalPowerSeries.monomialShiftedCoeff_derivative k

def exp : PowerSeriesDerivativeEntry where
  functionName := "exp x"
  derivativeName := "exp x"
  function := FormalPowerSeries.expCoeff
  derivative := FormalPowerSeries.expCoeff
  checked := FormalPowerSeries.expCoeff_hasFormalDerivative

def sin : PowerSeriesDerivativeEntry where
  functionName := "sin x"
  derivativeName := "cos x"
  function := FormalPowerSeries.sinCoeff
  derivative := FormalPowerSeries.cosCoeff
  checked := FormalPowerSeries.sinCoeff_hasFormalDerivative

def negCos : PowerSeriesDerivativeEntry where
  functionName := "-cos x"
  derivativeName := "sin x"
  function := FormalPowerSeries.neg FormalPowerSeries.cosCoeff
  derivative := FormalPowerSeries.sinCoeff
  checked := FormalPowerSeries.neg_cosCoeff_hasFormalDerivative

def cosh : PowerSeriesDerivativeEntry where
  functionName := "cosh x"
  derivativeName := "sinh x"
  function := FormalPowerSeries.coshCoeff
  derivative := FormalPowerSeries.sinhCoeff
  checked := FormalPowerSeries.coshCoeff_hasFormalDerivative

def sinh : PowerSeriesDerivativeEntry where
  functionName := "sinh x"
  derivativeName := "cosh x"
  function := FormalPowerSeries.sinhCoeff
  derivative := FormalPowerSeries.coshCoeff
  checked := FormalPowerSeries.sinhCoeff_hasFormalDerivative

def hasCheckedProof (entry : PowerSeriesDerivativeEntry) : Prop :=
  FormalPowerSeries.HasFormalDerivative entry.function entry.derivative

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
end FirstYearCalculus

end ComputableAnalysis
