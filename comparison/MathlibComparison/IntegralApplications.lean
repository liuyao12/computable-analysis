import MathlibComparison.Wallis
import MathlibComparison.BetaIntegral
import ComputableAnalysis.WallisBounds
import ComputableAnalysis.WallisFactorials
import ComputableAnalysis.BetaNormalization

/-! These are proofs of the SAME native computational statements.
Only shared algebra/order transports are reused, not a native analytic law. -/
namespace ComputableAnalysis.Wallis

theorem factorials_viaMathlib (n : Nat) : FactorialStatement n :=
  factorials_of_laws MathlibComparison.Wallis.lawsViaMathlib n

theorem productBounds_viaMathlib (n : Nat) : ProductBoundsStatement n :=
  product_bounds_of_laws MathlibComparison.Wallis.lawsViaMathlib n

end ComputableAnalysis.Wallis

namespace ComputableAnalysis.BetaIntegral

theorem normalization_viaMathlib (m n : Nat) : NormalizationStatement m n :=
  normalization_of_laws MathlibComparison.BetaIntegral.lawsViaMathlib m n

end ComputableAnalysis.BetaIntegral
