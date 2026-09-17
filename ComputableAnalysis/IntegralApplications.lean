import ComputableAnalysis.WallisViaFTC
import ComputableAnalysis.WallisBounds
import ComputableAnalysis.WallisFactorials
import ComputableAnalysis.BetaViaFTC
import ComputableAnalysis.BetaNormalization

/-! Closed integral applications, with no Mathlib dependency. Each statement
also has a same-type proof exported only by the optional comparison package. -/
namespace ComputableAnalysis.Wallis

theorem factorials_viaFTC (n : Nat) : FactorialStatement n := factorials_of_laws lawsViaFTC n

theorem productBounds_viaFTC (n : Nat) : ProductBoundsStatement n := product_bounds_of_laws lawsViaFTC n

end ComputableAnalysis.Wallis

namespace ComputableAnalysis.BetaIntegral

theorem normalization_viaFTC (m n : Nat) : NormalizationStatement m n :=
  normalization_of_laws lawsViaFTC m n

end ComputableAnalysis.BetaIntegral
