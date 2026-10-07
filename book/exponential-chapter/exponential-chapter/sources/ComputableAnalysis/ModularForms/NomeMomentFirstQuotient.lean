import ComputableAnalysis.ModularForms.PolynomialNomeMoments
import ComputableAnalysis.ModularForms.WeightedNomeQuotient

/-! First-degree base quotient for the constructed polynomial nome moments. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem polynomialNomeMomentRatio_one (r : Rat) : polynomialNomeMomentRatio r 1=4*r := by
  unfold polynomialNomeMomentRatio
  rw [Rat.pow_one]
  grind only

theorem polynomialNomeMomentSum_one_weighted (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) :
    (polynomialNomeMomentSum z r 1).Equiv (weightedNomeSum z r) := by
  have hl : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_one]; exact hlocal
  apply ScalarSeries.value_congr _ _ _ _ r _ (2*r) (4*r) hr
    (polynomialNomeMomentRatio_nonneg r 1 hr) (Rat.mul_nonneg (by decide) hr)
    (Rat.mul_nonneg (by decide) hr) hl hlocal
    (polynomialNomeMomentTerm_bound z r 1 hr hz) (weightedNomePower_bound z r hr hz)
  intro n
  simp only [polynomialNomeMomentTerm,weightedNomePower,Rat.pow_one]
  exact equiv_refl _ (weightedNomePower_valid z n)

theorem polynomialNomeMomentSum_one_quotient (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r)
    (hn : NonzeroBoxSearch.Nonzero (nomeDenominator z)) :
    (polynomialNomeMomentSum z r 1).Equiv
      (mul z.val (mul (RepresentedReciprocal.inverse (nomeDenominator z) hn).val
        (RepresentedReciprocal.inverse (nomeDenominator z) hn).val)) := by
  have hl : polynomialNomeMomentRatio r 1≤(1:Rat)/2 := by
    rw [polynomialNomeMomentRatio_one]; exact hlocal
  let j := RepresentedReciprocal.inverse (nomeDenominator z) hn
  exact equiv_trans (polynomialNomeMomentSum_valid z r 1 hr hl hz)
    (weightedNomeSum_valid z r hr hlocal hz) (mul_valid z.property (mul_valid j.property j.property))
    (polynomialNomeMomentSum_one_weighted z r hr hlocal hz)
    (weightedNomeSum_quotient z r hr hlocal hz hn)

end ComputableAnalysis.ModularForms
