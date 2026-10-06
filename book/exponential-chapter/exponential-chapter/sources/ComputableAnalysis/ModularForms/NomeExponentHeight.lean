import ComputableAnalysis.ModularForms.ExponentialSquaredMagnitude

/-! Exact dependence of the actual nome exponent on represented height. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Positive nome growth parameter, representing twice pi times the height. -/
def nomeHeightGrowth (z : Scalar) : RealRaw :=
  RealRaw.scaleRat 4 (RealRaw.mul GeometricPiRotation.halfPi z.val.imagPart)

theorem nomeHeightGrowth_valid (z : Scalar) : (nomeHeightGrowth z).Valid :=
  RealRaw.scaleRat_valid (RealRaw.mul_valid GeometricPiRotation.halfPi_valid (imagPart_valid z.property))

/-- The actual nome exponent has real part negative twice pi times the input height. -/
theorem nomeExponent_real_height (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (nomeExponentMap.eval z hz).val.realPart.Equiv (RealRaw.neg (nomeHeightGrowth z)) := by
  intro n
  let h := (GeometricPiRotation.halfPi.compute n).lo
  let p := (z.val.compute n).lo
  have hh := RealRaw.interval_order_of_valid GeometricPiRotation.halfPi GeometricPiRotation.halfPi_valid n
  have hp := valid_ordered z.property n
  have hs : (nomeSlope.val.compute n).lo≤(⟨0,4*h⟩ : QComplex) ∧
      (⟨0,4*h⟩ : QComplex)≤(nomeSlope.val.compute n).hi := by
    simp only [nomeSlope,scaleRat,mulI,ofRealRaw,QBox.scaleRat,
      if_pos (show (0:Rat)≤4 by decide +kernel),QComplex.le_def,Rat.neg_zero,Rat.mul_zero]
    change ((0:Rat)≤0 ∧ 4*h≤4*h) ∧ (0≤0 ∧ 4*h≤4*(GeometricPiRotation.halfPi.compute n).hi)
    have hm := Rat.mul_le_mul_of_nonneg_left hh (show (0:Rat)≤4 by decide +kernel)
    constructor
    · exact ⟨Rat.le_refl,Rat.le_refl⟩
    · exact ⟨Rat.le_refl,hm⟩
  have hm := QBox.mul_contains hs.1 hs.2 (QComplex.le_refl p) hp
  have hml := hm.1.1
  have hmu := hm.2.1
  simp only [QComplex.mul,Rat.zero_mul,Rat.sub_eq_add_neg,Rat.zero_add] at hml hmu
  change ((nomeExponentMap.eval z hz).val.compute n).lo.re≤ -(4*h*p.im) at hml
  change -(4*h*p.im)≤((nomeExponentMap.eval z hz).val.compute n).hi.re at hmu
  have ht := QBox.mulRealInterval_contains (show h≤h from Rat.le_refl) hh (show p.im≤p.im from Rat.le_refl) hp.2
  have htl := ht.1
  have htu := ht.2
  apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
  change ((nomeExponentMap.eval z hz).val.compute n).lo.re≤
      ((RealRaw.neg (nomeHeightGrowth z)).compute n).hi ∧
    ((RealRaw.neg (nomeHeightGrowth z)).compute n).lo≤
      ((nomeExponentMap.eval z hz).val.compute n).hi.re
  simp only [nomeHeightGrowth,RealRaw.neg,RealRaw.negCompute,RealRaw.scaleRat,
    RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤4 by decide +kernel),
    RealRaw.mul,RealRaw.mulCompute,imagPart]
  constructor <;> grind only

/-- The actual nome squared magnitude is a real exponential determined solely by height. -/
theorem nome_squared_magnitude_height (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (mul (nome.eval z hz).val (conj (nome.eval z hz).val)).Equiv
      (entireExponentialValue ⟨ofRealRaw (RealRaw.scaleRat 2 (RealRaw.neg (nomeHeightGrowth z))),
        ofRealRaw_valid _ (RealRaw.scaleRat_valid (RealRaw.neg_valid (nomeHeightGrowth_valid z)))⟩).val := by
  let a : Scalar := ⟨ofRealRaw (RealRaw.scaleRat 2 (nomeExponentMap.eval z hz).val.realPart),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid (nomeExponentMap.eval z hz).property))⟩
  let b : Scalar := ⟨ofRealRaw (RealRaw.scaleRat 2 (RealRaw.neg (nomeHeightGrowth z))),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (RealRaw.neg_valid (nomeHeightGrowth_valid z)))⟩
  have he : a.val.Equiv b.val :=
    ofRealRaw_equiv_of_equiv (RealRaw.scaleRat_valid (realPart_valid (nomeExponentMap.eval z hz).property))
      (RealRaw.scaleRat_valid (RealRaw.neg_valid (nomeHeightGrowth_valid z)))
      (RealRaw.scaleRat_equiv (nomeExponent_real_height z hz))
  exact equiv_trans (mul_valid (nome.eval z hz).property (conj_valid _ (nome.eval z hz).property))
    (entireExponentialValue a).property (entireExponentialValue b).property
    (nome_squared_magnitude z hz) (entireExponentialValue_congr a b he)

end ComputableAnalysis.ModularForms
