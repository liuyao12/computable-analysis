import ComputableAnalysis.RiemannHilbert.GeneralSeriesContinuity

/-! Holomorphic witnesses for actual sums of supplied bounded complex series. -/
namespace ComputableAnalysis.RiemannHilbert.BoundedSeries
open ComplexRaw FunctionTheory LocalODE

def seriesMap (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    CertifiedFunctions.Map where
  domain := interior R
  eval z := sumValue c z.val hc z.property C K R
  valid z hz := sumValue_valid c z.val hc z.property C K R hC hK hR hcB (interior_bound R z hz)
    (by have := Rat.mul_nonneg hK hR; grind)
  domain_congr z w hzw := by
    constructor
    · intro hz
      obtain ⟨r,hr,hrR,hz⟩ := hz
      exact ⟨r,hr,hrR,Small.congr z.property w.property hzw hz⟩
    · intro hw
      obtain ⟨r,hr,hrR,hw⟩ := hw
      exact ⟨r,hr,hrR,Small.congr w.property z.property (equiv_symm hzw) hw⟩
  eval_congr z w hz hw hzw :=
    coefficientSum_congr c c z.val w.val hc hc z.property w.property
      (fun i => equiv_refl _ (hc i)) hzw C K R hC hK hR hcB (interior_bound R z hz)
      (by have := Rat.mul_nonneg hK hR; grind)

def seriesMap_derivative (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 8*K*R ≤ (1 : Rat)/2)
    (a : Scalar) (ha : interior R a) :
    CertifiedFunctions.HasDerivativeAt (seriesMap c hc C K R hC hK hR hcB hlocal) a
      (sumDerivative c a.val hc a.property C K R) where
  point_mem := ha
  derivative_valid := sumDerivative_valid c a.val hc a.property C K R hC hK hR hcB
    (interior_bound R a ha) (by have := Rat.mul_nonneg hK hR; grind)
  delta := derivativeDelta C K hC hK
  estimate eps H z hz hH hza := sum_derivative_error c a.val z.val hc a.property z.property
    C K R hC hK hR hcB (interior_bound R a ha) (interior_bound R z hz) hlocal eps H hH hza

def seriesMap_holomorphic (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    CertifiedFunctions.Holomorphic (seriesMap c hc C K R hC hK hR hcB hlocal) where
  openDomain := {
    radius := interiorRadius R
    inside := interiorRadius_inside R }
  derivative a := sumDerivative c a.val hc a.property C K R
  atPoint a ha := seriesMap_derivative c hc C K R hC hK hR hcB hlocal a ha
  derivative_congr a z ha hz haz := sumDerivative_congr c a.val z.val hc a.property z.property
    haz C K R hC hK hR hcB (interior_bound R a ha)
    (by have := Rat.mul_nonneg hK hR; grind)
  continuousDerivative := {
    delta := fun _ _ eps => derivativeDelta C K hC hK eps
    estimate := fun a ha eps z hz hza =>
      sumDerivative_continuity_error c a.val z.val hc a.property z.property
        C K R hC hK hR hcB (interior_bound R a ha) (interior_bound R z hz) hlocal eps hza }

theorem seriesMap_initial (c : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid)
    (C K R : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    ((seriesMap c hc C K R hC hK hR hcB hlocal).eval ⟨zero, ofQComplex_valid _⟩).Equiv (c 0) :=
  coefficientSum_zero c hc C K R hC hK hR hcB (by have := Rat.mul_nonneg hK hR; grind)

theorem seriesMap_congr (c d : Nat → ComplexRaw) (hc : ∀ i, (c i).Valid) (hd : ∀ i, (d i).Valid)
    (hcd : ∀ i, (c i).Equiv (d i)) (C K R D L S : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hcB : ∀ i, Small (c i) (C*K^i)) (hdB : ∀ i, Small (d i) (D*L^i))
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (hs : 8*L*S ≤ (1 : Rat)/2)
    (z w : Scalar) (hz : interior R z) (hw : interior S w) (hzw : z.val.Equiv w.val) :
    ((seriesMap c hc C K R hC hK hR hcB hlocal).eval z).Equiv
      ((seriesMap d hd D L S hD hL hS hdB hs).eval w) :=
  coefficientSum_congr_of_bounds c d z.val w.val hc hd z.property w.property hcd hzw C K R D L S
    hC hK hR hD hL hS hcB hdB (interior_bound R z hz) (interior_bound S w hw)
    (by have := Rat.mul_nonneg hK hR; grind) (by have := Rat.mul_nonneg hL hS; grind)

end ComputableAnalysis.RiemannHilbert.BoundedSeries
