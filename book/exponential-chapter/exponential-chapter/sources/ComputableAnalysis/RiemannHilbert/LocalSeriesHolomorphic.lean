import ComputableAnalysis.RiemannHilbert.EffectiveNeighborhood
import ComputableAnalysis.RiemannHilbert.LocalSeriesContinuity
import ComputableAnalysis.RiemannHilbert.LocalODEInitialValue

/-! Constructing the complete local scalar holomorphic series witness. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def seriesMap_holomorphic (b : Nat → ComplexRaw) (initial : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    CertifiedFunctions.Holomorphic
      (seriesMap b initial hb h0 M C K R hM hC hK hR hMK hbB hinit hlocal) where
  openDomain := {
    radius := interiorRadius R
    inside := interiorRadius_inside R }
  derivative a := sumDerivative b initial a.val hb h0 a.property C K R
  atPoint a ha := seriesMap_derivative b initial hb h0 M C K R hM hC hK hR hMK hbB hinit hlocal a ha
  derivative_congr a z ha hz haz := sumDerivative_congr b b initial initial a.val z.val
    hb hb h0 h0 a.property z.property
    (fun n => equiv_refl _ (hb n)) (equiv_refl _ h0) haz
    M C K R hM hC hK hR hMK hbB hinit (interior_bound R a ha)
    (by have := Rat.mul_nonneg hK hR; grind)
  continuousDerivative := {
    delta := fun _ _ eps => derivativeDelta C K hC hK eps
    estimate := fun a ha eps z hz hza =>
      sumDerivative_continuity_error b initial a.val z.val hb h0 a.property z.property
        M C K R hM hC hK hR hMK hbB hinit (interior_bound R a ha) (interior_bound R z hz)
        hlocal eps hza }

theorem seriesMap_initial (b : Nat → ComplexRaw) (initial : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) :
    ((seriesMap b initial hb h0 M C K R hM hC hK hR hMK hbB hinit hlocal).eval
      ⟨zero, ofQComplex_valid _⟩).Equiv initial :=
  sumValue_initial b initial hb h0 M C K R hM hC hK hR hMK hbB hinit
    (by have := Rat.mul_nonneg hK hR; grind)


theorem interior_zero (R : Rat) (hR : 0 < R) :
    interior R ⟨zero, ofQComplex_valid _⟩ :=
  ⟨0, by decide, hR, Small.zero (by decide)⟩

end ComputableAnalysis.RiemannHilbert.LocalODE
