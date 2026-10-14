import ComputableAnalysis.RiemannHilbert.CertifiedFunctions
import ComputableAnalysis.RiemannHilbert.LocalSeriesDerivative

/-! The local scalar series as a represented function with a proved derivative. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def interior (R : Rat) (z : Scalar) : Prop :=
  ∃ r : Rat, 0 ≤ r ∧ r < R ∧ Small z.val r

theorem interior_bound (R : Rat) (z : Scalar) (hz : interior R z) : Small z.val R := by
  obtain ⟨r,_,hr,hz⟩ := hz
  exact hz.mono (Rat.le_of_lt hr)

def seriesMap (b : Nat → ComplexRaw) (initial : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) : CertifiedFunctions.Map where
  domain := interior R
  eval z := sumValue b initial z.val hb h0 z.property C K R
  valid z hz := sumValue_valid b initial z.val hb h0 z.property M C K R hM hC hK hR
    hMK hbB hinit (interior_bound R z hz) (by have := Rat.mul_nonneg hK hR; grind)
  domain_congr z w hzw := by
    constructor
    · intro hz
      obtain ⟨r,hr,hrR,hz⟩ := hz
      exact ⟨r,hr,hrR,Small.congr z.property w.property hzw hz⟩
    · intro hw
      obtain ⟨r,hr,hrR,hw⟩ := hw
      exact ⟨r,hr,hrR,Small.congr w.property z.property (equiv_symm hzw) hw⟩
  eval_congr z w hz hw hzw := sumValue_congr b b initial initial z.val w.val
    hb hb h0 h0 z.property w.property
    (fun n => equiv_refl _ (hb n)) (equiv_refl _ h0) hzw
    M C K R hM hC hK hR hMK hbB hinit (interior_bound R z hz)
    (by have := Rat.mul_nonneg hK hR; grind)

def seriesMap_derivative (b : Nat → ComplexRaw) (initial : ComplexRaw)
    (hb : ∀ n, (b n).Valid) (h0 : initial.Valid)
    (M C K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hMK : 2*M ≤ K) (hbB : ∀ n, Small (b n) (M*K^n)) (hinit : Small initial C)
    (hlocal : 8*K*R ≤ (1 : Rat)/2) (a : Scalar) (ha : interior R a) :
    CertifiedFunctions.HasDerivativeAt
      (seriesMap b initial hb h0 M C K R hM hC hK hR hMK hbB hinit hlocal) a
      (sumDerivative b initial a.val hb h0 a.property C K R) where
  point_mem := ha
  derivative_valid := sumDerivative_valid b initial a.val hb h0 a.property M C K R
    hM hC hK hR hMK hbB hinit (interior_bound R a ha)
    (by have := Rat.mul_nonneg hK hR; grind)
  delta := derivativeDelta C K hC hK
  estimate eps H z hz hH hza := sum_derivative_error b initial a.val z.val hb h0 a.property z.property
    M C K R hM hC hK hR hMK hbB hinit (interior_bound R a ha) (interior_bound R z hz)
    hlocal eps H hH hza

/-- The specified interior domain contains a rational neighborhood of every
one of its points. This is existence of the neighborhood, separate from a
computable procedure selecting a witness. -/
theorem interior_open (R : Rat) (a : Scalar) (ha : interior R a) :
    ∃ delta : QPos, ∀ z : Scalar, Small (sub z.val a.val) delta.val → interior R z := by
  obtain ⟨r,hr,hrR,ha⟩ := ha
  let delta : QPos := ⟨(R-r)/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
  refine ⟨delta, ?_⟩
  intro z hz
  have hs := small_add ha hz
  have hzBound : Small z.val (r+delta.val) := Small.congr
    (add_valid a.property (sub_valid z.property a.property)) z.property
    (SeriesLimitLaws.add_difference z.val a.val z.property a.property) hs
  exact ⟨r+delta.val, Rat.add_nonneg hr (Rat.le_of_lt delta.property), by dsimp [delta]; grind, hzBound⟩

end ComputableAnalysis.RiemannHilbert.LocalODE
