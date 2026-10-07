import ComputableAnalysis.ModularForms.LambertRemainderBound
import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Checked derivatives of the actual Lambert map on supplied small disks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def lambertDiskMap (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) : DomainFunctions.Map where
  domain z := Small z.val r
  eval z hz := ⟨lambertFactor z r,lambertFactor_valid z r hr hlocal hz⟩
  domain_congr z w he := ⟨fun h => Small.congr z.property w.property he h,
    fun h => Small.congr w.property z.property (equiv_symm he) h⟩
  eval_congr z w hz hw he := lambertFactor_congr z w r r hr hr hlocal hlocal hz hw he

def lambertDiskDerivative (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) : Scalar :=
  ⟨mul (nomeGeometricSum z r) (nomeGeometricSum z r),
    mul_valid (nomeGeometricSum_valid z r hr hlocal hz) (nomeGeometricSum_valid z r hr hlocal hz)⟩

def lambertDiskMap_hasDerivativeAt (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (a : Scalar) (ha : Small a.val r) :
    HasDerivativeAt (lambertDiskMap r hr hlocal) a ha (lambertDiskDerivative a r hr hlocal ha) where
  delta eps := divideRadius eps ⟨1024,by decide +kernel⟩
  estimate eps H z hz hH hza := by
    have hb := lambertFactor_remainder_bound a z r r H.val hr hr
      (Rat.le_of_lt H.property) hlocal hlocal ha hz hza
    have hc : (sub (sub (lambertFactor z r) (lambertFactor a r))
        (mul (sub z.val a.val) (lambertDiskDerivative a r hr hlocal ha).val)).Equiv
        (DomainFunctions.remainder (lambertDiskMap r hr hlocal) a ha
          (lambertDiskDerivative a r hr hlocal ha) z hz) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := sub_valid (sub_valid (lambertFactor_valid z r hr hlocal hz)
          (lambertFactor_valid a r hr hlocal ha))
          (mul_valid (sub_valid z.property a.property) (lambertDiskDerivative a r hr hlocal ha).property))
        (hright := DomainFunctions.remainder_valid (lambertDiskMap r hr hlocal) a ha (lambertDiskDerivative a r hr hlocal ha) z hz)
      let F := ComplexRawQuotient.ofRaw (lambertFactor z r) (lambertFactor_valid z r hr hlocal hz)
      let G := ComplexRawQuotient.ofRaw (lambertFactor a r) (lambertFactor_valid a r hr hlocal ha)
      let X := ComplexRawQuotient.ofRaw (sub z.val a.val) (sub_valid z.property a.property)
      let D := ComplexRawQuotient.ofRaw (lambertDiskDerivative a r hr hlocal ha).val
        (lambertDiskDerivative a r hr hlocal ha).property
      change (F-G)-X*D=(F-G)-D*X
      grind only
    have h := Small.congr
      (sub_valid (sub_valid (lambertFactor_valid z r hr hlocal hz) (lambertFactor_valid a r hr hlocal ha))
        (mul_valid (sub_valid z.property a.property) (lambertDiskDerivative a r hr hlocal ha).property))
      (DomainFunctions.remainder_valid (lambertDiskMap r hr hlocal) a ha (lambertDiskDerivative a r hr hlocal ha) z hz) hc hb
    apply h.mono
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show (0:Rat)≤1024 by decide)
    rw [divideRadius_identity eps ⟨1024,by decide +kernel⟩] at hm
    have hp := Rat.mul_le_mul_of_nonneg_right hm (Rat.le_of_lt H.property)
    rw [Rat.pow_succ, Rat.pow_succ, Rat.pow_zero]
    grind only

/-- Uniform bound on the actual Lambert derivative throughout its supplied disk. -/
theorem lambertDiskDerivative_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    Small (lambertDiskDerivative z r hr hlocal hz).val 32 := by
  have hg := nomeGeometricSum_bound z r hr hlocal hz
  have hv := nomeGeometricSum_valid z r hr hlocal hz
  have h := Small.mul hv hv (by decide +kernel : (0:Rat)≤4)
    (by decide +kernel : (0:Rat)≤4) hg hg
  simpa only [lambertDiskDerivative, show (2:Rat)*4*4=32 by decide +kernel] using h

end ComputableAnalysis.ModularForms
