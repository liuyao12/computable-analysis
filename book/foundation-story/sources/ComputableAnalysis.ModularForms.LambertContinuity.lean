import ComputableAnalysis.ModularForms.LambertDerivativeContinuity

/-! Value continuity and representation agreement of actual Lambert derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem lambertDiskDerivative_congr (a z : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (ha : Small a.val r) (hz : Small z.val s) (he : a.val.Equiv z.val) :
    (lambertDiskDerivative a r hr hrlocal ha).val.Equiv
      (lambertDiskDerivative z s hs hslocal hz).val := by
  have hv := nomeGeometricSum_valid a r hr hrlocal ha
  have hw := nomeGeometricSum_valid z s hs hslocal hz
  have h := nomeGeometricSum_congr a z r s hr hs hrlocal hslocal ha hz he
  exact mul_equiv hv hw hv hw h h

theorem lambertFactor_difference_bound (a z : Scalar) (r s H : Rat)
    (hr : 0≤r) (hs : 0≤s) (hH : 0≤H)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (ha : Small a.val r) (hz : Small z.val s) (hd : Small (sub z.val a.val) H) :
    Small (sub (lambertFactor z s) (lambertFactor a r)) (64*H) := by
  have va := nomeGeometricSum_valid a r hr hrlocal ha
  have vz := nomeGeometricSum_valid z s hs hslocal hz
  have ba := nomeGeometricSum_bound a r hr hrlocal ha
  have bz := nomeGeometricSum_bound z s hs hslocal hz
  have bp := Small.mul vz va (show (0:Rat)≤4 by decide) (by decide) bz ba
  rw [show (2:Rat)*4*4=32 by decide +kernel] at bp
  have b := Small.mul (sub_valid z.property a.property) (mul_valid vz va)
    hH (show (0:Rat)≤32 by decide) hd bp
  rw [show (2:Rat)*H*32=64*H by grind only] at b
  exact Small.congr (mul_valid (sub_valid z.property a.property) (mul_valid vz va))
    (sub_valid (lambertFactor_valid z s hs hslocal hz) (lambertFactor_valid a r hr hrlocal ha))
    (equiv_symm (lambertFactor_difference z a s r hs hr hslocal hrlocal hz ha)) b

def lambertDiskMap_continuous (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    ContinuousOn (lambertDiskMap r hr hlocal).domain (lambertDiskMap r hr hlocal).eval where
  delta _ _ eps := divideRadius eps ⟨64,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := lambertFactor_difference_bound a z r r
      (divideRadius eps ⟨64,by decide +kernel⟩).val hr hr
      (Rat.le_of_lt (divideRadius eps ⟨64,by decide +kernel⟩).property)
      hlocal hlocal ha hz hd
    rw [divideRadius_identity eps ⟨64,by decide +kernel⟩] at h
    exact h

end ComputableAnalysis.ModularForms
