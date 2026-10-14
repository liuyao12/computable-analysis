import ComputableAnalysis.ModularForms.LambertDerivative

/-! Explicit continuity of the actual Lambert derivative on supplied disks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem lambertDerivative_difference_bound (r H : Rat) (hr : 0≤r) (hH : 0≤H)
    (hlocal : 2*r≤(1:Rat)/2) (a z : Scalar) (ha : Small a.val r) (hz : Small z.val r)
    (hd : Small (sub z.val a.val) H) :
    Small (sub (lambertDiskDerivative z r hr hlocal hz).val
      (lambertDiskDerivative a r hr hlocal ha).val) (1024*H) := by
  have va := nomeGeometricSum_valid a r hr hlocal ha
  have vz := nomeGeometricSum_valid z r hr hlocal hz
  have ba := nomeGeometricSum_bound a r hr hlocal ha
  have bz := nomeGeometricSum_bound z r hr hlocal hz
  have ia := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) a.property) va)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse a r hr hlocal ha)
  have iz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) vz)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hlocal hz)
  have vd := sub_valid z.property a.property
  have vp := mul_valid va vz
  have vs := add_valid va vz
  have he : (sub (lambertDiskDerivative z r hr hlocal hz).val
      (lambertDiskDerivative a r hr hlocal ha).val).Equiv
      (mul (mul (sub z.val a.val) (mul (nomeGeometricSum a r) (nomeGeometricSum z r)))
        (add (nomeGeometricSum a r) (nomeGeometricSum z r))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (lambertDiskDerivative z r hr hlocal hz).property
        (lambertDiskDerivative a r hr hlocal ha).property)
      (hright := mul_valid (mul_valid vd vp) vs)
    let A := ComplexRawQuotient.ofRaw (nomeGeometricSum a r) va
    let B := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) vz
    let X := ComplexRawQuotient.ofRaw a.val a.property
    let Y := ComplexRawQuotient.ofRaw z.val z.property
    change (1-X)*A=1 at ia
    change (1-Y)*B=1 at iz
    change B*B-A*A=((Y-X)*(A*B))*(A+B)
    grind only
  have bp := Small.mul va vz (show (0:Rat)≤4 by decide) (by decide) ba bz
  rw [show (2:Rat)*4*4=32 by decide +kernel] at bp
  have bs := LocalODE.small_add ba bz
  rw [show (4:Rat)+4=8 by decide +kernel] at bs
  have bdp := Small.mul vd vp hH (show (0:Rat)≤32 by decide) hd bp
  have b := Small.mul (mul_valid vd vp) vs
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hH) (show (0:Rat)≤32 by decide))
    (show (0:Rat)≤8 by decide) bdp bs
  rw [show (2:Rat)*(2*H*32)*8=1024*H by grind only] at b
  exact Small.congr (mul_valid (mul_valid vd vp) vs)
    (sub_valid (lambertDiskDerivative z r hr hlocal hz).property
      (lambertDiskDerivative a r hr hlocal ha).property) (equiv_symm he) b

def lambertDiskDerivative_continuous (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    ContinuousOn (lambertDiskMap r hr hlocal).domain
      (fun z hz => lambertDiskDerivative z r hr hlocal hz) where
  delta _ _ eps := divideRadius eps ⟨1024,by decide +kernel⟩
  estimate a ha eps z hz hd := by
    have h := lambertDerivative_difference_bound r (divideRadius eps ⟨1024,by decide +kernel⟩).val
      hr (Rat.le_of_lt (divideRadius eps ⟨1024,by decide +kernel⟩).property) hlocal a z ha hz hd
    rw [divideRadius_identity eps ⟨1024,by decide +kernel⟩] at h
    exact h

end ComputableAnalysis.ModularForms
