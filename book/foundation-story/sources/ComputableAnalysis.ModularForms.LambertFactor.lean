import ComputableAnalysis.ModularForms.NomeGeometricInverse

/-! Actual small-disk Lambert factors, with exact multiplication and bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def lambertFactor (z : Scalar) (r : Rat) : ComplexRaw := mul z.val (nomeGeometricSum z r)

theorem lambertFactor_valid (z : Scalar) (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hz : Small z.val r) : (lambertFactor z r).Valid :=
  mul_valid z.property (nomeGeometricSum_valid z r hr hlocal hz)

theorem lambertFactor_bound (z : Scalar) (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (hz : Small z.val r) : Small (lambertFactor z r) (8*r) := by
  have hs := ScalarSeries.value_bound (LocalODE.power z.val) (LocalODE.power_valid _ z.property)
    1 (2*r) (by decide) (Rat.mul_nonneg (by decide) hr) hlocal
    (fun n => by
      apply (LocalODE.power_small z.val z.property r hr hz n).mono
      have hp := Rat.pow_nonneg (n := n) (Rat.mul_nonneg (show (0:Rat)≤2 by decide) hr)
      grind only)
  rw [show (4:Rat)*1=4 by decide +kernel] at hs
  have hb := Small.mul z.property (nomeGeometricSum_valid z r hr hlocal hz) hr (by decide) hz hs
  have he : (2:Rat)*r*4=8*r := by grind only
  rw [he] at hb
  exact hb

theorem lambertFactor_multiplication (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (mul (sub (ofQComplex QComplex.one) z.val) (lambertFactor z r)).Equiv z.val := by
  have hv := nomeGeometricSum_valid z r hr hlocal hz
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) hv)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) (lambertFactor_valid z r hr hlocal hz))
    (hright := z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hv
  change (1-Z)*S=1 at ht
  change (1-Z)*(Z*S)=Z
  grind only

end ComputableAnalysis.ModularForms
