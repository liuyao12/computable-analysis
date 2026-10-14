import ComputableAnalysis.ModularForms.LambertAgreement

/-! Exact resolvent differences for actual geometric and Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem lambertFactor_difference (z w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) :
    (sub (lambertFactor z r) (lambertFactor w s)).Equiv
      (mul (sub z.val w.val) (mul (nomeGeometricSum z r) (nomeGeometricSum w s))) := by
  have hvz := nomeGeometricSum_valid z r hr hrlocal hz
  have hvw := nomeGeometricSum_valid w s hs hslocal hw
  have iz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) hvz)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hrlocal hz)
  have iw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) w.property) hvw)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse w s hs hslocal hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (lambertFactor_valid z r hr hrlocal hz)
      (lambertFactor_valid w s hs hslocal hw))
    (hright := mul_valid (sub_valid z.property w.property) (mul_valid hvz hvw))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let A := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hvz
  let B := ComplexRawQuotient.ofRaw (nomeGeometricSum w s) hvw
  change (1-Z)*A=1 at iz
  change (1-W)*B=1 at iw
  change Z*A-W*B=(Z-W)*(A*B)
  grind only

theorem lambertFactor_quadratic_identity (z w : Scalar) (r s : Rat)
    (hr : 0≤r) (hs : 0≤s) (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) :
    (sub (sub (lambertFactor w s) (lambertFactor z r))
      (mul (sub w.val z.val) (mul (nomeGeometricSum z r) (nomeGeometricSum z r)))).Equiv
      (mul (mul (sub w.val z.val) (sub w.val z.val))
        (mul (mul (nomeGeometricSum z r) (nomeGeometricSum z r)) (nomeGeometricSum w s))) := by
  have hvz := nomeGeometricSum_valid z r hr hrlocal hz
  have hvw := nomeGeometricSum_valid w s hs hslocal hw
  have iz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) hvz)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hrlocal hz)
  have iw := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) w.property) hvw)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse w s hs hslocal hw)
  have hd := sub_valid w.property z.property
  have haa := mul_valid hvz hvz
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (sub_valid (lambertFactor_valid w s hs hslocal hw)
      (lambertFactor_valid z r hr hrlocal hz)) (mul_valid hd haa))
    (hright := mul_valid (mul_valid hd hd) (mul_valid haa hvw))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let A := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hvz
  let B := ComplexRawQuotient.ofRaw (nomeGeometricSum w s) hvw
  change (1-Z)*A=1 at iz
  change (1-W)*B=1 at iw
  change (W*B-Z*A)-(W-Z)*(A*A)=((W-Z)*(W-Z))*((A*A)*B)
  grind only

end ComputableAnalysis.ModularForms
