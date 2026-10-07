import ComputableAnalysis.ModularForms.LambertFactor

/-! Representation and radius invariance of actual geometric and Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem nomeGeometricSum_congr (z w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hzw : z.val.Equiv w.val) :
    (nomeGeometricSum z r).Equiv (nomeGeometricSum w s) := by
  have hvz := nomeGeometricSum_valid z r hr hrlocal hz
  have hvw := nomeGeometricSum_valid w s hs hslocal hw
  have hzid := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) hvz)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hrlocal hz)
  have hwid := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) w.property) hvw)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse w s hs hslocal hw)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := z.property) (hright := w.property) hzw
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := hvz) (hright := hvw)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let A := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hvz
  let B := ComplexRawQuotient.ofRaw (nomeGeometricSum w s) hvw
  change (1-Z)*A=1 at hzid
  change (1-W)*B=1 at hwid
  change Z=W at he
  change A=B
  grind only

theorem lambertFactor_congr (z w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrlocal : 2*r≤(1:Rat)/2) (hslocal : 2*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hzw : z.val.Equiv w.val) :
    (lambertFactor z r).Equiv (lambertFactor w s) :=
  mul_equiv z.property w.property (nomeGeometricSum_valid z r hr hrlocal hz)
    (nomeGeometricSum_valid w s hs hslocal hw) hzw
    (nomeGeometricSum_congr z w r s hr hs hrlocal hslocal hz hw hzw)

end ComputableAnalysis.ModularForms
