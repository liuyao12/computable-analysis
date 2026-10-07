import ComputableAnalysis.ModularForms.LambertRemainderBound

/-! Exact geometric expansion and shrinking literal prefixes for Lambert values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem lambertFactor_eq_geometric_sub_one (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (lambertFactor z r).Equiv (sub (nomeGeometricSum z r) (ofQComplex QComplex.one)) := by
  have hv := nomeGeometricSum_valid z r hr hlocal hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) hv)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := lambertFactor_valid z r hr hlocal hz)
    (hright := sub_valid hv (ofQComplex_valid _))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hv
  change (1-Z)*S=1 at hi
  change Z*S=S-1
  grind only

def lambertGeometricPrefix (z : Scalar) (N : Nat) : ComplexRaw :=
  sub (nomeGeometricPrefix z (N+1)) (ofQComplex QComplex.one)

theorem lambertGeometricPrefix_valid (z : Scalar) (N : Nat) :
    (lambertGeometricPrefix z N).Valid :=
  sub_valid (nomeGeometricPrefix_valid z (N+1)) (ofQComplex_valid _)

theorem lambertGeometricPrefix_close (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (lambertFactor z r) (lambertGeometricPrefix z N)) (4*(2*r)^(N+1)) := by
  have hv := nomeGeometricSum_valid z r hr hlocal hz
  have hp := nomeGeometricPrefix_valid z (N+1)
  have h := nomeGeometricSum_close z r hr hlocal hz (N+1)
  have he : (sub (lambertFactor z r) (lambertGeometricPrefix z N)).Equiv
      (sub (nomeGeometricSum z r) (nomeGeometricPrefix z (N+1))) := by
    have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := lambertFactor_valid z r hr hlocal hz)
      (hright := sub_valid hv (ofQComplex_valid _))
      (lambertFactor_eq_geometric_sub_one z r hr hlocal hz)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (lambertFactor_valid z r hr hlocal hz) (lambertGeometricPrefix_valid z N))
      (hright := sub_valid hv hp)
    let L := ComplexRawQuotient.ofRaw (lambertFactor z r) (lambertFactor_valid z r hr hlocal hz)
    let S := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) hv
    let P := ComplexRawQuotient.ofRaw (nomeGeometricPrefix z (N+1)) hp
    change L=S-1 at hi
    change L-(P-1)=S-P
    grind only
  exact Small.congr (sub_valid hv hp)
    (sub_valid (lambertFactor_valid z r hr hlocal hz) (lambertGeometricPrefix_valid z N))
    (equiv_symm he) h

end ComputableAnalysis.ModularForms
