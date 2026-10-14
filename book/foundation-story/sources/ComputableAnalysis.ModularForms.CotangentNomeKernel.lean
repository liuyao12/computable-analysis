import ComputableAnalysis.ModularForms.LambertPositivePowers

/-! The actual nome quotient kernel used in the cotangent Fourier argument. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def cotangentNomeKernel (z : Scalar) (r : Rat) : ComplexRaw :=
  add (ofQComplex QComplex.one) (add (lambertFactor z r) (lambertFactor z r))

theorem cotangentNomeKernel_valid (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) : (cotangentNomeKernel z r).Valid :=
  add_valid (ofQComplex_valid _) (add_valid (lambertFactor_valid z r hr hlocal hz)
    (lambertFactor_valid z r hr hlocal hz))

theorem cotangentNomeKernel_identity (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (mul (sub (ofQComplex QComplex.one) z.val) (cotangentNomeKernel z r)).Equiv
      (add (ofQComplex QComplex.one) z.val) := by
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property)
      (lambertFactor_valid z r hr hlocal hz)) (hright := z.property)
    (lambertFactor_multiplication z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property)
      (cotangentNomeKernel_valid z r hr hlocal hz))
    (hright := add_valid (ofQComplex_valid _) z.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let L := ComplexRawQuotient.ofRaw (lambertFactor z r) (lambertFactor_valid z r hr hlocal hz)
  change (1-Z)*L=Z at hi
  change (1-Z)*(1+(L+L))=1+Z
  grind only

def cotangentNomePrefix (z : Scalar) (N : Nat) : ComplexRaw :=
  add (ofQComplex QComplex.one) (add (lambertPositivePrefix z N) (lambertPositivePrefix z N))

theorem cotangentNomePrefix_valid (z : Scalar) (N : Nat) : (cotangentNomePrefix z N).Valid :=
  add_valid (ofQComplex_valid _) (add_valid (lambertPositivePrefix_valid z N) (lambertPositivePrefix_valid z N))

theorem cotangentNomePrefix_close (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) (N : Nat) :
    Small (sub (cotangentNomeKernel z r) (cotangentNomePrefix z N)) (8*(2*r)^(N+1)) := by
  have vl := lambertFactor_valid z r hr hlocal hz
  have vp := lambertPositivePrefix_valid z N
  have h := lambertPositivePrefix_close z r hr hlocal hz N
  have hb := LocalODE.small_add h h
  have he : (sub (cotangentNomeKernel z r) (cotangentNomePrefix z N)).Equiv
      (add (sub (lambertFactor z r) (lambertPositivePrefix z N))
        (sub (lambertFactor z r) (lambertPositivePrefix z N))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (cotangentNomeKernel_valid z r hr hlocal hz) (cotangentNomePrefix_valid z N))
      (hright := add_valid (sub_valid vl vp) (sub_valid vl vp))
    let L := ComplexRawQuotient.ofRaw (lambertFactor z r) vl
    let P := ComplexRawQuotient.ofRaw (lambertPositivePrefix z N) vp
    change (1+(L+L))-(1+(P+P))=(L-P)+(L-P)
    grind only
  have hb' := Small.congr (add_valid (sub_valid vl vp) (sub_valid vl vp))
    (sub_valid (cotangentNomeKernel_valid z r hr hlocal hz) (cotangentNomePrefix_valid z N))
    (equiv_symm he) hb
  rw [show (4:Rat)*(2*r)^(N+1)+4*(2*r)^(N+1)=8*(2*r)^(N+1) by grind only] at hb'
  exact hb'

end ComputableAnalysis.ModularForms
