import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Quantitative comparison of actual function and derivative remainders. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

theorem remainder_comparison (f g : Map) (a z : Scalar)
    (hfa : f.domain a) (hfz : f.domain z) (hga : g.domain a) (hgz : g.domain z)
    (d e : Scalar) :
    (sub (remainder f a hfa d z hfz) (remainder g a hga e z hgz)).Equiv
      (sub (sub (sub (f.eval z hfz).val (g.eval z hgz).val)
        (sub (f.eval a hfa).val (g.eval a hga).val))
        (mul (sub d.val e.val) (sub z.val a.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (hright := sub_valid
      (sub_valid (sub_valid (f.eval z hfz).property (g.eval z hgz).property)
        (sub_valid (f.eval a hfa).property (g.eval a hga).property))
      (mul_valid (sub_valid d.property e.property) (sub_valid z.property a.property)))
  let FZ := ComplexRawQuotient.ofRaw (f.eval z hfz).val (f.eval z hfz).property
  let FA := ComplexRawQuotient.ofRaw (f.eval a hfa).val (f.eval a hfa).property
  let GZ := ComplexRawQuotient.ofRaw (g.eval z hgz).val (g.eval z hgz).property
  let GA := ComplexRawQuotient.ofRaw (g.eval a hga).val (g.eval a hga).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let E := ComplexRawQuotient.ofRaw e.val e.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change ((FZ + -FA) + -(D*(Z + -A))) + -((GZ + -GA) + -(E*(Z + -A))) =
    ((FZ + -GZ) + -(FA + -GA)) + -((D + -E)*(Z + -A))
  grind only

theorem remainder_comparison_bound (f g : Map) (a z : Scalar)
    (hfa : f.domain a) (hfz : f.domain z) (hga : g.domain a) (hgz : g.domain z)
    (d e : Scalar) (B C T H : Rat) (hT : 0≤T) (hH : 0≤H)
    (hz : Small (sub (f.eval z hfz).val (g.eval z hgz).val) B)
    (ha : Small (sub (f.eval a hfa).val (g.eval a hga).val) C)
    (hd : Small (sub d.val e.val) T) (hza : Small (sub z.val a.val) H) :
    Small (sub (remainder f a hfa d z hfz) (remainder g a hga e z hgz))
      (B+C+2*T*H) := by
  have hmul := Small.mul (sub_valid d.property e.property) (sub_valid z.property a.property)
    hT hH hd hza
  have hs := SeriesLimitLaws.small_sub (SeriesLimitLaws.small_sub hz ha) hmul
  exact Small.congr
    (sub_valid (sub_valid (sub_valid (f.eval z hfz).property (g.eval z hgz).property)
      (sub_valid (f.eval a hfa).property (g.eval a hga).property))
      (mul_valid (sub_valid d.property e.property) (sub_valid z.property a.property)))
    (sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (equiv_symm (remainder_comparison f g a z hfa hfz hga hgz d e)) hs

end ComputableAnalysis.RiemannHilbert.DomainFunctions
