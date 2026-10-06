import ComputableAnalysis.RiemannHilbert.DomainHolomorphicValueLaws

/-! Uniqueness of the actual complex derivative on an open domain.
Rational displacements and inverse rational scaling compare the supplied
remainders. Shrinking exact error bounds prove represented value equality;
no completed scalar field or analytic uniqueness axiom is used. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory

def realStep (r : QPos) : Scalar := ⟨scaleRat r.val one,scaleRat_valid (r := r.val) (ofQComplex_valid _)⟩

theorem realStep_small (r : QPos) : Small (realStep r).val r.val := by
  have hOne : Small one 1 := ⟨by intro n m; change (-1 : Rat) ≤ 1; decide,
    by intro n m; change (1 : Rat) ≤ 1; decide,
    by intro n m; change (-1 : Rat) ≤ 0; decide,
    by intro n m; change (0 : Rat) ≤ 1; decide⟩
  simpa only [realStep,Rat.mul_one] using LocalODE.small_scale (Rat.le_of_lt r.property) hOne

def rationalShift (a : Scalar) (r : QPos) : Scalar := scalarSum a (realStep r)

theorem rationalShift_difference (a : Scalar) (r : QPos) :
    (sub (rationalShift a r).val a.val).Equiv (realStep r).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (rationalShift a r).property a.property) (hright := (realStep r).property)
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change (A + ComplexRawQuotient.scaleRat r.val 1) + -A = ComplexRawQuotient.scaleRat r.val 1
  grind

theorem rationalShift_small (a : Scalar) (r : QPos) : Small (sub (rationalShift a r).val a.val) r.val :=
  Small.congr (realStep r).property (sub_valid (rationalShift a r).property a.property)
    (equiv_symm (rationalShift_difference a r)) (realStep_small r)

theorem inverse_realStep_scaling (x : Scalar) (r : QPos) :
    (scaleRat (1/r.val) (mul x.val (realStep r).val)).Equiv x.val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := scaleRat_valid (mul_valid x.property (realStep r).property)) (hright := x.property)
  let X := ComplexRawQuotient.ofRaw x.val x.property
  change ComplexRawQuotient.scaleRat (1/r.val) (X * ComplexRawQuotient.scaleRat r.val 1) = X
  rw [ComplexRawQuotient.mul_scaleRat]
  have hOne : X * (1 : ComplexRawQuotient.Value) = X := by grind
  rw [hOne,ComplexRawQuotient.scaleRat_scaleRat,
    Rat.div_mul_cancel (Rat.ne_of_gt r.property),ComplexRawQuotient.scaleRat_one]

theorem derivative_remainder_difference (f : Map) (a : Scalar) (ha : f.domain a) (d e : Scalar)
    (z : Scalar) (hz : f.domain z) :
    (sub (remainder f a ha e z hz) (remainder f a ha d z hz)).Equiv
      (mul (sub d.val e.val) (sub z.val a.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (hright := mul_valid (sub_valid d.property e.property) (sub_valid z.property a.property))
  let X := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let Y := ComplexRawQuotient.ofRaw (f.eval a ha).val (f.eval a ha).property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let E := ComplexRawQuotient.ofRaw e.val e.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  change ((X-Y)-E*(Z-A))-((X-Y)-D*(Z-A)) = (D-E)*(Z-A)
  grind

/-- A finite quantitative comparison of two actual derivative witnesses.
The displacement is computed from their radii and the open-domain radius. -/
theorem HasDerivativeAt.difference_small {f : Map} {a : Scalar} {ha : f.domain a} {d e : Scalar}
    (h : HasDerivativeAt f a ha d) (k : HasDerivativeAt f a ha e) (hOpen : OpenDomain f)
    (eps : QPos) : Small (sub d.val e.val) (2*eps.val) := by
  let r := minRadius (hOpen.radius a ha) (minRadius (h.delta eps) (k.delta eps))
  let z := rationalShift a r
  have hza := rationalShift_small a r
  have hz := hOpen.inside a ha z (hza.mono (minRadius_left _ _))
  have hrh : r.val ≤ (h.delta eps).val := Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)
  have hrk : r.val ≤ (k.delta eps).val := Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)
  have hb := SeriesLimitLaws.small_sub (k.estimate eps r z hz hrk hza) (h.estimate eps r z hz hrh hza)
  have heq := equiv_trans (sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (mul_valid (sub_valid d.property e.property) (sub_valid z.property a.property))
    (mul_valid (sub_valid d.property e.property) (realStep r).property)
    (derivative_remainder_difference f a ha d e z hz)
    (mul_equiv (sub_valid d.property e.property) (sub_valid d.property e.property)
      (sub_valid z.property a.property) (realStep r).property
      (equiv_refl _ (sub_valid d.property e.property)) (rationalShift_difference a r))
  have hs := Small.congr (sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (mul_valid (sub_valid d.property e.property) (realStep r).property) heq hb
  have hi := LocalODE.small_scale (c := 1/r.val)
    (by simpa only [Rat.div_def,Rat.one_mul] using Rat.le_of_lt ((Rat.inv_pos).2 r.property)) hs
  have hcancel := Rat.div_mul_cancel (Rat.ne_of_gt r.property) (a := (1 : Rat))
  have hnum : (1/r.val)*(eps.val*r.val+eps.val*r.val)=2*eps.val := by grind
  rw [hnum] at hi
  exact Small.congr (scaleRat_valid (mul_valid (sub_valid d.property e.property) (realStep r).property))
    (sub_valid d.property e.property) (inverse_realStep_scaling ⟨sub d.val e.val,sub_valid d.property e.property⟩ r) hi

/-- The complex derivative value is unique at every represented point of
the supplied open domain, including irrational points and derivatives. -/
theorem HasDerivativeAt.unique {f : Map} {a : Scalar} {ha : f.domain a} {d e : Scalar}
    (h : HasDerivativeAt f a ha d) (k : HasDerivativeAt f a ha e) (hOpen : OpenDomain f) : d ≈ e := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed (sub d.val e.val) 0
    (fun n => 2*(RepresentedCauchySum.error n).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks 2 (by decide +kernel))
  intro n
  simpa only [Rat.zero_add] using h.difference_small k hOpen (RepresentedCauchySum.error n)

theorem Holomorphic.derivative_unique {f : Map} (hf hg : Holomorphic f) (a : Scalar) (ha : f.domain a) :
    hf.derivative a ha ≈ hg.derivative a ha :=
  (hf.atPoint a ha).unique (hg.atPoint a ha) hf.openDomain

end ComputableAnalysis.RiemannHilbert.DomainFunctions
