import ComputableAnalysis.RiemannHilbert.UnitIntervalApproximation
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.AffineSegments

/-! Affine paths evaluated at every represented real unit parameter.
Their entire images stay in any centered disk containing both endpoints;
the proof passes uniform rational bounds through explicit shrinking errors. -/
namespace ComputableAnalysis.RiemannHilbert.RepresentedAffineSegment
open ComplexRaw FunctionTheory DomainFunctions LocalODE

def function (p q : Scalar) : DomainFunctions.Map := DomainFunctions.affine p (Centered.offset p q)
def point (p q : Scalar) (t : UnitInterval.Point) : Scalar := (function p q).eval (UnitInterval.scalar t) trivial

theorem point_congr {p p' q q' : Scalar} {s t : UnitInterval.Point}
    (hp : p ≈ p') (hq : q ≈ q') (hst : s ≈ t) : point p q s ≈ point p' q' t :=
  add_equiv hp (mul_equiv (Centered.offset p q).property (Centered.offset p' q').property
    (UnitInterval.scalar s).property (UnitInterval.scalar t).property
    (Centered.offset_congr p p' q q' hp hq) (UnitInterval.scalar_congr hst))

def continuousData (p q : Scalar) : UnitInterval.ScalarContinuousData (point p q) :=
  UnitInterval.ofDomainContinuous (function p q)
    (DomainFunctions.affine_holomorphic p (Centered.offset p q)).continuous (fun _ => trivial)

theorem continuous (p q : Scalar) : UnitInterval.ScalarContinuous (point p q) := (continuousData p q).continuous

private theorem rational_as_scale (r : Rat) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    (UnitInterval.scalar (UnitInterval.rational r h0 h1)).val.Equiv (scaleRat r (ofQComplex QComplex.one)) := by
  intro k
  apply (compareAt_overlap_iff _ _ k k).2
  simp [UnitInterval.scalar,UnitInterval.rational,ofRealRaw,RealRaw.ofRat,
    scaleRat,ofQComplex,QBox.scaleRat,QBox.Overlaps,QComplex.one,QComplex.le_def,h0]

theorem rational_agreement (p q : Scalar) (r : Rat) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    point p q (UnitInterval.rational r h0 h1) ≈ AffineSegment.point p q r := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (point p q (UnitInterval.rational r h0 h1)).property)
    (hright := (AffineSegment.point p q r).property)
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (UnitInterval.scalar (UnitInterval.rational r h0 h1)).property)
    (hright := scaleRat_valid (ofQComplex_valid _)) (rational_as_scale r h0 h1)
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let T := ComplexRawQuotient.ofRaw (UnitInterval.scalar (UnitInterval.rational r h0 h1)).val
    (UnitInterval.scalar (UnitInterval.rational r h0 h1)).property
  change T=ComplexRawQuotient.scaleRat r 1 at ht
  change P+(Q-P)*T=P+ComplexRawQuotient.scaleRat r (Q-P)
  have hmul : (Q-P)*1=Q-P := by grind only
  rw [ht,ComplexRawQuotient.mul_scaleRat,hmul]

theorem point_zero (p q : Scalar) : point p q UnitInterval.zero ≈ p :=
  Setoid.trans (rational_agreement p q 0 _ _) (AffineSegment.point_zero p q)

theorem point_one (p q : Scalar) : point p q UnitInterval.one ≈ q :=
  Setoid.trans (rational_agreement p q 1 _ _) (AffineSegment.point_one p q)

theorem point_self (p : Scalar) (t : UnitInterval.Point) : point p p t ≈ p := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (point p p t).property) (hright := p.property)
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let T := ComplexRawQuotient.ofRaw (UnitInterval.scalar t).val (UnitInterval.scalar t).property
  change P+(P-P)*T=P
  grind only

theorem difference (p q : Scalar) (s t : UnitInterval.Point) :
    (sub (point p q t).val (point p q s).val).Equiv
      (mul (Centered.offset p q).val (sub (UnitInterval.scalar t).val (UnitInterval.scalar s).val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (point p q t).property (point p q s).property)
    (hright := mul_valid (Centered.offset p q).property
      (sub_valid (UnitInterval.scalar t).property (UnitInterval.scalar s).property))
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let S := ComplexRawQuotient.ofRaw (UnitInterval.scalar s).val (UnitInterval.scalar s).property
  let T := ComplexRawQuotient.ofRaw (UnitInterval.scalar t).val (UnitInterval.scalar t).property
  change (P+(Q-P)*T)-(P+(Q-P)*S)=(Q-P)*(T-S)
  grind only

theorem difference_bound (p q : Scalar) (s t : UnitInterval.Point) (W H : Rat)
    (hW : 0 ≤ W) (hH : 0 ≤ H) (hd : Small (Centered.offset p q).val W)
    (hst : Small (sub (UnitInterval.scalar t).val (UnitInterval.scalar s).val) H) :
    Small (sub (point p q t).val (point p q s).val) (2*W*H) :=
  Small.congr (mul_valid (Centered.offset p q).property
    (sub_valid (UnitInterval.scalar t).property (UnitInterval.scalar s).property))
    (sub_valid (point p q t).property (point p q s).property) (equiv_symm (difference p q s t))
    (Small.mul (Centered.offset p q).property
      (sub_valid (UnitInterval.scalar t).property (UnitInterval.scalar s).property) hW hH hd hst)

theorem offset_bound (c p q : Scalar) (t : UnitInterval.Point) (r : Rat)
    (hp : Small (Centered.offset c p).val r) (hq : Small (Centered.offset c q).val r) :
    Small (Centered.offset c (point p q t)).val r := by
  let W := scalarBound (Centered.offset p q)
  let eps := RepresentedCauchySum.error
  let approx := fun N => UnitInterval.approximatePoint t (eps N)
  let a := fun N => (Centered.offset c (point p q (approx N))).val
  apply SeriesLimitLaws.small_of_prefix_bound (Centered.offset c (point p q t)).val
    (Centered.offset c (point p q t)).property a (fun N => (Centered.offset c (point p q (approx N))).property)
    r (fun N => (2*W)*(eps N).val)
    (SeriesLimitLaws.shrinks_scale (fun N => (eps N).val) RepresentedCauchySum.error_shrinks (2*W)
      (by have h := scalarBound_pos (Centered.offset p q); dsimp [W]; grind only))
  · intro N
    have hd := difference_bound p q (approx N) t W (eps N).val
      (Rat.le_of_lt (scalarBound_pos _)) (Rat.le_of_lt (eps N).property)
      (scalar_small _) (UnitInterval.approximatePoint_error t (eps N))
    exact Small.congr (sub_valid (point p q t).property (point p q (approx N)).property)
      (sub_valid (Centered.offset c (point p q t)).property (Centered.offset c (point p q (approx N))).property)
      (equiv_symm (Centered.offset_difference c (point p q (approx N)) (point p q t))) hd
  · intro N
    let v := UnitInterval.approximation t (eps N)
    have hv := UnitInterval.approximation_bounds t (eps N)
    have h1 : 0 ≤ 1-v := by dsimp [v]; grind only
    have hb := small_add (small_scale h1 hp) (small_scale hv.1 hq)
    have he : (1-v)*r+v*r=r := by grind only
    rw [he] at hb
    have hb' := Small.congr
      (add_valid (scaleRat_valid (Centered.offset c p).property) (scaleRat_valid (Centered.offset c q).property))
      (Centered.offset c (AffineSegment.point p q v)).property (equiv_symm (AffineSegment.offset_barycentric c p q v)) hb
    exact Small.congr (Centered.offset c (AffineSegment.point p q v)).property
      (Centered.offset c (point p q (approx N))).property
      (Centered.offset_congr c c _ _ (equiv_refl _ c.property)
        (equiv_symm (rational_agreement p q v hv.1 hv.2))) hb'

theorem mem (c p q : Scalar) (R : Rat) (hp : Centered.domain c R p) (hq : Centered.domain c R q)
    (t : UnitInterval.Point) : Centered.domain c R (point p q t) := by
  obtain ⟨rp,hrp,hrpR,hpr⟩ := hp
  obtain ⟨rq,hrq,hrqR,hqr⟩ := hq
  let r := max rp rq
  have hr : 0 ≤ r := by dsimp [r]; grind
  have hrR : r < R := by dsimp [r]; grind
  exact ⟨r,hr,hrR,offset_bound c p q t r
    (hpr.mono (by dsimp [r]; grind)) (hqr.mono (by dsimp [r]; grind))⟩

theorem reverse (p q : Scalar) (t : UnitInterval.Point) :
    point p q (UnitInterval.reverse t) ≈ point q p t := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (point p q (UnitInterval.reverse t)).property) (hright := (point q p t).property)
  have ht := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (UnitInterval.scalar (UnitInterval.reverse t)).property)
    (hright := sub_valid (ofQComplex_valid _) (UnitInterval.scalar t).property) (UnitInterval.scalar_reverse t)
  let P := ComplexRawQuotient.ofRaw p.val p.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  let T := ComplexRawQuotient.ofRaw (UnitInterval.scalar t).val (UnitInterval.scalar t).property
  let RT := ComplexRawQuotient.ofRaw (UnitInterval.scalar (UnitInterval.reverse t)).val
    (UnitInterval.scalar (UnitInterval.reverse t)).property
  change RT=1-T at ht
  change P+(Q-P)*RT=Q+(P-Q)*T
  grind only

end ComputableAnalysis.RiemannHilbert.RepresentedAffineSegment
