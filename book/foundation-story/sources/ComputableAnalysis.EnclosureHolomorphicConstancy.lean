import ComputableAnalysis.EnclosureHolomorphic
import ComputableAnalysis.ModularForms.DomainLocalEndpointVariationError
import ComputableAnalysis.ModularForms.DomainSegmentBisectionJoin

/-! Whole-segment variation by represented rational bisection, retaining
actual segment domains. No uniform mesh-radius assumption is used. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions ComputableAnalysis.ModularForms

/-- A genuine derivative bound on the represented segment controls its
endpoint difference. Local error radii may vary freely along the segment. -/
theorem segment_variation_error (f : DomainFunctions.Map)
    (df : ∀ a, f.domain a → Scalar)
    (hderiv : ∀ a ha, HasDerivativeAt f a ha (df a ha))
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (B : Rat) (hB : 0≤B)
    (hbound : ∀ t : UnitInterval.Point,
      Small (df (RepresentedAffineSegment.point p q t) (mem t)).val B)
    (eps W : QPos) (hd : Small (AffineSegment.displacement p q).val W.val) :
    Small (sub (f.eval q hq).val (f.eval p hp).val) ((2*B+4*eps.val)*W.val) := by
  let rmem := domainSegment_rational_mem f p q mem
  have good : domainSegmentEndpointGood f p q rmem (2*B+4*eps.val) W.val ⟨0,1⟩ := by
    apply bisection_cover_principle (domainSegmentEndpointGood f p q rmem (2*B+4*eps.val) W.val) ⟨0,1⟩
      (domainSegmentEndpointGood_join f p q rmem (2*B+4*eps.val) W.val)
    intro choice
    have hx := bisectionReal_enclosed (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0
    let t : UnitInterval.Point := ⟨bisectionReal ⟨0,1⟩ choice,
      bisectionReal_valid ⟨0,1⟩ (by decide +kernel) choice,hx.1,hx.2⟩
    let a := RepresentedAffineSegment.point p q t
    let D := (hderiv a (mem t)).delta eps
    let N := RationalMajorant.natRateStage (2*W.val) D
    let J := bisectionInterval ⟨0,1⟩ choice N
    have hw : J.width=((1:Rat)/2)^N := by
      have h := bisectionInterval_width (⟨0,1⟩ : QInterval) choice N
      simpa only [QInterval.width,show (1:Rat)-0=1 by decide +kernel,Rat.one_mul] using h
    have hwpos : 0<J.width := by
      rw [hw]
      exact Rat.pow_pos (by decide +kernel)
    have h2W : 0<2*W.val := Rat.mul_pos (by decide +kernel) W.property
    let H : QPos := ⟨2*W.val*J.width,Rat.mul_pos h2W hwpos⟩
    have hH : H.val≤D.val := by
      have hp := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ N)
        (Rat.le_of_lt h2W)
      have hr := RationalMajorant.natRateStage_spec_of_le (Rat.le_of_lt h2W) D (Nat.le_refl N)
      change 2*W.val*J.width≤D.val
      rw [hw]
      have he : (2*W.val)*(1/((N+1:Nat):Rat))=(2*W.val)/((N+1:Nat):Rat) := by
        rw [Rat.div_def,Rat.div_def,Rat.one_mul]
      rw [he] at hp
      exact Rat.le_trans hp hr
    have ho := bisectionInterval_ordered (⟨0,1⟩ : QInterval) (by decide +kernel) choice N
    have he := bisectionInterval_nested (⟨0,1⟩ : QInterval) (by decide +kernel)
      choice 0 N (Nat.zero_le N)
    have near (u : Rat) (hulo : J.lo≤u) (huhi : u≤J.hi) :
        Small (sub (AffineSegment.point p q u).val a.val) H.val := by
      have hn := bisectionReal_stage_neighborhood (⟨0,1⟩ : QInterval)
        (by decide +kernel) choice N u hulo huhi
      exact representedAffine_rational_neighborhood p q t u
        (Rat.le_trans he.1 hulo) (Rat.le_trans huhi he.2.2) W.val J.width
        (Rat.le_of_lt W.property) (Rat.le_of_lt hwpos) hd hn.1 hn.2
    have hz := near J.hi ho Rat.le_refl
    have hl := near J.lo Rat.le_refl ho
    have hdisp := AffineSegment.difference_bound p q W.val J.lo J.hi hd
      (by change 0≤J.width; exact Rat.le_of_lt hwpos)
    have hhi0 := Rat.le_trans he.1 ho
    have hlo1 := Rat.le_trans ho he.2.2
    have hv := domain_local_endpoint_variation_error f a
      (AffineSegment.point p q J.hi) (AffineSegment.point p q J.lo)
      (df a (mem t)) (mem t)
      (rmem J.hi hhi0 he.2.2) (rmem J.lo he.1 hlo1)
      (hderiv a (mem t)) B (J.width*W.val) hB
      (Rat.mul_nonneg (Rat.le_of_lt hwpos) (Rat.le_of_lt W.property))
      (hbound t) eps H hH hz hl hdisp
    refine ⟨N, ?_⟩
    intro _ _ _
    apply hv.mono
    change 2*B*(J.width*W.val)+2*eps.val*(2*W.val*J.width)≤(2*B+4*eps.val)*W.val*J.width
    grind only
  have hg := good (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hw : (⟨0,1⟩ : QInterval).width=1 := by decide +kernel
  rw [hw,Rat.mul_one] at hg
  exact Small.congr
    (sub_valid (f.eval (AffineSegment.point p q 1) (rmem 1 (by decide +kernel) (by decide +kernel))).property
      (f.eval (AffineSegment.point p q 0) (rmem 0 (by decide +kernel) (by decide +kernel))).property)
    (sub_valid (f.eval q hq).property (f.eval p hp).property)
    (FunctionTheory.sub_congr
      (f.eval_congr _ _ _ hq (AffineSegment.point_one p q))
      (f.eval_congr _ _ _ hp (AffineSegment.point_zero p q))) hg

end ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory

namespace ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions ComputableAnalysis.ModularForms

/-- Endpoint variation controlled by an actual derivative bound, from the bare
covered-enclosure definition. Local radii vary along the entire segment. -/
theorem segment_variation (f : DomainFunctions.Map) (hf : IsEnclosureDifferentiable f)
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (B : Rat) (hB : 0≤B)
    (bound : ∀ t, Small (hf.derivative (RepresentedAffineSegment.point p q t) (mem t)).val B)
    (eps W : QPos) (hd : Small (AffineSegment.displacement p q).val W.val) :
    Small (sub (f.eval q hq).val (f.eval p hp).val) ((2*B+4*eps.val)*W.val) :=
  segment_variation_error f hf.derivative hf.quantitativeAt p q hp hq mem B hB bound eps W hd

/-- Zero derivative on a whole represented segment gives exact endpoint
agreement. There is no derivative-continuity or uniform-radius hypothesis. -/
theorem zero_derivative_segment_constant (f : DomainFunctions.Map) (hf : IsEnclosureDifferentiable f)
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hzero : ∀ t, (hf.derivative (RepresentedAffineSegment.point p q t) (mem t)).val.Equiv zero) :
    (f.eval q hq).val.Equiv (f.eval p hp).val := by
  let W : QPos := ⟨scalarBound (AffineSegment.displacement p q),scalarBound_pos _⟩
  have hz (t : UnitInterval.Point) :
      Small (hf.derivative (RepresentedAffineSegment.point p q t) (mem t)).val 0 :=
    Small.congr (ofQComplex_valid _)
      (hf.derivative (RepresentedAffineSegment.point p q t) (mem t)).property
      (equiv_symm (hzero t)) (Small.zero (by decide +kernel))
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0
    (fun j => (4*W.val)*(RepresentedCauchySum.error j).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks (4*W.val)
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt W.property)))
  intro j
  have h := segment_variation f hf p q hp hq mem 0 (by decide +kernel) hz
    (RepresentedCauchySum.error j) W (scalar_small _)
  have he : (2*(0:Rat)+4*(RepresentedCauchySum.error j).val)*W.val=
      0+(4*W.val)*(RepresentedCauchySum.error j).val := by grind only
  rw [he] at h
  exact h


/-- Remove the arbitrary error allowance from the whole-segment bound. -/
theorem segment_variation_bound (f : DomainFunctions.Map) (hf : IsEnclosureDifferentiable f)
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (B : Rat) (hB : 0≤B)
    (bound : ∀ t, Small (hf.derivative (RepresentedAffineSegment.point p q t) (mem t)).val B)
    (W : QPos) (hd : Small (AffineSegment.displacement p q).val W.val) :
    Small (sub (f.eval q hq).val (f.eval p hp).val) (2*B*W.val) := by
  apply SeriesLimitLaws.small_closed _ (2*B*W.val)
    (fun j => (4*W.val)*(RepresentedCauchySum.error j).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks (4*W.val)
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt W.property)))
  intro j
  have h := segment_variation f hf p q hp hq mem B hB bound (RepresentedCauchySum.error j) W hd
  have he : (2*B+4*(RepresentedCauchySum.error j).val)*W.val=
      2*B*W.val+(4*W.val)*(RepresentedCauchySum.error j).val := by grind only
  rw [he] at h
  exact h

/-- Same actual derivatives and one equal value identify two functions along
any whole segment in their common domain. Internal bisections are hidden. -/
theorem same_derivative_segment_agreement (f g : DomainFunctions.Map)
    (hf : IsEnclosureDifferentiable f) (hg : IsEnclosureDifferentiable g)
    (inside : ∀ z, f.domain z → g.domain z)
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (mem : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (same : ∀ t, hf.derivative (RepresentedAffineSegment.point p q t) (mem t) ≈
      hg.derivative (RepresentedAffineSegment.point p q t) (inside _ (mem t)))
    (seed : f.eval p hp ≈ g.eval p (inside p hp)) :
    f.eval q hq ≈ g.eval q (inside q hq) := by
  let F := sumOn f (negate g) inside
  have H : IsEnclosureDifferentiable F := hf.sumOn hg.negate inside
  have hz (t : UnitInterval.Point) : (H.derivative (RepresentedAffineSegment.point p q t) (mem t)).val.Equiv zero := by
    let z := RepresentedAffineSegment.point p q t
    have hd := (sumDerivative f (negate g) inside z (mem t) _ _ (hf.quantitativeAt z (mem t))
      (negateDerivative g z (inside z (mem t)) _ (hg.quantitativeAt z (inside z (mem t))))).enclosure
    have e := H.derivative_eq hd
    exact equiv_trans (H.derivative z (mem t)).property
      (scalarSum (hf.derivative z (mem t)) (scalarNeg (hg.derivative z (inside z (mem t))))).property
      (ofQComplex_valid _) e
      (equiv_trans
        (scalarSum (hf.derivative z (mem t)) (scalarNeg (hg.derivative z (inside z (mem t))))).property
        (add_valid (hg.derivative z (inside z (mem t))).property (neg_valid (hg.derivative z (inside z (mem t))).property))
        (ofQComplex_valid _)
        (add_equiv (same t) (equiv_refl _ (scalarNeg (hg.derivative z (inside z (mem t)))).property))
        (add_neg_equiv _ (hg.derivative z (inside z (mem t))).property))
  have eq := zero_derivative_segment_constant F H p q hp hq mem hz
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (f.eval p hp).property)
    (hright := (g.eval p (inside p hp)).property) seed
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (F.eval q hq).property)
    (hright := (F.eval p hp).property) eq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (f.eval q hq).property)
    (hright := (g.eval q (inside q hq)).property)
  let FP := ComplexRawQuotient.ofRaw (f.eval p hp).val (f.eval p hp).property
  let GP := ComplexRawQuotient.ofRaw (g.eval p (inside p hp)).val (g.eval p (inside p hp)).property
  let FQ := ComplexRawQuotient.ofRaw (f.eval q hq).val (f.eval q hq).property
  let GQ := ComplexRawQuotient.ofRaw (g.eval q (inside q hq)).val (g.eval q (inside q hq)).property
  change FP=GP at hs
  change FQ + -GQ=FP + -GP at he
  change FQ=GQ
  grind only

end ComputableAnalysis.RiemannHilbert.DomainFunctions.EnclosureTheory
