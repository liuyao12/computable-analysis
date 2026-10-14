import ComputableAnalysis.ParametrizedComplexContinuity
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.ContourSegmentBisection
import ComputableAnalysis.SecantBoxBounds

/-!
# Holomorphicity by covered rational enclosures

Holomorphicity uses covered shrinking rational boxes for every nearby two-point
complex secant. The actual quotient is computed by a terminating reciprocal
algorithm. A balanced separation bound proves equivalence with division-free
strict first-order estimates. Derivative continuity is derived, and the previous
continuous-derivative contract is proved equivalent. The weaker anchored
pointwise derivative specification is retained unchanged.
-/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw RawLimit

/-- Recover an unnormalized exact bound; scaling by a known positive rational
requires neither a complex reciprocal nor a choice of norm representation. -/
theorem denormalized_small {z : ComplexRaw} (hz : z.Valid) (H : QPos) (eps : Rat)
    (h : Small (scaleRat (1/H.val) z) eps) : Small z (eps*H.val) := by
  have hs := RiemannHilbert.LocalODE.small_scale (Rat.le_of_lt H.property) h
  have he := scaleRat_scaleRat_equiv H.val (1/H.val) z hz
  have hc : H.val*(1/H.val)=1 := by
    rw [Rat.div_def,Rat.one_mul,Rat.mul_inv_cancel _ (Rat.ne_of_gt H.property)]
  rw [hc] at he
  have hOne : (scaleRat 1 z).Equiv z := scaleRat_one_equiv z hz
  exact Small.congr (scaleRat_valid (scaleRat_valid hz)) hz
    (equiv_trans (scaleRat_valid (scaleRat_valid hz)) (scaleRat_valid hz) hz he hOne)
    (by simpa only [Rat.mul_comm] using hs)

/-- A zero-centered coordinate enclosure is exactly a `Small` bound. -/
theorem small_of_zero_enclosures {z : ComplexRaw} {eps : Rat}
    (hr : InInterval z.realPart (QInterval.expand ((RealRaw.ofRat 0).compute 0) eps))
    (hi : InInterval z.imagPart (QInterval.expand ((RealRaw.ofRat 0).compute 0) eps)) :
    Small z eps := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    have b := hr.1 i j
    change 0-eps ≤ (z.compute j).hi.re at b
    change -eps ≤ (z.compute j).hi.re
    grind only
  · intro i j; simpa only [RealRaw.ofRat, QInterval.expand, Rat.zero_add] using hr.2 i j
  · intro i j
    have b := hi.1 i j
    change 0-eps ≤ (z.compute j).hi.im at b
    change -eps ≤ (z.compute j).hi.im
    grind only
  · intro i j; simpa only [RealRaw.ofRat, QInterval.expand, Rat.zero_add] using hi.2 i j

end ComputableAnalysis.FunctionTheory

namespace ComputableAnalysis.RawLimit
/-- Refining the covered observation set retains the same valid diagonal. -/
theorem HasEnclosureValue.mono {tests narrower : Nat → RealRaw → Prop} {c : RealRaw}
    (h : HasEnclosureValue tests c) (sub : ∀ n y, narrower n y → tests n y) :
    HasEnclosureValue narrower c := by
  obtain ⟨hc,Q,n,m,hn,hm,hv,he,cover⟩ := h
  exact ⟨hc,Q,n,m,hn,hm,hv,he,fun k y hy => cover k y (sub _ y hy)⟩
end ComputableAnalysis.RawLimit

namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory RawLimit
set_option maxHeartbeats 2000000

/-- All normalized errors on a whole neighborhood, in one output coordinate. -/
def remainderObservations (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (radius : Nat → QPos) (coordinate : ComplexRaw → RealRaw) (n : Nat) (y : RealRaw) : Prop :=
  ∃ H : QPos, ∃ z hz, H.val ≤ (radius n).val ∧ Small (sub z.val a.val) H.val ∧
    y = coordinate (scaleRat (1/H.val) (remainder f a ha d z hz))

/-- Two-index rational enclosure semantics for a complex derivative. Radius
nesting is harmless finite-minimum normalization; no precision modulus or
continuity of the derivative is demanded of the caller. -/
def HasEnclosureDerivativeAt (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar) : Prop :=
  ∃ radius : Nat → QPos,
    (∀ i j, i ≤ j → (radius j).val ≤ (radius i).val) ∧
    (∀ n, (radius n).val ≤ allowance n) ∧
    HasEnclosureValue (remainderObservations f a ha d radius realPart) (RealRaw.ofRat 0) ∧
    HasEnclosureValue (remainderObservations f a ha d radius imagPart) (RealRaw.ofRat 0)

theorem remainderObservations_antitone (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar)
    (radius : Nat → QPos) (anti : ∀ i j, i ≤ j → (radius j).val ≤ (radius i).val)
    (coordinate : ComplexRaw → RealRaw) :
    ∀ i j, i ≤ j → ∀ y, remainderObservations f a ha d radius coordinate j y →
      remainderObservations f a ha d radius coordinate i y := by
  rintro i j hij y ⟨H,z,hz,hH,near,hy⟩
  exact ⟨H,z,hz,Rat.le_trans hH (anti i j hij),near,hy⟩

theorem HasDerivativeAt.enclosure {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasDerivativeAt f a ha d) : HasEnclosureDerivativeAt f a ha d := by
  let r := runningRadius (fun n => h.delta ⟨allowance n,allowance_pos n⟩)
  let t := fun n => minRadius (r n) ⟨allowance n,allowance_pos n⟩
  have anti : ∀ i j, i ≤ j → (t j).val ≤ (t i).val := by
    intro i j hij
    have hr := runningRadius_antitone (fun n => h.delta ⟨allowance n,allowance_pos n⟩) i j hij
    have he := allowance_antitone hij
    dsimp [t,minRadius]
    grind
  have subtests (coordinate : ComplexRaw → RealRaw) : ∀ n y,
      remainderObservations f a ha d t coordinate n y →
      remainderObservations f a ha d r coordinate n y := by
    rintro n y ⟨H,z,hz,hH,near,hy⟩
    exact ⟨H,z,hz,Rat.le_trans hH (minRadius_left _ _),near,hy⟩
  exact ⟨t,anti,fun _ => minRadius_right _ _,
    h.hasRemainderCoordinates.1.mono (subtests realPart),
    h.hasRemainderCoordinates.2.mono (subtests imagPart)⟩

/-- Covered cofinal diagonals recover a positive error radius. This is logical
existence; supplied quantitative witnesses retain their executable moduli. -/
theorem HasEnclosureDerivativeAt.quantitative {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasEnclosureDerivativeAt f a ha d) : Nonempty (HasDerivativeAt f a ha d) := by
  classical
  obtain ⟨r,anti,_shrinks,hr,hi⟩ := h
  have R := (enclosureValue_iff (remainderObservations_antitone f a ha d r anti realPart)).mp hr
  have I := (enclosureValue_iff (remainderObservations_antitone f a ha d r anti imagPart)).mp hi
  let nr := fun eps : QPos => Classical.choose (R.2 0 eps)
  let ni := fun eps : QPos => Classical.choose (I.2 0 eps)
  refine ⟨{ delta := fun eps => r (max (nr eps) (ni eps)), estimate := ?_ }⟩
  intro eps H z hz hH near
  have br := Classical.choose_spec (R.2 0 eps) _
    (show remainderObservations f a ha d r realPart (nr eps)
      (scaleRat (1/H.val) (remainder f a ha d z hz)).realPart from
      ⟨H,z,hz,Rat.le_trans hH (anti _ _ (Nat.le_max_left _ _)),near,rfl⟩)
  have bi := Classical.choose_spec (I.2 0 eps) _
    (show remainderObservations f a ha d r imagPart (ni eps)
      (scaleRat (1/H.val) (remainder f a ha d z hz)).imagPart from
      ⟨H,z,hz,Rat.le_trans hH (anti _ _ (Nat.le_max_right _ _)),near,rfl⟩)
  exact denormalized_small (remainder_valid f a ha d z hz) H eps.val
    (small_of_zero_enclosures br bi)

theorem enclosureDerivative_iff {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar} :
    HasEnclosureDerivativeAt f a ha d ↔ Nonempty (HasDerivativeAt f a ha d) :=
  ⟨HasEnclosureDerivativeAt.quantitative,fun ⟨h⟩ => h.enclosure⟩

theorem HasEnclosureDerivativeAt.unique {f : Map} {a : Scalar} {ha : f.domain a} {d e : Scalar}
    (h : HasEnclosureDerivativeAt f a ha d) (k : HasEnclosureDerivativeAt f a ha e)
    (o : OpenDomain f) : d ≈ e := by
  obtain ⟨h⟩ := h.quantitative
  obtain ⟨k⟩ := k.quantitative
  exact h.unique k o

theorem HasEnclosureDerivativeAt.congrDerivative {f : Map} {a : Scalar} {ha : f.domain a} {d e : Scalar}
    (h : HasEnclosureDerivativeAt f a ha d) (he : d ≈ e) : HasEnclosureDerivativeAt f a ha e := by
  obtain ⟨h⟩ := h.quantitative
  exact (h.congrDerivative he).enclosure

theorem HasEnclosureDerivativeAt.congrPoint {f : Map} {a b : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasEnclosureDerivativeAt f a ha d) (hb : f.domain b) (he : a ≈ b) :
    HasEnclosureDerivativeAt f b hb d := by
  obtain ⟨h⟩ := h.quantitative
  exact (h.congrPoint hb he).enclosure

/-- The legacy raw-map derivative has precisely the same enclosure meaning
on valid represented inputs; no evaluator or domain is replaced. -/
theorem rawDerivative_iff (f : FunctionTheory.Map) (a d : ComplexRaw)
    (ha : a.Valid) (hfa : f.domain a) (hd : d.Valid) :
    HasEnclosureDerivativeAt (ofCertified (CertifiedFunctions.ofRawMap f))
      ⟨a,ha⟩ hfa ⟨d,hd⟩ ↔ Nonempty (FunctionTheory.HasDerivativeAt f a d) := by
  constructor
  · intro h
    obtain ⟨k⟩ := h.quantitative
    exact ⟨{ point_valid := ha
             point_mem := hfa
             derivative_valid := hd
             delta := k.delta
             estimate := fun eps H z hz hfz hH near => k.estimate eps H ⟨z,hz⟩ hfz hH near }⟩
  · rintro ⟨h⟩
    have k : HasDerivativeAt (ofCertified (CertifiedFunctions.ofRawMap f)) ⟨a,ha⟩ hfa ⟨d,hd⟩ := {
      delta := h.delta
      estimate := fun eps H z hz hH near => h.estimate eps H z.val z.property hz hH near }
    exact k.enclosure

/-- Pointwise complex differentiability throughout an open domain. Radius
and diagonal choices are hidden beneath this proposition. This weaker property
is retained for laws that do not require continuity of the derivative. -/
def IsEnclosureDifferentiable (f : Map) : Prop :=
  Nonempty (OpenDomain f) ∧ ∀ a (ha : f.domain a), ∃ d, HasEnclosureDerivativeAt f a ha d

theorem Holomorphic.enclosureDifferentiable {f : Map} (h : Holomorphic f) : IsEnclosureDifferentiable f :=
  ⟨⟨h.openDomain⟩,fun a ha => ⟨h.derivative a ha,(h.atPoint a ha).enclosure⟩⟩

/-- A canonical derivative value, independent (up to equivalence) of all
radius, enclosure, and represented-name choices. Choice here is logical,
not an executable derivative constructor. -/
noncomputable def IsEnclosureDifferentiable.derivative {f : Map} (h : IsEnclosureDifferentiable f)
    (a : Scalar) (ha : f.domain a) : Scalar := Classical.choose (h.2 a ha)

theorem IsEnclosureDifferentiable.atPoint {f : Map} (h : IsEnclosureDifferentiable f)
    (a : Scalar) (ha : f.domain a) : HasEnclosureDerivativeAt f a ha (h.derivative a ha) :=
  Classical.choose_spec (h.2 a ha)

noncomputable def IsEnclosureDifferentiable.quantitativeAt {f : Map} (h : IsEnclosureDifferentiable f)
    (a : Scalar) (ha : f.domain a) : HasDerivativeAt f a ha (h.derivative a ha) :=
  Classical.choice (h.atPoint a ha).quantitative

noncomputable def IsEnclosureDifferentiable.openDomain {f : Map} (h : IsEnclosureDifferentiable f) : OpenDomain f :=
  Classical.choice h.1

/-- Holomorphicity implies continuity of values, without derivative continuity. -/
noncomputable def IsEnclosureDifferentiable.continuous {f : Map} (h : IsEnclosureDifferentiable f) :
    ContinuousOn f.domain f.eval := continuousOn_of_derivative f h.derivative h.quantitativeAt

theorem IsEnclosureDifferentiable.derivative_congr {f : Map} (h : IsEnclosureDifferentiable f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) :
    h.derivative a ha ≈ h.derivative b hb :=
  ((h.atPoint a ha).congrPoint hb he).unique (h.atPoint b hb) h.openDomain

/-- Two holomorphicity witnesses compute the same derivative value. -/
theorem IsEnclosureDifferentiable.derivative_unique {f : Map} (h k : IsEnclosureDifferentiable f)
    (a : Scalar) (ha : f.domain a) : h.derivative a ha ≈ k.derivative a ha :=
  (h.atPoint a ha).unique (k.atPoint a ha) h.openDomain

/-- The chain rule, including openness of the actual composition domain. -/
theorem IsEnclosureDifferentiable.compose {f g : Map} (hf : IsEnclosureDifferentiable f)
    (hg : IsEnclosureDifferentiable g) : IsEnclosureDifferentiable (compose f g) := by
  refine ⟨⟨composeOpen f g hf.openDomain hg.openDomain hg.continuous⟩,?_⟩
  intro a ha
  exact ⟨scalarProduct (hf.derivative (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha))
    (hg.derivative a (compose_inner_mem ha)),
    (composeDerivative f g a ha _ _
      (hf.quantitativeAt _ (compose_outer_mem ha)) (hg.quantitativeAt a (compose_inner_mem ha))).enclosure⟩

theorem IsEnclosureDifferentiable.sumOn {f g : Map} (hf : IsEnclosureDifferentiable f)
    (hg : IsEnclosureDifferentiable g) (inside : ∀ z, f.domain z → g.domain z) :
    IsEnclosureDifferentiable (sumOn f g inside) := by
  refine ⟨⟨⟨hf.openDomain.radius,hf.openDomain.inside⟩⟩,?_⟩
  intro a ha
  exact ⟨scalarSum (hf.derivative a ha) (hg.derivative a (inside a ha)),
    (sumDerivative f g inside a ha _ _ (hf.quantitativeAt a ha) (hg.quantitativeAt a (inside a ha))).enclosure⟩

theorem IsEnclosureDifferentiable.productOn {f g : Map} (hf : IsEnclosureDifferentiable f)
    (hg : IsEnclosureDifferentiable g) (inside : ∀ z, f.domain z → g.domain z) :
    IsEnclosureDifferentiable (productOn f g inside) := by
  refine ⟨⟨⟨hf.openDomain.radius,hf.openDomain.inside⟩⟩,?_⟩
  intro a ha
  exact ⟨productSlope (f.eval a ha) (g.eval a (inside a ha))
    (hf.derivative a ha) (hg.derivative a (inside a ha)),
    (productDerivative f g inside a ha _ _ (hf.quantitativeAt a ha) (hg.quantitativeAt a (inside a ha))).enclosure⟩


/-- The chosen derivative of the composition equals the chain-rule value;
no chosen modulus or diagonal appears in the exact identity. -/
theorem IsEnclosureDifferentiable.compose_derivative {f g : Map}
    (hf : IsEnclosureDifferentiable f) (hg : IsEnclosureDifferentiable g)
    (a : Scalar) (ha : (DomainFunctions.compose f g).domain a) :
    (hf.compose hg).derivative a ha ≈
      scalarProduct (hf.derivative (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha))
        (hg.derivative a (compose_inner_mem ha)) :=
  ((hf.compose hg).atPoint a ha).unique
    (composeDerivative f g a ha _ _ (hf.quantitativeAt _ (compose_outer_mem ha))
      (hg.quantitativeAt a (compose_inner_mem ha))).enclosure (hf.compose hg).openDomain

/-- Exact product rule for arbitrary represented coefficients and inputs. -/
theorem IsEnclosureDifferentiable.product_derivative {f g : Map}
    (hf : IsEnclosureDifferentiable f) (hg : IsEnclosureDifferentiable g)
    (inside : ∀ z, f.domain z → g.domain z) (a : Scalar) (ha : f.domain a) :
    (hf.productOn hg inside).derivative a ha ≈
      productSlope (f.eval a ha) (g.eval a (inside a ha))
        (hf.derivative a ha) (hg.derivative a (inside a ha)) :=
  ((hf.productOn hg inside).atPoint a ha).unique
    (productDerivative f g inside a ha _ _ (hf.quantitativeAt a ha)
      (hg.quantitativeAt a (inside a ha))).enclosure (hf.productOn hg inside).openDomain


/-- Any justified pointwise derivative agrees with the semantic derivative. -/
theorem IsEnclosureDifferentiable.derivative_eq {f : Map} (h : IsEnclosureDifferentiable f)
    {a : Scalar} {ha : f.domain a} {d : Scalar} (k : HasEnclosureDerivativeAt f a ha d) :
    h.derivative a ha ≈ d := (h.atPoint a ha).unique k h.openDomain

theorem IsEnclosureDifferentiable.negate {f : Map} (h : IsEnclosureDifferentiable f) :
    IsEnclosureDifferentiable (DomainFunctions.negate f) := by
  refine ⟨⟨⟨h.openDomain.radius,h.openDomain.inside⟩⟩,?_⟩
  intro a ha
  exact ⟨scalarNeg (h.derivative a ha),(negateDerivative f a ha _ (h.quantitativeAt a ha)).enclosure⟩

/-- A two-point first-order estimate: the error is scaled by the separation
of the two points, not by their distance from the center. -/
structure HasStrictDerivativeAt (f : Map) (a : Scalar) (ha : f.domain a) (d : Scalar) where
  delta : QPos → QPos
  estimate : ∀ (eps H : QPos) (z : Scalar) (hz : f.domain z) (w : Scalar) (hw : f.domain w),
    Small (sub z.val a.val) (delta eps).val →
    Small (sub w.val a.val) (delta eps).val →
    Small (sub z.val w.val) H.val →
    Small (remainder f w hw d z hz) (eps.val*H.val)

/-- All two-point normalized errors in a neighborhood, including every
represented direction and every positive rational separation bound. -/
def secantErrorObservations (f : Map) (a d : Scalar) (radius : Nat → QPos)
    (coordinate : ComplexRaw → RealRaw) (n : Nat) (y : RealRaw) : Prop :=
  ∃ H : QPos, ∃ z hz w hw,
    Small (sub z.val a.val) (radius n).val ∧
    Small (sub w.val a.val) (radius n).val ∧ Small (sub z.val w.val) H.val ∧
    y = coordinate (scaleRat (1/H.val) (remainder f w hw d z hz))

/-- Division-free shrinking secant boxes. Both coordinates of every two-point
normalized error are covered by valid cofinal rational interval diagonals at zero.
The positive rational separation bound avoids division by an uncertain input. -/
def HasTwoPointErrorBoxes (f : Map) (a : Scalar) (_ha : f.domain a) (d : Scalar) : Prop :=
  ∃ radius : Nat → QPos,
    (∀ i j, i ≤ j → (radius j).val ≤ (radius i).val) ∧
    (∀ n, (radius n).val ≤ allowance n) ∧
    HasEnclosureValue (secantErrorObservations f a d radius realPart) (RealRaw.ofRat 0) ∧
    HasEnclosureValue (secantErrorObservations f a d radius imagPart) (RealRaw.ofRat 0)

theorem secantErrorObservations_antitone (f : Map) (a d : Scalar) (radius : Nat → QPos)
    (anti : ∀ i j, i ≤ j → (radius j).val ≤ (radius i).val)
    (coordinate : ComplexRaw → RealRaw) :
    ∀ i j, i ≤ j → ∀ y, secantErrorObservations f a d radius coordinate j y →
      secantErrorObservations f a d radius coordinate i y := by
  rintro i j hij y ⟨H,z,hz,w,hw,hznear,hwnear,step,hy⟩
  exact ⟨H,z,hz,w,hw,hznear.mono (anti i j hij),hwnear.mono (anti i j hij),step,hy⟩

theorem HasStrictDerivativeAt.errorBoxes {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasStrictDerivativeAt f a ha d) : HasTwoPointErrorBoxes f a ha d := by
  let r := runningRadius (fun n => minRadius (h.delta ⟨allowance n,allowance_pos n⟩)
    ⟨allowance n,allowance_pos n⟩)
  have v := RealRaw.ofRat_valid 0
  have covered (k : Nat) (H : QPos) (z : Scalar) (hz : f.domain z) (w : Scalar) (hw : f.domain w)
      (hnz : Small (sub z.val a.val) (r k).val)
      (hnw : Small (sub w.val a.val) (r k).val) (step : Small (sub z.val w.val) H.val) :=
    normalized_small H (allowance k) (h.estimate ⟨allowance k,allowance_pos k⟩ H z hz w hw
      (hnz.mono (Rat.le_trans (runningRadius_le _ k) (minRadius_left _ _)))
      (hnw.mono (Rat.le_trans (runningRadius_le _ k) (minRadius_left _ _))) step)
  refine ⟨r,runningRadius_antitone _,fun n => Rat.le_trans (runningRadius_le _ n) (minRadius_right _ _),?_,?_⟩
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,w,hw,hnz,hnw,step,rfl⟩
    exact (small_zero_enclosures (covered k H z hz w hw hnz hnw step) k).1
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨H,z,hz,w,hw,hnz,hnw,step,rfl⟩
    exact (small_zero_enclosures (covered k H z hz w hw hnz hnw step) k).2

theorem HasTwoPointErrorBoxes.quantitative {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasTwoPointErrorBoxes f a ha d) : Nonempty (HasStrictDerivativeAt f a ha d) := by
  classical
  obtain ⟨r,anti,_shrinks,hr,hi⟩ := h
  have R := (enclosureValue_iff (secantErrorObservations_antitone f a d r anti realPart)).mp hr
  have I := (enclosureValue_iff (secantErrorObservations_antitone f a d r anti imagPart)).mp hi
  let nr := fun eps : QPos => Classical.choose (R.2 0 eps)
  let ni := fun eps : QPos => Classical.choose (I.2 0 eps)
  refine ⟨{ delta := fun eps => r (max (nr eps) (ni eps)), estimate := ?_ }⟩
  intro eps H z hz w hw hnz hnw step
  have br := Classical.choose_spec (R.2 0 eps) _
    (show secantErrorObservations f a d r realPart (nr eps)
      (scaleRat (1/H.val) (remainder f w hw d z hz)).realPart from
      ⟨H,z,hz,w,hw,hnz.mono (anti _ _ (Nat.le_max_left _ _)),
        hnw.mono (anti _ _ (Nat.le_max_left _ _)),step,rfl⟩)
  have bi := Classical.choose_spec (I.2 0 eps) _
    (show secantErrorObservations f a d r imagPart (ni eps)
      (scaleRat (1/H.val) (remainder f w hw d z hz)).imagPart from
      ⟨H,z,hz,w,hw,hnz.mono (anti _ _ (Nat.le_max_right _ _)),
        hnw.mono (anti _ _ (Nat.le_max_right _ _)),step,rfl⟩)
  exact denormalized_small (remainder_valid f w hw d z hz) H eps.val
    (small_of_zero_enclosures br bi)

theorem twoPointErrorBoxes_iff {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar} :
    HasTwoPointErrorBoxes f a ha d ↔ Nonempty (HasStrictDerivativeAt f a ha d) :=
  ⟨HasTwoPointErrorBoxes.quantitative,fun ⟨h⟩ => h.errorBoxes⟩

theorem point_self_small (a : Scalar) (r : Rat) (hr : 0≤r) : Small (sub a.val a.val) r :=
  Small.congr (ofQComplex_valid _) (sub_valid a.property a.property)
    (equiv_symm (add_neg_equiv a.val a.property)) (Small.zero hr)

def HasStrictDerivativeAt.pointwise {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasStrictDerivativeAt f a ha d) : HasDerivativeAt f a ha d where
  delta := h.delta
  estimate eps H z hz hH near := h.estimate eps H z hz a ha
    (near.mono hH) (point_self_small a _ (Rat.le_of_lt (h.delta eps).property)) near

/-- Continuous derivatives control every sufficiently close pair, using the
proved represented segment bound. The entire small segment lies in the domain. -/
def Holomorphic.strictAt {f : Map} (h : Holomorphic f) (a : Scalar) (ha : f.domain a) :
    HasStrictDerivativeAt f a ha (h.derivative a ha) where
  delta eps := minRadius (h.openDomain.radius a ha)
    (h.continuousDerivative.delta a ha ⟨eps.val/4,by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩)
  estimate eps H z hz w hw hnz hnw step := by
    let eta : QPos := ⟨eps.val/4,by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
    have mem (t : UnitInterval.Point) : f.domain (RepresentedAffineSegment.point w z t) :=
      h.openDomain.inside a ha _ (RepresentedAffineSegment.offset_bound a w z t _
        (hnw.mono (minRadius_left _ _)) (hnz.mono (minRadius_left _ _)))
    have hb := RectangularContour.domainNeighborhood_segment_remainder_bound f h a w z ha hw hz H eta
      mem step (hnw.mono (minRadius_right _ _)) (hnz.mono (minRadius_right _ _))
    have eq : 4*eta.val*H.val=eps.val*H.val := by dsimp [eta]; grind only
    rw [eq] at hb
    exact hb

/-- Quantitative form of shrinking boxes around the actual complex quotient. -/
structure HasSecantBoundAt (f : Map) (a : Scalar) (_ha : f.domain a) (d : Scalar) where
  delta : QPos → QPos
  estimate : ∀ (eps : QPos) (z : Scalar) (hz : f.domain z) (w : Scalar) (hw : f.domain w)
    (apart : NonzeroBoxSearch.Nonzero (Centered.offset w z)),
    Small (sub z.val a.val) (delta eps).val →
    Small (sub w.val a.val) (delta eps).val →
    Small (sub (complexSecant f z w hz hw apart).val d.val) eps.val

theorem complexSecant_error (f : Map) (z w d : Scalar) (hz : f.domain z) (hw : f.domain w)
    (apart : NonzeroBoxSearch.Nonzero (Centered.offset w z)) :
    (sub (complexSecant f z w hz hw apart).val d.val).Equiv
      (mul (remainder f w hw d z hz) (RepresentedReciprocal.inverse (Centered.offset w z) apart).val) := by
  have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (Centered.offset w z).property (RepresentedReciprocal.inverse _ apart).property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse _ apart)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (complexSecant f z w hz hw apart).property d.property)
    (hright := mul_valid (remainder_valid _ _ _ _ _ _) (RepresentedReciprocal.inverse _ apart).property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  let FZ := ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property
  let FW := ComplexRawQuotient.ofRaw (f.eval w hw).val (f.eval w hw).property
  let V := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse (Centered.offset w z) apart).val
    (RepresentedReciprocal.inverse (Centered.offset w z) apart).property
  change (Z-W)*V=1 at hu
  change (FZ-FW)*V-D=((FZ-FW)-D*(Z-W))*V
  grind only

def HasStrictDerivativeAt.secantBound {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasStrictDerivativeAt f a ha d) : HasSecantBoundAt f a ha d where
  delta eps := h.delta ⟨eps.val/32,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  estimate eps z hz w hw apart hnz hnw := by
    let eta : QPos := ⟨eps.val/32,by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
    obtain ⟨H,K,step,inv,hk⟩ := balanced_separation (Centered.offset w z) apart
    have hb := h.estimate eta H z hz w hw hnz hnw step
    have hs := Small.mul (remainder_valid _ _ _ _ _ _) (RepresentedReciprocal.inverse _ apart).property
      (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property))
      (Rat.le_of_lt K.property) hb inv
    have hc := Rat.mul_le_mul_of_nonneg_left hk (Rat.le_of_lt eta.property)
    have hnum : 2*(eta.val*H.val)*K.val≤eps.val := by dsimp [eta] at *; grind only
    exact Small.congr
      (mul_valid (remainder_valid _ _ _ _ _ _) (RepresentedReciprocal.inverse _ apart).property)
      (sub_valid (complexSecant f z w hz hw apart).property d.property)
      (equiv_symm (complexSecant_error f z w d hz hw apart)) (hs.mono hnum)

def HasSecantBoundAt.strict {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasSecantBoundAt f a ha d) : HasStrictDerivativeAt f a ha d where
  delta eps := h.delta ⟨eps.val/2,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  estimate eps H z hz w hw hnz hnw step := by
    classical
    let v := Centered.offset w z
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
    by_cases apart : NonzeroBoxSearch.Nonzero v
    · have hb := h.estimate eta z hz w hw apart hnz hnw
      have hs := Small.mul (sub_valid (complexSecant f z w hz hw apart).property d.property)
        v.property (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property) hb step
      have hu := ComplexRawQuotient.ofRaw_eq_ofRaw
        (hleft := mul_valid (RepresentedReciprocal.inverse v apart).property v.property)
        (hright := ofQComplex_valid _) (RepresentedReciprocal.inverse_mul v apart)
      have he := complexSecant_error f z w d hz hw apart
      have heq : (mul (sub (complexSecant f z w hz hw apart).val d.val) v.val).Equiv
          (remainder f w hw d z hz) := by
        have e := ComplexRawQuotient.ofRaw_eq_ofRaw
          (hleft := sub_valid (complexSecant f z w hz hw apart).property d.property)
          (hright := mul_valid (remainder_valid _ _ _ _ _ _) (RepresentedReciprocal.inverse v apart).property) he
        apply ComplexRawQuotient.equiv_of_ofRaw_eq
          (hleft := mul_valid (sub_valid (complexSecant f z w hz hw apart).property d.property) v.property)
          (hright := remainder_valid _ _ _ _ _ _)
        let V := ComplexRawQuotient.ofRaw v.val v.property
        let I := ComplexRawQuotient.ofRaw (RepresentedReciprocal.inverse v apart).val (RepresentedReciprocal.inverse v apart).property
        let E := ComplexRawQuotient.ofRaw (sub (complexSecant f z w hz hw apart).val d.val)
          (sub_valid (complexSecant f z w hz hw apart).property d.property)
        let R := ComplexRawQuotient.ofRaw (remainder f w hw d z hz) (remainder_valid _ _ _ _ _ _)
        change I*V=1 at hu
        change E=R*I at e
        change E*V=R
        grind only
      have hnum : 2*eta.val*H.val=eps.val*H.val := by dsimp [eta]; grind only
      rw [hnum] at hs
      exact Small.congr (mul_valid (sub_valid (complexSecant f z w hz hw apart).property d.property) v.property)
        (remainder_valid _ _ _ _ _ _) heq hs
    · have vz : v.val.Equiv zero := Classical.not_not.mp apart
      have zw : z≈w := by
        have e := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v.property) (hright := ofQComplex_valid _) vz
        apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := w.property)
        change ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw w.val w.property=0 at e
        grind only
      have fzw := f.eval_congr z w hz hw zw
      have rz : (remainder f w hw d z hz).Equiv zero := by
        have e := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (f.eval z hz).property) (hright := (f.eval w hw).property) fzw
        have v0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := v.property) (hright := ofQComplex_valid _) vz
        apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := remainder_valid _ _ _ _ _ _) (hright := ofQComplex_valid _)
        change ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw w.val w.property=0 at v0
        change (ComplexRawQuotient.ofRaw (f.eval z hz).val (f.eval z hz).property -
          ComplexRawQuotient.ofRaw (f.eval w hw).val (f.eval w hw).property) -
          ComplexRawQuotient.ofRaw d.val d.property *
            (ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw w.val w.property)=0
        grind only
      exact Small.congr (ofQComplex_valid _) (remainder_valid _ _ _ _ _ _) (equiv_symm rz)
        (Small.zero (Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt H.property)))

/-- Every actual nonzero two-point secant error in the entire neighborhood. -/
def secantObservations (f : Map) (a d : Scalar) (radius : Nat → QPos)
    (coordinate : ComplexRaw → RealRaw) (n : Nat) (y : RealRaw) : Prop :=
  ∃ z hz w hw, ∃ apart : NonzeroBoxSearch.Nonzero (Centered.offset w z),
    Small (sub z.val a.val) (radius n).val ∧ Small (sub w.val a.val) (radius n).val ∧
    y = coordinate (sub (complexSecant f z w hz hw apart).val d.val)

/-- Shrinking rational rectangles for all complex secants at a point. Translating
by the represented derivative gives the equivalent zero-centered secant-error
boxes used here. Both coordinates have covered valid cofinal diagonals. -/
def HasShrinkingSecantBoxes (f : Map) (a : Scalar) (_ha : f.domain a) (d : Scalar) : Prop :=
  ∃ radius : Nat → QPos,
    (∀ i j, i ≤ j → (radius j).val ≤ (radius i).val) ∧
    (∀ n, (radius n).val ≤ allowance n) ∧
    HasEnclosureValue (secantObservations f a d radius realPart) (RealRaw.ofRat 0) ∧
    HasEnclosureValue (secantObservations f a d radius imagPart) (RealRaw.ofRat 0)

theorem secantObservations_antitone (f : Map) (a d : Scalar) (radius : Nat → QPos)
    (anti : ∀ i j, i ≤ j → (radius j).val ≤ (radius i).val)
    (coordinate : ComplexRaw → RealRaw) :
    ∀ i j, i ≤ j → ∀ y, secantObservations f a d radius coordinate j y →
      secantObservations f a d radius coordinate i y := by
  rintro i j hij y ⟨z,hz,w,hw,apart,hnz,hnw,hy⟩
  exact ⟨z,hz,w,hw,apart,hnz.mono (anti i j hij),hnw.mono (anti i j hij),hy⟩

theorem HasSecantBoundAt.boxes {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasSecantBoundAt f a ha d) : HasShrinkingSecantBoxes f a ha d := by
  let r := runningRadius (fun n => minRadius (h.delta ⟨allowance n,allowance_pos n⟩)
    ⟨allowance n,allowance_pos n⟩)
  have v := RealRaw.ofRat_valid 0
  have covered (k : Nat) (z : Scalar) (hz : f.domain z) (w : Scalar) (hw : f.domain w)
      (apart : NonzeroBoxSearch.Nonzero (Centered.offset w z))
      (hnz : Small (sub z.val a.val) (r k).val) (hnw : Small (sub w.val a.val) (r k).val) :=
    h.estimate ⟨allowance k,allowance_pos k⟩ z hz w hw apart
      (hnz.mono (Rat.le_trans (runningRadius_le _ k) (minRadius_left _ _)))
      (hnw.mono (Rat.le_trans (runningRadius_le _ k) (minRadius_left _ _)))
  refine ⟨r,runningRadius_antitone _,fun n => Rat.le_trans (runningRadius_le _ n) (minRadius_right _ _),?_,?_⟩
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨z,hz,w,hw,apart,hnz,hnw,rfl⟩
    exact (small_zero_enclosures (covered k z hz w hw apart hnz hnw) k).1
  · refine ⟨v,(fun n m => QInterval.expand ((RealRaw.ofRat 0).compute m) (allowance n)),
      (fun n => n),(fun n => n),cofinal_id,cofinal_id,enlarged_valid v,enlarged_equiv v,?_⟩
    rintro k y ⟨z,hz,w,hw,apart,hnz,hnw,rfl⟩
    exact (small_zero_enclosures (covered k z hz w hw apart hnz hnw) k).2

theorem HasShrinkingSecantBoxes.secantBound {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasShrinkingSecantBoxes f a ha d) : Nonempty (HasSecantBoundAt f a ha d) := by
  classical
  obtain ⟨r,anti,_shrinks,hr,hi⟩ := h
  have R := (enclosureValue_iff (secantObservations_antitone f a d r anti realPart)).mp hr
  have I := (enclosureValue_iff (secantObservations_antitone f a d r anti imagPart)).mp hi
  let nr := fun eps : QPos => Classical.choose (R.2 0 eps)
  let ni := fun eps : QPos => Classical.choose (I.2 0 eps)
  refine ⟨{ delta := fun eps => r (max (nr eps) (ni eps)), estimate := ?_ }⟩
  intro eps z hz w hw apart hnz hnw
  have br := Classical.choose_spec (R.2 0 eps) _
    (show secantObservations f a d r realPart (nr eps)
      (sub (complexSecant f z w hz hw apart).val d.val).realPart from
      ⟨z,hz,w,hw,apart,hnz.mono (anti _ _ (Nat.le_max_left _ _)),
        hnw.mono (anti _ _ (Nat.le_max_left _ _)),rfl⟩)
  have bi := Classical.choose_spec (I.2 0 eps) _
    (show secantObservations f a d r imagPart (ni eps)
      (sub (complexSecant f z w hz hw apart).val d.val).imagPart from
      ⟨z,hz,w,hw,apart,hnz.mono (anti _ _ (Nat.le_max_right _ _)),
        hnw.mono (anti _ _ (Nat.le_max_right _ _)),rfl⟩)
  exact small_of_zero_enclosures br bi

theorem HasStrictDerivativeAt.boxes {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasStrictDerivativeAt f a ha d) : HasShrinkingSecantBoxes f a ha d := h.secantBound.boxes

theorem HasShrinkingSecantBoxes.quantitative {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar}
    (h : HasShrinkingSecantBoxes f a ha d) : Nonempty (HasStrictDerivativeAt f a ha d) := by
  obtain ⟨k⟩ := h.secantBound
  exact ⟨k.strict⟩

theorem shrinkingSecantBoxes_iff {f : Map} {a : Scalar} {ha : f.domain a} {d : Scalar} :
    HasShrinkingSecantBoxes f a ha d ↔ Nonempty (HasStrictDerivativeAt f a ha d) :=
  ⟨HasShrinkingSecantBoxes.quantitative,fun ⟨h⟩ => h.boxes⟩

/-- Historical contract, retained explicitly for the equivalence theorem. -/
def IsContinuousEnclosureHolomorphic (f : Map) : Prop :=
  ∃ derivative : ∀ a, f.domain a → Scalar,
    Nonempty (OpenDomain f) ∧
    (∀ a ha, HasEnclosureDerivativeAt f a ha (derivative a ha)) ∧
    Nonempty (ContinuousOn f.domain derivative)

/-- Holomorphicity by shrinking covered two-point boxes on an open domain.
Derivative continuity, Cauchy and Taylor conclusions are not assumptions. -/
def IsEnclosureHolomorphic (f : Map) : Prop :=
  ∃ derivative : ∀ a, f.domain a → Scalar,
    Nonempty (OpenDomain f) ∧
    ∀ a ha, HasShrinkingSecantBoxes f a ha (derivative a ha)

theorem Holomorphic.enclosure {f : Map} (h : Holomorphic f) : IsEnclosureHolomorphic f :=
  ⟨h.derivative,⟨h.openDomain⟩,fun a ha => (h.strictAt a ha).boxes⟩

noncomputable def IsEnclosureHolomorphic.derivative {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : Scalar := Classical.choose h a ha

noncomputable def IsEnclosureHolomorphic.openDomain {f : Map} (h : IsEnclosureHolomorphic f) : OpenDomain f :=
  Classical.choice (Classical.choose_spec h).1

theorem IsEnclosureHolomorphic.atPoint {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasEnclosureDerivativeAt f a ha (h.derivative a ha) :=
  (Classical.choice ((Classical.choose_spec h).2 a ha).quantitative).pointwise.enclosure

noncomputable def IsEnclosureHolomorphic.quantitativeAt {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasDerivativeAt f a ha (h.derivative a ha) :=
  Classical.choice (h.atPoint a ha).quantitative

/-- Nearby pointwise derivatives lie in the same secant box. The small
rational step is allowed to depend on the neighboring derivative witness. -/
theorem HasStrictDerivativeAt.neighbor_derivative_bound {f : Map} {a : Scalar}
    {ha : f.domain a} {d : Scalar} (h : HasStrictDerivativeAt f a ha d)
    (o : OpenDomain f) (b e : Scalar) (hb : f.domain b) (k : HasDerivativeAt f b hb e)
    (eps : QPos) (near : Small (sub b.val a.val) ((h.delta eps).val/2)) :
    Small (sub e.val d.val) eps.val := by
  apply SeriesLimitLaws.small_closed _ eps.val (fun n => (RepresentedCauchySum.error n).val)
    RepresentedCauchySum.error_shrinks
  intro n
  let eta := RepresentedCauchySum.error n
  let half : QPos := ⟨(h.delta eps).val/2,by
    rw [Rat.div_def]; exact Rat.mul_pos (h.delta eps).property (by decide +kernel)⟩
  let r := minRadius (o.radius b hb) (minRadius (k.delta eta) half)
  let z := rationalShift b r
  have hzb := rationalShift_small b r
  have hz := o.inside b hb z (hzb.mono (minRadius_left _ _))
  have hrk : r.val≤(k.delta eta).val := Rat.le_trans (minRadius_right _ _) (minRadius_left _ _)
  have hrhalf : r.val≤half.val := Rat.le_trans (minRadius_right _ _) (minRadius_right _ _)
  have hza : Small (sub z.val a.val) (h.delta eps).val := by
    have ht := LocalODE.small_add (hzb.mono hrhalf) near
    have hs := Small.congr
      (add_valid (sub_valid z.property b.property) (sub_valid b.property a.property))
      (sub_valid z.property a.property) (RectangularContour.representedDifference_split z b a) ht
    exact hs.mono (by dsimp [half]; grind only)
  have hba : Small (sub b.val a.val) (h.delta eps).val := near.mono (by
    have hp := (h.delta eps).property; grind only)
  have bound := SeriesLimitLaws.small_sub (h.estimate eps r z hz b hb hza hba hzb)
    (k.estimate eta r z hz hrk hzb)
  have eq := equiv_trans
    (sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (mul_valid (sub_valid e.property d.property) (sub_valid z.property b.property))
    (mul_valid (sub_valid e.property d.property) (realStep r).property)
    (derivative_remainder_difference f b hb e d z hz)
    (mul_equiv (sub_valid e.property d.property) (sub_valid e.property d.property)
      (sub_valid z.property b.property) (realStep r).property
      (equiv_refl _ (sub_valid e.property d.property)) (rationalShift_difference b r))
  have hs := Small.congr (sub_valid (remainder_valid _ _ _ _ _ _) (remainder_valid _ _ _ _ _ _))
    (mul_valid (sub_valid e.property d.property) (realStep r).property) eq bound
  have hi := LocalODE.small_scale (c := 1/r.val)
    (by simpa only [Rat.div_def,Rat.one_mul] using Rat.le_of_lt ((Rat.inv_pos).2 r.property)) hs
  have hc := Rat.div_mul_cancel (Rat.ne_of_gt r.property) (a := (1 : Rat))
  have hnum : (1/r.val)*(eps.val*r.val+eta.val*r.val)=eps.val+eta.val := by grind only
  rw [hnum] at hi
  exact Small.congr (scaleRat_valid (mul_valid (sub_valid e.property d.property) (realStep r).property))
    (sub_valid e.property d.property) (inverse_realStep_scaling ⟨sub e.val d.val,sub_valid e.property d.property⟩ r) hi

noncomputable def IsEnclosureHolomorphic.strictAt {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasStrictDerivativeAt f a ha (h.derivative a ha) :=
  Classical.choice ((Classical.choose_spec h).2 a ha).quantitative

theorem IsEnclosureHolomorphic.secantBoxes {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasShrinkingSecantBoxes f a ha (h.derivative a ha) :=
  (Classical.choose_spec h).2 a ha

/-- Continuity is derived from uniform coverage of all nearby pairs, not
extracted from a continuity field and not deduced from the weaker pointwise relation. -/
noncomputable def IsEnclosureHolomorphic.continuousDerivative {f : Map} (h : IsEnclosureHolomorphic f) :
    ContinuousOn f.domain h.derivative where
  delta a ha eps := ⟨((h.strictAt a ha).delta eps).val/2,by
    rw [Rat.div_def]; exact Rat.mul_pos ((h.strictAt a ha).delta eps).property (by decide +kernel)⟩
  estimate a ha eps b hb near := (h.strictAt a ha).neighbor_derivative_bound
    h.openDomain b (h.derivative b hb) hb (h.quantitativeAt b hb) eps near

/-- Representation invariance of the derivative is proved, not postulated. -/
theorem IsEnclosureHolomorphic.derivative_congr {f : Map} (h : IsEnclosureHolomorphic f)
    (a b : Scalar) (ha : f.domain a) (hb : f.domain b) (he : a ≈ b) :
    h.derivative a ha ≈ h.derivative b hb :=
  ((h.atPoint a ha).congrPoint hb he).unique (h.atPoint b hb) h.openDomain

/-- The enclosure definition supplies exactly the legacy construction contract.
The derivative estimate and its representation invariance are derived. -/
noncomputable def IsEnclosureHolomorphic.toHolomorphic {f : Map} (h : IsEnclosureHolomorphic f) : Holomorphic f where
  openDomain := h.openDomain
  derivative := h.derivative
  atPoint := h.quantitativeAt
  derivative_congr := h.derivative_congr
  continuousDerivative := h.continuousDerivative

theorem enclosureHolomorphic_iff {f : Map} : IsEnclosureHolomorphic f ↔ Nonempty (Holomorphic f) :=
  ⟨fun h => ⟨h.toHolomorphic⟩,fun ⟨h⟩ => h.enclosure⟩

/-- Exact equivalence with the previous enclosure-plus-continuity definition. -/
theorem shrinkingHolomorphic_iff_continuous {f : Map} :
    IsEnclosureHolomorphic f ↔ IsContinuousEnclosureHolomorphic f := by
  constructor
  · intro h
    exact ⟨h.derivative,⟨h.openDomain⟩,h.atPoint,⟨h.continuousDerivative⟩⟩
  · rintro ⟨d,⟨o⟩,hd,⟨hc⟩⟩
    have H : Holomorphic f := {
      openDomain := o
      derivative := d
      atPoint := fun a ha => Classical.choice (hd a ha).quantitative
      derivative_congr := fun a b ha hb he => ((hd a ha).congrPoint hb he).unique (hd b hb) o
      continuousDerivative := hc }
    exact H.enclosure

theorem IsEnclosureHolomorphic.differentiable {f : Map} (h : IsEnclosureHolomorphic f) :
    IsEnclosureDifferentiable f := ⟨⟨h.openDomain⟩,fun a ha => ⟨h.derivative a ha,h.atPoint a ha⟩⟩

noncomputable def IsEnclosureHolomorphic.continuous {f : Map} (h : IsEnclosureHolomorphic f) :
    ContinuousOn f.domain f.eval := h.toHolomorphic.continuous

theorem IsEnclosureHolomorphic.derivative_unique {f : Map} (h k : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : h.derivative a ha ≈ k.derivative a ha :=
  (h.atPoint a ha).unique (k.atPoint a ha) h.openDomain

theorem IsEnclosureHolomorphic.derivative_eq {f : Map} (h : IsEnclosureHolomorphic f)
    {a : Scalar} {ha : f.domain a} {d : Scalar} (k : HasEnclosureDerivativeAt f a ha d) :
    h.derivative a ha ≈ d := (h.atPoint a ha).unique k h.openDomain

theorem IsEnclosureHolomorphic.compose {f g : Map} (hf : IsEnclosureHolomorphic f)
    (hg : IsEnclosureHolomorphic g) : IsEnclosureHolomorphic (DomainFunctions.compose f g) :=
  (hf.toHolomorphic.compose hg.toHolomorphic).enclosure

theorem IsEnclosureHolomorphic.sumOn {f g : Map} (hf : IsEnclosureHolomorphic f)
    (hg : IsEnclosureHolomorphic g) (inside : ∀ z, f.domain z → g.domain z) :
    IsEnclosureHolomorphic (DomainFunctions.sumOn f g inside) :=
  (hf.toHolomorphic.sumOn hg.toHolomorphic inside).enclosure

theorem IsEnclosureHolomorphic.productOn {f g : Map} (hf : IsEnclosureHolomorphic f)
    (hg : IsEnclosureHolomorphic g) (inside : ∀ z, f.domain z → g.domain z) :
    IsEnclosureHolomorphic (DomainFunctions.productOn f g inside) :=
  (hf.toHolomorphic.productOn hg.toHolomorphic inside).enclosure

theorem IsEnclosureHolomorphic.negate {f : Map} (h : IsEnclosureHolomorphic f) :
    IsEnclosureHolomorphic (DomainFunctions.negate f) := h.toHolomorphic.negate.enclosure

theorem IsEnclosureHolomorphic.compose_derivative {f g : Map}
    (hf : IsEnclosureHolomorphic f) (hg : IsEnclosureHolomorphic g)
    (a : Scalar) (ha : (DomainFunctions.compose f g).domain a) :
    (hf.compose hg).derivative a ha ≈
      scalarProduct (hf.derivative (g.eval a (compose_inner_mem ha)) (compose_outer_mem ha))
        (hg.derivative a (compose_inner_mem ha)) :=
  (hf.compose hg).derivative_eq
    (composeDerivative f g a ha _ _ (hf.quantitativeAt _ (compose_outer_mem ha))
      (hg.quantitativeAt a (compose_inner_mem ha))).enclosure

theorem IsEnclosureHolomorphic.product_derivative {f g : Map}
    (hf : IsEnclosureHolomorphic f) (hg : IsEnclosureHolomorphic g)
    (inside : ∀ z, f.domain z → g.domain z) (a : Scalar) (ha : f.domain a) :
    (hf.productOn hg inside).derivative a ha ≈
      productSlope (f.eval a ha) (g.eval a (inside a ha))
        (hf.derivative a ha) (hg.derivative a (inside a ha)) :=
  (hf.productOn hg inside).derivative_eq
    (productDerivative f g inside a ha _ _ (hf.quantitativeAt a ha)
      (hg.quantitativeAt a (inside a ha))).enclosure

end ComputableAnalysis.RiemannHilbert.DomainFunctions
