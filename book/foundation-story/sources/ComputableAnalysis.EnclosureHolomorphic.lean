import ComputableAnalysis.ParametrizedComplexContinuity
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums

/-!
# Holomorphicity by covered rational enclosures

Both coordinates of the normalized first-order remainder have covered valid
cofinal diagonals with value zero. The observations contain every represented
complex neighbor, and every positive rational displacement bound up to the
selected radius. The pointwise derivative specification does not require derivative continuity.
Holomorphicity below additionally requires continuity of the derivative.
The quantitative interface is proved equivalent, not assumed as a field.
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

/-- Holomorphicity for this development: covered enclosure derivatives on an
open domain, with a continuous represented derivative. Cauchy identities,
Taylor expansions and higher derivatives are not part of this definition. -/
def IsEnclosureHolomorphic (f : Map) : Prop :=
  ∃ derivative : ∀ a, f.domain a → Scalar,
    Nonempty (OpenDomain f) ∧
    (∀ a ha, HasEnclosureDerivativeAt f a ha (derivative a ha)) ∧
    Nonempty (ContinuousOn f.domain derivative)

theorem Holomorphic.enclosure {f : Map} (h : Holomorphic f) : IsEnclosureHolomorphic f :=
  ⟨h.derivative,⟨h.openDomain⟩,fun a ha => (h.atPoint a ha).enclosure,⟨h.continuousDerivative⟩⟩

noncomputable def IsEnclosureHolomorphic.derivative {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : Scalar := Classical.choose h a ha

noncomputable def IsEnclosureHolomorphic.openDomain {f : Map} (h : IsEnclosureHolomorphic f) : OpenDomain f :=
  Classical.choice (Classical.choose_spec h).1

theorem IsEnclosureHolomorphic.atPoint {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasEnclosureDerivativeAt f a ha (h.derivative a ha) :=
  (Classical.choose_spec h).2.1 a ha

/-- This extracts the explicitly required continuity data. It is not a theorem
that pointwise differentiability alone forces derivative continuity. -/
noncomputable def IsEnclosureHolomorphic.continuousDerivative {f : Map} (h : IsEnclosureHolomorphic f) :
    ContinuousOn f.domain h.derivative := Classical.choice (Classical.choose_spec h).2.2

noncomputable def IsEnclosureHolomorphic.quantitativeAt {f : Map} (h : IsEnclosureHolomorphic f)
    (a : Scalar) (ha : f.domain a) : HasDerivativeAt f a ha (h.derivative a ha) :=
  Classical.choice (h.atPoint a ha).quantitative

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
