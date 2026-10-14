import ComputableAnalysis.ElementarySineODESolutions
import ComputableAnalysis.ElementarySineComparison
import ComputableAnalysis.ElementaryAngleAlgebra

/-! The global ODE comparison applied to the primary elementary functions.
Rational functions remain primary; the complex evaluations below are derived
add-ons. The primary construction bridges and quantitative center convergence
are separate from the ODE proof in `ElementarySineODESolutions`. -/
namespace ComputableAnalysis.ElementarySineODE
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions ModularForms
set_option maxHeartbeats 2000000

def piScalar : Scalar :=
  ⟨ofRealRaw ElementaryRational.pi,ofRealRaw_valid _ ElementaryRational.pi_valid⟩

def powerSeriesExtension (z : Scalar) : Scalar :=
  Fiber.coordinate ((seriesVector oneScalar).eval z trivial) 0
def sinPiExtension (z : Scalar) : Scalar := (sine piScalar).eval z trivial

theorem powerSeriesExtension_congr (z w : Scalar) (h : z.val.Equiv w.val) :
    (powerSeriesExtension z).val.Equiv (powerSeriesExtension w).val :=
  (seriesVector oneScalar).eval_congr z w trivial trivial h 0
theorem sinPiExtension_congr (z w : Scalar) (h : z.val.Equiv w.val) :
    (sinPiExtension z).val.Equiv (sinPiExtension w).val :=
  (sine piScalar).eval_congr z w trivial trivial h

/-- Full-domain identity after the actual coordinate change. Neither the
endpoint nor the computed pi coefficient is restricted to rational values. -/
theorem sinPi_powerSeries_global (z : Scalar) :
    (sinPiExtension z).val.Equiv (powerSeriesExtension (scalarProduct piScalar z)).val :=
  scaled_sine_agrees_global piScalar z

private theorem rationalProduct (p q : QComplex) :
    (mul (ofQComplex p) (ofQComplex q)).Equiv (ofQComplex (QComplex.mul p q)) :=
  equiv_trans (mul_valid (ofQComplex_valid _) (ofQComplex_valid _))
    (qcomplexLeftMul_valid p (ofQComplex_valid q)) (ofQComplex_valid _)
    (equiv_symm (qcomplexLeftMul_equiv_mul_ofQComplex p (ofQComplex_valid q)))
    (qcomplexLeftMul_ofQComplex p q)

private theorem exponentialAt_rational (a : Scalar) (p q : QComplex)
    (h : a.val.Equiv (ofQComplex p)) :
    ((exponentialAt a).eval ⟨ofQComplex q,ofQComplex_valid q⟩ trivial).val.Equiv
      (ElementaryRational.exponentialValue (QComplex.mul p q)) := by
  let z : Scalar := ⟨ofQComplex q,ofQComplex_valid q⟩
  let w : Scalar := ⟨ofQComplex (QComplex.mul p q),ofQComplex_valid _⟩
  have hi : (scalarProduct a z).val.Equiv w.val :=
    equiv_trans (scalarProduct a z).property
      (mul_valid (ofQComplex_valid p) z.property) w.property
      (mul_equiv a.property (ofQComplex_valid p) z.property z.property h (equiv_refl _ z.property))
      (rationalProduct p q)
  exact equiv_trans ((exponentialAt a).eval z trivial).property
    (entireExponentialValue w).property (ElementaryRational.exponentialValue_valid _)
    (entireExponentialValue_congr _ _ hi)
    (ExponentialComputations.Rational.rational_powerSeries_agrees (QComplex.mul p q))

private theorem positiveFrequency_one :
    (positiveFrequency oneScalar).val.Equiv (ofQComplex ⟨0,1⟩) :=
  mul_one_equiv iScalar.val iScalar.property

private theorem negativeFrequency_one :
    (negativeFrequency oneScalar).val.Equiv (ofQComplex ⟨0,-1⟩) := by
  apply equiv_trans (negativeFrequency oneScalar).property (neg_valid iScalar.property)
    (ofQComplex_valid _) (neg_equiv positiveFrequency_one)
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  change ((-(0:Rat)≤0 ∧ -(1:Rat)≤ -1) ∧ (0≤ -(0:Rat) ∧ -1≤ -(1:Rat)))
  decide +kernel

/-- Exact primary-to-extension bridge for every rational complex argument.
Finite odd-prefix agreement identifies the primary computation; the global
ODE result identifies the independent matrix Taylor computation. -/
theorem powerSeries_primary_agrees (q : QComplex) :
    (ElementaryPowerSeries.sineValue q).Equiv
      (powerSeriesExtension ⟨ofQComplex q,ofQComplex_valid q⟩).val := by
  let z : Scalar := ⟨ofQComplex q,ofQComplex_valid q⟩
  have hp := exponentialAt_rational (positiveFrequency oneScalar) ⟨0,1⟩ q positiveFrequency_one
  have hm := exponentialAt_rational (negativeFrequency oneScalar) ⟨0,-1⟩ q negativeFrequency_one
  have he : QComplex.mul (⟨0,-1⟩ : QComplex) q =
      QComplex.neg (QComplex.mul ElementaryRational.imaginaryUnit q) :=
    QComplex.neg_mul_cert ElementaryRational.imaginaryUnit q
  rw [he] at hm
  have hformula : ((sine oneScalar).eval z trivial).val.Equiv
      (ElementaryRational.sineRadianValue q) :=
    mul_equiv sineFactor.property sineFactor.property
      (sub_valid ((exponentialAt (positiveFrequency oneScalar)).eval z trivial).property
        ((exponentialAt (negativeFrequency oneScalar)).eval z trivial).property)
      (sub_valid (ElementaryRational.exponentialValue_valid _) (ElementaryRational.exponentialValue_valid _))
      (equiv_refl _ sineFactor.property) (FunctionTheory.sub_congr hp hm)
  exact equiv_trans (ElementaryPowerSeries.sineValue_valid q)
    ((sine oneScalar).eval z trivial).property (powerSeriesExtension z).property
    (equiv_trans (ElementaryPowerSeries.sineValue_valid q) (ElementaryRational.sineRadianValue_valid q)
      ((sine oneScalar).eval z trivial).property (ElementaryPowerSeries.sineValue_agrees q)
      (equiv_symm hformula))
    (computations_agree_global oneScalar z 0)

private theorem paired_imaginary_value (e : ComplexRaw) (he : e.Valid) :
    (mul sineFactor.val (sub e (conj e))).Equiv (ofRealRaw e.imagPart) := by
  intro n
  let p := (e.compute n).center
  have hp := QBox.center_mem (valid_ordered he n)
  have hc : ((conj e).compute n).lo ≤ QComplex.conj p ∧
      QComplex.conj p ≤ ((conj e).compute n).hi :=
    ⟨⟨hp.1.1,Rat.neg_le_neg hp.2.2⟩,⟨hp.2.1,Rat.neg_le_neg hp.1.2⟩⟩
  have hn := QBox.neg_contains hc
  have hs := QBox.add_contains hp.1 hp.2 hn.1 hn.2
  have hm := QBox.mul_contains (A := QBox.point ⟨0,-(1/2)⟩) (B := (sub e (conj e)).compute n)
    (z := ⟨0,-(1/2)⟩) (w := QComplex.sub p (QComplex.conj p))
    (QComplex.le_refl _) (QComplex.le_refl _) hs.1 hs.2
  have hq : QComplex.mul ⟨0,-(1/2)⟩ (QComplex.sub p (QComplex.conj p)) = ⟨p.im,0⟩ := by
    simp only [QComplex.mul,QComplex.sub,QComplex.add,QComplex.neg,QComplex.conj]
    congr 1 <;> grind only
  rw [hq] at hm
  apply (compareAt_overlap_iff _ _ n n).mpr
  apply QBox.overlaps_of_common_point hm
  exact ⟨⟨hp.1.2,Rat.le_refl⟩,⟨hp.2.2,Rat.le_refl⟩⟩

private theorem negative_product (a z : Scalar) :
    (mul (neg a.val) z.val).Equiv (neg (mul a.val z.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (neg_valid a.property) z.property)
    (hright := neg_valid (mul_valid a.property z.property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change (-A)*Z= -(A*Z)
  grind only

private theorem negative_axis_conjugate (x : RealRaw) (hx : x.Valid) :
    (neg (imaginaryAxis x)).Equiv (conj (imaginaryAxis x)) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid x hx n
  simp only [conj,imaginaryAxis,mulI,ofRealRaw,neg,QBox.conj,QBox.neg,
    Rat.neg_zero,QBox.Overlaps,QComplex.le_def]
  constructor <;> constructor <;> grind only

/-- The complex sine formula recovers the actual rotation coordinate on a
represented real angle. This is a finite conjugation computation, separate
from the comparison of the two solution calculations. -/
theorem sine_at_real_angle (a z : Scalar) (x : RealRaw) (hx : x.Valid)
    (hi : (mul (positiveFrequency a).val z.val).Equiv (imaginaryAxis x)) :
    ((sine a).eval z trivial).val.Equiv
      (ofRealRaw (ElementaryInverseBranches.sineAtAngle x hx)) := by
  let w : Scalar := ⟨imaginaryAxis x,imaginaryAxis_valid hx⟩
  let v : Scalar := scalarProduct (negativeFrequency a) z
  have hv : v.val.Equiv (exponentialConjugateInput w).val :=
    equiv_trans v.property (neg_valid (mul_valid (positiveFrequency a).property z.property))
      (exponentialConjugateInput w).property (negative_product (positiveFrequency a) z)
      (equiv_trans (neg_valid (mul_valid (positiveFrequency a).property z.property))
        (neg_valid w.property) (exponentialConjugateInput w).property
        (neg_equiv hi) (negative_axis_conjugate x hx))
  have hp : ((exponentialAt (positiveFrequency a)).eval z trivial).val.Equiv
      (entireExponentialValue w).val := entireExponentialValue_congr _ _ hi
  have hm : ((exponentialAt (negativeFrequency a)).eval z trivial).val.Equiv
      (conj (entireExponentialValue w).val) :=
    equiv_trans (entireExponentialValue v).property
      (entireExponentialValue (exponentialConjugateInput w)).property
      (conj_valid _ (entireExponentialValue w).property)
      (entireExponentialValue_congr _ _ hv) (equiv_symm (entireExponential_conjugation w))
  exact equiv_trans ((sine a).eval z trivial).property
    (mul_valid sineFactor.property (sub_valid (entireExponentialValue w).property
      (conj_valid _ (entireExponentialValue w).property)))
    (ofRealRaw_valid _ (ElementaryInverseBranches.sineAtAngle_valid x hx))
    (mul_equiv sineFactor.property sineFactor.property
      (sub_valid ((exponentialAt (positiveFrequency a)).eval z trivial).property
        ((exponentialAt (negativeFrequency a)).eval z trivial).property)
      (sub_valid (entireExponentialValue w).property (conj_valid _ (entireExponentialValue w).property))
      (equiv_refl _ sineFactor.property) (FunctionTheory.sub_congr hp hm))
    (paired_imaginary_value _ (entireExponentialValue w).property)

private theorem imaginary_product (x : RealRaw) (hx : x.Valid) :
    (mul iScalar.val (ofRealRaw x)).Equiv (imaginaryAxis x) := by
  intro n
  let p : QComplex := ⟨(x.compute n).midpoint,0⟩
  have hp := QInterval.midpoint_mem (RealRaw.interval_order_of_valid x hx n)
  have hm := QBox.mul_contains (A := QBox.point ⟨0,1⟩) (B := (ofRealRaw x).compute n)
    (z := ⟨0,1⟩) (w := p) (QComplex.le_refl _) (QComplex.le_refl _)
    (show ((ofRealRaw x).compute n).lo ≤ p from ⟨hp.1,Rat.le_refl⟩)
    (show p ≤ ((ofRealRaw x).compute n).hi from ⟨hp.2,Rat.le_refl⟩)
  have hq : QComplex.mul ⟨0,1⟩ p = ⟨0,p.re⟩ := by
    simp [p,QComplex.mul,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.zero_mul,Rat.mul_zero,Rat.one_mul,Rat.zero_add,Rat.add_zero]
  rw [hq] at hm
  apply (compareAt_overlap_iff _ _ n n).mpr
  apply QBox.overlaps_of_common_point hm
  exact ⟨⟨by simp [imaginaryAxis,mulI,ofRealRaw],hp.1⟩,
    ⟨by simp [imaginaryAxis,mulI,ofRealRaw],hp.2⟩⟩

private theorem normalized_input (r : Rat) :
    (mul (positiveFrequency piScalar).val (ofRealRaw (RealRaw.ofRat r))).Equiv
      (imaginaryAxis (ElementaryRational.piAngle r)) := by
  let z : Scalar := ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩
  let x := ElementaryRational.piAngle r
  have hs : (mul piScalar.val z.val).Equiv (ofRealRaw x) :=
    equiv_trans (mul_valid piScalar.property z.property)
      (mul_valid z.property piScalar.property) (ofRealRaw_valid _ (ElementaryRational.piAngle_valid r))
      (mul_comm_equiv _ _ piScalar.property z.property)
      (equiv_symm (ElementaryArctangentBranch.real_scale_as_product r ElementaryRational.pi ElementaryRational.pi_valid))
  exact equiv_trans (mul_valid (positiveFrequency piScalar).property z.property)
    (mul_valid iScalar.property (mul_valid piScalar.property z.property)) (imaginaryAxis_valid (ElementaryRational.piAngle_valid r))
    (mul_assoc_equiv _ _ _ iScalar.property piScalar.property z.property)
    (equiv_trans (mul_valid iScalar.property (mul_valid piScalar.property z.property))
      (mul_valid iScalar.property (ofRealRaw_valid _ (ElementaryRational.piAngle_valid r)))
      (imaginaryAxis_valid (ElementaryRational.piAngle_valid r))
      (mul_equiv iScalar.property iScalar.property (mul_valid piScalar.property z.property)
        (ofRealRaw_valid _ (ElementaryRational.piAngle_valid r)) (equiv_refl _ iScalar.property) hs)
      (imaginary_product _ (ElementaryRational.piAngle_valid r)))

theorem sinPi_primary_agrees (r : Rat) :
    (ofRealRaw (ElementaryRational.sinPi.evalRaw r trivial)).Equiv
      (sinPiExtension ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩).val := by
  let z : Scalar := ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩
  exact equiv_trans (ofRealRaw_valid _ (ElementaryRational.sinPi_valid r trivial))
    (ofRealRaw_valid _ (ElementaryInverseBranches.sineAtAngle_valid _ (ElementaryRational.piAngle_valid r)))
    (sinPiExtension z).property
    (ofRealRaw_equiv_of_equiv (ElementaryRational.sinPi_valid r trivial)
      (ElementaryInverseBranches.sineAtAngle_valid _ (ElementaryRational.piAngle_valid r))
      (ElementarySineComparison.sinPi_agrees_derived_powerSeries r))
    (equiv_symm (sine_at_real_angle piScalar z _ (ElementaryRational.piAngle_valid r) (normalized_input r)))

/-- The continuity modulus and shrinking input boxes supply a precision
schedule for evaluation from the primary rational complex values. -/
theorem powerSeries_primary_converges (z : Scalar) (eps : QPos) :
    ∃ N, ∀ n, N ≤ n →
      Small (sub (ElementaryPowerSeries.sineValue (z.val.compute n).center)
        (powerSeriesExtension z).val) eps.val := by
  let h := ((seriesVector_holomorphic oneScalar).coordinates 0).continuous
  obtain ⟨N,hN⟩ := centerError_shrinks z.val z.property (h.delta z trivial eps)
  refine ⟨N,fun n hn => ?_⟩
  have hi := (RepresentedCauchySum.small_sub_symm _ _ _
    (rational_center_error z.val z.property n)).mono (hN n hn)
  have ho := h.estimate z trivial eps (rationalCenter z n) trivial hi
  exact Small.congr
    (sub_valid (powerSeriesExtension (rationalCenter z n)).property (powerSeriesExtension z).property)
    (sub_valid (ElementaryPowerSeries.sineValue_valid _) (powerSeriesExtension z).property)
    (FunctionTheory.sub_congr (equiv_symm (powerSeries_primary_agrees _))
      (equiv_refl _ (powerSeriesExtension z).property)) ho

private theorem real_center (x : RealRaw) (n : Nat) :
    ofQComplex ((ofRealRaw x).compute n).center =
      ofRealRaw (RealRaw.ofRat (x.compute n).midpoint) := by
  have hc : ((ofRealRaw x).compute n).center = ⟨(x.compute n).midpoint,0⟩ := by
    simp only [ofRealRaw,QBox.center,QInterval.midpoint,Rat.zero_add,Rat.div_def,Rat.zero_mul]
  rw [hc]
  rfl

/-- Every represented real input is obtained as the limit of the actual
pi-scaled rational computation at the computed rational midpoints. -/
theorem sinPi_primary_converges (x : RealRaw) (hx : x.Valid) (eps : QPos) :
    ∃ N, ∀ n, N ≤ n →
      Small (sub (ofRealRaw (ElementaryRational.sinPi.evalRaw (x.compute n).midpoint trivial))
        (sinPiExtension ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩).val) eps.val := by
  let z : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  let h := (sine_holomorphic piScalar).continuous
  obtain ⟨N,hN⟩ := centerError_shrinks z.val z.property (h.delta z trivial eps)
  refine ⟨N,fun n hn => ?_⟩
  have hi := (RepresentedCauchySum.small_sub_symm _ _ _
    (rational_center_error z.val z.property n)).mono (hN n hn)
  have ho := h.estimate z trivial eps (rationalCenter z n) trivial hi
  have hc : (ofRealRaw (ElementaryRational.sinPi.evalRaw (x.compute n).midpoint trivial)).Equiv
      (sinPiExtension (rationalCenter z n)).val := by
    have hp := sinPi_primary_agrees (x.compute n).midpoint
    apply equiv_trans (ofRealRaw_valid _ (ElementaryRational.sinPi_valid _ trivial))
      (sinPiExtension ⟨ofRealRaw (RealRaw.ofRat (x.compute n).midpoint),
        ofRealRaw_valid _ (RealRaw.ofRat_valid _)⟩).property
      (sinPiExtension (rationalCenter z n)).property hp
    apply sinPiExtension_congr
    rw [show (rationalCenter z n).val = ofRealRaw (RealRaw.ofRat (x.compute n).midpoint) from real_center x n]
    exact equiv_refl _ (ofRealRaw_valid _ (RealRaw.ofRat_valid _))
  exact Small.congr
    (sub_valid (sinPiExtension (rationalCenter z n)).property (sinPiExtension z).property)
    (sub_valid (ofRealRaw_valid _ (ElementaryRational.sinPi_valid _ trivial)) (sinPiExtension z).property)
    (FunctionTheory.sub_congr (equiv_symm hc) (equiv_refl _ (sinPiExtension z).property)) ho

/-- The primary normalized function, compared through the checked global
ODE route with the derived radian power series at its physical angle. -/
theorem sinPi_primary_ode_comparison (r : Rat) :
    (ofRealRaw (ElementaryRational.sinPi.evalRaw r trivial)).Equiv
      (powerSeriesExtension (scalarProduct piScalar
        ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩)).val :=
  equiv_trans (ofRealRaw_valid _ (ElementaryRational.sinPi_valid r trivial))
    (sinPiExtension ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩).property
    (powerSeriesExtension (scalarProduct piScalar
      ⟨ofRealRaw (RealRaw.ofRat r),ofRealRaw_valid _ (RealRaw.ofRat_valid r)⟩)).property
    (sinPi_primary_agrees r) (sinPi_powerSeries_global _)

end ComputableAnalysis.ElementarySineODE
