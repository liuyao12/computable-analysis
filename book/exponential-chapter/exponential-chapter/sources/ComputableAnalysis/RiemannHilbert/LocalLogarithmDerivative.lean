import ComputableAnalysis.RiemannHilbert.LocalLogarithmSeries
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
import ComputableAnalysis.RiemannHilbert.DomainDerivativeUniqueness

/-! The derivative of the actual represented Taylor logarithm is the
reciprocal of one plus its argument. Finite geometric cancellation and
shrinking derivative tails prove the inverse identity; it is not assumed. -/
namespace ComputableAnalysis.RiemannHilbert.LocalLogarithm
open ComplexRaw FunctionTheory LocalODE

theorem altSign_succ (k : Nat) : FormalPowerSeries.altSign (k+1) = -FormalPowerSeries.altSign k := by
  unfold FormalPowerSeries.altSign
  split <;> split
  all_goals first | decide +kernel | omega

def geometricTerm (z : Scalar) (k : Nat) : ComplexRaw :=
  scaleRat (FormalPowerSeries.altSign k) (power z.val k)

theorem geometricTerm_valid (z : Scalar) (k : Nat) : (geometricTerm z k).Valid :=
  scaleRat_valid (power_valid z.val z.property k)

theorem derivativeTerm_agreement (z : Scalar) (k : Nat) :
    (BoundedSeries.derivativeTerm coefficient z.val k).Equiv (geometricTerm z k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := BoundedSeries.derivativeTerm_valid coefficient z.val coefficient_valid z.property k)
    (hright := geometricTerm_valid z k)
  let P := ComplexRawQuotient.ofRaw (power z.val k) (power_valid z.val z.property k)
  change ComplexRawQuotient.scaleRat ((k+1 : Nat) : Rat)
    (ComplexRawQuotient.scaleRat (coefficientRat (k+1)) (1 : ScalarAlgebra.Value)*P) =
    ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign k) P
  rw [← ComplexRawQuotient.scaleRat_mul]
  have hone : (1 : ScalarAlgebra.Value)*P=P := by grind only
  rw [hone, ComplexRawQuotient.scaleRat_scaleRat, coefficient_equation]

theorem geometricTerm_zero (z : Scalar) : (geometricTerm z 0).Equiv one := by
  have h : FormalPowerSeries.altSign 0=1 := by decide +kernel
  simp only [geometricTerm, h, power]
  exact scaleRat_one_equiv _ (ofQComplex_valid _)

theorem geometricTerm_succ (z : Scalar) (k : Nat) :
    (geometricTerm z (k+1)).Equiv (neg (mul z.val (geometricTerm z k))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := geometricTerm_valid z (k+1)) (hright := neg_valid (mul_valid z.property (geometricTerm_valid z k)))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let P := ComplexRawQuotient.ofRaw (power z.val k) (power_valid z.val z.property k)
  change ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign (k+1)) (P*Z) =
    -(Z*ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign k) P)
  rw [altSign_succ, ← ComplexRawQuotient.neg_scaleRat, ComplexRawQuotient.mul_scaleRat]
  congr 2
  exact ComplexRawQuotient.mul_comm P Z

theorem geometricTerm_bound (z : Scalar) (hz : interior radius.val z) (k : Nat) :
    Small (geometricTerm z k) ((2*radius.val)^k) := by
  have h := power_small z.val z.property radius.val (Rat.le_of_lt radius.property) (interior_bound radius.val z hz) k
  unfold geometricTerm FormalPowerSeries.altSign
  split
  · exact Small.congr (power_valid z.val z.property k) (scaleRat_valid (power_valid z.val z.property k))
      (equiv_symm (scaleRat_one_equiv _ (power_valid z.val z.property k))) h
  · exact Small.congr (neg_valid (power_valid z.val z.property k)) (scaleRat_valid (power_valid z.val z.property k))
      (neg_equiv_scaleRat_neg_one _ (power_valid z.val z.property k)) (SeriesLimitLaws.small_neg h)

def geometricPrefix (z : Scalar) (N : Nat) : ComplexRaw := ScalarSeries.block (geometricTerm z) 0 N

theorem geometricPrefix_valid (z : Scalar) (N : Nat) : (geometricPrefix z N).Valid :=
  ScalarSeries.block_valid _ (geometricTerm_valid z) 0 N

theorem derivativePrefix_agreement (z : Scalar) (N : Nat) :
    (BoundedSeries.derivativeBlock coefficient z.val 0 N).Equiv (geometricPrefix z N) := by
  rw [BoundedSeries.derivativeBlock_as_terms]
  exact ScalarSeries.block_congr _ _ (derivativeTerm_agreement z) 0 N

def onePlus (z : Scalar) : Scalar := ⟨add one z.val, add_valid (ofQComplex_valid _) z.property⟩

theorem geometricPrefix_inverse_error (z : Scalar) (N : Nat) :
    (sub (mul (onePlus z).val (geometricPrefix z N)) one).Equiv (neg (geometricTerm z N)) := by
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let P := fun k => ComplexRawQuotient.ofRaw (geometricPrefix z k) (geometricPrefix_valid z k)
  let T := fun k => ComplexRawQuotient.ofRaw (geometricTerm z k) (geometricTerm_valid z k)
  have ht0 : T 0=1 := ComplexRawQuotient.ofRaw_eq_ofRaw (geometricTerm_zero z)
  have ht : ∀ k, T (k+1) = -(Z*T k) := fun k => ComplexRawQuotient.ofRaw_eq_ofRaw (geometricTerm_succ z k)
  have hp : ∀ k, (1+Z)*P k=1-T k := by
    intro k
    induction k with
    | zero => change (1+Z)*0=1-T 0; rw [ht0]; grind only
    | succ k ih =>
      have hps : P (k+1)=P k+T k := by
        simp only [P, geometricPrefix, ScalarSeries.block.eq_2, Nat.zero_add]
        rfl
      rw [hps]
      rw [ht k]
      grind only
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid (onePlus z).property (geometricPrefix_valid z N)) (ofQComplex_valid _))
    (hright := neg_valid (geometricTerm_valid z N))
  change (1+Z)*P N-1= -T N
  have := hp N
  grind only

def derivativeValue (z : Scalar) (hz : interior radius.val z) : Scalar := holomorphic.derivative z hz

theorem derivativeValue_close_prefix (z : Scalar) (hz : interior radius.val z) (N : Nat) :
    Small (sub (derivativeValue z hz).val (geometricPrefix z N)) (derivativeTail 1 1 radius.val N) :=
  Small.congr (sub_valid (derivativeValue z hz).property
    (BoundedSeries.derivativeBlock_valid coefficient z.val coefficient_valid z.property 0 N))
    (sub_valid (derivativeValue z hz).property (geometricPrefix_valid z N))
    (FunctionTheory.sub_congr (equiv_refl _ (derivativeValue z hz).property) (derivativePrefix_agreement z N))
    (BoundedSeries.sumDerivative_close_prefix coefficient z.val coefficient_valid z.property 1 1 radius.val
      (by decide) (by decide) (by decide +kernel) coefficient_bound (interior_bound radius.val z hz) (by decide +kernel) N)

theorem derivativeValue_inverse (z : Scalar) (hz : interior radius.val z) :
    (mul (onePlus z).val (derivativeValue z hz).val).Equiv one := by
  let S := onePlus z
  let D := derivativeValue z hz
  let e := fun N => (2*(1+radius.val))*derivativeTail 1 1 radius.val N + valueTail 1 1 radius.val N
  have hs : Small S.val (1+radius.val) := small_add (ScalarNeumannInverse.unit_bound 0) (interior_bound radius.val z hz)
  have he : ShrinksToZero e := RepresentedCauchySum.sum_shrinks _ _
    (SeriesLimitLaws.shrinks_scale _ (derivativeTail_shrinks 1 1 radius.val
      (by decide) (by decide) (by decide +kernel) (by decide +kernel)) (2*(1+radius.val)) (by decide +kernel))
    (tail_bound_shrinks 1 (2*1*radius.val) (by decide) (by decide +kernel) (by decide +kernel))
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 e he
  intro N
  let P := geometricPrefix z N
  have h1 := Small.mul S.property (sub_valid D.property (geometricPrefix_valid z N))
    (show 0 ≤ 1+radius.val by decide +kernel)
    (show 0 ≤ derivativeTail 1 1 radius.val N from
      Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))) hs (derivativeValue_close_prefix z hz N)
  have h2 := SeriesLimitLaws.small_neg (geometricTerm_bound z hz N)
  have h2b : Small (sub (mul S.val P) one) (valueTail 1 1 radius.val N) := by
    apply Small.congr (neg_valid (geometricTerm_valid z N))
      (sub_valid (mul_valid S.property (geometricPrefix_valid z N)) (ofQComplex_valid _))
      (equiv_symm (geometricPrefix_inverse_error z N))
    apply h2.mono
    change (2*radius.val)^N ≤ 4*1*(2*1*radius.val)^N
    simp only [Rat.mul_one]
    have := Rat.pow_nonneg (n := N) (show 0 ≤ 2*radius.val by decide +kernel)
    grind
  have hsplit : (add (mul S.val (sub D.val P)) (sub (mul S.val P) one)).Equiv (sub (mul S.val D.val) one) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (mul_valid S.property (sub_valid D.property (geometricPrefix_valid z N)))
        (sub_valid (mul_valid S.property (geometricPrefix_valid z N)) (ofQComplex_valid _)))
      (hright := sub_valid (mul_valid S.property D.property) (ofQComplex_valid _))
    change ComplexRawQuotient.ofRaw S.val S.property*
        (ComplexRawQuotient.ofRaw D.val D.property-ComplexRawQuotient.ofRaw P (geometricPrefix_valid z N))+
      (ComplexRawQuotient.ofRaw S.val S.property*ComplexRawQuotient.ofRaw P (geometricPrefix_valid z N)-1) =
      ComplexRawQuotient.ofRaw S.val S.property*ComplexRawQuotient.ofRaw D.val D.property-1
    grind only
  simpa only [Rat.zero_add, e, S, D, ComplexRaw.one] using Small.congr
    (add_valid (mul_valid S.property (sub_valid D.property (geometricPrefix_valid z N)))
      (sub_valid (mul_valid S.property (geometricPrefix_valid z N)) (ofQComplex_valid _)))
    (sub_valid (mul_valid S.property D.property) (ofQComplex_valid _)) hsplit (small_add h1 h2b)

theorem onePlus_nonzero (z : Scalar) (hz : interior radius.val z) : NonzeroBoxSearch.Nonzero (onePlus z) :=
  RepresentedReciprocal.nonzero_of_inverse _ (derivativeValue z hz) (derivativeValue_inverse z hz)

theorem derivative_reciprocal (hH : DomainFunctions.Holomorphic function)
    (z : Scalar) (hz : interior radius.val z) :
    (hH.derivative z hz).val.Equiv (RepresentedReciprocal.inverse (onePlus z) (onePlus_nonzero z hz)).val :=
  equiv_trans (hH.derivative z hz).property (derivativeValue z hz).property
    (RepresentedReciprocal.inverse (onePlus z) (onePlus_nonzero z hz)).property
    (hH.derivative_unique holomorphic z hz)
    (equiv_symm (RepresentedReciprocal.inverse_unique _ _ (derivativeValue z hz) (derivativeValue_inverse z hz)))

end ComputableAnalysis.RiemannHilbert.LocalLogarithm
