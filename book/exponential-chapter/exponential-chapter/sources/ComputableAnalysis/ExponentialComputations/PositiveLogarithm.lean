import ComputableAnalysis.ExponentialComputations.RealExponential
import ComputableAnalysis.RiemannHilbert.NonzeroLogarithmConstruction
import ComputableAnalysis.ModularForms.ExponentialLogarithmAgreement

/-! A global real logarithm on positive represented inputs. The complex
continuation algorithm constructs a logarithm; its real coordinate is
independent of the route because exponential fibers have equal real parts.
This module proves the inverse laws. Integral identification is separate. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000
private def scalarClass (z : Scalar) := ComplexRawQuotient.ofRaw z.val z.property

abbrev PositiveInput := {x : RealInput // x.val.Pos}
def complexLog (x : PositiveInput) : Scalar :=
  NonzeroLogarithmConstruction.value (realAxis x.val) (positive_real_nonzero x.val x.property)
def log (x : PositiveInput) : RealInput :=
  ⟨(complexLog x).val.realPart,realPart_valid (complexLog x).property⟩

theorem complexLog_exponential (x : PositiveInput) :
    (entireExponentialValue (complexLog x)).val.Equiv (realAxis x.val).val :=
  equiv_trans (entireExponentialValue (complexLog x)).property
    (MatrixExponential.scalarExponential (complexLog x)).property (realAxis x.val).property
    (equiv_symm (scalarExponential_agreement _))
    (NonzeroLogarithmConstruction.exponential _ _)

theorem log_congr (x y : PositiveInput) (h : x.val.val.Equiv y.val.val) :
    (log x).val.Equiv (log y).val := by
  apply entireExponential_fiber_realPart (complexLog x) (complexLog y)
  exact equiv_trans (entireExponentialValue (complexLog x)).property (realAxis x.val).property
    (entireExponentialValue (complexLog y)).property (complexLog_exponential x)
    (equiv_trans (realAxis x.val).property (realAxis y.val).property
      (entireExponentialValue (complexLog y)).property (real_embedding_congr x.val.property y.val.property h)
      (equiv_symm (complexLog_exponential y)))

/-- One inverse law on every valid represented real input. -/
theorem log_exp (x : RealInput) :
    (log ⟨exp x,exp_positive x⟩).val.Equiv x.val := by
  apply entireExponential_fiber_realPart (complexLog ⟨exp x,exp_positive x⟩) (realAxis x)
  exact equiv_trans (entireExponentialValue _).property (realAxis (exp x)).property
    (entireExponentialValue (realAxis x)).property
    (complexLog_exponential _) (equiv_symm (exp_real_embedding x))

theorem realAxis_conjugate (x : RealInput) : (conj (realAxis x).val).Equiv (realAxis x).val := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid x.val x.property n
  simp only [realAxis,ofRealRaw,conj,QBox.conj,QComplex.conj]
  constructor <;> constructor <;> simp only [Rat.neg_zero] <;> first | exact ho | exact Rat.le_refl

private theorem positive_sum (x y : RealInput) (hx : x.val.Pos) (hy : y.val.Pos) :
    (RealRaw.add x.val y.val).Pos := by
  obtain ⟨i,hi⟩ := hx
  obtain ⟨j,hj⟩ := hy
  let k := max i j
  have hxi := (x.property.2.1 i k (Nat.le_max_left _ _)).1
  have hyj := (y.property.2.1 j k (Nat.le_max_right _ _)).1
  refine ⟨k,?_⟩
  change 0<(x.val.compute k).lo+(y.val.compute k).lo
  change 0<(x.val.compute i).lo at hi
  change 0<(y.val.compute j).lo at hj
  grind only

/-- The second inverse law retains only the genuine positivity domain. -/
theorem exp_log (x : PositiveInput) : (exp (log x)).val.Equiv x.val.val := by
  let l := complexLog x
  let a := exp (log x)
  let A := realAxis a
  let X := realAxis x.val
  have hprod := mul_equiv (entireExponentialValue l).property X.property
    (conj_valid _ (entireExponentialValue l).property) (conj_valid _ X.property)
    (complexLog_exponential x) (conj_equiv (complexLog_exponential x))
  have hxx := mul_equiv X.property X.property (conj_valid _ X.property) X.property
    (equiv_refl _ X.property) (realAxis_conjugate x.val)
  have hmag := entireExponential_squared_magnitude l
  let r : Scalar := ⟨ofRealRaw (RealRaw.scaleRat 2 l.val.realPart),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid l.property))⟩
  have hadd : (add (realAxis (log x)).val (realAxis (log x)).val).Equiv r.val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    have ho := RealRaw.interval_order_of_valid (log x).val (log x).property n
    change ((complexLog x).val.compute n).lo.re ≤ ((complexLog x).val.compute n).hi.re at ho
    simp only [r,l,realAxis,log,ofRealRaw,realPart,add,QBox.add,QComplex.add,RealRaw.scaleRat,RealRaw.scaleRatCompute,
      if_pos (show (0:Rat)≤2 by decide +kernel)]
    constructor <;> constructor <;> grind only
  have heA := exp_real_embedding (log x)
  have hAA := equiv_trans (mul_valid A.property A.property)
    (mul_valid (entireExponentialValue (realAxis (log x))).property (entireExponentialValue (realAxis (log x))).property)
    (entireExponentialValue r).property
    (mul_equiv A.property (entireExponentialValue (realAxis (log x))).property
      A.property (entireExponentialValue (realAxis (log x))).property (equiv_symm heA) (equiv_symm heA))
    (equiv_trans (mul_valid (entireExponentialValue (realAxis (log x))).property (entireExponentialValue (realAxis (log x))).property)
      (entireExponentialValue ⟨add (realAxis (log x)).val (realAxis (log x)).val,add_valid (realAxis (log x)).property (realAxis (log x)).property⟩).property
      (entireExponentialValue r).property (entireExponential_addition _ _)
      (entireExponentialValue_congr _ _ hadd))
  have heq := equiv_trans (mul_valid A.property A.property) (entireExponentialValue r).property
    (mul_valid X.property X.property) hAA
    (equiv_trans (entireExponentialValue r).property
      (mul_valid (entireExponentialValue l).property (conj_valid _ (entireExponentialValue l).property))
      (mul_valid X.property X.property) (equiv_symm hmag)
      (equiv_trans (mul_valid (entireExponentialValue l).property (conj_valid _ (entireExponentialValue l).property))
        (mul_valid X.property (conj_valid _ X.property)) (mul_valid X.property X.property) hprod hxx))
  let S : Scalar := scalarSum A X
  have hS : NonzeroBoxSearch.Nonzero S := by
    have hp := positive_sum a x.val (exp_positive (log x)) x.property
    have hs : S.val.Equiv (realAxis ⟨RealRaw.add a.val x.val.val,RealRaw.add_valid a.property x.val.property⟩).val := by
      intro n
      apply (compareAt_overlap_iff _ _ n n).mpr
      have ho := RealRaw.interval_order_of_valid (RealRaw.add a.val x.val.val)
        (RealRaw.add_valid a.property x.val.property) n
      simp only [S,scalarSum,A,X,realAxis,ofRealRaw,add,QBox.add,QComplex.add,RealRaw.add,RealRaw.addCompute,Rat.zero_add]
      constructor <;> constructor <;> first | exact ho | exact Rat.le_refl
    intro hz
    exact positive_real_nonzero _ hp (equiv_trans
      (realAxis ⟨RealRaw.add a.val x.val.val,RealRaw.add_valid a.property x.val.property⟩).property
      S.property (ofQComplex_valid _)
      (equiv_symm hs) hz)
  let I := RepresentedReciprocal.inverse S hS
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid S.property I.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse S hS)
  have hh := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid A.property A.property) (hright := mul_valid X.property X.property) heq
  have hc : A.val.Equiv X.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := A.property) (hright := X.property)
    let AA := scalarClass A
    let XX := scalarClass X
    let II := scalarClass I
    change (AA+XX)*II=1 at hi
    change AA*AA=XX*XX at hh
    change AA=XX
    grind only
  exact realPart_equiv hc

/-- A constructed local analytic extension of the real logarithm. -/
def logChart (x : PositiveInput) : DomainFunctions.Map :=
  NonzeroLogarithmConstruction.localFunction (realAxis x.val) (positive_real_nonzero x.val x.property)
def logChartHolomorphic (x : PositiveInput) : DomainFunctions.Holomorphic (logChart x) :=
  NonzeroLogarithmConstruction.localHolomorphic _ _

theorem logChart_real_agreement (x y : PositiveInput)
    (hy : (logChart x).domain (realAxis y.val)) :
    ((logChart x).eval (realAxis y.val) hy).val.realPart.Equiv (log y).val := by
  apply entireExponential_fiber_realPart _ (complexLog y)
  have he := NonzeroLogarithmConstruction.local_exponential
    (realAxis x.val) (positive_real_nonzero x.val x.property) (realAxis y.val) hy
  exact equiv_trans (entireExponentialValue _).property
    (MatrixExponential.scalarExponential _).property (entireExponentialValue (complexLog y)).property
    (equiv_symm (scalarExponential_agreement _))
    (equiv_trans (MatrixExponential.scalarExponential _).property (realAxis y.val).property
      (entireExponentialValue (complexLog y)).property he (equiv_symm (complexLog_exponential y)))

/-- The actual derivative of the locally agreeing logarithm is the reciprocal,
with the chart and its center-domain evidence constructed internally. -/
theorem logChart_derivative (x : PositiveInput) :
    ((logChartHolomorphic x).derivative (realAxis x.val)
      (RelativeLogarithm.center_mem _ (positive_real_nonzero x.val x.property))).val.Equiv
      (RepresentedReciprocal.inverse (realAxis x.val) (positive_real_nonzero x.val x.property)).val :=
  NonzeroLogarithmConstruction.local_derivative _ _ (logChartHolomorphic x) _ _

/-- Any real computation whose exponential is the target agrees with log. -/
theorem log_unique (x : PositiveInput) (a : RealInput)
    (h : (exp a).val.Equiv x.val.val) : a.val.Equiv (log x).val :=
  exp_injective a (log x) (RealRaw.equiv_trans (exp a).property x.val.property
    (exp (log x)).property h (RealRaw.equiv_symm (exp_log x)))

/-- Any supplied computation inverted by log must be the exponential.
No conclusion about an unproved integral interpretation is inferred here. -/
theorem exp_unique_of_log (x : RealInput) (y : PositiveInput)
    (h : (log y).val.Equiv x.val) : y.val.val.Equiv (exp x).val :=
  RealRaw.equiv_trans y.val.property (exp (log y)).property (exp x).property
    (RealRaw.equiv_symm (exp_log y)) (exp_congr (log y) x h)
end ComputableAnalysis.ExponentialComputations
