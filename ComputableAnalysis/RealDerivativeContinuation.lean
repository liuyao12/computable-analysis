import ComputableAnalysis.DerivativeContinuation

/-! Real derivatives use the same continuous-quotient definition. Restricting
represented complex functions to the real axis and taking real parts gives
actual real derivative witnesses, including arbitrary represented inputs. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw

/-- Restrict to represented real inputs and take the real component. -/
def Map.realRestriction (f : Map) : RealFunctionTheory.Map where
  domain := fun x => f.domain (ofRealRaw x)
  eval := fun x => (f.eval (ofRealRaw x)).realPart
  valid := fun x hx h => realPart_valid (f.valid _ (ofRealRaw_valid x hx) h)
  domain_congr := fun hx hy he => f.domain_congr (ofRealRaw_valid _ hx) (ofRealRaw_valid _ hy)
    (ofRealRaw_equiv_of_equiv hx hy he)
  eval_congr := fun hx hy h1 h2 he => realPart_equiv
    (f.eval_congr (ofRealRaw_valid _ hx) (ofRealRaw_valid _ hy) h1 h2
      (ofRealRaw_equiv_of_equiv hx hy he))

private theorem realPart_sub_compute (u v : ComplexRaw) :
    (sub u v).realPart.compute = (u.realPart - v.realPart).compute := by
  change (sub u v).realPart.compute = (RealRaw.sub u.realPart v.realPart).compute
  funext n
  simp only [sub,add,neg,realPart,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
    RealRaw.sub,RealRaw.subCompute,Rat.sub_eq_add_neg]

private theorem real_small_sub {u v : ComplexRaw} {r : Rat} (h : Small (sub u v) r) :
    RealFunctionTheory.Small (u.realPart-v.realPart) r := by
  constructor
  · intro n m
    have k := h.1 n m
    change -r ≤ ((sub u v).realPart.compute m).hi at k
    rw [realPart_sub_compute] at k
    exact k
  · intro n m
    have k := h.2.1 n m
    change ((sub u v).realPart.compute n).lo ≤ r at k
    rw [realPart_sub_compute] at k
    exact k

private theorem embed_small_sub {x y : RealRaw} {r : Rat} (hr : 0 ≤ r)
    (h : RealFunctionTheory.Small (x-y) r) : Small (sub (ofRealRaw x) (ofRealRaw y)) r := by
  refine ⟨?_,?_,?_,?_⟩
  · intro n m
    have k := h.1 n m
    change -r ≤ (x.compute m).hi - (y.compute m).lo at k
    simpa only [sub,add,neg,realPart,ofRealRaw,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
      RealRaw.Le,RealRaw.ofRat,RealRaw.sub,RealRaw.subCompute,Rat.sub_eq_add_neg] using k
  · intro n m
    have k := h.2 n m
    change (x.compute n).lo - (y.compute n).hi ≤ r at k
    simpa only [sub,add,neg,realPart,ofRealRaw,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
      RealRaw.Le,RealRaw.ofRat,RealRaw.sub,RealRaw.subCompute,Rat.sub_eq_add_neg] using k
  · intro n m
    simpa only [sub,add,neg,imagPart,ofRealRaw,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
      RealRaw.ofRat,Rat.neg_zero,Rat.zero_add] using (show -r ≤ 0 by grind)
  · intro n m
    simpa only [sub,add,neg,imagPart,ofRealRaw,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
      RealRaw.ofRat,Rat.neg_zero,Rat.zero_add] using hr

private theorem real_factor_compute (x y : RealRaw) (q : ComplexRaw) :
    (mul (sub (ofRealRaw x) (ofRealRaw y)) q).realPart.compute =
      ((x-y)*q.realPart).compute := by
  change (mul (sub (ofRealRaw x) (ofRealRaw y)) q).realPart.compute =
    (RealRaw.mul (RealRaw.sub x y) q.realPart).compute
  funext n
  simp [mul,sub,add,neg,realPart,ofRealRaw,QBox.mul,QBox.mulRealInterval,QBox.add,QBox.neg,
    QComplex.add,QComplex.neg,RealRaw.mul,RealRaw.mulCompute,RealRaw.sub,RealRaw.subCompute,
    min4,max4,minRat,maxRat2,Rat.sub_eq_add_neg,Rat.zero_add,Rat.add_zero,Rat.zero_mul,Rat.neg_zero]
  constructor <;> rfl

/-- A complex quotient extension restricts to an actual real quotient extension. -/
def DerivativeAt.realRestriction {f : Map} {a : RealRaw} {d : ComplexRaw}
    (ha : a.Valid) (h : DerivativeAt f (ofRealRaw a) d) :
    RealFunctionTheory.DerivativeAt f.realRestriction a d.realPart where
  quotient := fun y => (h.quotient (ofRealRaw y)).realPart
  quotient_valid := fun y hy hfy => realPart_valid (h.quotient_valid _ (ofRealRaw_valid y hy) hfy)
  quotient_congr := fun hy hz h1 h2 he => realPart_equiv
    (h.quotient_congr (ofRealRaw_valid _ hy) (ofRealRaw_valid _ hz) h1 h2
      (ofRealRaw_equiv_of_equiv hy hz he))
  quotient_continuous := {
    point_valid := ha
    point_mem := h.point_mem
    delta := h.quotient_continuous.delta
    estimate := by
      intro eps y hy hfy hya
      exact real_small_sub (h.quotient_continuous.estimate eps (ofRealRaw y)
        (ofRealRaw_valid y hy) hfy
        (embed_small_sub (Rat.le_of_lt (h.quotient_continuous.delta eps).property) hya)) }
  derivative_valid := realPart_valid h.derivative_valid
  value_at := realPart_equiv h.value_at
  factorization := by
    intro y hy hfy
    have hY := ofRealRaw_valid y hy
    have vY := f.valid _ hY hfy
    have vA := f.valid _ h.point_valid h.point_mem
    have vQ := h.quotient_valid _ hY hfy
    have first := RealRaw.equiv_symm (RealRaw.equiv_of_compute_eq
      (realPart_valid (sub_valid vY vA)) (realPart_sub_compute _ _))
    have middle := realPart_equiv (h.factorization _ hY hfy)
    have last := RealRaw.equiv_of_compute_eq
      (realPart_valid (mul_valid (sub_valid hY h.point_valid) vQ)) (real_factor_compute y a _)
    exact RealRaw.equiv_trans (RealRaw.sub_valid (realPart_valid vY) (realPart_valid vA))
      (realPart_valid (sub_valid vY vA))
      (RealRaw.mul_valid (RealRaw.sub_valid hy ha) (realPart_valid vQ)) first
      (RealRaw.equiv_trans (realPart_valid (sub_valid vY vA))
        (realPart_valid (mul_valid (sub_valid hY h.point_valid) vQ))
        (RealRaw.mul_valid (RealRaw.sub_valid hy ha) (realPart_valid vQ)) middle last)

end ComputableAnalysis.FunctionTheory
