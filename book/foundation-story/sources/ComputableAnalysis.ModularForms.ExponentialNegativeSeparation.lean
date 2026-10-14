import ComputableAnalysis.ModularForms.ExponentialConjugation
import ComputableAnalysis.ModularForms.RealExponentialSeparation

/-! Exact separation from one for exponentials with negative real part. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem entireExponential_negative_real_ne_one (x : RealRaw) (hx : x.Valid) (hp : x.Pos) :
    ¬ (entireExponentialValue ⟨neg (ofRealRaw x),neg_valid (ofRealRaw_valid _ hx)⟩).val.Equiv
      (ofQComplex QComplex.one) := by
  let a : Scalar := ⟨ofRealRaw x,ofRealRaw_valid _ hx⟩
  let b : Scalar := ⟨neg a.val,neg_valid a.property⟩
  have he := entireExponentialValue_congr
    ⟨add a.val b.val,add_valid a.property b.property⟩ ⟨zero,ofQComplex_valid _⟩ (add_neg_equiv a.val a.property)
  have hprod := equiv_trans (mul_valid (entireExponentialValue a).property (entireExponentialValue b).property)
    (entireExponentialValue ⟨add a.val b.val,add_valid a.property b.property⟩).property (ofQComplex_valid _)
    (entireExponential_addition a b)
    (equiv_trans (entireExponentialValue ⟨add a.val b.val,add_valid a.property b.property⟩).property
      (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).property (ofQComplex_valid _) he entireExponential_zero)
  intro hb
  apply entireExponential_positive_ne_one x hx hp
  have hP := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue a).property (entireExponentialValue b).property)
    (hright := ofQComplex_valid _) hprod
  have hB := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue b).property) (hright := ofQComplex_valid _) hb
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (entireExponentialValue a).property) (hright := ofQComplex_valid _)
  let A := ComplexRawQuotient.ofRaw (entireExponentialValue a).val (entireExponentialValue a).property
  let B := ComplexRawQuotient.ofRaw (entireExponentialValue b).val (entireExponentialValue b).property
  change A*B=1 at hP
  change B=1 at hB
  change A=1
  grind only

def negativeRealDouble (z : Scalar) : RealRaw := RealRaw.add (-z.val.realPart) (-z.val.realPart)

theorem negativeRealDouble_valid (z : Scalar) : (negativeRealDouble z).Valid :=
  RealRaw.add_valid (RealRaw.neg_valid (realPart_valid z.property)) (RealRaw.neg_valid (realPart_valid z.property))

theorem negativeRealDouble_positive (z : Scalar) (hp : (-z.val.realPart).Pos) : (negativeRealDouble z).Pos := by
  obtain ⟨N,hN⟩ := hp
  refine ⟨N,?_⟩
  change 0<((-z.val.realPart).compute N).lo at hN
  change 0<((-z.val.realPart).compute N).lo+((-z.val.realPart).compute N).lo
  grind only

theorem conjugateSum_negativeRealDouble (z : Scalar) :
    (add z.val (conj z.val)).Equiv (neg (ofRealRaw (negativeRealDouble z))) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := valid_ordered z.property n
  simp only [add,conj,neg,ofRealRaw,negativeRealDouble,RealRaw.add,RealRaw.addCompute,
    RealRaw.neg,RealRaw.negCompute,realPart,QBox.add,QBox.conj,QBox.neg,QComplex.add,QComplex.conj,QComplex.neg]
  simp only [QBox.Ordered,QComplex.le_def] at ho
  change ((z.val.compute n).lo.re+(z.val.compute n).lo.re≤ -(-((z.val.compute n).hi.re)+ -((z.val.compute n).hi.re)) ∧
    (z.val.compute n).lo.im+ -((z.val.compute n).hi.im)≤0) ∧
    (-(-((z.val.compute n).lo.re)+ -((z.val.compute n).lo.re))≤(z.val.compute n).hi.re+(z.val.compute n).hi.re ∧
      0≤(z.val.compute n).hi.im+ -((z.val.compute n).lo.im))
  grind only

theorem entireExponential_negative_realPart_ne_one (z : Scalar) (hp : (-z.val.realPart).Pos) :
    ¬ (entireExponentialValue z).val.Equiv (ofQComplex QComplex.one) := by
  intro he
  have hc1 : (conj (ofQComplex QComplex.one)).Equiv (ofQComplex QComplex.one) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    change QComplex.conj QComplex.one≤QComplex.one ∧ QComplex.one≤QComplex.conj QComplex.one
    decide +kernel
  have hc := equiv_trans (conj_valid _ (entireExponentialValue z).property)
    (conj_valid _ (ofQComplex_valid _)) (ofQComplex_valid _) (conj_equiv he) hc1
  have hunit := mul_equiv (entireExponentialValue z).property (ofQComplex_valid _)
    (conj_valid _ (entireExponentialValue z).property) (ofQComplex_valid _) he hc
  have hs := entireExponential_conjugate_product z
  have ht := entireExponentialValue_congr
    ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩
    ⟨neg (ofRealRaw (negativeRealDouble z)),neg_valid (ofRealRaw_valid _ (negativeRealDouble_valid z))⟩
    (conjugateSum_negativeRealDouble z)
  apply entireExponential_negative_real_ne_one (negativeRealDouble z) (negativeRealDouble_valid z)
    (negativeRealDouble_positive z hp)
  have hT := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (entireExponentialValue ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩).property)
    (hright := (entireExponentialValue ⟨neg (ofRealRaw (negativeRealDouble z)),neg_valid (ofRealRaw_valid _ (negativeRealDouble_valid z))⟩).property) ht
  have hS := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue z).property (conj_valid _ (entireExponentialValue z).property))
    (hright := (entireExponentialValue ⟨add z.val (conj z.val),add_valid z.property (conj_valid _ z.property)⟩).property) hs
  have hU := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (entireExponentialValue z).property (conj_valid _ (entireExponentialValue z).property))
    (hright := mul_valid (ofQComplex_valid QComplex.one) (ofQComplex_valid QComplex.one)) hunit
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (entireExponentialValue ⟨neg (ofRealRaw (negativeRealDouble z)),neg_valid (ofRealRaw_valid _ (negativeRealDouble_valid z))⟩).property)
    (hright := ofQComplex_valid _)
  change _=(1:ComplexRawQuotient.Value)*(1:ComplexRawQuotient.Value) at hU
  change ComplexRawQuotient.ofRaw
    (entireExponentialValue ⟨neg (ofRealRaw (negativeRealDouble z)),neg_valid (ofRealRaw_valid _ (negativeRealDouble_valid z))⟩).val
    (entireExponentialValue ⟨neg (ofRealRaw (negativeRealDouble z)),neg_valid (ofRealRaw_valid _ (negativeRealDouble_valid z))⟩).property = 1
  grind only

end ComputableAnalysis.ModularForms
