import ComputableAnalysis.ModularForms.LatticeJInvariant
import ComputableAnalysis.ModularForms.UpperLatticeCM163Agreement

/-! Exact agreement of the general discriminant evaluator with the CM lattice sums. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

private def scaledG2 (x : Scalar) : Scalar :=
  ⟨mul (ofQComplex ⟨60,0⟩) x.val,mul_valid (ofQComplex_valid _) x.property⟩
private def scaledG3 (x : Scalar) : Scalar :=
  ⟨mul (ofQComplex ⟨140,0⟩) x.val,mul_valid (ofQComplex_valid _) x.property⟩

def latticeDiscriminantExpression (x y : Scalar) : Scalar :=
  let a := scaledG2 x
  let b := scaledG3 y
  ⟨add (mul (mul a.val a.val) a.val) (neg (mul (ofQComplex ⟨27,0⟩) (mul b.val b.val))),
    add_valid (mul_valid (mul_valid a.property a.property) a.property)
      (neg_valid (mul_valid (ofQComplex_valid _) (mul_valid b.property b.property)))⟩

theorem latticeDiscriminantExpression_congr (x y v w : Scalar)
    (hx : x.val.Equiv v.val) (hy : y.val.Equiv w.val) :
    (latticeDiscriminantExpression x y).val.Equiv (latticeDiscriminantExpression v w).val := by
  have ha : (scaledG2 x).val.Equiv (scaledG2 v).val :=
    mul_equiv (ofQComplex_valid _) (ofQComplex_valid _) x.property v.property
      (equiv_refl _ (ofQComplex_valid _)) hx
  have hb : (scaledG3 y).val.Equiv (scaledG3 w).val :=
    mul_equiv (ofQComplex_valid _) (ofQComplex_valid _) y.property w.property
      (equiv_refl _ (ofQComplex_valid _)) hy
  have haa := mul_equiv (scaledG2 x).property (scaledG2 v).property
    (scaledG2 x).property (scaledG2 v).property ha ha
  have hbb := mul_equiv (scaledG3 y).property (scaledG3 w).property
    (scaledG3 y).property (scaledG3 w).property hb hb
  exact add_equiv
    (mul_equiv (mul_valid (scaledG2 x).property (scaledG2 x).property)
      (mul_valid (scaledG2 v).property (scaledG2 v).property)
      (scaledG2 x).property (scaledG2 v).property haa ha)
    (neg_equiv (mul_equiv (ofQComplex_valid _) (ofQComplex_valid _)
      (mul_valid (scaledG3 y).property (scaledG3 y).property)
      (mul_valid (scaledG3 w).property (scaledG3 w).property)
      (equiv_refl _ (ofQComplex_valid _)) hbb))

def cmDiscriminant163 : Scalar :=
  latticeDiscriminantExpression ⟨weightFourLatticeSum163,weightFourLatticeSum163_valid⟩
    ⟨weightSixLatticeSum163,weightSixLatticeSum163_valid⟩

theorem latticeDiscriminantMap_cm_agreement :
    (latticeDiscriminantMap.eval cmScalar163 cmPoint163_upper).val.Equiv cmDiscriminant163.val :=
  latticeDiscriminantExpression_congr
    ⟨upperWeightFourLatticeSum cmScalar163 cmPoint163_upper,upperWeightFourLatticeSum_valid _ _⟩
    ⟨upperWeightSixLatticeSum cmScalar163 cmPoint163_upper,upperWeightSixLatticeSum_valid _ _⟩
    ⟨weightFourLatticeSum163,weightFourLatticeSum163_valid⟩
    ⟨weightSixLatticeSum163,weightSixLatticeSum163_valid⟩
    upperWeightFourLatticeSum_cm_agreement upperWeightSixLatticeSum_cm_agreement

theorem latticeJMap_cm_domain_iff :
    latticeJMap.domain cmScalar163 ↔ NonzeroBoxSearch.Nonzero cmDiscriminant163 := by
  have hc := NonzeroBoxSearch.nonzero_congr
    (latticeDiscriminantMap.eval cmScalar163 cmPoint163_upper) cmDiscriminant163
    latticeDiscriminantMap_cm_agreement
  constructor
  · intro hz
    exact hc.mp hz.2
  · intro hn
    exact ⟨cmPoint163_upper,hc.mpr hn⟩

end ComputableAnalysis.ModularForms
