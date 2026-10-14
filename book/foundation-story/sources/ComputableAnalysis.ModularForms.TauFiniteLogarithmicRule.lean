import ComputableAnalysis.ModularForms.TauFiniteProductNonvanishing

/-! Exact finite logarithmic product rule for the actual Euler products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauEulerFactorLogarithmicSlope (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) : Scalar :=
  scalarProduct (tauEulerFactorSlope q N)
    (RepresentedReciprocal.inverse (tauEulerFactorValue q N) (tauEulerFactorValue_nonzero q hq N))

/-- The logarithmic slope increases by the next actual factor's logarithmic slope. -/
theorem finiteDiscriminantEulerLogarithmicSlope_step (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (finiteDiscriminantEulerLogarithmicSlope q hq (N+1)).val.Equiv
      (add (finiteDiscriminantEulerLogarithmicSlope q hq N).val
        (tauEulerFactorLogarithmicSlope q hq N).val) := by
  let P := finiteDiscriminantEulerProduct q N
  let F := tauEulerFactorValue q N
  let D := finiteDiscriminantEulerSlope q N
  let G := tauEulerFactorSlope q N
  let I := RepresentedReciprocal.inverse P (finiteDiscriminantEulerProduct_nonzero q hq N)
  let J := RepresentedReciprocal.inverse F (tauEulerFactorValue_nonzero q hq N)
  let K := RepresentedReciprocal.inverse (finiteDiscriminantEulerProduct q (N+1))
    (finiteDiscriminantEulerProduct_nonzero q hq (N+1))
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid P.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse P (finiteDiscriminantEulerProduct_nonzero q hq N))
  have hj := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid F.property J.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse F (tauEulerFactorValue_nonzero q hq N))
  have hk := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (finiteDiscriminantEulerProduct q (N+1)).property K.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse
      (finiteDiscriminantEulerProduct q (N+1)) (finiteDiscriminantEulerProduct_nonzero q hq (N+1)))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (finiteDiscriminantEulerLogarithmicSlope q hq (N+1)).property)
    (hright := add_valid (finiteDiscriminantEulerLogarithmicSlope q hq N).property
      (tauEulerFactorLogarithmicSlope q hq N).property)
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let j := ComplexRawQuotient.ofRaw J.val J.property
  let k := ComplexRawQuotient.ofRaw K.val K.property
  change p*i=1 at hi
  change f*j=1 at hj
  change (p*f)*k=1 at hk
  change (d*f+p*g)*k=d*i+g*j
  have hki : k=i*j := by
    calc k = k*((p*i)*(f*j)) := by rw [hi,hj]; grind only
         _ = ((p*f)*k)*(i*j) := by grind only
         _ = i*j := by rw [hk]; grind only
  rw [hki]
  calc (d*f+p*g)*(i*j) = (d*i)*(f*j)+(g*j)*(p*i) := by grind only
       _ = d*i+g*j := by rw [hi,hj]; grind only

/-- Executable sum of the justified factor logarithmic slopes. -/
def tauEulerFactorLogarithmicSum (q : Scalar) (hq : tauEulerNomeDomain q) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | N+1 => scalarSum (tauEulerFactorLogarithmicSum q hq N) (tauEulerFactorLogarithmicSlope q hq N)

/-- The actual finite-product logarithmic slope is the finite factor sum. -/
theorem finiteDiscriminantEulerLogarithmicSlope_sum (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (finiteDiscriminantEulerLogarithmicSlope q hq N).val.Equiv (tauEulerFactorLogarithmicSum q hq N).val := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (finiteDiscriminantEulerLogarithmicSlope q hq 0).property) (hright := ofQComplex_valid _)
    let I := RepresentedReciprocal.inverse (finiteDiscriminantEulerProduct q 0)
      (finiteDiscriminantEulerProduct_nonzero q hq 0)
    change (0:ComplexRawQuotient.Value)*ComplexRawQuotient.ofRaw I.val I.property=0
    grind only
  | succ N ih =>
    exact equiv_trans (finiteDiscriminantEulerLogarithmicSlope q hq (N+1)).property
      (add_valid (finiteDiscriminantEulerLogarithmicSlope q hq N).property (tauEulerFactorLogarithmicSlope q hq N).property)
      (tauEulerFactorLogarithmicSum q hq (N+1)).property
      (finiteDiscriminantEulerLogarithmicSlope_step q hq N)
      (add_equiv ih (equiv_refl _ (tauEulerFactorLogarithmicSlope q hq N).property))

end ComputableAnalysis.ModularForms
