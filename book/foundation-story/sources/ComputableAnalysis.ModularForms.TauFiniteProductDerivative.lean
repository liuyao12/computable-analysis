import ComputableAnalysis.ModularForms.TauEulerSlopeBounds

/-! Executable slopes of whole finite Euler products and actual derivative agreement. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauEulerFactorValue (q : Scalar) (N : Nat) : Scalar :=
  ⟨LocalODE.power (sub one (LocalODE.power q.val (N+1))) 24,
    LocalODE.power_valid _ (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)) 24⟩

/-- A finite arithmetic recurrence using the explicit factor slopes. -/
def finiteDiscriminantEulerSlope (q : Scalar) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | N+1 => scalarSum
      (scalarProduct (finiteDiscriminantEulerSlope q N) (tauEulerFactorValue q N))
      (scalarProduct (finiteDiscriminantEulerProduct q N) (tauEulerFactorSlope q N))

/-- Agreement is proved with the actual holomorphic derivative, not assumed. -/
theorem finiteDiscriminantEulerSlope_actual (q : Scalar) (N : Nat) :
    ((finiteDiscriminantEulerMap_holomorphic N).derivative q trivial).val.Equiv
      (finiteDiscriminantEulerSlope q N).val := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    let D := (finiteDiscriminantEulerMap_holomorphic N).derivative q trivial
    let F := (tauMapPower (tauEulerFactorMap N) 24).eval q trivial
    let P := finiteDiscriminantEulerProduct q N
    let G := (tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative q trivial
    change (add (mul D.val F.val) (mul P.val G.val)).Equiv
      (add (mul (finiteDiscriminantEulerSlope q N).val (tauEulerFactorValue q N).val)
        (mul P.val (tauEulerFactorSlope q N).val))
    exact add_equiv
      (mul_equiv D.property (finiteDiscriminantEulerSlope q N).property F.property
        (tauEulerFactorValue q N).property ih (equiv_refl _ F.property))
      (mul_equiv P.property P.property G.property (tauEulerFactorSlope q N).property
        (equiv_refl _ P.property) (tauEulerFactorSlope_actual q N))

theorem tauEulerFactorSlope_congr (q w : Scalar) (he : q.val.Equiv w.val) (N : Nat) :
    (tauEulerFactorSlope q N).val.Equiv (tauEulerFactorSlope w N).val := by
  let H := tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24
  exact equiv_trans (tauEulerFactorSlope q N).property (H.derivative q trivial).property
    (tauEulerFactorSlope w N).property (equiv_symm (tauEulerFactorSlope_actual q N))
    (equiv_trans (H.derivative q trivial).property (H.derivative w trivial).property
      (tauEulerFactorSlope w N).property (H.derivative_congr q w trivial trivial he)
      (tauEulerFactorSlope_actual w N))

theorem finiteDiscriminantEulerSlope_congr (q w : Scalar) (he : q.val.Equiv w.val) (N : Nat) :
    (finiteDiscriminantEulerSlope q N).val.Equiv (finiteDiscriminantEulerSlope w N).val := by
  let H := finiteDiscriminantEulerMap_holomorphic N
  exact equiv_trans (finiteDiscriminantEulerSlope q N).property (H.derivative q trivial).property
    (finiteDiscriminantEulerSlope w N).property (equiv_symm (finiteDiscriminantEulerSlope_actual q N))
    (equiv_trans (H.derivative q trivial).property (H.derivative w trivial).property
      (finiteDiscriminantEulerSlope w N).property (H.derivative_congr q w trivial trivial he)
      (finiteDiscriminantEulerSlope_actual w N))

/-- Increment of the executable whole-product slope, with its small factor deviation exposed. -/
theorem finiteDiscriminantEulerSlope_increment (q : Scalar) (N : Nat) :
    (sub (finiteDiscriminantEulerSlope q (N+1)).val (finiteDiscriminantEulerSlope q N).val).Equiv
      (add (mul (finiteDiscriminantEulerSlope q N).val (sub (tauEulerFactorValue q N).val one))
        (mul (finiteDiscriminantEulerProduct q N).val (tauEulerFactorSlope q N).val)) := by
  let D := finiteDiscriminantEulerSlope q N
  let F := tauEulerFactorValue q N
  let P := finiteDiscriminantEulerProduct q N
  let G := tauEulerFactorSlope q N
  have ho : one.Valid := ofQComplex_valid _
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (finiteDiscriminantEulerSlope q (N+1)).property D.property)
    (hright := add_valid (mul_valid D.property (sub_valid F.property ho)) (mul_valid P.property G.property))
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  change (d*f+p*g)-d=d*(f-1)+p*g
  grind only

end ComputableAnalysis.ModularForms
