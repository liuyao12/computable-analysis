import ComputableAnalysis.ModularForms.WideEulerTailSlopeBounds
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual finite tail as a holomorphic map of all represented complex inputs. -/
def wideEulerTailMap (N : Nat) : DomainFunctions.Map where
  domain _ := True
  eval q _ := wideEulerTailPrefix q N
  domain_congr _ _ _ := Iff.rfl
  eval_congr q w _ _ he := wideEulerTailPrefix_congr q w he N

def wideEulerTailMap_holomorphic (N : Nat) : Holomorphic (wideEulerTailMap N) := by
  induction N with
  | zero =>
    let E : ScalarTopology.OpenData (fun _ : Scalar => True) := {
      invariant := fun _ _ _ => Iff.rfl
      radius := fun _ _ => unitError
      inside := fun _ _ _ _ => trivial }
    exact (constantOn_holomorphic E oneScalar).transfer (wideEulerTailMap 0)
      (fun _ _ => trivial) { radius := fun _ _ => unitError, inside := fun _ _ _ _ => trivial }
      (fun _ _ => equiv_refl _ oneScalar.property)
  | succ N ih =>
    let h := ih.productOn
      (tauMapPower_holomorphic (tauEulerFactorMap (N+2)) (tauEulerFactorMap_holomorphic (N+2)) 24)
      (fun _ _ => trivial)
    exact h.transfer (wideEulerTailMap (N+1)) (fun _ _ => trivial)
      { radius := h.openDomain.radius, inside := h.openDomain.inside }
      (fun q _ => equiv_refl _ (wideEulerTailPrefix q (N+1)).property)

/-- A finite arithmetic recurrence using the explicit factor slopes. -/
def wideEulerTailSlope (q : Scalar) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | N+1 => scalarSum
      (scalarProduct (wideEulerTailSlope q N) (tauEulerFactorValue q (N+2)))
      (scalarProduct (wideEulerTailPrefix q N) (tauEulerFactorSlope q (N+2)))

/-- Agreement is proved with the actual holomorphic derivative, not assumed. -/
theorem wideEulerTailSlope_actual (q : Scalar) (N : Nat) :
    ((wideEulerTailMap_holomorphic N).derivative q trivial).val.Equiv
      (wideEulerTailSlope q N).val := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    let D := (wideEulerTailMap_holomorphic N).derivative q trivial
    let F := (tauMapPower (tauEulerFactorMap (N+2)) 24).eval q trivial
    let P := wideEulerTailPrefix q N
    let G := (tauMapPower_holomorphic (tauEulerFactorMap (N+2)) (tauEulerFactorMap_holomorphic (N+2)) 24).derivative q trivial
    change (add (mul D.val F.val) (mul P.val G.val)).Equiv
      (add (mul (wideEulerTailSlope q N).val (tauEulerFactorValue q (N+2)).val)
        (mul P.val (tauEulerFactorSlope q (N+2)).val))
    exact add_equiv
      (mul_equiv D.property (wideEulerTailSlope q N).property F.property
        (tauEulerFactorValue q (N+2)).property ih (equiv_refl _ F.property))
      (mul_equiv P.property P.property G.property (tauEulerFactorSlope q (N+2)).property
        (equiv_refl _ P.property) (tauEulerFactorSlope_actual q (N+2)))

/-- Increment of the executable whole-product slope, with its small factor deviation exposed. -/
theorem wideEulerTailSlope_increment (q : Scalar) (N : Nat) :
    (sub (wideEulerTailSlope q (N+1)).val (wideEulerTailSlope q N).val).Equiv
      (add (mul (wideEulerTailSlope q N).val (sub (tauEulerFactorValue q (N+2)).val one))
        (mul (wideEulerTailPrefix q N).val (tauEulerFactorSlope q (N+2)).val)) := by
  let D := wideEulerTailSlope q N
  let F := tauEulerFactorValue q (N+2)
  let P := wideEulerTailPrefix q N
  let G := tauEulerFactorSlope q (N+2)
  have ho : one.Valid := ofQComplex_valid _
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (wideEulerTailSlope q (N+1)).property D.property)
    (hright := add_valid (mul_valid D.property (sub_valid F.property ho)) (mul_valid P.property G.property))
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let g := ComplexRawQuotient.ofRaw G.val G.property
  change (d*f+p*g)-d=d*(f-1)+p*g
  grind only



/-- Representation invariance follows from agreement with the actual finite derivative. -/
theorem wideEulerTailSlope_congr (q w : Scalar) (he : q.val.Equiv w.val) (N : Nat) :
    (wideEulerTailSlope q N).val.Equiv (wideEulerTailSlope w N).val := by
  let H := wideEulerTailMap_holomorphic N
  exact equiv_trans (wideEulerTailSlope q N).property (H.derivative q trivial).property
    (wideEulerTailSlope w N).property (equiv_symm (wideEulerTailSlope_actual q N))
    (equiv_trans (H.derivative q trivial).property (H.derivative w trivial).property
      (wideEulerTailSlope w N).property (H.derivative_congr q w trivial trivial he)
      (wideEulerTailSlope_actual w N))

end ComputableAnalysis.ModularForms
