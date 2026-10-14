import ComputableAnalysis.ModularForms.TauEulerLimitRemainder

/-! The normalized holomorphic Euler discriminant candidate on the nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Literal normalized Euler product; modular discriminant agreement is separate. -/
def tauNormalizedEulerMap : DomainFunctions.Map :=
  productOn tauEulerNomeMap tauCoordinateMap (fun _ _ => trivial)

noncomputable def tauNormalizedEulerMap_holomorphic : Holomorphic tauNormalizedEulerMap :=
  tauEulerNomeMap_holomorphic.productOn tauCoordinateMap_holomorphic (fun _ _ => trivial)

/-- Exact derivative formula at every represented input in the nome disk. -/
theorem tauNormalizedEulerMap_derivative (q : Scalar) (hq : tauEulerNomeDomain q) :
    ((tauNormalizedEulerMap_holomorphic).derivative q hq).val.Equiv
      (add (mul (tauEulerNomeDerivativeCandidate q hq).val q.val) (tauEulerNomeMap.eval q hq).val) := by
  let D := tauEulerNomeDerivativeCandidate q hq
  let P := tauEulerNomeMap.eval q hq
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (tauNormalizedEulerMap_holomorphic.derivative q hq).property)
    (hright := add_valid (mul_valid D.property q.property) P.property)
  let d := ComplexRawQuotient.ofRaw D.val D.property
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change d*Q+p*1=d*Q+p
  grind only

/-- The normalized product has the required first-order coefficient one. -/
theorem tauNormalizedEulerMap_derivative_at_zero (q : Scalar) (hq : tauEulerNomeDomain q)
    (hz : q.val.Equiv zero) :
    (tauNormalizedEulerMap_holomorphic.derivative q hq).val.Equiv one := by
  let D := tauEulerNomeDerivativeCandidate q hq
  let P := tauEulerNomeMap.eval q hq
  have hq0 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property)
    (hright := ofQComplex_valid _) hz
  have hp1 := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := P.property)
    (hright := ofQComplex_valid _) (tauEulerNomeMap_at_zero q hq hz)
  have hd := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (tauNormalizedEulerMap_holomorphic.derivative q hq).property)
    (hright := add_valid (mul_valid D.property q.property) P.property)
    (tauNormalizedEulerMap_derivative q hq)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (tauNormalizedEulerMap_holomorphic.derivative q hq).property)
    (hright := ofQComplex_valid _)
  rw [hd,ComplexRawQuotient.ofRaw_add _ _ (mul_valid D.property q.property) P.property,
    ComplexRawQuotient.ofRaw_mul _ _ D.property q.property,hq0,hp1]
  change ComplexRawQuotient.ofRaw D.val D.property*0+1=1
  grind only

/-- Multiplication by the nome preserves explicit finite-product convergence. -/
theorem tauNormalizedEulerMap_close_prefix (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    Small (sub (tauNormalizedEulerMap.eval q hq).val
      (mul (finiteDiscriminantEulerProduct q N).val q.val))
      (2*tauEulerProductTail (1/1024) N*(1/1024)) := by
  let P := tauEulerNomeMap.eval q hq
  let F := finiteDiscriminantEulerProduct q N
  have he : (sub (mul P.val q.val) (mul F.val q.val)).Equiv
      (mul (sub P.val F.val) q.val) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (mul_valid P.property q.property) (mul_valid F.property q.property))
      (hright := mul_valid (sub_valid P.property F.property) q.property)
    let p := ComplexRawQuotient.ofRaw P.val P.property
    let f := ComplexRawQuotient.ofRaw F.val F.property
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change p*Q-f*Q=(p-f)*Q
    grind only
  have hn : 0≤tauEulerProductTail (1/1024) N := by
    unfold tauEulerProductTail
    exact Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (by decide +kernel))
  exact Small.congr (mul_valid (sub_valid P.property F.property) q.property)
    (sub_valid (mul_valid P.property q.property) (mul_valid F.property q.property))
    (equiv_symm he)
    (Small.mul (sub_valid P.property F.property) q.property hn (by decide +kernel)
      (tauEulerProduct_close_prefix q (1/1024) (by decide +kernel) Rat.le_refl
        (LocalODE.interior_bound _ q hq) N) (LocalODE.interior_bound _ q hq))

end ComputableAnalysis.ModularForms
