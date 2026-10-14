import ComputableAnalysis.ModularForms.TauPowerDerivative

/-! Explicit formulas for the actual holomorphic Euler-factor derivatives. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem tauEulerFactorMap_derivative (q : Scalar) (N : Nat) :
    ((tauEulerFactorMap_holomorphic N).derivative q trivial).val.Equiv
      (neg (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N))) := by
  have h := tauMapPower_derivative tauCoordinateMap tauCoordinateMap_holomorphic q trivial N
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property)
    (hright := scaleRat_valid (mul_valid (LocalODE.power_valid _ q.property N) (ofQComplex_valid _))) h
  let P := ComplexRawQuotient.ofRaw
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).val
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property
  let Q := ComplexRawQuotient.ofRaw q.val q.property
  change P=ComplexRawQuotient.scaleRat ((N+1:Nat):Rat)
    (ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)*1) at he
  rw [ScalarAlgebra.ofRaw_power _ q.property N] at he
  change P=ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) (Q^N*1) at he
  have hone : Q^N*1=Q^N := by grind only
  rw [hone] at he
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((tauEulerFactorMap_holomorphic N).derivative q trivial).property)
    (hright := neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N)))
  change 0 + -P = -(ComplexRawQuotient.scaleRat ((N+1:Nat):Rat)
    (ComplexRawQuotient.ofRaw (LocalODE.power q.val N) (LocalODE.power_valid _ q.property N)))
  rw [ScalarAlgebra.ofRaw_power _ q.property N]
  change 0 + -P = -(ComplexRawQuotient.scaleRat ((N+1:Nat):Rat) (Q^N))
  rw [he]
  grind only

/-- Executable degree-24 factor slope, before the finite-product product rule. -/
def tauEulerFactorSlope (q : Scalar) (N : Nat) : Scalar :=
  let F : Scalar := ⟨sub one (LocalODE.power q.val (N+1)),
    sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)⟩
  let D : Scalar := ⟨neg (scaleRat ((N+1:Nat):Rat) (LocalODE.power q.val N)),
    neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N))⟩
  ⟨scaleRat 24 (mul (LocalODE.power F.val 23) D.val),
    scaleRat_valid (mul_valid (LocalODE.power_valid _ F.property 23) D.property)⟩

theorem tauEulerFactorSlope_actual (q : Scalar) (N : Nat) :
    ((tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative q trivial).val.Equiv
      (tauEulerFactorSlope q N).val := by
  let F := (tauEulerFactorMap N).eval q trivial
  let D := (tauEulerFactorMap_holomorphic N).derivative q trivial
  have hp := LocalODE.power_valid F.val F.property 23
  have h := tauMapPower_derivative (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) q trivial 23
  have hd := tauEulerFactorMap_derivative q N
  have hh := scaleRat_equiv (r := 24) (mul_equiv hp hp D.property
    (neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property N))) (equiv_refl _ hp) hd)
  exact equiv_trans
    ((tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24).derivative q trivial).property
    (scaleRat_valid (mul_valid hp D.property)) (tauEulerFactorSlope q N).property h hh

end ComputableAnalysis.ModularForms
