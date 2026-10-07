import ComputableAnalysis.ModularForms.UpperPositiveLatticeRows
import ComputableAnalysis.ModularForms.ExponentialAddition
import ComputableAnalysis.ModularForms.ExponentialDerivative
import ComputableAnalysis.ModularForms.LambertPowers

/-! Exact natural scaling of the actual exponential and nome evaluators. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem integerScale_zero (x : Scalar) :
    (integerScaleScalar x 0).val.Equiv ComplexRaw.zero := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerScaleScalar x 0).property) (hright := ofQComplex_valid _)
  change ComplexRawQuotient.ofRaw (integerAffine 0 0 x.val) _=(0:ScalarAlgebra.Value)
  rw [integerAffine_class]
  grind only

private theorem integerScale_succ (x : Scalar) (n : Nat) :
    (integerScaleScalar x ((n+1:Nat):Int)).val.Equiv
      (add (integerScaleScalar x (n:Int)).val x.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerScaleScalar x ((n+1:Nat):Int)).property)
    (hright := add_valid (integerScaleScalar x (n:Int)).property x.property)
  change ComplexRawQuotient.ofRaw (integerAffine ((n+1:Nat):Int) 0 x.val) _=
    ComplexRawQuotient.ofRaw (integerAffine (n:Int) 0 x.val) (integerAffine_valid _ _ x.property)+
      ComplexRawQuotient.ofRaw x.val x.property
  rw [integerAffine_class,integerAffine_class]
  grind only

/-- Exact integer scaling for the entire represented factorial exponential. -/
theorem entireExponential_integerScale (x : Scalar) (n : Nat) :
    (entireExponentialValue (integerScaleScalar x (n:Int))).val.Equiv
      (LocalODE.power (entireExponentialValue x).val n) := by
  induction n with
  | zero =>
    exact equiv_trans (entireExponentialValue (integerScaleScalar x 0)).property
      (entireExponentialValue ⟨ComplexRaw.zero,ofQComplex_valid _⟩).property
      (ofQComplex_valid _)
      (entireExponentialValue_congr _ _ (integerScale_zero x)) entireExponential_zero
  | succ n ih =>
    let y := integerScaleScalar x (n:Int)
    let a : Scalar := ⟨add y.val x.val,add_valid y.property x.property⟩
    have he := entireExponentialValue_congr (integerScaleScalar x ((n+1:Nat):Int)) a
      (integerScale_succ x n)
    exact equiv_trans (entireExponentialValue (integerScaleScalar x ((n+1:Nat):Int))).property
      (entireExponentialValue a).property
      (LocalODE.power_valid _ (entireExponentialValue x).property (n+1)) he
      (equiv_trans (entireExponentialValue a).property
        (mul_valid (entireExponentialValue y).property (entireExponentialValue x).property)
        (LocalODE.power_valid _ (entireExponentialValue x).property (n+1))
        (equiv_symm (entireExponential_addition y x))
        (mul_equiv (entireExponentialValue y).property
          (LocalODE.power_valid _ (entireExponentialValue x).property n)
          (entireExponentialValue x).property (entireExponentialValue x).property
          ih (equiv_refl _ (entireExponentialValue x).property)))

private theorem nomeExponent_integerScale (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) (hn : 0<n) :
    (nomeExponentMap.eval (integerScaleScalar z (n:Int))
      (integerScaleScalar_upper z hz (n:Int) (by exact_mod_cast hn))).val.Equiv
      (integerScaleScalar (nomeExponentMap.eval z hz) (n:Int)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (nomeExponentMap.eval (integerScaleScalar z (n:Int))
      (integerScaleScalar_upper z hz (n:Int) (by exact_mod_cast hn))).property)
    (hright := (integerScaleScalar (nomeExponentMap.eval z hz) (n:Int)).property)
  change ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property*
      ComplexRawQuotient.ofRaw (integerAffine (n:Int) 0 z.val) (integerAffine_valid _ _ z.property)=
    ComplexRawQuotient.ofRaw (integerAffine (n:Int) 0 (nomeExponentMap.eval z hz).val) _
  rw [integerAffine_class,integerAffine_class]
  let S := ComplexRawQuotient.ofRaw nomeSlope.val nomeSlope.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  change S*(((n:Int):ScalarAlgebra.Value)*Z+((0:Int):ScalarAlgebra.Value))=
    ((n:Int):ScalarAlgebra.Value)*(S*Z)+((0:Int):ScalarAlgebra.Value)
  grind only

/-- Scaling an upper-half-plane input multiplies the exponent and takes a nome power. -/
theorem nome_integerScale_power (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) (hn : 0<n) :
    (nome.eval (integerScaleScalar z (n:Int))
      (integerScaleScalar_upper z hz (n:Int) (by exact_mod_cast hn))).val.Equiv
      (LocalODE.power (nome.eval z hz).val n) :=
  equiv_trans (nome.eval (integerScaleScalar z (n:Int))
      (integerScaleScalar_upper z hz (n:Int) (by exact_mod_cast hn))).property
    (entireExponentialValue (integerScaleScalar (nomeExponentMap.eval z hz) (n:Int))).property
    (LocalODE.power_valid _ (nome.eval z hz).property n)
    (entireExponentialValue_congr _ _ (nomeExponent_integerScale z hz n hn))
    (entireExponential_integerScale (nomeExponentMap.eval z hz) n)

theorem nome_integerScale_small (z : Scalar) (hz : InUpperHalfPlane z.val)
    (r : Rat) (hr : 0≤r) (hq : Small (nome.eval z hz).val r) (n : Nat) :
    Small (nome.eval (integerScaleScalar z ((n+1:Nat):Int))
      (integerScaleScalar_upper z hz _ (by omega))).val (nomePowerRadius r n) :=
  Small.congr (LocalODE.power_valid _ (nome.eval z hz).property (n+1))
    (nome.eval (integerScaleScalar z ((n+1:Nat):Int)) (integerScaleScalar_upper z hz _ (by omega))).property
    (equiv_symm (nome_integerScale_power z hz (n+1) (by omega)))
    (LocalODE.power_small _ (nome.eval z hz).property r hr hq (n+1))

end ComputableAnalysis.ModularForms
