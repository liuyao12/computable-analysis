import ComputableAnalysis.ModularForms.TauEulerPrefixBounds
import ComputableAnalysis.ModularForms.TauFiniteProductNonvanishing
import ComputableAnalysis.ModularForms.WideLambertFifthDerivative
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Actual finite Euler tail, beginning with the factor at the third nome power. -/
def wideEulerTailPrefix (q : Scalar) : Nat → Scalar
  | 0 => oneScalar
  | N+1 => scalarProduct (wideEulerTailPrefix q N) (tauEulerFactorValue q (N+2))

/-- The third and later Euler factors have a small uniform geometric deviation. -/
theorem wideEulerTailFactor_deviation (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (tauEulerFactorValue q (N+2)).val one)
      ((3/64:Rat)*((1:Rat)/32)^(N+1)) := by
  let x : Scalar := ⟨LocalODE.power q.val (N+3),LocalODE.power_valid _ q.property _⟩
  have hx : Small x.val (((1:Rat)/32)^(N+3)) := by
    have h := LocalODE.power_small _ q.property (1/64) (by decide +kernel) hq (N+3)
    rw [show (2:Rat)*(1/64)=1/32 by decide +kernel] at h
    exact h
  have hp := tauEulerGeometricPower_le_first ((1:Rat)/32) (by decide +kernel) (by decide +kernel) N
  have hs : ((1:Rat)/32)^(N+3)≤(1:Rat)/128 := by
    have h := Rat.mul_le_mul_of_nonneg_right hp (show (0:Rat)≤((1:Rat)/32)^2 by decide +kernel)
    rw [Rat.pow_succ ((1:Rat)/32) (N+2),Rat.pow_succ ((1:Rat)/32) (N+1)]
    have hc : ((1:Rat)/32)^2=(1/32)*(1/32) := by decide +kernel
    rw [hc] at h
    have he : ((1:Rat)/32)^(N+1)*(1/32)*(1/32)=((1:Rat)/32)^(N+1)*((1/32)*(1/32)) := by grind only
    rw [he]
    exact Rat.le_trans h (by decide +kernel)
  have h := eulerFactor_power_deviation_bound x (((1:Rat)/32)^(N+3))
    (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)) hs hx 24 (by omega)
  have he : 2*((24:Nat):Rat)*((1:Rat)/32)^(N+3)=(3/64:Rat)*((1:Rat)/32)^(N+1) := by
    rw [Rat.pow_succ ((1:Rat)/32) (N+2),Rat.pow_succ ((1:Rat)/32) (N+1)]
    grind only
  rw [he] at h
  exact h

/-- Every actual finite Euler factor is nonzero on the wider disk. -/
theorem tauEulerFactorValue_wide_nonzero (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    NonzeroBoxSearch.Nonzero (tauEulerFactorValue q N) := by
  let x : Scalar := ⟨LocalODE.power q.val (N+1),LocalODE.power_valid _ q.property _⟩
  have hp := LocalODE.power_small _ q.property (1/64) (by decide +kernel) hq (N+1)
  rw [show (2:Rat)*(1/64)=1/32 by decide +kernel] at hp
  have hx : Small x.val ((1:Rat)/32) := hp.mono
    (tauEulerGeometricPower_le_first (1/32) (by decide +kernel) (by decide +kernel) N)
  have hn := nomeDenominator_nonzero x (1/32) (by decide +kernel) (by decide +kernel) hx
  exact scalar_power_nonzero (nomeDenominator x) hn 24

/-- Every finite Euler product is nonzero throughout the wider nome disk. -/
theorem finiteDiscriminantEulerProduct_wide_nonzero (q : Scalar)
    (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    NonzeroBoxSearch.Nonzero (finiteDiscriminantEulerProduct q N) := by
  induction N with
  | zero =>
    exact RepresentedReciprocal.nonzero_of_inverse oneScalar oneScalar (by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid oneScalar.property oneScalar.property) (hright := ofQComplex_valid _)
      change (1:ComplexRawQuotient.Value)*1=1
      grind only)
  | succ N ih =>
    exact scalar_mul_nonzero (finiteDiscriminantEulerProduct q N)
      (tauEulerFactorValue q N) ih (tauEulerFactorValue_wide_nonzero q hq N)

/-- Finite tail factorization retains the first two actual factors exactly. -/
theorem finiteDiscriminantEulerProduct_wide_tail (q : Scalar) (N : Nat) :
    (finiteDiscriminantEulerProduct q (N+2)).val.Equiv
      (mul (finiteDiscriminantEulerProduct q 2).val (wideEulerTailPrefix q N).val) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (finiteDiscriminantEulerProduct q 2).property)
      (hright := mul_valid (finiteDiscriminantEulerProduct q 2).property oneScalar.property)
    let P := ComplexRawQuotient.ofRaw (finiteDiscriminantEulerProduct q 2).val
      (finiteDiscriminantEulerProduct q 2).property
    change P=P*1
    grind only
  | succ N ih =>
    have h := mul_equiv (finiteDiscriminantEulerProduct q (N+2)).property
      (mul_valid (finiteDiscriminantEulerProduct q 2).property (wideEulerTailPrefix q N).property)
      (tauEulerFactorValue q (N+2)).property (tauEulerFactorValue q (N+2)).property ih
      (equiv_refl _ (tauEulerFactorValue q (N+2)).property)
    have ha : (mul (mul (finiteDiscriminantEulerProduct q 2).val (wideEulerTailPrefix q N).val)
        (tauEulerFactorValue q (N+2)).val).Equiv
        (mul (finiteDiscriminantEulerProduct q 2).val (wideEulerTailPrefix q (N+1)).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := mul_valid (mul_valid (finiteDiscriminantEulerProduct q 2).property
          (wideEulerTailPrefix q N).property) (tauEulerFactorValue q (N+2)).property)
        (hright := mul_valid (finiteDiscriminantEulerProduct q 2).property (wideEulerTailPrefix q (N+1)).property)
      let A := ComplexRawQuotient.ofRaw (finiteDiscriminantEulerProduct q 2).val (finiteDiscriminantEulerProduct q 2).property
      let B := ComplexRawQuotient.ofRaw (wideEulerTailPrefix q N).val (wideEulerTailPrefix q N).property
      let C := ComplexRawQuotient.ofRaw (tauEulerFactorValue q (N+2)).val (tauEulerFactorValue q (N+2)).property
      change (A*B)*C=A*(B*C)
      grind only
    exact equiv_trans (finiteDiscriminantEulerProduct q (N+1+2)).property
      (mul_valid (mul_valid (finiteDiscriminantEulerProduct q 2).property (wideEulerTailPrefix q N).property)
        (tauEulerFactorValue q (N+2)).property)
      (mul_valid (finiteDiscriminantEulerProduct q 2).property (wideEulerTailPrefix q (N+1)).property) h ha

end ComputableAnalysis.ModularForms
