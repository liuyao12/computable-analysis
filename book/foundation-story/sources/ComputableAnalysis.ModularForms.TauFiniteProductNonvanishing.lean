import ComputableAnalysis.ModularForms.TauEulerLogarithmicSlope
import ComputableAnalysis.ModularForms.NomeDenominator

/-! Constructed nonvanishing for every actual finite Euler factor and product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- Every base factor has a justified executable reciprocal on the nome disk. -/
theorem tauEulerBaseFactor_nonzero (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    NonzeroBoxSearch.Nonzero ((tauEulerFactorMap N).eval q trivial) := by
  let X : Scalar := ⟨LocalODE.power q.val (N+1),LocalODE.power_valid _ q.property _⟩
  have hp := LocalODE.power_small q.val q.property (1/1024) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (N+1)
  have he : (2:Rat)*(1/1024)=1/512 := by decide +kernel
  rw [he] at hp
  have hb := tauEulerGeometricPower_le_first (1/512) (by decide +kernel) (by decide +kernel) N
  have hX : Small X.val (1/512) := hp.mono hb
  exact nomeDenominator_nonzero X (1/512) (by decide +kernel) (by decide +kernel) hX

/-- Raising the nonzero base to degree 24 preserves nonvanishing. -/
theorem tauEulerFactorValue_nonzero (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    NonzeroBoxSearch.Nonzero (tauEulerFactorValue q N) :=
  scalar_power_nonzero ((tauEulerFactorMap N).eval q trivial) (tauEulerBaseFactor_nonzero q hq N) 24

/-- Every actual finite Euler product is nonzero on the nome disk. -/
theorem finiteDiscriminantEulerProduct_nonzero (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
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
      (tauEulerFactorValue q N) ih (tauEulerFactorValue_nonzero q hq N)

/-- Executable division of the actual finite-product derivative by its value. -/
def finiteDiscriminantEulerLogarithmicSlope (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) : Scalar :=
  scalarProduct (finiteDiscriminantEulerSlope q N)
    (RepresentedReciprocal.inverse (finiteDiscriminantEulerProduct q N)
      (finiteDiscriminantEulerProduct_nonzero q hq N))

end ComputableAnalysis.ModularForms
