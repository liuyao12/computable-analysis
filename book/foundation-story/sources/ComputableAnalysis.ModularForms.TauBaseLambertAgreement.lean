import ComputableAnalysis.ModularForms.TauFactorLogarithmicQuotient
import ComputableAnalysis.ModularForms.LambertPowers

/-! Agreement of the actual Lambert factor with the Euler base reciprocal. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The existing convergent Lambert factor at a nome power is exactly the
nome power times the justified Euler base reciprocal. -/
theorem nomeLambertPower_euler_reciprocal (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    (nomeLambertPower q (1/1024) N).Equiv
      (mul (LocalODE.power q.val (N+1))
        (RepresentedReciprocal.inverse ((tauEulerFactorMap N).eval q trivial)
          (tauEulerBaseFactor_nonzero q hq N)).val) := by
  let B := (tauEulerFactorMap N).eval q trivial
  let I := RepresentedReciprocal.inverse B (tauEulerBaseFactor_nonzero q hq N)
  let X := nomePowerScalar q N
  let L : Scalar := ⟨nomeLambertPower q (1/1024) N,
    nomeLambertPower_valid q (1/1024) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N⟩
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid B.property I.property)
    (hright := ofQComplex_valid _) (RepresentedReciprocal.mul_inverse B (tauEulerBaseFactor_nonzero q hq N))
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := mul_valid B.property L.property)
    (hright := X.property) (nomeLambertPower_multiplication q (1/1024)
      (by decide +kernel) (by decide +kernel) (LocalODE.interior_bound _ q hq) N)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := L.property)
    (hright := mul_valid X.property I.property)
  let b := ComplexRawQuotient.ofRaw B.val B.property
  let i := ComplexRawQuotient.ofRaw I.val I.property
  let x := ComplexRawQuotient.ofRaw X.val X.property
  let l := ComplexRawQuotient.ofRaw L.val L.property
  change b*i=1 at hi
  change b*l=x at hl
  change l=x*i
  calc l = l*(b*i) := by rw [hi]; grind only
       _ = (b*l)*i := by grind only
       _ = x*i := by rw [hl]

end ComputableAnalysis.ModularForms
