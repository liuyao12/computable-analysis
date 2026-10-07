import ComputableAnalysis.ModularForms.LambertPowers

/-! Composition of actual represented nome powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem value_power_power (x : ScalarAlgebra.Value) (a b : Nat) :
    (x^a)^b=x^(a*b) := by
  induction b with
  | zero => simp only [Nat.mul_zero, Lean.Grind.Semiring.pow_zero]
  | succ b ih =>
    rw [Lean.Grind.Semiring.pow_succ, ih, Nat.mul_succ, Lean.Grind.Semiring.pow_add]

/-- Iterated raw powers agree with the single product exponent. -/
theorem representedPower_power (z : Scalar) (a b : Nat) :
    (LocalODE.power (LocalODE.power z.val a) b).Equiv (LocalODE.power z.val (a*b)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := LocalODE.power_valid _ (LocalODE.power_valid _ z.property a) b)
    (hright := LocalODE.power_valid _ z.property (a*b))
  rw [ScalarAlgebra.ofRaw_power _ (LocalODE.power_valid _ z.property a),
    ScalarAlgebra.ofRaw_power _ z.property, ScalarAlgebra.ofRaw_power _ z.property]
  exact value_power_power _ a b

/-- Swapping the two positive exponents preserves the represented power. -/
theorem nomePowerScalar_power_comm (z : Scalar) (n m : Nat) :
    (LocalODE.power (nomePowerScalar z n).val (m+1)).Equiv
      (LocalODE.power (nomePowerScalar z m).val (n+1)) := by
  have h := representedPower_power z (n+1) (m+1)
  have g := representedPower_power z (m+1) (n+1)
  rw [Nat.mul_comm (m+1) (n+1)] at g
  exact equiv_trans (LocalODE.power_valid _ (nomePowerScalar z n).property (m+1))
    (LocalODE.power_valid _ z.property ((n+1)*(m+1)))
    (LocalODE.power_valid _ (nomePowerScalar z m).property (n+1)) h
    (equiv_symm g)

end ComputableAnalysis.ModularForms
