import ComputableAnalysis.ModularForms.ExponentialAddition
import ComputableAnalysis.ModularForms.ExponentialDerivative

/-! Integer-multiple exponential laws, needed to turn a quarter rotation
into a full period. The geometric quarter-turn identity is not assumed. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem entireExponential_nat_multiple (z : Scalar) (n : Nat) :
    (entireExponentialValue ⟨scaleRat (n : Rat) z.val, scaleRat_valid z.property⟩).val.Equiv
      (LocalODE.power (entireExponentialValue z).val n) := by
  induction n with
  | zero =>
    have hz := scaleRat_zeroScalar_equiv z.val z.property
    exact equiv_trans
      (entireExponentialValue ⟨scaleRat 0 z.val, scaleRat_valid z.property⟩).property
      (entireExponentialValue ⟨zero,ofQComplex_valid _⟩).property (ofQComplex_valid _)
      (entireExponentialValue_congr _ _ hz) entireExponential_zero
  | succ n ih =>
    let a : Scalar := ⟨scaleRat (n : Rat) z.val, scaleRat_valid z.property⟩
    let b : Scalar := ⟨add a.val z.val, add_valid a.property z.property⟩
    let c : Scalar := ⟨scaleRat ((n+1 : Nat) : Rat) z.val, scaleRat_valid z.property⟩
    have hbc : b.val.Equiv c.val := by
      have h := add_scaleRat_equiv (n : Rat) 1 z.val z.property
      have h1 := scaleRat_one_equiv z.val z.property
      have ha := add_equiv (equiv_refl a.val a.property) (equiv_symm h1)
      have he : (n : Rat)+1=((n+1 : Nat) : Rat) := by rw [Rat.natCast_add]; rfl
      rw [he] at h
      exact equiv_trans b.property
        (add_valid a.property (scaleRat_valid z.property)) c.property ha h
    have hp := entireExponential_addition a z
    have hm := mul_equiv (entireExponentialValue a).property
      (LocalODE.power_valid _ (entireExponentialValue z).property n)
      (entireExponentialValue z).property (entireExponentialValue z).property
      ih (equiv_refl _ (entireExponentialValue z).property)
    exact equiv_trans (entireExponentialValue c).property
      (entireExponentialValue b).property
      (LocalODE.power_valid _ (entireExponentialValue z).property (n+1))
      (entireExponentialValue_congr c b (equiv_symm hbc))
      (equiv_trans (entireExponentialValue b).property
        (mul_valid (entireExponentialValue a).property (entireExponentialValue z).property)
        (LocalODE.power_valid _ (entireExponentialValue z).property (n+1))
        (equiv_symm hp) hm)

end ComputableAnalysis.ModularForms
