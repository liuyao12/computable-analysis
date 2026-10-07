import ComputableAnalysis.ModularForms.CMOrbitLatticeReciprocal163
import ComputableAnalysis.RiemannHilbert.LocalODESum

/-! Exact inverse-power transformation at modular transforms of the CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

private theorem valuePower_mul (x y : ScalarAlgebra.Value) (k : Nat) :
    (x*y)^k=x^k*y^k := by
  induction k with
  | zero => change 1=1*1; grind
  | succ k ih =>
    change (x*y)^k*(x*y)=(x^k*x)*(y^k*y)
    rw [ih]
    grind

/-- Natural powers preserve multiplication at every pair of valid represented inputs. -/
theorem representedPower_mul (x y : ComplexRaw) (hx : x.Valid) (hy : y.Valid) (k : Nat) :
    (LocalODE.power (ComplexRaw.mul x y) k).Equiv
      (ComplexRaw.mul (LocalODE.power x k) (LocalODE.power y k)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := LocalODE.power_valid _ (ComplexRaw.mul_valid hx hy) k)
    (hright := ComplexRaw.mul_valid (LocalODE.power_valid x hx k) (LocalODE.power_valid y hy k))
  rw [ScalarAlgebra.ofRaw_power _ (ComplexRaw.mul_valid hx hy) k,ComplexRawQuotient.ofRaw_mul _ _ hx hy,
    ComplexRawQuotient.ofRaw_mul _ _ (LocalODE.power_valid x hx k) (LocalODE.power_valid y hy k),
    ScalarAlgebra.ofRaw_power x hx k,ScalarAlgebra.ofRaw_power y hy k]
  exact valuePower_mul _ _ k

/-- Each inverse-power lattice term gains precisely the corresponding power
of the automorphy denominator. -/
theorem cmOrbitLatticeInverse163_power_transform (g : SL2Z) (u : QuadraticOrder163)
    (hu : u≠zero) (k : Nat) :
    (LocalODE.power (cmOrbitLatticeInverse163 g u hu).val k).Equiv
      (ComplexRaw.mul (LocalODE.power (cmOrbitDenominator163 g).val k)
        (LocalODE.power
          (complexInverse (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)).val k)) := by
  let inv := complexInverse (basisIndex (latticeIndexMatrix g) u) (basisIndex_nonzero _ u hu)
  exact ComplexRaw.equiv_trans
    (LocalODE.power_valid _ (cmOrbitLatticeInverse163 g u hu).property k)
    (LocalODE.power_valid _ (ComplexRaw.mul_valid (cmOrbitDenominator163 g).property inv.property) k)
    (ComplexRaw.mul_valid (LocalODE.power_valid _ (cmOrbitDenominator163 g).property k)
      (LocalODE.power_valid _ inv.property k))
    (LocalODE.power_congr _ _ (cmOrbitLatticeInverse163 g u hu).property
      (ComplexRaw.mul_valid (cmOrbitDenominator163 g).property inv.property)
      (cmOrbitLatticeInverse163_transform g u hu) k)
    (representedPower_mul _ _ (cmOrbitDenominator163 g).property inv.property k)

end ComputableAnalysis.ModularForms
