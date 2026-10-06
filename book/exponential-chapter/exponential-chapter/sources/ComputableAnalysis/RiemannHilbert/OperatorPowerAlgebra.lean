import ComputableAnalysis.RiemannHilbert.NeumannOperatorAgreement
import ComputableAnalysis.RiemannHilbert.ExponentialInverse
import ComputableAnalysis.RiemannHilbert.LocalLogarithmDerivative

/-! Exact power identities for represented linear operators. Scalar scaling,
negation and intertwiners act on finite powers without any analytic limit. -/
namespace ComputableAnalysis.RiemannHilbert.OperatorPower
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n m : Nat}
set_option maxHeartbeats 1000000

theorem intertwines (E : ValueMap (Fiber n) (Fiber n)) (F : ValueMap (Fiber m) (Fiber m))
    (N : ValueMap (Fiber n) (Fiber m)) (hEF : ∀ x, N.eval (E.eval x) ≈ F.eval (N.eval x)) (x : Fiber n) (k : Nat) :
    N.eval ((Neumann.power E k).eval x) ≈ (Neumann.power F k).eval (N.eval x) := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih => exact Setoid.trans (hEF _) (F.congr ih)

theorem commutes (E : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (k : Nat) :
    E.eval ((Neumann.power E k).eval x) ≈ (Neumann.power E k).eval (E.eval x) :=
  intertwines E E E (fun _ => Setoid.refl _) x k

def scaled (E : ValueMap (Fiber n) (Fiber n)) (a : Scalar) := E.followedBy (Fiber.scaleMap a)

theorem scaled_linear (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (a : Scalar) :
    IsLinear (scaled E a) := IsLinear.followedBy hE (Fiber.scaleMap_linear a)

theorem power_scaled (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (a : Scalar) (x : Fiber n) (k : Nat) :
    (Neumann.power (scaled E a) k).eval x ≈ Fiber.scale ⟨power a.val k,power_valid a.val a.property k⟩ ((Neumann.power E k).eval x) := by
  induction k with
  | zero => exact fun i => equiv_symm (one_mul_equiv _ (x.property i))
  | succ k ih =>
    have h1 := Fiber.scale_congr (equiv_refl _ a.property)
      (Setoid.trans (E.congr ih) (hE.2 ⟨power a.val k,power_valid a.val a.property k⟩ ((Neumann.power E k).eval x)))
    have h2 := Fiber.scale_scale a ⟨power a.val k,power_valid a.val a.property k⟩ (E.eval ((Neumann.power E k).eval x))
    have h3 : Fiber.scale ⟨mul a.val (power a.val k),mul_valid a.property (power_valid a.val a.property k)⟩
        (E.eval ((Neumann.power E k).eval x)) ≈
        Fiber.scale ⟨power a.val (k+1),power_valid a.val a.property (k+1)⟩ (E.eval ((Neumann.power E k).eval x)) :=
      Fiber.scale_congr (mul_comm_equiv _ _ a.property (power_valid a.val a.property k))
      (Setoid.refl (E.eval ((Neumann.power E k).eval x)))
    exact Setoid.trans h1 (Setoid.trans h2 h3)

theorem power_negative (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (x : Fiber n) (k : Nat) :
    (Neumann.power (MatrixExponential.negativeOperator E) k).eval x ≈
      ratScale (FormalPowerSeries.altSign k) ((Neumann.power E k).eval x) := by
  induction k with
  | zero => exact fun i => equiv_symm (scaleRat_one_equiv _ (x.property i))
  | succ k ih =>
    have h1 := MatrixExponential.negativeOperator_value E ((Neumann.power (MatrixExponential.negativeOperator E) k).eval x)
    have h2 : Fiber.neg (E.eval ((Neumann.power (MatrixExponential.negativeOperator E) k).eval x)) ≈
        Fiber.neg (ratScale (FormalPowerSeries.altSign k) (E.eval ((Neumann.power E k).eval x))) :=
      fun i => neg_equiv (Setoid.trans (E.congr ih) (MatrixExponential.linear_ratScale E hE _ _) i)
    have h3 : Fiber.neg (ratScale (FormalPowerSeries.altSign k) (E.eval ((Neumann.power E k).eval x))) ≈
        ratScale (FormalPowerSeries.altSign (k+1)) ((Neumann.power E (k+1)).eval x) := by
      intro i
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := (Fiber.neg (ratScale (FormalPowerSeries.altSign k) (E.eval ((Neumann.power E k).eval x)))).property i)
        (hright := (ratScale (FormalPowerSeries.altSign (k+1)) ((Neumann.power E (k+1)).eval x)).property i)
      change -ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign k)
        (ComplexRawQuotient.ofRaw ((E.eval ((Neumann.power E k).eval x)).val i) ((E.eval ((Neumann.power E k).eval x)).property i)) =
        ComplexRawQuotient.scaleRat (FormalPowerSeries.altSign (k+1))
        (ComplexRawQuotient.ofRaw ((E.eval ((Neumann.power E k).eval x)).val i) ((E.eval ((Neumann.power E k).eval x)).property i))
      rw [ComplexRawQuotient.neg_scaleRat,LocalLogarithm.altSign_succ]
    exact Setoid.trans h1 (Setoid.trans h2 h3)

theorem negative_scaled_power (E : ValueMap (Fiber n) (Fiber n)) (hE : IsLinear E) (z : Scalar) (x : Fiber n) (k : Nat) :
    (Neumann.power (scaled (MatrixExponential.negativeOperator E) z) k).eval (E.eval x) ≈
      Fiber.scale ⟨power z.val k,power_valid z.val z.property k⟩
        (ratScale (FormalPowerSeries.altSign k) ((Neumann.power E (k+1)).eval x)) :=
  Setoid.trans (power_scaled _ (MatrixExponential.negativeOperator_linear E hE) z (E.eval x) k)
    (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property k))
      (Setoid.trans (power_negative E hE (E.eval x) k) (ratScale_congr _ (Setoid.symm (commutes E x k)))))

end ComputableAnalysis.RiemannHilbert.OperatorPower
