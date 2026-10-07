import ComputableAnalysis.ModularForms.LambertAgreement

/-! Actual Lambert factors at positive nome powers, with decaying bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def nomePowerScalar (z : Scalar) (n : Nat) : Scalar :=
  ⟨LocalODE.power z.val (n+1), LocalODE.power_valid _ z.property (n+1)⟩

def nomePowerRadius (r : Rat) (n : Nat) : Rat := (2*r)^(n+1)

theorem nomePowerRadius_nonneg (r : Rat) (hr : 0≤r) (n : Nat) :
    0≤nomePowerRadius r n :=
  Rat.pow_nonneg (Rat.mul_nonneg (by decide) hr)

theorem nomePowerRadius_le (r : Rat) (hr : 0≤r) (hsmall : 2*r≤1) (n : Nat) :
    nomePowerRadius r n≤2*r := by
  have hbase : 0≤2*r := Rat.mul_nonneg (by decide) hr
  have hp : ∀ k : Nat, (2*r)^k≤1 := by
    intro k
    induction k with
    | zero => rw [Rat.pow_zero]; exact Rat.le_refl
    | succ k ih =>
      rw [Rat.pow_succ]
      have hm := Rat.mul_le_mul_of_nonneg_right ih hbase
      grind only
  unfold nomePowerRadius
  rw [Rat.pow_succ]
  have hm := Rat.mul_le_mul_of_nonneg_right (hp n) hbase
  grind only

theorem nomePowerRadius_local (r : Rat) (hr : 0≤r) (hlocal : 4*r≤(1:Rat)/2)
    (n : Nat) : 2*nomePowerRadius r n≤(1:Rat)/2 := by
  have hsmall : 2*r≤1 := by grind only
  have hm := Rat.mul_le_mul_of_nonneg_left (nomePowerRadius_le r hr hsmall n)
    (show (0:Rat)≤2 by decide)
  grind only

theorem nomePowerScalar_small (z : Scalar) (r : Rat) (hr : 0≤r)
    (hz : Small z.val r) (n : Nat) : Small (nomePowerScalar z n).val (nomePowerRadius r n) :=
  LocalODE.power_small _ z.property r hr hz (n+1)

def nomeLambertPower (z : Scalar) (r : Rat) (n : Nat) : ComplexRaw :=
  lambertFactor (nomePowerScalar z n) (nomePowerRadius r n)

theorem nomeLambertPower_valid (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    (nomeLambertPower z r n).Valid :=
  lambertFactor_valid _ _ (nomePowerRadius_nonneg r hr n)
    (nomePowerRadius_local r hr hlocal n) (nomePowerScalar_small z r hr hz n)

theorem nomeLambertPower_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (nomeLambertPower z r n) (8*(2*r)^(n+1)) :=
  lambertFactor_bound _ _ (nomePowerRadius_nonneg r hr n)
    (nomePowerRadius_local r hr hlocal n) (nomePowerScalar_small z r hr hz n)

theorem nomeLambertPower_multiplication (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    (mul (sub (ofQComplex QComplex.one) (LocalODE.power z.val (n+1)))
      (nomeLambertPower z r n)).Equiv (LocalODE.power z.val (n+1)) :=
  lambertFactor_multiplication (nomePowerScalar z n) (nomePowerRadius r n) (nomePowerRadius_nonneg r hr n)
    (nomePowerRadius_local r hr hlocal n) (nomePowerScalar_small z r hr hz n)

theorem nomeLambertPower_congr (z w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrlocal : 4*r≤(1:Rat)/2) (hslocal : 4*s≤(1:Rat)/2)
    (hz : Small z.val r) (hw : Small w.val s) (hzw : z.val.Equiv w.val) (n : Nat) :
    (nomeLambertPower z r n).Equiv (nomeLambertPower w s n) :=
  lambertFactor_congr _ _ _ _ (nomePowerRadius_nonneg r hr n)
    (nomePowerRadius_nonneg s hs n) (nomePowerRadius_local r hr hrlocal n)
    (nomePowerRadius_local s hs hslocal n) (nomePowerScalar_small z r hr hz n)
    (nomePowerScalar_small w s hs hw n)
    (LocalODE.power_congr _ _ z.property w.property hzw (n+1))

end ComputableAnalysis.ModularForms
