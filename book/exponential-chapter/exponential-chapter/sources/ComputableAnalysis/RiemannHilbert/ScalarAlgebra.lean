import ComputableAnalysis.ComplexRawQuotient
import ComputableAnalysis.RiemannHilbert.LocalODEMajorant

/-!
Proof-facing finite algebra on certified represented values. The quotient
identifies valid names; it does not construct a completion or an analytic limit.
-/
namespace ComputableAnalysis.RiemannHilbert.ScalarAlgebra
abbrev Value := ComplexRawQuotient.Value

def natural : Nat → Value
  | 0 => 0
  | 1 => 1
  | n+2 => natural (n+1) + 1

theorem natural_succ (n : Nat) : natural (n+1) = natural n + 1 := by
  cases n with
  | zero => exact (ComplexRawQuotient.zero_add _).symm
  | succ n => rfl

def power (x : Value) : Nat → Value
  | 0 => 1
  | n+1 => power x n * x

instance : NatCast Value where natCast := natural
instance (n : Nat) : OfNat Value n where ofNat := natural n
instance : SMul Nat Value where smul n x := natural n * x
instance : HPow Value Nat Value where hPow := power

instance : Lean.Grind.CommSemiring Value where
  add := ComplexRawQuotient.add
  mul := ComplexRawQuotient.mul
  natCast := inferInstance
  ofNat := fun n => inferInstance
  nsmul := inferInstance
  npow := inferInstance
  add_zero := ComplexRawQuotient.add_zero
  add_comm := ComplexRawQuotient.add_comm
  add_assoc := ComplexRawQuotient.add_assoc
  mul_assoc := ComplexRawQuotient.mul_assoc
  mul_one := ComplexRawQuotient.mul_one
  one_mul := ComplexRawQuotient.one_mul
  left_distrib := ComplexRawQuotient.mul_add
  right_distrib := ComplexRawQuotient.add_mul
  zero_mul := ComplexRawQuotient.zero_mul
  mul_zero := ComplexRawQuotient.mul_zero
  mul_comm := ComplexRawQuotient.mul_comm
  pow_zero := fun _ => rfl
  pow_succ := fun _ _ => rfl
  ofNat_succ := natural_succ

theorem ofRaw_power (z : ComplexRaw) (hz : z.Valid) (n : Nat) :
    ComplexRawQuotient.ofRaw (LocalODE.power z n) (LocalODE.power_valid z hz n) = (ComplexRawQuotient.ofRaw z hz)^n := by
  induction n with
  | zero => rfl
  | succ n ih => change ComplexRawQuotient.ofRaw (LocalODE.power z n) (LocalODE.power_valid z hz n) * ComplexRawQuotient.ofRaw z hz = _
                 rw [ih]; rfl

theorem add_sub_cancel (x y : Value) : y + (x + -y) = x := by
  rw [ComplexRawQuotient.add_comm x (-y), ← ComplexRawQuotient.add_assoc, ComplexRawQuotient.add_neg, ComplexRawQuotient.zero_add]

theorem sub_add_cancel (x y : Value) : (x + y) + -y = x := by
  rw [ComplexRawQuotient.add_assoc, ComplexRawQuotient.add_neg, ComplexRawQuotient.add_zero]


theorem natural_scale (n : Nat) :
    natural n = ComplexRawQuotient.scaleRat (n : Rat) 1 := by
  induction n with
  | zero => exact (ComplexRawQuotient.scaleRat_zeroScalar _).symm
  | succ n ih =>
    rw [natural_succ, ih]
    have hc : ((n+1 : Nat) : Rat) = (n : Rat)+1 := by exact_mod_cast Nat.add_one n
    rw [hc, ← ComplexRawQuotient.add_scaleRat, ComplexRawQuotient.scaleRat_one]
    rfl

theorem scale_natural (n : Nat) (x : Value) :
    ComplexRawQuotient.scaleRat (n : Rat) x = (n : Value)*x := by
  change ComplexRawQuotient.scaleRat (n : Rat) x = natural n * x
  rw [natural_scale, ← ComplexRawQuotient.scaleRat_mul]
  congr 1
  exact (ComplexRawQuotient.one_mul x).symm


instance : IntCast Value where
  intCast i := ComplexRawQuotient.scaleRat (i : Rat) 1
instance : SMul Int Value where
  smul i x := ComplexRawQuotient.scaleRat (i : Rat) x

instance : Lean.Grind.CommRing Value where
  toSemiring := inferInstance
  neg := ComplexRawQuotient.neg
  sub x y := x + -y
  intCast := inferInstance
  zsmul := inferInstance
  neg_add_cancel := fun x => (ComplexRawQuotient.add_comm (-x) x).trans (ComplexRawQuotient.add_neg x)
  sub_eq_add_neg := by intros; rfl
  neg_zsmul := by
    intro i x
    change ComplexRawQuotient.scaleRat ((-i : Int) : Rat) x =
      -ComplexRawQuotient.scaleRat (i : Rat) x
    rw [Rat.intCast_neg]
    exact (ComplexRawQuotient.neg_scaleRat _ _).symm
  zsmul_natCast_eq_nsmul := by
    intro n x
    change ComplexRawQuotient.scaleRat ((n : Int) : Rat) x = (n : Value)*x
    rw [Rat.intCast_natCast]
    exact scale_natural n x
  intCast_ofNat := by
    intro n
    change ComplexRawQuotient.scaleRat ((n : Int) : Rat) 1 = natural n
    rw [Rat.intCast_natCast]
    exact (natural_scale n).symm
  intCast_neg := by
    intro i
    change ComplexRawQuotient.scaleRat ((-i : Int) : Rat) 1 =
      -ComplexRawQuotient.scaleRat (i : Rat) 1
    rw [Rat.intCast_neg]
    exact (ComplexRawQuotient.neg_scaleRat _ _).symm
  mul_comm := ComplexRawQuotient.mul_comm

theorem ring_example (x y z : Value) : (x-y)*z = x*z-y*z := by grind

theorem extract_remainder (x y r : Value) :
    ((x+y+r)+ -x)+ -y = r := by
  rw [ComplexRawQuotient.add_assoc x y r,
    ComplexRawQuotient.add_comm (x+(y+r)) (-x),
    ← ComplexRawQuotient.add_assoc (-x) x (y+r),
    ComplexRawQuotient.add_comm (-x) x,
    ComplexRawQuotient.add_neg, ComplexRawQuotient.zero_add,
    ComplexRawQuotient.add_comm y r,
    ComplexRawQuotient.add_assoc, ComplexRawQuotient.add_neg,
    ComplexRawQuotient.add_zero]

theorem add_left_comm (x y z : Value) : x+(y+z)=y+(x+z) := by
  rw [← ComplexRawQuotient.add_assoc, ComplexRawQuotient.add_comm x y, ComplexRawQuotient.add_assoc]

theorem mul_left_comm (x y z : Value) : x*(y*z)=y*(x*z) := by
  rw [← ComplexRawQuotient.mul_assoc, ComplexRawQuotient.mul_comm x y, ComplexRawQuotient.mul_assoc]

end ComputableAnalysis.RiemannHilbert.ScalarAlgebra
