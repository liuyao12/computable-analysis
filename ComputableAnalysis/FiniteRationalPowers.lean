import ComputableAnalysis.Basic

/-! Finite power identities used by the shared algebra of the moment argument. -/
namespace ComputableAnalysis.FiniteRationalPowers

theorem one_pow (n : Nat) : (1:Rat)^n=1 := by
  induction n with
  | zero => exact Rat.pow_zero _
  | succ n ih => rw [Rat.pow_succ,ih,Rat.mul_one]

theorem zero_pow {n : Nat} (hn : 0<n) : (0:Rat)^n=0 := by
  cases n with
  | zero => omega
  | succ n => rw [Rat.pow_succ,Rat.mul_zero]

theorem pow_add (x : Rat) (n m : Nat) : x^(n+m)=x^n*x^m := by
  induction m with
  | zero => rw [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ m ih =>
    rw [show n+(m+1)=(n+m)+1 by omega,Rat.pow_succ,ih,Rat.pow_succ,Rat.mul_assoc]

theorem pow_mul (x : Rat) (n m : Nat) : x^(n*m)=(x^n)^m := by
  induction m with
  | zero => rw [Nat.mul_zero,Rat.pow_zero,Rat.pow_zero]
  | succ m ih =>
    rw [Nat.mul_add,Nat.mul_one,pow_add,ih,Rat.pow_succ]

theorem mul_pow (x y : Rat) (n : Nat) : (x*y)^n=x^n*y^n := by
  induction n with
  | zero => rw [Rat.pow_zero,Rat.pow_zero,Rat.pow_zero,Rat.one_mul]
  | succ n ih => rw [Rat.pow_succ,ih,Rat.pow_succ,Rat.pow_succ];grind only

theorem pow_nonneg {x : Rat} (hx : 0≤x) (n : Nat) : 0≤x^n := by
  induction n with
  | zero => rw [Rat.pow_zero];decide
  | succ n ih => rw [Rat.pow_succ];exact Rat.mul_nonneg ih hx

theorem abs_pow (x : Rat) (n : Nat) : qabs (x^n)=(qabs x)^n := by
  induction n with
  | zero => rw [Rat.pow_zero,Rat.pow_zero];decide +kernel
  | succ n ih => rw [Rat.pow_succ,qabs_mul,ih,Rat.pow_succ]

theorem pow_mono {x y : Rat} (hx : 0≤x) (hxy : x≤y) (n : Nat) : x^n≤y^n := by
  induction n with
  | zero => rw [Rat.pow_zero,Rat.pow_zero];exact Rat.le_refl
  | succ n ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hx)
      (Rat.mul_le_mul_of_nonneg_left hxy (pow_nonneg (Rat.le_trans hx hxy) n))

end ComputableAnalysis.FiniteRationalPowers
