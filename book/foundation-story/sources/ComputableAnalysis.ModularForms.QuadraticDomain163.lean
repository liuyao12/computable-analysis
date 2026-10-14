import ComputableAnalysis.ModularForms.QuadraticUnits163

/-! No zero divisors and cancellation in the concrete quadratic order. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

theorem mul_zero (u : QuadraticOrder163) : mul u zero=zero := by
  apply ext <;> simp [mul,zero]

theorem zero_mul (u : QuadraticOrder163) : mul zero u=zero := by
  rw [mul_comm,mul_zero]

theorem mul_eq_zero_iff (u v : QuadraticOrder163) :
    mul u v=zero ↔ u=zero ∨ v=zero := by
  constructor
  · intro huv
    by_cases hu : u=zero
    · exact Or.inl hu
    · right
      by_cases hv : v=zero
      · exact hv
      · have hp := Int.mul_pos (norm_positive u hu) (norm_positive v hv)
        have hn := norm_mul u v
        rw [huv] at hn
        change 0=norm u*norm v at hn
        omega
  · intro h
    rcases h with hu | hv
    · rw [hu,zero_mul]
    · rw [hv,mul_zero]

def sub (u v : QuadraticOrder163) : QuadraticOrder163 := add u (neg v)

theorem sub_eq_zero_iff (u v : QuadraticOrder163) : sub u v=zero ↔ u=v := by
  constructor
  · intro h
    have hx := congrArg QuadraticOrder163.x h
    have hy := congrArg QuadraticOrder163.y h
    simp only [sub,add,neg,zero] at hx hy
    apply ext <;> omega
  · intro h
    rw [h]
    apply ext <;> simp only [sub,add,neg,zero] <;> omega

theorem mul_sub (u v w : QuadraticOrder163) :
    mul u (sub v w)=sub (mul u v) (mul u w) := by
  apply ext <;> simp only [mul,sub,add,neg] <;> grind

theorem mul_left_cancel (u v w : QuadraticOrder163) (hu : u≠zero)
    (h : mul u v=mul u w) : v=w := by
  have hz : mul u (sub v w)=zero := by
    rw [mul_sub]
    exact (sub_eq_zero_iff _ _).mpr h
  have hs := (mul_eq_zero_iff u (sub v w)).mp hz
  rcases hs with hs | hs
  · exact False.elim (hu hs)
  · exact (sub_eq_zero_iff v w).mp hs

theorem mul_right_cancel (u v w : QuadraticOrder163) (hu : u≠zero)
    (h : mul v u=mul w u) : v=w := by
  apply mul_left_cancel u v w hu
  rw [mul_comm u v,mul_comm u w]
  exact h

end ComputableAnalysis.ModularForms.QuadraticOrder163
