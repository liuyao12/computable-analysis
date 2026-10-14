import ComputableAnalysis.ModularForms.TauAbsoluteMajorant
import ComputableAnalysis.ModularForms.TauFiniteProductEvaluation

/-! Finite rational weighted sums for positive Euler coefficient majorants. -/
namespace ComputableAnalysis.ModularForms

def positiveCoefficientWeight (a : Nat → Nat) (r : Rat) : Nat → Rat
  | 0 => 0
  | L+1 => positiveCoefficientWeight a r L+(a L:Rat)*r^L

private theorem power_add (r : Rat) (m n : Nat) : r^(m+n)=r^m*r^n := by
  induction n with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ n ih =>
    change r^((m+n)+1)=r^m*r^(n+1)
    rw [Rat.pow_succ,ih,Rat.pow_succ]
    grind only

/-- Exact finite weighted evaluation of a positive shifted factor. -/
theorem positiveCoefficientWeight_addShift (a : Nat → Nat) (r : Rat) (m L : Nat) :
    positiveCoefficientWeight (addShift m a) r L=
      positiveCoefficientWeight a r L+r^m*positiveCoefficientWeight a r (L-m) := by
  induction L with
  | zero => simp only [positiveCoefficientWeight,Nat.zero_sub,Rat.mul_zero,Rat.add_zero]
  | succ L ih =>
    by_cases h : m≤L
    · have hs : L+1-m=(L-m)+1 := by omega
      have he : L=m+(L-m) := by omega
      rw [positiveCoefficientWeight,ih,hs,positiveCoefficientWeight,positiveCoefficientWeight]
      simp only [addShift,if_pos h,Rat.natCast_add]
      have hp : r^L=r^m*r^(L-m) := by
        calc r^L = r^(m+(L-m)) := congrArg (fun k => r^k) he
             _ = r^m*r^(L-m) := power_add r m (L-m)
      rw [hp]
      grind only
    · have hl : L-m=0 := by omega
      have hs : L+1-m=0 := by omega
      rw [positiveCoefficientWeight,ih,hl,hs,positiveCoefficientWeight,positiveCoefficientWeight]
      simp only [addShift,if_neg h,Rat.mul_zero,Rat.add_zero]

theorem positiveCoefficientWeight_nonnegative (a : Nat → Nat) (r : Rat)
    (hr : 0≤r) (L : Nat) : 0≤positiveCoefficientWeight a r L := by
  induction L with
  | zero => exact Rat.le_refl
  | succ L ih => exact Rat.add_nonneg ih (Rat.mul_nonneg Rat.natCast_nonneg (Rat.pow_nonneg hr))

/-- Increasing the degree cutoff only increases a nonnegative weighted sum. -/
theorem positiveCoefficientWeight_mono (a : Nat → Nat) (r : Rat) (hr : 0≤r)
    (K L : Nat) (hKL : K≤L) : positiveCoefficientWeight a r K≤positiveCoefficientWeight a r L := by
  induction L with
  | zero =>
    have he : K=0 := by omega
    subst K
    exact Rat.le_refl
  | succ L ih =>
    by_cases h : K≤L
    · have hs : positiveCoefficientWeight a r L≤positiveCoefficientWeight a r (L+1) := by
        have hp := Rat.mul_nonneg (Rat.natCast_nonneg : 0≤(a L:Rat)) (Rat.pow_nonneg hr : 0≤r^L)
        change positiveCoefficientWeight a r L≤positiveCoefficientWeight a r L+(a L:Rat)*r^L
        grind only
      exact Rat.le_trans (ih h) hs
    · have he : K=L+1 := by omega
      subst K
      exact Rat.le_refl

/-- A positive shifted factor multiplies any finite weighted bound by at most its value. -/
theorem positiveCoefficientWeight_addShift_bound (a : Nat → Nat) (r : Rat) (hr : 0≤r) (m L : Nat) :
    positiveCoefficientWeight (addShift m a) r L≤(1+r^m)*positiveCoefficientWeight a r L := by
  rw [positiveCoefficientWeight_addShift]
  have hm := Rat.mul_le_mul_of_nonneg_left
    (positiveCoefficientWeight_mono a r hr (L-m) L (by omega)) (Rat.pow_nonneg hr : 0≤r^m)
  grind only

end ComputableAnalysis.ModularForms
