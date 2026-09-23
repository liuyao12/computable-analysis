import ComputableAnalysis.FormalPowerSeriesAlgebra
import ComputableAnalysis.Series

/-! Finite rational sums used in the Basel comparison. -/
namespace ComputableAnalysis.Basel
open FormalPowerSeries

 theorem sum_shift (f : Nat → Rat) (n : Nat) :
    sumBelow f (n+1) = f 0 + sumBelow (fun k => f (k+1)) n := by
  induction n with
  | zero => simp [sumBelow_succ]; grind only
  | succ n ih => simp only [sumBelow_succ] at *; grind only

 theorem sum_block (f : Nat → Rat) (n m : Nat) :
    sumBelow f (n+m) = sumBelow f n + sumBelow (fun k => f (n+k)) m := by
  induction m with
  | zero => simp <;> grind only
  | succ m ih => rw [show n+(m+1)=(n+m)+1 by omega, sumBelow_succ, ih, sumBelow_succ]; grind only

 theorem sum_sub (f g : Nat → Rat) (n : Nat) :
    sumBelow (fun k => f k-g k) n = sumBelow f n-sumBelow g n := by
  induction n with
  | zero => simp <;> grind only
  | succ n ih => simp only [sumBelow_succ, ih]; grind only

 theorem sum_const (c : Rat) (n : Nat) : sumBelow (fun _ => c) n = (n:Rat)*c := by
  induction n with
  | zero => simp <;> grind only
  | succ n ih => simp only [sumBelow_succ, ih, Rat.natCast_add]; grind only

 theorem sum_le {f g : Nat → Rat} {n : Nat} (h : ∀ k, k<n → f k≤g k) :
    sumBelow f n ≤ sumBelow g n := by
  induction n with
  | zero => simp <;> grind only
  | succ n ih => rw [sumBelow_succ, sumBelow_succ]; have := ih (fun k hk => h k (by omega)); have := h n (by omega); grind only

 theorem sum_nonneg {f : Nat → Rat} {n : Nat} (h : ∀ k, k<n → 0≤f k) :
    0≤sumBelow f n := by
  have := sum_le (g:=f) (f:=fun _=>0) h
  simpa [sum_const] using this

 theorem sum_abs (f : Nat → Rat) (n : Nat) :
    qabs (sumBelow f n) ≤ sumBelow (fun k => qabs (f k)) n := by
  induction n with
  | zero => simp [qabs]
  | succ n ih => rw [sumBelow_succ, sumBelow_succ]; have := qabs_add_le (sumBelow f n) (f n); grind only

 theorem sum_reverse (f : Nat → Rat) (n : Nat) :
    sumBelow (fun k => f (n-1-k)) n = sumBelow f n := by
  induction n generalizing f with
  | zero => simp <;> grind only
  | succ n ih =>
    rw [sumBelow_succ]
    have h := ih (fun k => f (k+1))
    have he : sumBelow (fun k => f (n+1-1-k)) n = sumBelow (fun k => f (n-1-k+1)) n := by
      apply sumBelow_congr; intro k hk; congr 1; omega
    rw [he, h, sum_shift f n]
    simp
    grind only

 theorem sum_swap (f : Nat → Nat → Rat) (n m : Nat) :
    sumBelow (fun i => sumBelow (f i) m) n =
    sumBelow (fun j => sumBelow (fun i => f i j) n) m := by
  induction n with
  | zero => simp; rw [sum_const]; simp
  | succ n ih =>
    simp only [sumBelow_succ, ih]
    rw [sumBelow_add]

 theorem sum_triangle (f : Nat → Nat → Rat) (n : Nat) :
    sumBelow (fun i => sumBelow (fun j => f i j) (n-i)) n =
    sumBelow (fun d => sumBelow (fun i => f i (d-i)) (d+1)) n := by
  induction n with
  | zero => simp <;> grind only
  | succ n ih =>
    rw [sumBelow_succ]
    have he : sumBelow (fun i => sumBelow (f i) (n+1-i)) n =
        sumBelow (fun i => sumBelow (f i) (n-i) + f i (n-i)) n := by
      apply sumBelow_congr; intro i hi
      rw [show n+1-i=(n-i)+1 by omega, sumBelow_succ]
    rw [he, sumBelow_add, ih, sumBelow_succ, sumBelow_succ]
    rw [show n+1-n=1 by omega]
    simp only [Nat.sub_self, sumBelow_succ, sumBelow_zero, Rat.zero_add]
    grind only

 theorem sum_square (f : Nat → Nat → Rat) (n : Nat) :
    sumBelow (fun i => sumBelow (f i) n) n =
      sumBelow (fun i => f i i) n +
      sumBelow (fun i => sumBelow (fun j => f i (i+1+j) + f (i+1+j) i) (n-1-i)) n := by
  induction n with
  | zero => simp <;> grind only
  | succ n ih =>
    rw [sumBelow_succ]
    have he : sumBelow (fun i => sumBelow (f i) (n+1)) n =
      sumBelow (fun i => sumBelow (f i) n + f i n) n := by
      apply sumBelow_congr; intro i _; rw [sumBelow_succ]
    rw [he, sumBelow_add, ih, sumBelow_succ, sumBelow_succ]
    have ht : sumBelow (fun i => sumBelow (fun j => f i (i+1+j)+f (i+1+j) i) (n+1-1-i)) n =
      sumBelow (fun i => sumBelow (fun j => f i (i+1+j)+f (i+1+j) i) (n-1-i) + f i n + f n i) n := by
      apply sumBelow_congr; intro i hi
      rw [show n+1-1-i=(n-1-i)+1 by omega, sumBelow_succ]
      rw [show i+1+(n-1-i)=n by omega]
      grind only
    rw [sumBelow_succ (fun i => sumBelow (fun j => f i (i+1+j)+f (i+1+j) i) (n+1-1-i)), ht, sumBelow_add, sumBelow_add]
    simp only [show n+1-1-n=0 by omega, sumBelow_zero]
    grind only

 theorem sign_sq (n : Nat) : Series.alternatingSign n * Series.alternatingSign n = 1 := by
  unfold Series.alternatingSign; split <;> grind only

 theorem sign_succ (n : Nat) : Series.alternatingSign (n+1) = -Series.alternatingSign n := by
  unfold Series.alternatingSign
  by_cases h : n%2=0
  · have : (n+1)%2≠0 := by omega
    simp [h, this]
  · have : (n+1)%2=0 := by omega
    simp [h, this]

 theorem sum_signed (f : Nat → Rat) (n : Nat) :
    sumBelow (fun k => Series.alternatingSign k*f k) n = Series.partialSum f n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumBelow_succ, ih]; rfl

theorem alternating_shift (f : Nat → Rat) (n : Nat) :
    Series.partialSum f (n+1) = f 0-Series.partialSum (fun k=>f (k+1)) n := by
  induction n with
  | zero => simp [Series.partialSum, Series.signedTerm, Series.alternatingSign]; grind only
  | succ n ih =>
    rw [Series.partialSum, ih, Series.partialSum]
    simp only [Series.signedTerm, sign_succ]
    grind only

/-- Finite alternating sums of decreasing nonnegative magnitudes. -/
theorem alternating_decreasing (f : Nat → Rat) (n : Nat)
    (hn : ∀ k, 0≤f k) (hm : ∀ k, f (k+1)≤f k) :
    0 ≤ Series.partialSum f n ∧ Series.partialSum f n ≤ f 0 := by
  induction n generalizing f with
  | zero => simp only [Series.partialSum]; have := hn 0; grind only
  | succ n ih =>
    rw [alternating_shift]
    have ht := ih (fun k=>f (k+1)) (fun k=>hn _) (fun k=>hm _)
    have := hm 0
    grind only

/-- Increasing magnitudes: the signed sum lies between zero and its last term. -/
theorem alternating_increasing (f : Nat → Rat) (n : Nat)
    (hn : ∀ k, k≤n → 0≤f k) (hm : ∀ k, k<n → f k≤f (k+1)) :
    0 ≤ Series.alternatingSign n * Series.partialSum f (n+1) ∧
    Series.alternatingSign n * Series.partialSum f (n+1) ≤ f n := by
  induction n with
  | zero => simp [Series.partialSum, Series.signedTerm, Series.alternatingSign]; have := hn 0 (by omega); grind only
  | succ n ih =>
    have ht := ih (fun k hk=>hn k (by omega)) (fun k hk=>hm k (by omega))
    have := hm n (by omega)
    have := sign_sq n
    rw [Series.partialSum, Series.signedTerm, sign_succ]
    unfold Series.alternatingSign at *
    split at ht <;> simp_all <;> grind only

theorem triangle_swap (f : Nat → Nat → Rat) (n : Nat) :
    sumBelow (fun i => sumBelow (f i) (n-i)) n =
    sumBelow (fun j => sumBelow (fun i => f i j) (n-j)) n := by
  rw [sum_triangle, sum_triangle]
  apply sumBelow_congr; intro d _
  rw [← sum_reverse (fun i => f (d-i) i) (d+1)]
  apply sumBelow_congr; intro i hi
  simp only [show d+1-1-i=d-i by omega, show d-(d-i)=i by omega]

end ComputableAnalysis.Basel
