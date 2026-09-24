import ComputableAnalysis.PowerSeries

/-! Finite Taylor sums and a quantitative obstruction to convergence outside
arctangent's unit interval. No completed real type or infinite-sum definition
is used. The obstruction concerns actual consecutive polynomial sums. -/
namespace ComputableAnalysis.ArctanTaylor

def term (x : Rat) (n : Nat) : Rat := (-x*x)^n*x/(2*(n:Rat)+1)

def partialSum (x : Rat) : Nat → Rat
  | 0 => 0
  | n+1 => partialSum x n + term x n

/-- The ordinary Cauchy condition for rational samples. -/
def IsCauchy (s : Nat → Rat) : Prop :=
  ∀ eps : QPos, ∃ N, ∀ n m, N ≤ n → N ≤ m → qabs (s n-s m) ≤ eps.val

/-- Approximation to a represented value: every output box meets the
specified error interval around each sufficiently late partial sum. -/
def ConvergesTo (s : Nat → Rat) (v : RealRaw) : Prop :=
  v.Valid ∧ ∀ eps : QPos, ∃ N, ∀ n, N ≤ n → ∀ k,
    (v.compute k).lo ≤ s n+eps.val ∧ s n-eps.val ≤ (v.compute k).hi

theorem convergesTo_isCauchy {s : Nat → Rat} {v : RealRaw}
    (h : ConvergesTo s v) : IsCauchy s := by
  intro eps
  let e : QPos := ⟨eps.val/4, by have := eps.property; grind⟩
  obtain ⟨N,hN⟩ := h.2 e
  obtain ⟨K,hK⟩ := h.1.2.2 e
  refine ⟨N,?_⟩
  intro n m hn hm
  have ha := hN n hn K
  have hb := hN m hm K
  have hw := hK K (Nat.le_refl _)
  simp only [QInterval.width,e] at *
  unfold qabs
  split <;> grind

/-- Bernoulli's finite inequality, with a rational nonnegative increment. -/
theorem bernoulli (d : Rat) (hd : 0 ≤ d) (n : Nat) :
    1+(n:Rat)*d ≤ (1+d)^n := by
  induction n with
  | zero => simp; grind
  | succ n ih =>
    have hm := Rat.mul_le_mul_of_nonneg_right ih (show 0 ≤ 1+d by grind)
    have hs := Rat.mul_nonneg (Rat.mul_nonneg (Rat.natCast_nonneg (a:=n)) hd) hd
    rw [Rat.pow_succ]
    simp only [Rat.natCast_add] at *
    grind

theorem abs_term (x : Rat) (n : Nat) :
    qabs (term x n) = (qabs x*qabs x)^n*qabs x/(2*(n:Rat)+1) := by
  have hd : 0 < 2*(n:Rat)+1 := by have := Rat.natCast_nonneg (a:=n); grind
  simp only [term,Rat.div_def,qabs_mul,RationalMajorant.qabs_pow_eq_pow_qabs,qabs_neg]
  rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (Rat.inv_pos.mpr hd))]

/-- A fixed positive lower bound for every term after the linear term.
It suffices to refute convergence, even arbitrarily close to the boundary. -/
theorem term_lower_bound {x : Rat} (hx : 1 < qabs x) (n : Nat) (hn : 1 ≤ n) :
    qabs x*(qabs x*qabs x-1)/3 ≤ qabs (term x n) := by
  let y := qabs x
  have hy : 1 < y := hx
  have hy0 : 0 < y := by grind
  have hyy := Rat.mul_lt_mul_of_pos_right hy hy0
  have hd : 0 < y*y-1 := by grind
  have hb := bernoulli (y*y-1) (Rat.le_of_lt hd) n
  have hn1 : (1:Rat) ≤ (n:Rat) := by exact_mod_cast hn
  have he : 1+(y*y-1) = y*y := by grind
  rw [he] at hb
  rw [abs_term]
  change y*(y*y-1)/3 ≤ (y*y)^n*y/(2*(n:Rat)+1)
  have hm := Rat.mul_le_mul_of_nonneg_right hb (show 0 ≤ y by grind)
  have hp : 0 < 2*(n:Rat)+1 := by grind
  have hbonus := Rat.mul_nonneg (Rat.mul_nonneg (show 0 ≤ (n:Rat)-1 by grind) (Rat.le_of_lt hd)) (Rat.le_of_lt hy0)
  have hi := Rat.mul_inv_cancel (2*(n:Rat)+1) (Rat.ne_of_gt hp)
  apply Rat.le_of_mul_le_mul_right (c:=2*(n:Rat)+1) _ hp
  simp only [Rat.div_def]
  have hc : ((y*y)^n*y*(2*(n:Rat)+1)⁻¹)*(2*(n:Rat)+1) = (y*y)^n*y := by
    rw [Rat.mul_assoc, Rat.inv_mul_cancel _ (Rat.ne_of_gt hp), Rat.mul_one]
  change (y*(y*y-1)*3⁻¹)*(2*(n:Rat)+1) ≤ _
  rw [hc]
  apply Rat.le_of_mul_le_mul_right (c:=3) _ (by decide)
  have hm3 := Rat.mul_le_mul_of_nonneg_right hm (show (0:Rat) ≤ 3 by decide)
  have hthree : (3:Rat)⁻¹*3 = 1 := Rat.inv_mul_cancel 3 (by decide)
  grind only

theorem partialSum_step (x : Rat) (n : Nat) :
    partialSum x (n+1)-partialSum x n = term x n := by rw [partialSum]; grind

theorem not_cauchy {x : Rat} (hx : 1 < qabs x) : ¬ IsCauchy (partialSum x) := by
  intro h
  let d := qabs x*(qabs x*qabs x-1)/3
  have hy0 : 0 < qabs x := by grind
  have hyy := Rat.mul_lt_mul_of_pos_right hx hy0
  have hprod := Rat.mul_pos hy0 (show 0 < qabs x*qabs x-1 by grind)
  have hd : 0 < d := by dsimp [d]; exact Rat.mul_pos hprod (Rat.inv_pos.mpr (by decide))
  obtain ⟨N,hN⟩ := h ⟨d/2, by grind⟩
  have ha := hN (N+2) (N+1) (by omega) (by omega)
  rw [partialSum_step] at ha
  have hb := term_lower_bound hx (N+1) (by omega)
  change d ≤ _ at hb
  change _ ≤ d/2 at ha
  grind

theorem not_converges {x : Rat} (hx : 1 < qabs x) (v : RealRaw) :
    ¬ ConvergesTo (partialSum x) v := fun h => not_cauchy hx (convergesTo_isCauchy h)

end ComputableAnalysis.ArctanTaylor
