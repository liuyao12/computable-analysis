import ComputableAnalysis.ModularForms.LambertWeightBound
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem power_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) (k : Nat) : a^k≤b^k := by
  have hb := Rat.le_trans ha hab
  induction k with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ k ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := k) hb))

private theorem fifth_step (a : Rat) (ha : 4≤a) : (a+1)^5≤4*a^5 := by
  have h := power_mono (a+1) ((5/4)*a) (by grind only) (by grind only) 5
  rw [LocalODE.rational_mul_pow] at h
  have hc : ((5/4:Rat)^5)≤4 := by decide +kernel
  exact Rat.le_trans h (Rat.mul_le_mul_of_nonneg_right hc (Rat.pow_nonneg (by grind only)))

private theorem shifted_fifth_bound (n : Nat) : ((n+4:Nat):Rat)^5≤4*(4:Rat)^(n+4) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have ha : (4:Rat)≤((n+4:Nat):Rat) := by
      simp only [Rat.natCast_add]
      have hn : (0:Rat)≤(n:Rat) := Rat.natCast_nonneg
      grind only
    have hs := fifth_step _ ha
    have hm := Rat.mul_le_mul_of_nonneg_left ih (show (0:Rat)≤4 by decide +kernel)
    have he : n+1+4=(n+4)+1 := by omega
    rw [he,Rat.natCast_add]
    change (((n+4:Nat):Rat)+1)^5≤4*(4:Rat)^((n+4)+1)
    rw [show (4:Rat)^((n+4)+1)=(4:Rat)^(n+4)*4 from Rat.pow_succ _ _]
    exact Rat.le_trans hs (by grind only)

/-- A base-four majorant for the fifth powers used by the actual weight-six Lambert series. -/
theorem lambertFifthWeight_sharp_bound (n : Nat) : ((n+1:Nat):Rat)^5≤16*(4:Rat)^n := by
  cases n with
  | zero => decide +kernel
  | succ n =>
    cases n with
    | zero => decide +kernel
    | succ n =>
      cases n with
      | zero => decide +kernel
      | succ n =>
        have h := shifted_fifth_bound n
        have hidx : n+1+1+1+1=n+4 := by omega
        have hexp : n+4=(n+1+1+1)+1 := by omega
        rw [hidx]
        have hpow : (4:Rat)^(n+4)=(4:Rat)^(n+1+1+1)*4 := by
          calc
            (4:Rat)^(n+4)=(4:Rat)^((n+1+1+1)+1) := congrArg (fun m => (4:Rat)^m) hexp
            _=(4:Rat)^(n+1+1+1)*4 := Rat.pow_succ _ _
        rw [hpow] at h
        have he : 4*((4:Rat)^(n+1+1+1)*4)=16*(4:Rat)^(n+1+1+1) := by grind only
        rw [he] at h
        exact h

/-- The actual weight-six Lambert terms admit the sharper geometric ratio, with all evaluation guards retained. -/
theorem weightedLambertFifthTerm_sharp_bound (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 4*r≤(1:Rat)/2) (hz : Small z.val r) (n : Nat) :
    Small (weightedLambertTerm z r 5 n) (256*r*(8*r)^n) := by
  have h := LocalODE.small_scale (c := (((n+1:Nat):Rat)^5))
    (Rat.pow_nonneg (n := 5) Rat.natCast_nonneg) (nomeLambertPower_bound z r hr hlocal hz n)
  apply h.mono
  have hm := Rat.mul_le_mul_of_nonneg_right (lambertFifthWeight_sharp_bound n)
    (Rat.mul_nonneg (show (0:Rat)≤8 by decide +kernel) (nomePowerRadius_nonneg r hr n))
  unfold nomePowerRadius at hm
  rw [show (2*r)^(n+1)=(2*r)^n*(2*r) from Rat.pow_succ _ _] at hm ⊢
  have he : (8*r)^n=(2*r)^n*(4:Rat)^n := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    grind only
  rw [he]
  generalize (((n+1:Nat):Rat)^5) = A at hm ⊢
  generalize (4:Rat)^n = B at hm ⊢
  generalize (2*r)^n = D at hm ⊢
  grind only

/-- A concrete larger disk already has a certified shrinking bound for every actual term. -/
theorem weightedLambertFifthTerm_wide_disk_bound (z : Scalar)
    (hz : Small z.val ((1:Rat)/64)) (n : Nat) :
    Small (weightedLambertTerm z (1/64) 5 n) (4*((1:Rat)/8)^n) := by
  have h := weightedLambertFifthTerm_sharp_bound z (1/64)
    (by decide +kernel) (by decide +kernel) hz n
  have hc : (256:Rat)*(1/64)=4 := by decide +kernel
  have hr : (8:Rat)*(1/64)=1/8 := by decide +kernel
  rw [hc,hr] at h
  exact h
end ComputableAnalysis.ModularForms
