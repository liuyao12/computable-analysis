import ComputableAnalysis.ModularForms.WideEulerNomeMap
import ComputableAnalysis.ModularForms.TauFiniteDerivativeBounds
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem wideEulerTailFactor_power_deviation (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N m : Nat) (hm : m≤24) :
    Small (sub (LocalODE.power (sub one (LocalODE.power q.val (N+3))) m) one)
      (2*(m:Rat)*((1:Rat)/32)^(N+3)) := by
  let x : Scalar := ⟨LocalODE.power q.val (N+3),LocalODE.power_valid _ q.property _⟩
  have hx : Small x.val (((1:Rat)/32)^(N+3)) := by
    have h := LocalODE.power_small _ q.property (1/64) (by decide +kernel) hq (N+3)
    rw [show (2:Rat)*(1/64)=1/32 by decide +kernel] at h
    exact h
  have hp := tauEulerGeometricPower_le_first ((1:Rat)/32) (by decide +kernel) (by decide +kernel) N
  have hs : ((1:Rat)/32)^(N+3)≤(1:Rat)/128 := by
    have h := Rat.mul_le_mul_of_nonneg_right hp (show (0:Rat)≤((1:Rat)/32)^2 by decide +kernel)
    rw [Rat.pow_succ ((1:Rat)/32) (N+2),Rat.pow_succ ((1:Rat)/32) (N+1)]
    have hc : ((1:Rat)/32)^2=(1/32)*(1/32) := by decide +kernel
    rw [hc] at h
    have he : ((1:Rat)/32)^(N+1)*(1/32)*(1/32)=((1:Rat)/32)^(N+1)*((1/32)*(1/32)) := by grind only
    rw [he]
    exact Rat.le_trans h (by decide +kernel)
  exact eulerFactor_power_deviation_bound x (((1:Rat)/32)^(N+3))
    (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel)) hs hx m hm

private theorem power_mono (a b : Rat) (ha : 0≤a) (hb : 0≤b) (hab : a≤b) (N : Nat) :
    a^N≤b^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg hb))

private theorem shifted_factor_power_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (LocalODE.power (sub one (LocalODE.power q.val (N+3))) 23) 2 := by
  have h := wideEulerTailFactor_power_deviation q hq N 23 (by omega)
  have hp := tauEulerGeometricPower_le_first (1/32) (by decide +kernel) (by decide +kernel) (N+2)
  have hc := Rat.mul_le_mul_of_nonneg_left hp (show (0:Rat)≤46 by decide +kernel)
  -- Use two additional powers to keep the coordinate estimate below one.
  have hp0 := tauEulerGeometricPower_le_first (1/32) (by decide +kernel) (by decide +kernel) N
  have ht := Rat.mul_le_mul_of_nonneg_right hp0 (show (0:Rat)≤(1/32)*(1/32) by decide +kernel)
  have htail : ((1:Rat)/32)^(N+3)≤(1/32768:Rat) := by
    rw [Rat.pow_succ ((1:Rat)/32) (N+2),Rat.pow_succ ((1:Rat)/32) (N+1)]
    have he : ((1:Rat)/32)^(N+1)*(1/32)*(1/32)=((1:Rat)/32)^(N+1)*((1/32)*(1/32)) := by grind only
    rw [he]
    exact Rat.le_trans ht (by decide +kernel)
  have h46 := Rat.mul_le_mul_of_nonneg_left htail (show (0:Rat)≤46 by decide +kernel)
  have hone : Small one 1 := by
    simpa only [LocalODE.power,Rat.pow_zero] using
      LocalODE.power_small zero (ofQComplex_valid _) 0 Rat.le_refl (Small.zero Rat.le_refl) 0
  let P := LocalODE.power (sub one (LocalODE.power q.val (N+3))) 23
  have hv : P.Valid := LocalODE.power_valid _ (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)) 23
  have he : (add (sub P one) one).Equiv P := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hv (ofQComplex_valid _)) (ofQComplex_valid _)) (hright := hv)
    let A := ComplexRawQuotient.ofRaw P hv
    change (A-1)+1=A
    grind only
  exact (Small.congr (add_valid (sub_valid hv (ofQComplex_valid _)) (ofQComplex_valid _)) hv he
    (LocalODE.small_add h hone)).mono (by change 2*((23:Nat):Rat)*((1:Rat)/32)^(N+3)+1≤2; grind only)

private theorem shifted_index_bound (N : Nat) : ((N+3:Nat):Rat)≤3*(2:Rat)^N := by
  induction N with
  | zero => decide +kernel
  | succ N ih =>
    rw [Rat.pow_succ]
    have ht := Rat.mul_le_mul_of_nonneg_left ih (show (0:Rat)≤2 by decide +kernel)
    have hn : (0:Rat)≤(N:Rat) := Rat.natCast_nonneg
    simp only [Rat.natCast_add] at *
    grind only

/-- Literal slopes of all factors in the actual wider Euler tail have a summable majorant. -/
theorem wideEulerTailFactorSlope_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (tauEulerFactorSlope q (N+2)).val ((9/32:Rat)*((1:Rat)/16)^N) := by
  have hp := LocalODE.power_small _ q.property (1/64) (by decide +kernel) hq (N+2)
  rw [show (2:Rat)*(1/64)=1/32 by decide +kernel] at hp
  have hs := LocalODE.small_scale (c := ((N+3:Nat):Rat)) Rat.natCast_nonneg hp
  have hd := SeriesLimitLaws.small_neg hs
  have hf := shifted_factor_power_bound q hq N
  have hD : 0≤((N+3:Nat):Rat)*((1:Rat)/32)^(N+2) := Rat.mul_nonneg Rat.natCast_nonneg
    (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel))
  have hm := Small.mul
    (LocalODE.power_valid _ (sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)) 23)
    (neg_valid (scaleRat_valid (LocalODE.power_valid _ q.property (N+2))))
    (show (0:Rat)≤2 by decide +kernel) hD hf hd
  have h := LocalODE.small_scale (show (0:Rat)≤24 by decide +kernel) hm
  have hw := shifted_index_bound N
  have hb := Rat.mul_le_mul_of_nonneg_right hw
    (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel) (n := N+2))
  have he : ((1:Rat)/16)^N=(2:Rat)^N*((1:Rat)/32)^N := by
    rw [←LocalODE.rational_mul_pow]
    congr 1
    decide +kernel
  apply h.mono
  rw [he]
  rw [Rat.pow_succ ((1:Rat)/32) (N+1),Rat.pow_succ ((1:Rat)/32) N] at hb ⊢
  generalize (2:Rat)^N = A at hb ⊢
  generalize ((1:Rat)/32)^N = B at hb ⊢
  grind only

end ComputableAnalysis.ModularForms
