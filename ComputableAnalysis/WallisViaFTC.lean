import ComputableAnalysis.WallisLaws
import ComputableAnalysis.CartwrightCalculusData

/-! The cosine-power recurrence uses a reusable quantitative FTC applied to
s(t)c(t)^(n+1). No completed real or previously evaluated Wallis integral occurs. -/
namespace ComputableAnalysis.Wallis
open ClosedArctanInverse CartwrightMoments RationalSampleLimits IntervalSelections
open FiniteSampleCalculus UnitPowerCalculus

private theorem left_const (a b v : Rat) (n : Nat) : MonotoneAverage.left (fun _=>v) a b n=v := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [MonotoneAverage.left,ih,Rat.div_def]
    grind only

private theorem zero_law : Close (integralSample 0) (fun _=>1) := by
  apply close_of_pointwise
  intro q
  change MonotoneAverage.left (fun x=>sample 0 x q) 0 1 q=1
  simp only [sample,Rat.pow_zero]
  exact left_const 0 1 1 q

private theorem one_law : Close (fun q=>frequencySample q*integralSample 1 q) (fun _=>1) := by
  have h := chosen_samples_FTC sineModel (fun q=>frequencySample q*integralSample 1 q) 2 (by decide) (by
    intro d q hdq
    have e:=mesh_error 1 d q hdq
    have hf:=frequencySample_bounds q
    have hm:=mul_abs_bound (by decide : (0:Rat)≤2)
      (by rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)];exact hf.2) e
    have eqfun : (fun x=>sample 1 x q)=(fun x=>ClockTrigonometry.c x q) := by
      funext x;simp only [sample,Rat.pow_succ,Rat.pow_zero,Rat.one_mul]
    rw [eqfun] at hm
    rw [MonotoneAverage.left_mul]
    have he : frequencySample q*(integralSample 1 q-MonotoneAverage.left (fun x=>ClockTrigonometry.c x q) 0 1 d)=
      frequencySample q*integralSample 1 q-frequencySample q*MonotoneAverage.left (fun x=>ClockTrigonometry.c x q) 0 1 d := by grind only
    rw [he] at hm;exact hm)
  have he:=close_sub sine_one_close (close_zero_of_small sine_zero_small)
  have hb : Close (fun q=>ClockTrigonometry.s 1 q-ClockTrigonometry.s 0 q) (fun _=>1) := by
    simpa only [show (1:Rat)-0=1 by decide +kernel] using he
  exact close_trans h hb

def primitive (n : Nat) (x : Rat) (q : Nat) : Rat :=
  ClockTrigonometry.s x q*ClockTrigonometry.c x q^(n+1)

def derivative (n : Nat) (x : Rat) (q : Nat) : Rat :=
  frequencySample q*(((n+2:Nat):Rat)*sample (n+2) x q-((n+1:Nat):Rat)*sample n x q)

def primitiveModel (n : Nat) : Model (primitive n) (derivative n) := by
  apply (sineModel.mul (modelPower cosineModel (n+1))).congr
  · intro x q;rfl
  · intro x q
    change (frequencySample q*ClockTrigonometry.c x q)*ClockTrigonometry.c x q^(n+1)+
      ClockTrigonometry.s x q*((((n+1:Nat):Rat)*ClockTrigonometry.c x q^n)*(-frequencySample q*ClockTrigonometry.s x q))=derivative n x q
    have h:=ClockTrigonometry.sample_unit x q
    unfold derivative sample
    simp only [Rat.pow_succ,Rat.natCast_add,Rat.natCast_ofNat]
    grind only

private theorem recurrence_mesh (n d q : Nat) (hdq : d≤q) :
    qabs (frequencySample q*recurrenceSample n q-
      MonotoneAverage.left (fun x=>derivative n x q) 0 1 d)≤
        (2*(((n+2:Nat):Rat)+((n+1:Nat):Rat)))*meshRadius d := by
  have a0 : 0≤((n+2:Nat):Rat) := Rat.natCast_nonneg
  have b0 : 0≤((n+1:Nat):Rat) := Rat.natCast_nonneg
  have h1:=mul_abs_bound a0 (by rw [qabs_eq_self_of_nonneg a0];exact Rat.le_refl) (mesh_error (n+2) d q hdq)
  have h2:=mul_abs_bound b0 (by rw [qabs_eq_self_of_nonneg b0];exact Rat.le_refl) (mesh_error n d q hdq)
  have ht:=qabs_sub_le
    (((n+2:Nat):Rat)*(integralSample (n+2) q-MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d))
    (((n+1:Nat):Rat)*(integralSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d))
  have hb : qabs (recurrenceSample n q-
      (((n+2:Nat):Rat)*MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d-
       ((n+1:Nat):Rat)*MonotoneAverage.left (fun x=>sample n x q) 0 1 d)) ≤
      (((n+2:Nat):Rat)+((n+1:Nat):Rat))*meshRadius d := by
    unfold recurrenceSample
    have he : (((n+2:Nat):Rat)*(integralSample (n+2) q-MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d))-
      (((n+1:Nat):Rat)*(integralSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d)) =
      ((n+2:Nat):Rat)*integralSample (n+2) q-((n+1:Nat):Rat)*integralSample n q-
      (((n+2:Nat):Rat)*MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d-
       ((n+1:Nat):Rat)*MonotoneAverage.left (fun x=>sample n x q) 0 1 d) := by grind only
    rw [he] at ht;grind only
  have hf:=frequencySample_bounds q
  have hm:=mul_abs_bound (by decide : (0:Rat)≤2)
    (by rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)];exact hf.2) hb
  unfold derivative
  rw [MonotoneAverage.left_mul,MonotoneAverage.left_sub,MonotoneAverage.left_mul,MonotoneAverage.left_mul]
  have he : frequencySample q*(recurrenceSample n q-
      (((n+2:Nat):Rat)*MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d-
       ((n+1:Nat):Rat)*MonotoneAverage.left (fun x=>sample n x q) 0 1 d)) =
    frequencySample q*recurrenceSample n q-frequencySample q*
      (((n+2:Nat):Rat)*MonotoneAverage.left (fun x=>sample (n+2) x q) 0 1 d-
       ((n+1:Nat):Rat)*MonotoneAverage.left (fun x=>sample n x q) 0 1 d) := by grind only
  rw [he] at hm
  grind only

private theorem boundary_small (n : Nat) : Small (fun q=>primitive n 1 q-primitive n 0 q) := by
  have hb (x : Rat) (n : Nat) : Bounded (fun q=>ClockTrigonometry.c x q^n) 1 := by
    intro q;exact abs_le_unit (sample_unit n x q)
  have hs : Bounded (ClockTrigonometry.s 1) 1 := by
    intro q;exact abs_le_unit ⟨(ClockTrigonometry.sample_bounds 1 q).2.2.1,(ClockTrigonometry.sample_bounds 1 q).2.2.2⟩
  have h1:=small_mul_bounded (small_mul_bounded cosine_one_small (by decide : (0:Rat)≤1) (hb 1 n))
    (by decide : (0:Rat)≤1) hs
  have h0:=small_mul_bounded sine_zero_small (by decide : (0:Rat)≤1) (hb 0 (n+1))
  have h:=small_sub h1 h0
  have he : (fun q => (ClockTrigonometry.c 1 q*ClockTrigonometry.c 1 q^n)*ClockTrigonometry.s 1 q-
      ClockTrigonometry.s 0 q*ClockTrigonometry.c 0 q^(n+1)) =
      (fun q=>primitive n 1 q-primitive n 0 q) := by
    funext q;unfold primitive;simp only [Rat.pow_succ];grind only
  rw [he] at h;exact h

theorem recurrence_viaFTC (n : Nat) : Small (recurrenceSample n) := by
  have h:=chosen_samples_FTC (primitiveModel n) (fun q=>frequencySample q*recurrenceSample n q)
    (2*(((n+2:Nat):Rat)+((n+1:Nat):Rat)))
    (Rat.mul_nonneg (by decide) (Rat.add_nonneg Rat.natCast_nonneg Rat.natCast_nonneg)) (recurrence_mesh n)
  have ht:=small_add h (boundary_small n)
  have he : (fun q=>(frequencySample q*recurrenceSample n q-(primitive n 1 q-primitive n 0 q))+
      (primitive n 1 q-primitive n 0 q))=(fun q=>frequencySample q*recurrenceSample n q) := by funext q;grind only
  rw [he] at ht
  intro eps
  obtain ⟨N,hN⟩:=ht eps
  refine ⟨N,fun q hq => ?_⟩
  have hf:=frequencySample_bounds q
  have hl:=Rat.mul_le_mul_of_nonneg_right hf.1 (qabs_nonneg (recurrenceSample n q))
  have hh:=hN q hq
  rw [qabs_mul,qabs_eq_self_of_nonneg (by grind : 0≤frequencySample q)] at hh
  grind only

theorem lawsViaFTC : Laws := ⟨zero_law,one_law,recurrence_viaFTC⟩
theorem evaluation_viaFTC (n : Nat) : Statement n := evaluation_of_laws lawsViaFTC n

end ComputableAnalysis.Wallis
