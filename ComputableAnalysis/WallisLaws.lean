import ComputableAnalysis.WallisData
import ComputableAnalysis.RationalSampleLimits

/-! A common finite recurrence contract and its algebraic consequence.
Every exported evaluation below is closed by a separate proof of these laws. -/
namespace ComputableAnalysis.Wallis
open ClosedArctanInverse CartwrightMoments RationalSampleLimits IntervalSelections

def recurrenceSample (n q : Nat) : Rat :=
  ((n+2:Nat):Rat)*integralSample (n+2) q-((n+1:Nat):Rat)*integralSample n q

structure Laws : Prop where
  zero : Close (integralSample 0) (fun _=>1)
  one : Close (fun q=>frequencySample q*integralSample 1 q) (fun _=>1)
  recurrence : ∀ n, Small (recurrenceSample n)

theorem evaluation_samples (h : Laws) : (n : Nat) →
    Close (fun q=>paritySample n q*integralSample n q) (fun _=>coefficient n)
  | 0 => by simpa [paritySample,coefficient] using h.zero
  | 1 => by simpa [paritySample,coefficient] using h.one
  | n+2 => by
    let r : Rat := ((n+1:Nat):Rat)/((n+2:Nat):Rat)
    have hp : 0<((n+2:Nat):Rat) := (Rat.natCast_pos).2 (by omega)
    have hc := Rat.mul_inv_cancel ((n+2:Nat):Rat) (Rat.ne_of_gt hp)
    have hb : Bounded (paritySample n) 2 := by
      intro q
      rw [qabs_eq_self_of_nonneg (by have h:=parity_bounds n q;grind)]
      exact (parity_bounds n q).2
    have hh := small_bounded_mul (by decide : (0:Rat)≤2) hb (h.recurrence n)
    have hs := small_bounded_mul (qabs_nonneg (1/((n+2:Nat):Rat)))
      (bounded_const (1/((n+2:Nat):Rat))) hh
    have he : (fun q => (1/((n+2:Nat):Rat))*(paritySample n q*recurrenceSample n q)) =
      (fun q => paritySample (n+2) q*integralSample (n+2) q-r*(paritySample n q*integralSample n q)) := by
      funext q
      rw [parity_step]
      unfold recurrenceSample r
      simp only [Rat.div_def,Rat.one_mul]
      grind only
    rw [he] at hs
    have ht := close_scale r (evaluation_samples h n)
    exact close_trans hs ht

/-- The native conclusion is identical for the FTC and Mathlib routes. -/
theorem evaluation_of_laws (h : Laws) (n : Nat) : Statement n :=
  equiv_of_close (RealRaw.mul_valid (parity_valid n) (integral_valid n))
    (RealRaw.ofRat_valid (coefficient n))
    (fun q=>paritySample n q*integralSample n q) (fun _=>coefficient n)
    (fun q=>mul_mem (parity_mem n q) (integral_mem n q))
    (ClockTrigonometry.rat_mem (coefficient n)) (evaluation_samples h n)

end ComputableAnalysis.Wallis
