import ComputableAnalysis.UnitPowerCalculus
import ComputableAnalysis.CartwrightFrequency

/-! Independently computed cosine-power integrals on the unit quarter-turn
chart. The sample stage and dyadic subdivision depth are both k; the uniform
power-error bound below certifies this prescribed joint schedule. -/
namespace ComputableAnalysis.Wallis
open ClosedArctanInverse CartwrightMoments IntervalSelections
open UnitPowerCalculus

def sample (n : Nat) (x : Rat) (q : Nat) : Rat := ClockTrigonometry.c x q^n

theorem sample_unit (n : Nat) (x : Rat) (q : Nat) : Unit (sample n x q) :=
  power_unit ⟨(ClockTrigonometry.sample_bounds x q).1,(ClockTrigonometry.sample_bounds x q).2.1⟩ n

theorem sample_decreases (n q : Nat) : MonotoneAverage.Decreases (fun x => sample n x q) := by
  intro x y hx hy hxy
  exact power_mono (ClockTrigonometry.sample_bounds y q).1 (cosine_decreases q x y hx hy hxy) n

theorem sample_error (n : Nat) {x : Rat} (hx : Unit x) (q r : Nat) :
    qabs (sample n x q-sample n x r) ≤ ((56*n:Nat):Rat)*(meshRadius q+meshRadius r) := by
  have h := power_difference
    ⟨(ClockTrigonometry.sample_bounds x q).1,(ClockTrigonometry.sample_bounds x q).2.1⟩
    ⟨(ClockTrigonometry.sample_bounds x r).1,(ClockTrigonometry.sample_bounds x r).2.1⟩ n
  have hc := CartwrightMoments.sample_evaluation_error 0 hx q r
  have he : ∀ q, CartwrightMoments.sample 0 x q=ClockTrigonometry.c x q := by
    intro q;simp only [CartwrightMoments.sample,weight,Rat.pow_zero,Rat.one_mul]
  rw [he q,he r] at hc
  have hm := Rat.mul_le_mul_of_nonneg_left hc (Rat.natCast_nonneg (a:=n))
  change qabs (ClockTrigonometry.c x q^n-ClockTrigonometry.c x r^n) ≤ _
  simp only [Rat.natCast_mul,Rat.natCast_ofNat]
  grind only

def data (n : Nat) : MonotoneSampleIntegral.Data where
  sample := sample n
  bound := fun x q _ => sample_unit n x q
  decreasing := sample_decreases n
  errorConstant := 56*n
  evaluation_error := fun x hx q r => sample_error n hx q r

def integral (n : Nat) : RealRaw := MonotoneSampleIntegral.raw (data n)
def integralSample (n q : Nat) : Rat := MonotoneSampleIntegral.centre (data n) q

theorem integral_valid (n : Nat) : (integral n).Valid := MonotoneSampleIntegral.valid (data n)
theorem integral_mem (n q : Nat) : InBox (integralSample n q) ((integral n).compute q) :=
  MonotoneSampleIntegral.contains_future (data n) q q (Nat.le_refl q)
theorem integralSample_unit (n q : Nat) : Unit (integralSample n q) :=
  MonotoneSampleIntegral.centre_unit (data n) q

theorem integral_width (n k : Nat) : ((integral n).compute k).width ≤
    2*(1+112*(n:Rat))*meshRadius k := by
  have h:=MonotoneSampleIntegral.width (data n) k
  unfold MonotoneSampleIntegral.radius at h
  change _ ≤ 2*((1+2*((56*n:Nat):Rat))*meshRadius k) at h
  simp only [Rat.natCast_mul,Rat.natCast_ofNat] at h
  change ((MonotoneSampleIntegral.raw (data n)).compute k).width ≤ _
  grind only

theorem mesh_error (n d q : Nat) (hdq : d≤q) :
    qabs (integralSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d)≤meshRadius d := by
  have h:=MonotoneAverage.mesh_error (fun x=>sample n x q) (sample_decreases n q)
    (sample_unit n 1 q).1 (sample_unit n 0 q).2 hdq
  change qabs (MonotoneAverage.left (fun x=>sample n x q) 0 1 d-
    MonotoneAverage.left (fun x=>sample n x q) 0 1 q) ≤ _ at h
  have he : integralSample n q-MonotoneAverage.left (fun x=>sample n x q) 0 1 d =
      -(MonotoneAverage.left (fun x=>sample n x q) 0 1 d-integralSample n q) := by grind
  rw [he,qabs_neg];exact h

/-- Finite endpoint coefficient; not an integral definition. -/
def coefficient : Nat → Rat
  | 0 => 1
  | 1 => 1
  | n+2 => ((n+1:Nat):Rat)/((n+2:Nat):Rat)*coefficient n

def parityFactor (n : Nat) : RealRaw := if n%2=0 then RealRaw.one else frequency
def paritySample (n q : Nat) : Rat := if n%2=0 then 1 else frequencySample q

def Statement (n : Nat) : Prop :=
  (RealRaw.mul (parityFactor n) (integral n)).Equiv (RealRaw.ofRat (coefficient n))

theorem parity_valid (n : Nat) : (parityFactor n).Valid := by
  unfold parityFactor;split
  · exact RealRaw.ofRat_valid 1
  · exact frequency_valid

theorem parity_mem (n q : Nat) : InBox (paritySample n q) ((parityFactor n).compute q) := by
  unfold paritySample parityFactor;split
  · exact ClockTrigonometry.rat_mem 1 q
  · exact frequencySample_mem q

theorem parity_bounds (n q : Nat) : 1≤paritySample n q ∧ paritySample n q≤2 := by
  unfold paritySample;split
  · constructor <;> decide +kernel
  · exact frequencySample_bounds q

theorem parity_step (n q : Nat) : paritySample (n+2) q=paritySample n q := by
  unfold paritySample
  rw [Nat.add_mod]
  simp

end ComputableAnalysis.Wallis
