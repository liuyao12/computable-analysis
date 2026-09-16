import ComputableAnalysis.MonotoneSampleIntegral
import ComputableAnalysis.ClockTrigIdentities
import ComputableAnalysis.CosinePrimitiveData

/-! Independently computed weighted cosine moments.  Every sample uses the
closed arctangent evaluator; a fixed joint mesh/evaluation schedule is proved
successful without invoking the moment recurrence or its arithmetic value. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse SinPiIntegral IntervalSelections

abbrev weight (n : Nat) (x : Rat) : Rat := (1-x*x)^n

theorem power_unit {x : Rat} (hx : Unit x) (n : Nat) : Unit (x^n) := by
  induction n with
  | zero => simp only [Rat.pow_zero]; constructor <;> decide
  | succ n ih =>
    rw [Rat.pow_succ]
    have hu:=Rat.mul_le_mul_of_nonneg_right ih.2 hx.1
    exact ⟨Rat.mul_nonneg ih.1 hx.1,by have h:=hx.2; grind⟩

theorem power_mono {x y : Rat} (hx : 0 ≤ x) (hxy : x ≤ y) (n : Nat) : x^n ≤ y^n := by
  have hy : 0 ≤ y := Rat.le_trans hx hxy
  have nonneg (z : Rat) (hz : 0 ≤ z) (n : Nat) : 0 ≤ z^n := by
    induction n with
    | zero => simp only [Rat.pow_zero]; decide
    | succ n ih => rw [Rat.pow_succ]; exact Rat.mul_nonneg ih hz
  induction n with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ n ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih hx)
      (Rat.mul_le_mul_of_nonneg_left hxy (nonneg y hy n))

theorem weight_unit (n : Nat) {x : Rat} (hx : Unit x) : Unit (weight n x) := by
  have hh:=Rat.mul_le_mul_of_nonneg_right hx.2 hx.1
  have hp:=Rat.mul_nonneg hx.1 hx.1
  apply power_unit
  constructor <;> grind

theorem weight_decreases (n : Nat) : MonotoneAverage.Decreases (weight n) := by
  intro x y hx hy hxy
  have h1:=Rat.mul_le_mul_of_nonneg_left hxy hx.1
  have h2:=Rat.mul_le_mul_of_nonneg_right hxy hy.1
  have hsq:=Rat.mul_le_mul_of_nonneg_right hy.2 hy.1
  have h0 : 0 ≤ 1-y*y := by have h:=hy.2; grind
  exact power_mono h0 (by grind) n

theorem cosine_decreases (q : Nat) : MonotoneAverage.Decreases (fun x => ClockTrigonometry.c x q) := by
  intro x y hx hy hxy
  have hxy':=ClockTrigonometry.center_mono hxy q
  have hu:=center_unit x q; have hv:=center_unit y q
  have h:=(rationalCircleCosInterval_width_le (U:={lo:=center x q,hi:=center y q}) ⟨hu.1,hxy',hv.2⟩).1
  change 0 ≤ rationalCircleCos (center x q)-rationalCircleCos (center y q) at h
  change rationalCircleCos (center y q) ≤ rationalCircleCos (center x q)
  grind

def sample (n : Nat) (x : Rat) (q : Nat) : Rat := weight n x * ClockTrigonometry.c x q

theorem sample_unit (n : Nat) {x : Rat} (hx : Unit x) (q : Nat) : Unit (sample n x q) := by
  have hw:=weight_unit n hx
  have hc:=ClockTrigonometry.sample_bounds x q
  have h:=Rat.mul_le_mul_of_nonneg_right hw.2 hc.1
  exact ⟨Rat.mul_nonneg hw.1 hc.1,by unfold sample; grind⟩

theorem sample_decreases (n q : Nat) : MonotoneAverage.Decreases (fun x => sample n x q) := by
  intro x y hx hy hxy
  have hw:=weight_decreases n x y hx hy hxy
  have hc:=cosine_decreases q x y hx hy hxy
  have w0:=(weight_unit n hx).1
  have c0:=(ClockTrigonometry.sample_bounds y q).1
  unfold sample
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hw c0)
    (Rat.mul_le_mul_of_nonneg_left hc w0)

theorem sample_evaluation_error (n : Nat) {x : Rat} (hx : Unit x) (q r : Nat) :
    qabs (sample n x q-sample n x r) ≤ 56*(meshRadius q+meshRadius r) := by
  have hw:=weight_unit n hx
  have hu:=center_unit x q; have hv:=center_unit x r
  have h:=centers_close x hx q r
  have hc:=rationalCircleCos_difference_le_qabs hu.1 hu.2 hv.1 hv.2
  have he : sample n x q-sample n x r = weight n x *
      (rationalCircleCos (center x q)-rationalCircleCos (center x r)) := by
    unfold sample ClockTrigonometry.c
    grind
  rw [he,qabs_mul,qabs_eq_self_of_nonneg hw.1]
  have hmul:=Rat.mul_le_mul_of_nonneg_right hw.2
    (qabs_nonneg (rationalCircleCos (center x q)-rationalCircleCos (center x r)))
  grind

/-- The moment-specific schedule certificate; no limiting value is supplied. -/
def data (n : Nat) : MonotoneSampleIntegral.Data where
  sample := sample n
  bound := fun x q hx => sample_unit n hx q
  decreasing := sample_decreases n
  errorConstant := 56
  evaluation_error := fun x hx q r => sample_evaluation_error n hx q r

def moment (n : Nat) : RealRaw := MonotoneSampleIntegral.raw (data n)
def momentSample (n q : Nat) : Rat := MonotoneSampleIntegral.centre (data n) q

theorem moment_valid (n : Nat) : (moment n).Valid := MonotoneSampleIntegral.valid (data n)
theorem moment_range (n q : Nat) : subintervalOf ((moment n).compute q) 0 1 :=
  MonotoneSampleIntegral.range (data n) q

theorem momentSample_mem (n q : Nat) : InBox (momentSample n q) ((moment n).compute q) :=
  MonotoneSampleIntegral.contains_future (data n) q q (Nat.le_refl q)

theorem momentSample_unit (n q : Nat) : Unit (momentSample n q) :=
  MonotoneSampleIntegral.centre_unit (data n) q

/-- Mesh and evaluation depth are both q. This choice works for THESE samples
because of the uniform, proved evaluation-error bound above. -/
theorem moment_width (n q : Nat) : ((moment n).compute q).width ≤ 226*meshRadius q := by
  have h:=MonotoneSampleIntegral.width (data n) q
  change _ ≤ 2*((1+2*(56:Rat))*meshRadius q) at h
  change ((moment n).compute q).width ≤ 2*((1+2*(56:Rat))*meshRadius q) at h
  grind

end ComputableAnalysis.CartwrightMoments
