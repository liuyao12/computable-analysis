import ComputableAnalysis.CartwrightMoments
import ComputableAnalysis.RationalSampleLimits

/-! Positivity and size bounds for independently computed moments. These
proofs use monotone rectangles and finite arctangent inequalities only; they
never invoke the moment evaluation or its recurrence. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse ArctanGeometry SinPiIntegral IntervalSelections
open RationalSampleLimits

theorem centre_upper (t : Rat) (ht : Unit t) (q : Nat) :
    center t q ≤ 2*t+10*meshRadius q := by
  have hu:=center_unit t q
  have h:=clock_increment (x:=0) ⟨by decide +kernel,by decide +kernel⟩ hu hu.1 q q
  rw [arctanIntegralRectangleCompute_zero_lower] at h
  have hw:=clock_width (center t q) hu q
  have hr:=center_residual t ht q
  have hp:=self_le_qabs ((A (center t q) q).lo-t*(A 1 q).lo)
  have hi:=(arctanIntegralRectangleRaw_valid (by decide +kernel : (0:Rat)≤1) (by decide +kernel)).1 q
  have hOne:=arctanIntegralRectangleCompute_upper_le_input (x:=1) (by decide +kernel) q
  have hOneOrd:=RealRaw.interval_order_of_valid (arctanIntegralRectangleRaw 1)
    (arctanIntegralRectangleRaw_valid (by decide +kernel) (by decide +kernel)) q
  have hOneLo : (A 1 q).lo≤1 := Rat.le_trans hOneOrd hOne
  have hmul:=Rat.mul_le_mul_of_nonneg_left hOneLo ht.1
  unfold QInterval.width at hw
  simp only [Rat.div_def] at h
  grind only

theorem cosine_quarter_lower {t : Rat} (ht : Unit t) (ht4 : t≤(1:Rat)/4)
    {q : Nat} (hq : 6≤q) : (1:Rat)/4≤ClockTrigonometry.c t q := by
  have hc:=centre_upper t ht q
  have hr:=meshRadius_antitone hq
  rw [show meshRadius 6=(1:Rat)/64 by decide +kernel] at hr
  have hu:=center_unit t q
  have hsmall : center t q≤(3:Rat)/4 := by
    simp only [Rat.div_def] at ht4 hc hr ⊢
    grind only
  have h:=(rationalCircleCosInterval_width_le (U:={lo:=center t q,hi:=3/4})
    ⟨hu.1,hsmall,by change (3:Rat)/4≤1;decide +kernel⟩).1
  change 0≤rationalCircleCos (center t q)-rationalCircleCos (3/4) at h
  rw [show rationalCircleCos (3/4)=(7:Rat)/25 by decide +kernel] at h
  change (1:Rat)/4≤rationalCircleCos (center t q)
  simp only [Rat.div_def] at h ⊢
  grind only

def lowerBound (n : Nat) : Rat := ((15:Rat)/16)^n/16

theorem lowerBound_pos (n : Nat) : 0<lowerBound n := by
  unfold lowerBound
  rw [Rat.div_def]
  exact Rat.mul_pos (Rat.pow_pos (by decide +kernel)) ((Rat.inv_pos).2 (by decide +kernel))

theorem momentSample_lower (n : Nat) {q : Nat} (hq : 6≤q) :
    lowerBound n≤momentSample n q := by
  have hx : Unit ((1:Rat)/4) := ⟨by decide +kernel,by decide +kernel⟩
  have hc:=cosine_quarter_lower hx (Rat.le_refl) hq
  have hw:=weight_unit n hx
  have hm:=Rat.mul_le_mul_of_nonneg_left hc hw.1
  have hf0 (x : Rat) (hx : Unit x) : 0≤sample n x q := (sample_unit n hx q).1
  have hsum:=MonotoneAverage.quarter_mass (fun x=>sample n x q) (sample_decreases n q) hf0 (q-2)
  rw [show q-2+2=q by omega] at hsum
  have hweight : weight n (1/4)=((15:Rat)/16)^n := by
    unfold weight
    rw [show (1:Rat)-(1/4)*(1/4)=15/16 by decide +kernel]
  change sample n (1/4) q/4≤momentSample n q at hsum
  change weight n (1/4)*(1/4)≤sample n (1/4) q at hm
  rw [hweight] at hm
  unfold lowerBound
  simp only [Rat.div_def] at hm hsum ⊢
  grind only

/-- A quantitative positive lower bound, not merely nonnegativity. -/
theorem moment_lower (n : Nat) : (RealRaw.ofRat (lowerBound n)).Le (moment n) := by
  apply le_of_eventually (RealRaw.ofRat_valid _) (moment_valid n)
    (fun _=>lowerBound n) (momentSample n) (ClockTrigonometry.rat_mem _) (momentSample_mem n)
  intro eps
  refine ⟨6,fun q hq => ?_⟩
  have h:=momentSample_lower n hq
  have hp:=eps.property
  grind only

theorem moment_positive (n : Nat) : (moment n).Pos := by
  let eps : QPos := ⟨lowerBound n/2,by
    rw [Rat.div_def];exact Rat.mul_pos (lowerBound_pos n) ((Rat.inv_pos).2 (by decide +kernel))⟩
  obtain ⟨N,hN⟩:=(moment_valid n).2.2 eps
  let q:=max N 6
  have hw:=hN q (by dsimp [q];omega)
  have hl:=momentSample_lower n (q:=q) (by dsimp [q];omega)
  have hm:=momentSample_mem n q
  have hp:=lowerBound_pos n
  refine ⟨q,?_⟩
  dsimp [eps] at hw
  unfold QInterval.width at hw
  unfold InBox at hm
  simp only [Rat.div_def] at hw
  grind only

theorem moment_upper (n : Nat) : (moment n).Le RealRaw.one := by
  intro q r
  have h:=moment_range n q
  change ((moment n).compute q).lo≤1
  exact Rat.le_trans h.2.1 h.2.2

end ComputableAnalysis.CartwrightMoments
