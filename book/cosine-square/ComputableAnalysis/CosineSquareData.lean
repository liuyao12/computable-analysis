import ComputableAnalysis.CartwrightMoments

/-! A squared-cosine quadrature independent of either value proof.
The internal coordinate t is a fraction of a quarter turn; x=t/2 is the
public pi-normalized coordinate. Every sample is the rational circle cosine
of the closed arctangent search. No endpoint value enters the program. -/
namespace ComputableAnalysis.CosineSquare
open ClosedArctanInverse ClockTrigonometry MonotoneAverage IntervalSelections

abbrev sample (t : Rat) (q : Nat) : Rat := c t q * c t q

theorem sample_bounds (t : Rat) (q : Nat) : Unit (sample t q) := by
  have h := ClockTrigonometry.sample_bounds t q
  have hm := Rat.mul_le_mul_of_nonneg_left h.2.1 h.1
  exact ⟨Rat.mul_nonneg h.1 h.1, by dsimp [sample]; grind only⟩

theorem sample_decreases (q : Nat) : Decreases (fun t => sample t q) := by
  intro a b ha hb hab
  have hm := CartwrightMoments.cosine_decreases q a b ha hb hab
  have h1 := Rat.mul_le_mul_of_nonneg_left hm (ClockTrigonometry.sample_bounds b q).1
  have h2 := Rat.mul_le_mul_of_nonneg_right hm (ClockTrigonometry.sample_bounds a q).1
  dsimp [sample]
  exact Rat.le_trans h1 h2

theorem square_error {a b E : Rat} (ha : Unit a) (hb : Unit b)
    (h : qabs (a-b) ≤ E) : qabs (a*a-b*b) ≤ 2*E := by
  have hsum : 0 ≤ a+b := Rat.add_nonneg ha.1 hb.1
  have hsum2 : a+b ≤ 2 := by have h1:=ha.2;have h2:=hb.2;grind
  have he : a*a-b*b=(a-b)*(a+b) := by grind
  rw [he,qabs_mul,qabs_eq_self_of_nonneg hsum]
  have h1:=Rat.mul_le_mul_of_nonneg_left hsum2 (qabs_nonneg (a-b))
  have h2:=Rat.mul_le_mul_of_nonneg_left h (by decide +kernel : (0:Rat)≤2)
  grind only

theorem evaluation_error (t : Rat) (ht : Unit t) (q r : Nat) :
    qabs (sample t q-sample t r) ≤ 112*(meshRadius q+meshRadius r) := by
  have h:=CartwrightMoments.sample_evaluation_error 0 ht q r
  simp only [CartwrightMoments.sample,CartwrightMoments.weight,Rat.pow_zero,Rat.one_mul] at h
  have a:=ClockTrigonometry.sample_bounds t q
  have b:=ClockTrigonometry.sample_bounds t r
  have e:=square_error ⟨a.1,a.2.1⟩ ⟨b.1,b.2.1⟩ h
  dsimp [sample]
  grind only

def data : MonotoneSampleIntegral.Data where
  sample := sample
  bound := fun t q _ => sample_bounds t q
  decreasing := sample_decreases
  errorConstant := 112
  evaluation_error := evaluation_error

/-- Integral in the quarter-turn coordinate, on [0,1]. -/
def quarterIntegral : RealRaw := MonotoneSampleIntegral.raw data
/-- The actual integral of cos(pi*x)^2 on [0,1/2]. -/
def integral : RealRaw := RealRaw.scaleRat (1/2) quarterIntegral

def sumSample (q : Nat) : Rat := MonotoneSampleIntegral.centre data q

theorem quarterIntegral_valid : quarterIntegral.Valid := MonotoneSampleIntegral.valid data

theorem integral_valid : integral.Valid := RealRaw.scaleRat_valid quarterIntegral_valid

theorem sample_mem (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (sample t q) ((RealRaw.mul (cosine t) (cosine t)).compute q) :=
  mul_mem (c_mem ht q) (c_mem ht q)

theorem sumSample_mem (q : Nat) : InBox (sumSample q) (quarterIntegral.compute q) :=
  MonotoneSampleIntegral.contains_future data q q (Nat.le_refl q)

theorem integral_width (q : Nat) : (integral.compute q).width ≤ 225*meshRadius q := by
  have h:=MonotoneSampleIntegral.width data q
  change (quarterIntegral.compute q).width ≤ 2*((1+2*(112:Rat))*meshRadius q) at h
  have hw : (integral.compute q).width=(1/2:Rat)*(quarterIntegral.compute q).width := by
    exact RealRaw.scaleRat_width_of_nonneg (by decide +kernel : (0:Rat)≤1/2) quarterIntegral q
  rw [hw]
  have hm:=Rat.mul_le_mul_of_nonneg_left h (by decide +kernel : (0:Rat)≤1/2)
  simp only [Rat.div_def] at hm ⊢
  grind only

theorem mesh_comparison (d q : Nat) (hdq : d≤q) :
    qabs (sumSample q-left (fun t=>sample t q) 0 1 d) ≤ meshRadius d := by
  have h:=mesh_error (fun t=>sample t q) (sample_decreases q)
    (sample_bounds 1 q).1 (sample_bounds 0 q).2 hdq
  rw [show sumSample q-left (fun t=>sample t q) 0 1 d =
    -(left (fun t=>sample t q) 0 1 d-left (fun t=>sample t q) 0 1 q) by
      unfold sumSample MonotoneSampleIntegral.centre data; grind, qabs_neg]
  exact h

theorem normalize_value (h : quarterIntegral.Equiv (RealRaw.ofRat (1/2))) :
    integral.Equiv (RealRaw.ofRat (1/4)) := by
  have hs:=RealRaw.scaleRat_equiv (r:=1/2) h
  intro n
  have ho:=(RealRaw.compareAt_overlap_iff _ _ n n).1 (hs n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hp : (0:Rat)≤1/2 := by decide +kernel
  have he : (1/2:Rat)*(1/2)=1/4 := by decide +kernel
  simpa only [integral,RealRaw.scaleRat,RealRaw.scaleRatCompute,RealRaw.ofRat,
    if_pos hp,QInterval.Overlaps,he] using ho

end ComputableAnalysis.CosineSquare
