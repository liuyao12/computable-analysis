import ComputableAnalysis.FiniteSampleCalculus
import ComputableAnalysis.CartwrightFrequency

/-! Derivative certificates for the original closed sine/cosine computations.
The frequency is the independently computed geometric pi divided by two. -/
namespace ComputableAnalysis.CartwrightMoments
open ClosedArctanInverse SinPiIntegral IntervalSelections
open FiniteSampleCalculus RationalSampleLimits

theorem on_half {x : Rat} (hx : Unit x) : GeometricSineDerivative.OnHalf (x/2) := by
  have h0:=hx.1;have h1:=hx.2
  unfold GeometricSineDerivative.OnHalf
  simp only [Rat.div_def]
  constructor <;> grind only

theorem sine_public_mem {x : Rat} (hx : Unit x) (q : Nat) :
    InBox (ClockTrigonometry.s x q) ((sinPiRawOfArctan provider (x/2) (on_half hx)).compute q) := by
  change InBox (ClockTrigonometry.s x q) ((ClockTrigonometry.sine (2*(x/2))).compute q)
  rw [show (2:Rat)*(x/2)=x by simp only [Rat.div_def];grind]
  exact ClockTrigonometry.s_mem hx q

theorem cosine_public_mem {x : Rat} (hx : Unit x) (q : Nat) :
    InBox (ClockTrigonometry.c x q) ((cosPiRawOfArctan provider (x/2) (on_half hx)).compute q) := by
  change InBox (ClockTrigonometry.c x q) ((ClockTrigonometry.cosine (2*(x/2))).compute q)
  rw [show (2:Rat)*(x/2)=x by simp only [Rat.div_def];grind]
  exact ClockTrigonometry.c_mem hx q

def sineModel : Model ClockTrigonometry.s (fun x q => frequencySample q*ClockTrigonometry.c x q) where
  valueBound := 1
  slopeBound := 2
  errorBound := 1000
  valueBound_nonneg := by decide +kernel
  slopeBound_nonneg := by decide +kernel
  errorBound_nonneg := by decide +kernel
  value := by
    intro x q hx
    have h:=ClockTrigonometry.sample_bounds x q
    rw [qabs_eq_self_of_nonneg h.2.2.1]
    exact h.2.2.2
  slope := by
    intro x q hx
    have h:=ClockTrigonometry.sample_bounds x q
    have hp:=frequencySample_bounds q
    have h0 : 0≤frequencySample q := by grind
    have hm:=Rat.mul_le_mul_of_nonneg_left h.2.1 h0
    rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg h0 h.1)]
    grind only
  local_error := by
    intro a b ha hb hab
    have he : a/2+(b-a)/2=b/2 := by simp only [Rat.div_def];grind
    have hx:=on_half ha
    have hy : GeometricSineDerivative.OnHalf (a/2+(b-a)/2) := by rw [he];exact on_half hb
    have hh : 0<(b-a)/2 := by simp only [Rat.div_def];grind
    obtain ⟨N,hN⟩:=GeometricSineDirectBounds.positive_increment_error provider (a/2) ((b-a)/2) hx hy hh
    refine ⟨N,fun q hq => ?_⟩
    simp only [he] at hN
    have hA:=sine_public_mem ha q;have hB:=sine_public_mem hb q;have hC:=cosine_public_mem ha q
    have h:=hN q hq (ClockTrigonometry.s b q) (ClockTrigonometry.s a q) (ClockTrigonometry.c a q)
      (piCircleArea.compute q).lo hB.1 hB.2 hA.1 hA.2 hC.1 hC.2 Rat.le_refl (pi_stage_bounds q).2.1
    unfold frequencySample
    simp only [Rat.div_def] at h ⊢
    grind only

theorem complement_unit {x : Rat} (hx : Unit x) : Unit (1-x) := by
  have h0:=hx.1;have h1:=hx.2
  constructor <;> grind

/-- A cosine derivative is obtained from the already established complementary
angle identity and the sine increment estimate, not from its integral. -/
def cosineModel : Model ClockTrigonometry.c (fun x q => -frequencySample q*ClockTrigonometry.s x q) where
  valueBound := 1
  slopeBound := 2
  errorBound := 4000
  valueBound_nonneg := by decide +kernel
  slopeBound_nonneg := by decide +kernel
  errorBound_nonneg := by decide +kernel
  value := by
    intro x q hx
    have h:=ClockTrigonometry.sample_bounds x q
    rw [qabs_eq_self_of_nonneg h.1]
    exact h.2.1
  slope := by
    intro x q hx
    have h:=ClockTrigonometry.sample_bounds x q
    have hp:=frequencySample_bounds q
    have h0 : 0≤frequencySample q := by grind
    have hm:=Rat.mul_le_mul_of_nonneg_left h.2.2.2 h0
    have he : -frequencySample q*ClockTrigonometry.s x q= -(frequencySample q*ClockTrigonometry.s x q) := by grind
    rw [he,qabs_neg,qabs_eq_self_of_nonneg (Rat.mul_nonneg h0 h.2.2.1)]
    grind only
  local_error := by
    intro a b ha hb hab
    have hcomp : 1-b<1-a := by grind
    have hab0 : 0≤b-a := by grind
    have hab1 : b-a≤1 := by have h0:=ha.1;have h1:=hb.2;grind
    have hdiff : (1-a)-(1-b)=b-a := by grind
    obtain ⟨N,hN⟩:=sineModel.local_error (1-b) (1-a) (complement_unit hb) (complement_unit ha) hcomp
    obtain ⟨M,hM⟩:=sineModel.increment_eventual a b ha hb hab
    have smallError : Small (fun q => (944:Rat)*meshRadius q) :=
      small_of_geometric_bound 944 (by decide +kernel) (fun q=>by
        rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (meshRadius_pos q)))];exact Rat.le_refl)
    let eps : QPos := ⟨(b-a)*(b-a),Rat.mul_pos (by grind) (by grind)⟩
    obtain ⟨K,hK⟩:=smallError eps
    refine ⟨max N (max M K),fun q hq => ?_⟩
    have hn:=hN q (by omega)
    have hm:=hM q (by omega)
    have hk:=hK q (by omega)
    change qabs (ClockTrigonometry.s (1-a) q-ClockTrigonometry.s (1-b) q-
      ((1-a)-(1-b))*(frequencySample q*ClockTrigonometry.c (1-b) q)) ≤
      1000*((1-a)-(1-b))*((1-a)-(1-b)) at hn
    rw [hdiff] at hn
    change qabs (ClockTrigonometry.s b q-ClockTrigonometry.s a q) ≤ (b-a)*(2+1000) at hm
    have hca:=(ClockTrigonometry.sample_complement (complement_unit ha) q).1
    have hcb:=(ClockTrigonometry.sample_complement (complement_unit hb) q).1
    have hcs:=(ClockTrigonometry.sample_complement hb q).1
    rw [show (1:Rat)-(1-a)=a by grind] at hca
    rw [show (1:Rat)-(1-b)=b by grind] at hcb
    have hp:=frequencySample_bounds q
    have hp0 : 0≤frequencySample q := by grind
    have ph0 := Rat.mul_nonneg hab0 hp0
    have ph2 := Rat.mul_le_mul_of_nonneg_left hp.2 hab0
    have phbound : (b-a)*frequencySample q≤2 := by grind only
    have hsdelta : qabs (ClockTrigonometry.s a q-ClockTrigonometry.s b q)≤1002*(b-a) := by
      rw [show ClockTrigonometry.s a q-ClockTrigonometry.s b q= -(ClockTrigonometry.s b q-ClockTrigonometry.s a q) by grind,qabs_neg]
      grind only
    have hprod:=mul_abs_bound (Rat.mul_nonneg (by decide +kernel : (0:Rat)≤2) hab0)
      (by rw [qabs_eq_self_of_nonneg ph0];grind only : qabs ((b-a)*frequencySample q)≤2*(b-a)) hsdelta
    have hprod2:=mul_abs_bound (by decide +kernel : (0:Rat)≤2)
      (by rw [qabs_eq_self_of_nonneg ph0];exact phbound : qabs ((b-a)*frequencySample q)≤2) hcs
    let err := ClockTrigonometry.c b q-ClockTrigonometry.c a q-(b-a)*(-frequencySample q*ClockTrigonometry.s a q)
    have h1:=qabs_sub_le (ClockTrigonometry.c b q-ClockTrigonometry.s (1-b) q)
      (ClockTrigonometry.c a q-ClockTrigonometry.s (1-a) q)
    have h2:=qabs_sub_le ((ClockTrigonometry.c b q-ClockTrigonometry.s (1-b) q)-
      (ClockTrigonometry.c a q-ClockTrigonometry.s (1-a) q))
      (ClockTrigonometry.s (1-a) q-ClockTrigonometry.s (1-b) q-(b-a)*(frequencySample q*ClockTrigonometry.c (1-b) q))
    have h3:=qabs_add_le (((ClockTrigonometry.c b q-ClockTrigonometry.s (1-b) q)-
      (ClockTrigonometry.c a q-ClockTrigonometry.s (1-a) q))-
      (ClockTrigonometry.s (1-a) q-ClockTrigonometry.s (1-b) q-(b-a)*(frequencySample q*ClockTrigonometry.c (1-b) q)))
      (((b-a)*frequencySample q)*(ClockTrigonometry.s a q-ClockTrigonometry.s b q))
    have h4:=qabs_sub_le ((((ClockTrigonometry.c b q-ClockTrigonometry.s (1-b) q)-
      (ClockTrigonometry.c a q-ClockTrigonometry.s (1-a) q))-
      (ClockTrigonometry.s (1-a) q-ClockTrigonometry.s (1-b) q-(b-a)*(frequencySample q*ClockTrigonometry.c (1-b) q)))+
      (((b-a)*frequencySample q)*(ClockTrigonometry.s a q-ClockTrigonometry.s b q)))
      (((b-a)*frequencySample q)*(ClockTrigonometry.c (1-b) q-ClockTrigonometry.s b q))
    have he : (((ClockTrigonometry.c b q-ClockTrigonometry.s (1-b) q)-
      (ClockTrigonometry.c a q-ClockTrigonometry.s (1-a) q))-
      (ClockTrigonometry.s (1-a) q-ClockTrigonometry.s (1-b) q-(b-a)*(frequencySample q*ClockTrigonometry.c (1-b) q)))+
      (((b-a)*frequencySample q)*(ClockTrigonometry.s a q-ClockTrigonometry.s b q))-
      (((b-a)*frequencySample q)*(ClockTrigonometry.c (1-b) q-ClockTrigonometry.s b q))=err := by dsimp [err];grind only
    rw [he] at h4
    have hpK:=self_le_qabs ((944:Rat)*meshRadius q)
    dsimp [eps] at hk
    change qabs err≤4000*(b-a)*(b-a)
    have hhpos:=Rat.mul_nonneg hab0 hab0
    grind only

end ComputableAnalysis.CartwrightMoments
