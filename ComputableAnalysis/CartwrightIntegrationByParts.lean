import ComputableAnalysis.UniformGridFTC

/-! Integration by parts for the exact chosen moment grid. The derivative
and summation uncertainties remain explicit until the joint-stage limit. -/
namespace ComputableAnalysis.CartwrightIntegrationByParts
open CartwrightClockBounds CartwrightMoments CartwrightFiniteSums
open FiniteRiemannAlgebra RationalErrorCalculus
abbrev Unit := CartwrightClockBounds.Unit

def frequencySample (k : Nat) : Rat := p (sampleStage k)
def cosineSum (f : Rat → Rat) : Nat → Rat :=
  UniformGridFTC.riemann (fun q t=>f t*CartwrightClockBounds.c t q)
def sineSum (f : Rat → Rat) : Nat → Rat :=
  UniformGridFTC.riemann (fun q t=>f t*CartwrightClockBounds.s t q)

theorem frequencySample_bounds (k : Nat) : 1≤frequencySample k ∧ frequencySample k≤2 := p_bounds _

theorem frequencySample_bounded : Bounded frequencySample := by
  refine ⟨2,by decide +kernel,fun k=>?_⟩
  have h:=frequencySample_bounds k
  rw [qabs_eq_self_of_nonneg (by grind : 0≤frequencySample k)]
  exact h.2

theorem frequencySample_mem (k : Nat) : IntervalSelections.InBox (frequencySample k) (frequency.compute k) :=
  IntervalSelections.contains_later frequency_valid (by unfold sampleStage;omega) (p_mem (sampleStage k))

theorem cosineSum_scale (a : Rat) (f : Rat → Rat) (k : Nat) :
    cosineSum (fun t=>a*f t) k=a*cosineSum f k := by
  unfold cosineSum UniformGridFTC.riemann
  rw [←sum_mul]
  apply sum_congr;intro j hj;grind

theorem sineSum_scale (a : Rat) (f : Rat → Rat) (k : Nat) :
    sineSum (fun t=>a*f t) k=a*sineSum f k := by
  unfold sineSum UniformGridFTC.riemann
  rw [←sum_mul]
  apply sum_congr;intro j hj;grind

theorem cosineSum_sub (f g : Rat → Rat) (k : Nat) :
    cosineSum (fun t=>f t-g t) k=cosineSum f k-cosineSum g k := by
  unfold cosineSum UniformGridFTC.riemann
  rw [←sum_sub]
  apply sum_congr;intro j hj;grind

theorem cosineSum_zero (k : Nat) : cosineSum (fun _=>0) k=0 := by
  unfold cosineSum UniformGridFTC.riemann
  simp only [Rat.zero_mul,Rat.mul_zero]
  rw [sum_const,Rat.mul_zero]

theorem sineSum_zero (k : Nat) : sineSum (fun _=>0) k=0 := by
  unfold sineSum UniformGridFTC.riemann
  simp only [Rat.zero_mul,Rat.mul_zero]
  rw [sum_const,Rat.mul_zero]

theorem cosineSum_bounded {f : Rat → Rat} {B : Rat}
    (hB : 0≤B) (hf : ∀t,Unit t→qabs (f t)≤B) : Bounded (cosineSum f) := by
  refine ⟨B,hB,fun k=>?_⟩
  unfold cosineSum UniformGridFTC.riemann
  have hh:=step_pos k
  have bound:=sum_bound (N:=cells k) (a:=step k*B) (f:=fun j=>step k*(f (grid k j)*c (grid k j) (sampleStage k))) (by
    intro j hj
    have ha:=grid_unit k j (by omega)
    have hc:=ClockTrigonometry.sample_bounds (grid k j) (sampleStage k)
    have hfv:=hf _ ha
    rw [qabs_mul,qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hh),qabs_eq_self_of_nonneg hc.1]
    have h1:=Rat.mul_le_mul_of_nonneg_left hc.2.1 (qabs_nonneg (f (grid k j)))
    have h2:=Rat.mul_le_mul_of_nonneg_left (Rat.le_trans (by simpa only [Rat.mul_one] using h1) hfv) (Rat.le_of_lt hh)
    exact h2)
  have he : (cells k:Rat)*(step k*B)=B := by rw [←Rat.mul_assoc,cells_step,Rat.one_mul]
  rw [he] at bound
  exact bound

private theorem sample_endpoint_near (t : Rat) (ht : t=0 ∨ t=1) :
    Near (fun k=>c t (sampleStage k)) (fun _=>1-t) ∧
    Near (fun k=>s t (sampleStage k)) (fun _=>t) := by
  constructor
  · apply Near.geometric 56 (by decide +kernel)
    intro k
    have h:=(ClockTrigonometry.sample_endpoint ht (sampleStage k)).1
    have he:=ClosedArctanInverse.meshRadius_antitone (n:=k) (m:=sampleStage k) (by unfold sampleStage;omega)
    change qabs (c t (sampleStage k)-(1-t))≤_
    grind
  · apply Near.geometric 28 (by decide +kernel)
    intro k
    have h:=(ClockTrigonometry.sample_endpoint ht (sampleStage k)).2
    have he:=ClosedArctanInverse.meshRadius_antitone (n:=k) (m:=sampleStage k) (by unfold sampleStage;omega)
    change qabs (s t (sampleStage k)-t)≤_
    grind

theorem sine_boundary (f : Rat → Rat) :
    Near (UniformGridFTC.endpoint (fun q t=>f t*s t q)) (fun _=>f 1) := by
  have h1:=Near.scale (sample_endpoint_near 1 (Or.inr rfl)).2 (f 1)
  have h0:=Near.scale (sample_endpoint_near 0 (Or.inl rfl)).2 (f 0)
  have h:=Near.sub h1 h0
  change Near (fun k=>f 1*s 1 (sampleStage k)-f 0*s 0 (sampleStage k)) (fun _=>f 1)
  simpa only [Rat.mul_one,Rat.mul_zero,show ∀a:Rat,a-0=a by intro a;grind] using h

theorem cosine_boundary (f : Rat → Rat) :
    Near (UniformGridFTC.endpoint (fun q t=>f t*c t q)) (fun _=> -(f 0)) := by
  have h1:=Near.scale (sample_endpoint_near 1 (Or.inr rfl)).1 (f 1)
  have h0:=Near.scale (sample_endpoint_near 0 (Or.inl rfl)).1 (f 0)
  have h:=Near.sub h1 h0
  change Near (fun k=>f 1*c 1 (sampleStage k)-f 0*c 0 (sampleStage k)) (fun _=> -(f 0))
  simpa only [show (1:Rat)-1=0 by decide +kernel,
    show (1:Rat)-0=1 by decide +kernel,Rat.mul_one,Rat.mul_zero,
    show ∀a:Rat,0-a= -a by intro a;grind] using h

/-- Reusable FTC route, with the product certificate actually supplied. -/
theorem sine_parts_viaFTC {f df : Rat → Rat} (F : FiniteFirstOrderCalculus.Data f df) :
    Near (fun k=>frequencySample k*cosineSum f k+sineSum df k) (fun _=>f 1) := by
  have h:=UniformGridFTC.conclusion (UniformGridFTC.product F UniformGridFTC.sine_data)
  have he : UniformGridFTC.riemann (fun q t=>df t*UniformGridFTC.sine q t+f t*UniformGridFTC.sineDerivative q t) =
      (fun k=>frequencySample k*cosineSum f k+sineSum df k) := by
    funext k
    unfold UniformGridFTC.riemann UniformGridFTC.sine UniformGridFTC.sineDerivative frequencySample cosineSum sineSum
    unfold UniformGridFTC.riemann
    rw [←sum_mul,←sum_add]
    apply sum_congr;intro j hj;grind
  change Near (UniformGridFTC.riemann (fun q t=>df t*UniformGridFTC.sine q t+f t*UniformGridFTC.sineDerivative q t))
    (UniformGridFTC.endpoint (fun q t=>f t*s t q)) at h
  rw [he] at h
  exact Near.trans h (sine_boundary f)

theorem cosine_parts_viaFTC {f df : Rat → Rat} (F : FiniteFirstOrderCalculus.Data f df) :
    Near (fun k=>cosineSum df k-frequencySample k*sineSum f k) (fun _=> -(f 0)) := by
  have h:=UniformGridFTC.conclusion (UniformGridFTC.product F UniformGridFTC.cosine_data)
  have he : UniformGridFTC.riemann (fun q t=>df t*UniformGridFTC.cosine q t+f t*UniformGridFTC.cosineDerivative q t) =
      (fun k=>cosineSum df k-frequencySample k*sineSum f k) := by
    funext k
    unfold UniformGridFTC.riemann UniformGridFTC.cosine UniformGridFTC.cosineDerivative frequencySample cosineSum sineSum
    unfold UniformGridFTC.riemann
    rw [←sum_mul,←sum_sub]
    apply sum_congr;intro j hj;grind
  change Near (UniformGridFTC.riemann (fun q t=>df t*UniformGridFTC.cosine q t+f t*UniformGridFTC.cosineDerivative q t))
    (UniformGridFTC.endpoint (fun q t=>f t*c t q)) at h
  rw [he] at h
  exact Near.trans h (cosine_boundary f)

end ComputableAnalysis.CartwrightIntegrationByParts

namespace ComputableAnalysis.CartwrightMoments
open CartwrightIntegrationByParts CartwrightFiniteSums FiniteRiemannAlgebra
open CartwrightClockBounds IntervalSelections RationalErrorCalculus

/-- The rational left-sample selection; it is enclosed by the actual Darboux output. -/
def sample (n : Nat) : Nat → Rat := cosineSum (weight n)

theorem sample_mem (n k : Nat) : InBox (sample n k) ((integral n).compute k) := by
  rw [integral_compute]
  unfold sample cosineSum UniformGridFTC.riemann
  have hstep:=Rat.le_of_lt (step_pos k)
  constructor
  · apply sum_mono
    intro j hj
    have ha:=grid_unit k j (by omega);have hb:=grid_unit k (j+1) (by omega)
    have hs:=grid_step k j
    have hp:=step_pos k
    have hord:=value_antitone ha hb (by grind) n (sampleStage k)
    have hm:=scale_mem (ClockTrigonometry.c_mem ha (sampleStage k)) (r:=weight n (grid k j)) (weight_bounds ha n).1
    have hh : ((value n (grid k (j+1))).compute (sampleStage k)).lo ≤
        weight n (grid k j)*c (grid k j) (sampleStage k) := Rat.le_trans hord.1 hm.1
    exact Rat.mul_le_mul_of_nonneg_left hh hstep
  · apply sum_mono
    intro j hj
    have ha:=grid_unit k j (by omega)
    have hm:=scale_mem (ClockTrigonometry.c_mem ha (sampleStage k)) (r:=weight n (grid k j)) (weight_bounds ha n).1
    exact Rat.mul_le_mul_of_nonneg_left hm.2 hstep

theorem sample_bounds (n k : Nat) : 0≤sample n k ∧ sample n k≤1 := by
  have h:=sample_mem n k
  have hh:=integral_bounds n k
  unfold InBox at h
  constructor <;> grind

theorem sample_bounded (n : Nat) : Bounded (sample n) := by
  refine ⟨1,by decide +kernel,fun k=>?_⟩
  rw [qabs_eq_self_of_nonneg (sample_bounds n k).1]
  exact (sample_bounds n k).2

theorem sample_positive (n k : Nat) (hk : 1≤k) : positiveBound n ≤ sample n k := by
  have h0:=first_stage_positive n
  have hn:=(integral_valid n).2.1 1 k hk
  have hs:=(sample_mem n k).1
  grind

end ComputableAnalysis.CartwrightMoments
