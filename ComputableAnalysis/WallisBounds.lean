import ComputableAnalysis.WallisArithmetic
import ComputableAnalysis.WallisLaws

/-! Arithmetic application of the evaluation: the finite Wallis product
bounds geometric pi. The two calculus routes feed the same order argument. -/
namespace ComputableAnalysis.Wallis
open ClosedArctanInverse RationalSampleLimits IntervalSelections CartwrightMoments

private theorem left_order (f g : Rat → Rat)
    (h : ∀ x, Unit x → f x≤g x) {a b : Rat} (ha : Unit a) (hb : Unit b) (d : Nat) :
    MonotoneAverage.left f a b d≤MonotoneAverage.left g a b d := by
  induction d generalizing a b with
  | zero => exact h a ha
  | succ d ih =>
    have hm:=MonotoneAverage.midpoint_unit ha hb
    have h1:=ih ha hm;have h2:=ih hm hb
    simp only [MonotoneAverage.left,Rat.div_def]
    grind only

theorem integralSample_power_decreases (n q : Nat) : integralSample (n+1) q≤integralSample n q := by
  apply left_order (fun x=>sample (n+1) x q) (fun x=>sample n x q)
    (a:=0) (b:=1) _ ⟨by decide,by decide⟩ ⟨by decide,by decide⟩ q
  intro x hx
  have hc:=ClockTrigonometry.sample_bounds x q
  have hp:=sample_unit n x q
  have hm:=Rat.mul_le_mul_of_nonneg_left hc.2.1 hp.1
  simpa only [sample,Rat.pow_succ,Rat.mul_one] using hm

private theorem le_from_close {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (u v a b : Nat → Rat) (hu : ∀ q, InBox (u q) (X.compute q))
    (hv : ∀ q, InBox (v q) (Y.compute q)) (hx : Close u a) (hy : Close v b)
    (order : ∀ q, a q≤b q) : X.Le Y := by
  apply le_of_eventually hX hY u v hu hv
  intro eps
  let eta : QPos:=⟨eps.val/2,by rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩:=hx eta;obtain ⟨M,hM⟩:=hy eta
  refine ⟨max N M,fun q hq=>?_⟩
  have h1:=hN q (by omega);have h2:=hM q (by omega)
  have h3:=order q;have h4:=self_le_qabs (u q-a q);have h5:=neg_qabs_le_self (v q-b q)
  dsimp [eta] at h1 h2;simp only [Rat.div_def] at h1 h2
  grind only

private theorem frequency_bound : Bounded frequencySample 2 := by
  intro q;have h:=frequencySample_bounds q
  rw [qabs_eq_self_of_nonneg (by grind only)];exact h.2

private theorem even_samples (h : Laws) (n : Nat) :
    Close (integralSample (2*n)) (fun _=>coefficient (2*n)) := by
  have ht:=evaluation_samples h (2*n)
  have he : (2*n)%2=0 := by omega
  simpa [paritySample,he] using ht

private theorem odd_samples (h : Laws) (n : Nat) :
    Close (fun q=>frequencySample q*integralSample (2*n+1) q) (fun _=>coefficient (2*n+1)) := by
  have ht:=evaluation_samples h (2*n+1)
  have he : ¬(2*n+1)%2=0 := by omega
  simpa only [paritySample,if_neg he] using ht

/-- The squeeze is stated as bounds on the original geometric pi program. -/
def ProductBoundsStatement (n : Nat) : Prop :=
    (RealRaw.ofRat (2*product n)).Le CosinePrimitive.pi ∧
    CosinePrimitive.pi.Le (RealRaw.ofRat (2*(coefficient (2*n+1)/coefficient (2*n+2))))

theorem product_bounds_of_laws (h : Laws) (n : Nat) : ProductBoundsStatement n := by
  let A:=coefficient (2*n)
  let B:=coefficient (2*n+1)
  let D:=coefficient (2*n+2)
  have hA : 0<A:=coefficient_pos _
  have hD : 0<D:=coefficient_pos _
  have iA : 0≤1/A:=Rat.le_of_lt (Rat.mul_pos (by decide) ((Rat.inv_pos).2 hA))
  have iD : 0≤1/D:=Rat.le_of_lt (Rat.mul_pos (by decide) ((Rat.inv_pos).2 hD))
  have ca:=Rat.mul_inv_cancel A (Rat.ne_of_gt hA)
  have cd:=Rat.mul_inv_cancel D (Rat.ne_of_gt hD)
  have hE:=even_samples h n
  have hE2:=even_samples h (n+1)
  rw [show 2*(n+1)=2*n+2 by omega] at hE2
  have hO:=odd_samples h n
  have hEA:=close_bounded_mul hE (by decide : (0:Rat)≤2) frequency_bound
  have hED:=close_bounded_mul hE2 (by decide : (0:Rat)≤2) frequency_bound
  have pi_mem (q : Nat) : InBox (2*frequencySample q) (CosinePrimitive.pi.compute q) := by
    rw [CosinePrimitive.pi_compute]
    have he : 2*frequencySample q=(piCircleArea.compute q).lo := by
      unfold frequencySample;simp only [Rat.div_def];grind only
    rw [he];exact ⟨Rat.le_refl,(pi_stage_bounds q).2.1⟩
  have lowerA:=close_scale (2/A) (close_symm hO)
  have lowerB:=close_scale (2/A) (close_symm hEA)
  have upperA:=close_scale (2/D) (close_symm hED)
  have upperB:=close_scale (2/D) (close_symm hO)
  change Close (fun _=>(2/A)*B) _ at lowerA
  change Close (fun _=>(2/D)*B) _ at upperB
  have epA : (fun q=>(2/A)*(frequencySample q*A))=(fun q=>2*frequencySample q) := by
    funext q;simp only [Rat.div_def];grind only
  have epD : (fun q=>(2/D)*(frequencySample q*D))=(fun q=>2*frequencySample q) := by
    funext q;simp only [Rat.div_def];grind only
  change Close (fun q=>(2/A)*(frequencySample q*A)) _ at lowerB
  change Close (fun q=>(2/D)*(frequencySample q*D)) _ at upperA
  rw [epA] at lowerB;rw [epD] at upperA
  have vA : 0≤2/A:=Rat.mul_nonneg (by decide) (Rat.le_of_lt ((Rat.inv_pos).2 hA))
  have vD : 0≤2/D:=Rat.mul_nonneg (by decide) (Rat.le_of_lt ((Rat.inv_pos).2 hD))
  constructor
  · refine le_from_close (RealRaw.ofRat_valid (2*product n)) CosinePrimitive.pi_valid
      (fun _=>2*product n) (fun q=>2*frequencySample q)
      (fun q=>(2/A)*(frequencySample q*integralSample (2*n+1) q))
      (fun q=>(2/A)*(frequencySample q*integralSample (2*n) q))
      (ClockTrigonometry.rat_mem _) pi_mem ?_ lowerB ?_
    · have he : (2/A)*B=2*product n := by dsimp [A,B,product];simp only [Rat.div_def];grind only
      simpa only [he] using lowerA
    · intro q
      exact Rat.mul_le_mul_of_nonneg_left (Rat.mul_le_mul_of_nonneg_left
        (integralSample_power_decreases (2*n) q) (by have hb:=frequencySample_bounds q;grind only)) vA
  · refine le_from_close CosinePrimitive.pi_valid (RealRaw.ofRat_valid (2*(B/D)))
      (fun q=>2*frequencySample q) (fun _=>2*(B/D))
      (fun q=>(2/D)*(frequencySample q*integralSample (2*n+2) q))
      (fun q=>(2/D)*(frequencySample q*integralSample (2*n+1) q))
      pi_mem (ClockTrigonometry.rat_mem _) upperA ?_ ?_
    · have he : (2/D)*B=2*(B/D) := by simp only [Rat.div_def];grind only
      simpa only [he] using upperB
    · intro q
      exact Rat.mul_le_mul_of_nonneg_left (Rat.mul_le_mul_of_nonneg_left
        (integralSample_power_decreases (2*n+1) q) (by have hb:=frequencySample_bounds q;grind only)) vD

end ComputableAnalysis.Wallis
