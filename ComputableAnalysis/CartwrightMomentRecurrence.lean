import ComputableAnalysis.CartwrightIntegrationByParts

/-! The calculus middle ends at these moment laws. Their algebraic consumer
is shared by all derivations. This interface has an explicitly proved FTC
inhabitant below; it is not an assumed moment formula. -/
namespace ComputableAnalysis.CartwrightMomentRecurrence
open CartwrightMoments CartwrightIntegrationByParts CartwrightFiniteSums
open FiniteRiemannAlgebra RationalErrorCalculus CartwrightArithmetic

abbrev p := frequencySample
abbrev J := CartwrightMoments.sample

structure Laws : Prop where
  zero : Near (fun k=>p k*J 0 k) (fun _=>1)
  one : Near (fun k=>(p k)^3*J 1 k) (fun _=>2)
  recurrence : ∀n,Near (fun k=>(p k)^2*J (n+2) k)
    (fun k=>2*((n+2:Nat):Rat)*(2*(n:Rat)+3)*J (n+1) k-
      4*((n+1:Nat):Rat)*((n+2:Nat):Rat)*J n k)

/-- Algebraically eliminate the auxiliary sine moment; no integration occurs here. -/
theorem eliminate_auxiliary (X Y Z U : Nat → Rat) (A B C : Rat)
    (hs : Near (fun k=>p k*X k-A*U k) (fun _=>0))
    (hc : Near (fun k=>B*Y k-C*Z k-p k*U k) (fun _=>0)) :
    Near (fun k=>(p k)^2*X k) (fun k=>A*B*Y k-A*C*Z k) := by
  have h1:=Near.mul_left frequencySample_bounded hs
  have h2:=Near.scale hc A
  have hh:=Near.sub h1 h2
  have he : (fun k=>p k*(p k*X k-A*U k)-A*(B*Y k-C*Z k-p k*U k))=
      (fun k=>(p k)^2*X k-(A*B*Y k-A*C*Z k)) := by
    funext k;simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul];grind
  simp only [Rat.mul_zero,Rat.sub_self] at hh
  rw [he] at hh
  exact Near.of_difference hh

/-- Any fully supplied integration-by-parts pair gives the same recurrence.
This is a finite algebraic assembly lemma, shared by the alternate routes. -/
theorem laws_of_parts
    (sine_parts : ∀(f df : Rat → Rat),FiniteFirstOrderCalculus.Data f df→
      Near (fun k=>p k*cosineSum f k+sineSum df k) (fun _=>f 1))
    (cosine_parts : ∀(f df : Rat → Rat),FiniteFirstOrderCalculus.Data f df→
      Near (fun k=>cosineSum df k-p k*sineSum f k) (fun _=> -(f 0))) : Laws := by
  have weight_one_zero (n : Nat) : weight (n+1) 1=0 := by
    unfold weight
    rw [show (1:Rat)-1*1=0 by decide +kernel,Rat.pow_succ,Rat.mul_zero]
  have aux_zero (n : Nat) : auxWeight n 0=0 := by unfold auxWeight;exact Rat.zero_mul _
  have hs (n : Nat) : Near (fun k=>p k*J (n+1) k-2*((n+1:Nat):Rat)*sineSum (auxWeight n) k) (fun _=>0) := by
    have hh:=sine_parts (weight (n+1)) (weightDerivative (n+1)) (weightData (n+1))
    have hd : weightDerivative (n+1)=(fun t=> (-2*((n+1:Nat):Rat))*auxWeight n t) :=
      funext (derivative_weight_succ n)
    rw [hd,weight_one_zero] at hh
    simp only [sineSum_scale] at hh
    have he : (fun k=>p k*cosineSum (weight (n+1)) k+ -2*((n+1:Nat):Rat)*sineSum (auxWeight n) k)=
      (fun k=>p k*J (n+1) k-2*((n+1:Nat):Rat)*sineSum (auxWeight n) k) := by funext k;unfold J CartwrightMoments.sample;grind
    rw [he] at hh;exact hh
  have hc (n : Nat) : Near (fun k=>(2*((n+1:Nat):Rat)+1)*J (n+1) k-
      2*((n+1:Nat):Rat)*J n k-p k*sineSum (auxWeight (n+1)) k) (fun _=>0) := by
    have hh:=cosine_parts (auxWeight (n+1)) (auxDerivative (n+1)) (auxData (n+1))
    have hd : auxDerivative (n+1)=(fun t=>(2*((n+1:Nat):Rat)+1)*weight (n+1) t-
      2*((n+1:Nat):Rat)*weight n t) := funext (derivative_aux_succ n)
    rw [hd,aux_zero] at hh
    simp only [cosineSum_sub,cosineSum_scale,show -(0:Rat)=0 by decide +kernel] at hh
    exact hh
  have hz : Near (fun k=>p k*J 0 k) (fun _=>1) := by
    have hh:=sine_parts (weight 0) (weightDerivative 0) (weightData 0)
    have hw : weight 0=(fun _=>1) := by funext t;exact Rat.pow_zero _
    have hd : weightDerivative 0=(fun _=>0) := rfl
    rw [hd] at hh
    simp only [sineSum_zero,Rat.add_zero] at hh
    have he : weight 0 1=1 := Rat.pow_zero _
    rw [he] at hh
    exact hh
  have hbasecos : Near (fun k=>J 0 k-p k*sineSum (auxWeight 0) k) (fun _=>0) := by
    have hh:=cosine_parts (auxWeight 0) (auxDerivative 0) (auxData 0)
    have hd : auxDerivative 0=weight 0 := by
      funext t;rw [derivative_aux_zero,weight,Rat.pow_zero]
    rw [hd,aux_zero] at hh
    have hneg : -(0:Rat)=0 := by decide +kernel
    rw [hneg] at hh
    exact hh
  refine ⟨hz,?_,?_⟩
  · have hb : Near (fun k=>1*J 0 k-0*(0:Rat)-p k*sineSum (auxWeight 0) k) (fun _=>0) := by
      simpa only [Rat.one_mul,Rat.zero_mul,show ∀a:Rat,a-0=a by intro a;grind] using hbasecos
    have hS:=hs 0
    simp only [show ((0+1:Nat):Rat)=1 by decide +kernel,Rat.mul_one] at hS
    have hh:=eliminate_auxiliary (J 1) (J 0) (fun _=>0) (sineSum (auxWeight 0)) 2 1 0 hS hb
    simp only [Rat.mul_one,Rat.mul_zero,show ∀a:Rat,a-0=a by intro a;grind] at hh
    have hmul:=Near.mul_left frequencySample_bounded hh
    have hnext:=Near.scale hz 2
    have hpoly : (fun k=>p k*((p k)^2*J 1 k))=(fun k=>(p k)^3*J 1 k) := by
      funext k;simp only [Rat.pow_succ,Rat.pow_zero,Rat.one_mul];grind
    have hright : (fun k=>p k*(2*J 0 k))=(fun k=>2*(p k*J 0 k)) := by funext k;grind
    rw [hpoly,hright] at hmul
    simpa only [Rat.mul_one] using Near.trans hmul hnext
  · intro n
    have hh:=eliminate_auxiliary (J (n+2)) (J (n+1)) (J n) (sineSum (auxWeight (n+1)))
      (2*((n+2:Nat):Rat)) (2*((n+1:Nat):Rat)+1) (2*((n+1:Nat):Rat)) (hs (n+1)) (hc n)
    have he : (fun k=>2*((n+2:Nat):Rat)*(2*((n+1:Nat):Rat)+1)*J (n+1) k-
      2*((n+2:Nat):Rat)*(2*((n+1:Nat):Rat))*J n k)=
      (fun k=>2*((n+2:Nat):Rat)*(2*(n:Rat)+3)*J (n+1) k-
      4*((n+1:Nat):Rat)*((n+2:Nat):Rat)*J n k) := by
      funext k;simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel];grind
    rw [he] at hh;exact hh

/-- The closed FTC recurrence, with no caller-supplied calculus certificate. -/
theorem viaFTC : Laws := laws_of_parts
  (fun _ _ F=>sine_parts_viaFTC F) (fun _ _ F=>cosine_parts_viaFTC F)

end ComputableAnalysis.CartwrightMomentRecurrence
