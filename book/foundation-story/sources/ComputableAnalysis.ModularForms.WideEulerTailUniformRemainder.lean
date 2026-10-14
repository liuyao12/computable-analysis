import ComputableAnalysis.ModularForms.WideEulerTailRemainder
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem power_compare (a b : Rat) (ha : 0≤a) (hb : 0≤b) (hab : a≤b) (N : Nat) :
    a^N≤b^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ha)
      (Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg hb))

private theorem budget_bound (N : Nat) : tauEulerDerivativeBudget (1/8) N≤2 := by
  have h := tauEulerDerivativeBudget_identity (1/8) N
  have hp : 0≤((1:Rat)/8)^N := Rat.pow_nonneg (by decide +kernel)
  grind only

private theorem factor_variation (a z : Scalar) (ha : Small a.val ((1:Rat)/64))
    (hz : Small z.val ((1:Rat)/64)) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (sub (tauEulerFactorValue z (N+2)).val (tauEulerFactorValue a (N+2)).val)
      ((tauEulerFactorRemainderConstant/12288)*((1:Rat)/16)^N*H) := by
  have h := wideEulerFactorValue_geometric_variation_bound a z (1/64) H
    (by decide +kernel) Rat.le_refl hH ha hz hza (N+2)
  have he : 96*(4:Rat)^23*(4*(1/64:Rat))^(N+2)*H=
      (tauEulerFactorRemainderConstant/12288)*((1:Rat)/16)^N*H := by
    rw [show (4:Rat)*(1/64)=1/16 by decide +kernel,
      Rat.pow_succ ((1:Rat)/16) (N+1),Rat.pow_succ ((1:Rat)/16) N]
    have hc : (96:Rat)*(4:Rat)^23*(1/16)*(1/16)=tauEulerFactorRemainderConstant/12288 := by decide +kernel
    grind only
  rw [he] at h
  exact h

private theorem factor_remainder (a z : Scalar) (ha : Small a.val ((1:Rat)/64))
    (hz : Small z.val ((1:Rat)/64)) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (tauMapPower (tauEulerFactorMap (N+2)) 24) a trivial
      ((tauMapPower_holomorphic (tauEulerFactorMap (N+2)) (tauEulerFactorMap_holomorphic (N+2)) 24).derivative a trivial)
      z trivial) ((tauEulerFactorRemainderConstant/8)*((1:Rat)/8)^N*H^2) := by
  have h := wideEulerFactorPower_geometric_remainder_bound a z (1/64) H
    (by decide +kernel) Rat.le_refl hH ha hz hza (N+1)
  rw [show (8:Rat)*(1/64)=1/8 by decide +kernel,Rat.pow_succ ((1:Rat)/8) N] at h
  exact h.mono (by grind only)

private theorem finish_increment (K B H T U W : Rat)
    (hBT : B*T*(K*(H*H))≤2*T*(K*(H*H)))
    (hT : T*(K*(H*H))≤W*(K*(H*H)))
    (hU : U*(K*(H*H))≤W*(K*(H*H))) (hW : 0≤W*(K*(H*H))) :
    K*B*(H*H)+2*(K*B*(H*H))*(3/64*(T*(1/32)))+
      (2*2*(K/8*W*(H*H))+2*(2*2*H)*(K/12288*U*H))≤K*(B+W)*(H*H) := by
  have ht2 := Rat.mul_le_mul_of_nonneg_left hT (show (0:Rat)≤2 by decide +kernel)
  have he : 2*T*(K*(H*H))=2*(T*(K*(H*H))) := by grind only
  rw [he] at hBT
  have h1 := Rat.le_trans hBT ht2
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 (show (0:Rat)≤3/1024 by decide +kernel)
  have h3 := Rat.mul_le_mul_of_nonneg_left hU (show (0:Rat)≤1/1536 by decide +kernel)
  have h4 := Rat.mul_le_mul_of_nonneg_right
    (show (3/512:Rat)+1/2+1/1536≤1 by decide +kernel) hW
  grind only

/-- A summable quadratic budget for actual finite Euler tails on the wider disk. -/
theorem wideEulerTailRemainder_budget_bound (a z : Scalar) (ha : Small a.val ((1:Rat)/64))
    (hz : Small z.val ((1:Rat)/64)) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (wideEulerTailRemainder a z N).val
      (tauEulerFactorRemainderConstant*tauEulerDerivativeBudget (1/8) N*H^2) := by
  let C := tauEulerFactorRemainderConstant
  have hC : 0≤C := by decide +kernel
  have hH2 : 0≤H^2 := Rat.pow_nonneg hH
  induction N with
  | zero =>
    have he : (wideEulerTailRemainder a z 0).val.Equiv zero := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := (wideEulerTailRemainder a z 0).property) (hright := ofQComplex_valid _)
      change (1-1)-0*(ComplexRawQuotient.ofRaw z.val z.property-ComplexRawQuotient.ofRaw a.val a.property)=0
      grind only
    exact Small.congr (ofQComplex_valid _) (wideEulerTailRemainder a z 0).property
      (equiv_symm he) (Small.zero (by change 0≤C*0*H^2; grind only))
  | succ N ih =>
    let E := C*tauEulerDerivativeBudget (1/8) N*H^2
    let V := (3/64:Rat)*((1:Rat)/32)^(N+1)
    let L := (C/12288)*((1:Rat)/16)^N*H
    let F := (C/8)*((1:Rat)/8)^N*H^2
    have hE : 0≤E := Rat.mul_nonneg (Rat.mul_nonneg hC
      (tauEulerDerivativeBudget_nonnegative (1/8) (by decide +kernel) N)) hH2
    have hV : 0≤V := Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel))
    have hL : 0≤L := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤1/16 by decide +kernel))) hH
    have hF : 0≤F := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤1/8 by decide +kernel))) hH2
    have hs := wideEulerTailRemainder_step_bound a z N E 2 2 H V L F
      hE (by decide +kernel) (by decide +kernel) hH hV hL hF ih
      (wideEulerTailPrefix_bound a ha N) (wideEulerTailSlope_bound a ha N) hza
      (wideEulerTailFactor_deviation z hz N) (factor_variation a z ha hz H hH hza N)
      (factor_remainder a z ha hz H hH hza N)
    have hb := Rat.mul_le_mul_of_nonneg_right
      (Rat.mul_le_mul_of_nonneg_left (budget_bound N) hC) hH2
    have ht := power_compare (1/32) (1/8) (by decide +kernel) (by decide +kernel) (by decide +kernel) N
    have hu := power_compare (1/16) (1/8) (by decide +kernel) (by decide +kernel) (by decide +kernel) N
    have hp : 0≤((1:Rat)/8)^N := Rat.pow_nonneg (by decide +kernel)
    apply hs.mono
    rw [tauEulerDerivativeBudget]
    dsimp only [E,V,L,F] at *
    rw [Rat.pow_succ ((1:Rat)/32) N]
    have hT0 : 0≤((1:Rat)/32)^N := Rat.pow_nonneg (by decide +kernel)
    have hBT := Rat.mul_le_mul_of_nonneg_right (budget_bound N) hT0
    have hBTp := Rat.mul_le_mul_of_nonneg_right hBT (Rat.mul_nonneg hC hH2)
    have htp := Rat.mul_le_mul_of_nonneg_right ht (Rat.mul_nonneg hC hH2)
    have hup := Rat.mul_le_mul_of_nonneg_right hu (Rat.mul_nonneg hC hH2)
    simp only [Rat.pow_succ H 1,Rat.pow_one] at *
    dsimp only [C] at *
    generalize ((1:Rat)/32)^N=T at ht htp hBTp ⊢
    generalize ((1:Rat)/16)^N=U at hu hup ⊢
    have hW := Rat.mul_nonneg hp (Rat.mul_nonneg hC hH2)
    generalize ((1:Rat)/8)^N=W at ht hu hp htp hup hW ⊢
    generalize tauEulerDerivativeBudget (1/8) N=B at hb hBTp ⊢
    exact finish_increment _ B H T U W hBTp htp hup hW

/-- A single constant controls every actual finite-tail quadratic remainder. -/
theorem wideEulerTailRemainder_uniform_bound (a z : Scalar) (ha : Small a.val ((1:Rat)/64))
    (hz : Small z.val ((1:Rat)/64)) (H : Rat) (hH : 0≤H)
    (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (wideEulerTailRemainder a z N).val (2*tauEulerFactorRemainderConstant*H^2) := by
  have h := wideEulerTailRemainder_budget_bound a z ha hz H hH hza N
  have hb := Rat.mul_le_mul_of_nonneg_right
    (Rat.mul_le_mul_of_nonneg_left (budget_bound N) (show 0≤tauEulerFactorRemainderConstant by decide +kernel))
    (Rat.pow_nonneg (n := 2) hH)
  exact h.mono (by grind only)


/-- Uniform quadratic control of the actual holomorphic finite-tail remainders. -/
theorem wideEulerTailMap_actual_remainder_uniform_bound (a z : Scalar)
    (ha : Small a.val ((1:Rat)/64)) (hz : Small z.val ((1:Rat)/64))
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (wideEulerTailMap N) a trivial
      ((wideEulerTailMap_holomorphic N).derivative a trivial) z trivial)
      (2*tauEulerFactorRemainderConstant*H^2) :=
  Small.congr (wideEulerTailRemainder a z N).property (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (wideEulerTailRemainder_actual a z N))
    (wideEulerTailRemainder_uniform_bound a z ha hz H hH hza N)

end ComputableAnalysis.ModularForms
