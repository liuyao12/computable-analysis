import ComputableAnalysis.ModularForms.TauFiniteRemainderBase

/-! Uniform quadratic constants for the actual finite Euler products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem power_mono (t v : Rat) (ht : 0≤t) (hv : 0≤v) (htv : t≤v) (N : Nat) : t^N≤v^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ht)
      (Rat.mul_le_mul_of_nonneg_left htv (Rat.pow_nonneg hv))

private theorem geometric_budget_bound (v : Rat) (hv : 0≤v) (hvMax : v≤(1:Rat)/2) (N : Nat) :
    tauEulerDerivativeBudget v N≤2 := by
  have hg := tauEulerDerivativeBudget_nonnegative v hv N
  have hi := tauEulerDerivativeBudget_identity v N
  have hp : 0≤v^N := Rat.pow_nonneg hv
  have hm := Rat.mul_le_mul_of_nonneg_right (show (1/2:Rat)≤1-v by grind only) hg
  have hh : (1/2:Rat)*tauEulerDerivativeBudget v N≤1 := by grind only
  have htwo := Rat.mul_le_mul_of_nonneg_left hh (show (0:Rat)≤2 by decide +kernel)
  grind only

private theorem increment_bound (t u v K C : Rat) (ht : 0≤t) (hu : 0≤u) (hv : 0≤v)
    (hC : 0≤C) (hK : 0≤K) (hKC : K≤13*C)
    (htMax : t≤1/512) (huMax : u≤1/256) (htv : t≤v) (huv : u≤v) (N : Nat) :
    96*K*t^(N+2)+4*C*v^N+((512:Rat)/3*C)*u^(N+1)≤6*C*v^N := by
  have hp : 0≤v^N := Rat.pow_nonneg hv
  have htN := power_mono t v ht hv htv N
  have huN := power_mono u v hu hv huv N
  have ht2a := Rat.mul_le_mul_of_nonneg_right htMax ht
  have ht2b := Rat.mul_le_mul_of_nonneg_left htMax (show (0:Rat)≤1/512 by decide +kernel)
  have ht2 : t*t≤(1:Rat)/262144 := by grind only
  have hf1 := Rat.mul_le_mul_of_nonneg_right htN (Rat.mul_nonneg ht ht)
  have hf2 := Rat.mul_le_mul_of_nonneg_right ht2 hp
  have hf : t^(N+2)≤v^N/262144 := by
    rw [Rat.pow_succ,Rat.pow_succ]
    grind only
  have hs1 := Rat.mul_le_mul_of_nonneg_right huN hu
  have hs2 := Rat.mul_le_mul_of_nonneg_left huMax hp
  have hs : u^(N+1)≤v^N/256 := by rw [Rat.pow_succ]; grind only
  have hb1 := Rat.mul_le_mul_of_nonneg_left hf (Rat.mul_nonneg (show (0:Rat)≤96 by decide +kernel) hK)
  have hb2 := Rat.mul_le_mul_of_nonneg_right hKC hp
  have hb3 := Rat.mul_le_mul_of_nonneg_left hs
    (Rat.mul_nonneg (show (0:Rat)≤512/3 by decide +kernel) hC)
  have hCp := Rat.mul_nonneg hC hp
  grind only

/-- The executable constants are controlled by a bounded geometric sum. -/
theorem tauEulerQuadraticBudget_geometric_bound (R : Rat) (hR : 0≤R)
    (hRMax : R≤(1:Rat)/1024) (N : Nat) :
    tauEulerQuadraticBudget R N≤tauEulerFactorRemainderConstant+
      6*tauEulerFactorRemainderConstant*tauEulerDerivativeBudget (8*R) N := by
  have hc : 0≤tauEulerFactorRemainderConstant := by decide +kernel
  have ht : 0≤2*R := Rat.mul_nonneg (by decide +kernel) hR
  have hu : 0≤4*R := Rat.mul_nonneg (by decide +kernel) hR
  have hv : 0≤8*R := Rat.mul_nonneg (by decide +kernel) hR
  have htM := Rat.mul_le_mul_of_nonneg_left hRMax (show (0:Rat)≤2 by decide +kernel)
  have huM := Rat.mul_le_mul_of_nonneg_left hRMax (show (0:Rat)≤4 by decide +kernel)
  have hvM := Rat.mul_le_mul_of_nonneg_left hRMax (show (0:Rat)≤8 by decide +kernel)
  induction N with
  | zero => change tauEulerFactorRemainderConstant≤tauEulerFactorRemainderConstant+6*tauEulerFactorRemainderConstant*0; grind only
  | succ N ih =>
    have hg := geometric_budget_bound (8*R) hv (Rat.le_trans hvM (by decide +kernel)) N
    have hgC := Rat.mul_le_mul_of_nonneg_left hg (Rat.mul_nonneg (show (0:Rat)≤6 by decide +kernel) hc)
    have hKC : tauEulerQuadraticBudget R N≤13*tauEulerFactorRemainderConstant := by grind only
    have hi := increment_bound (2*R) (4*R) (8*R) (tauEulerQuadraticBudget R N)
      tauEulerFactorRemainderConstant ht hu hv hc (tauEulerQuadraticBudget_nonnegative R hR N)
      hKC (by grind only) (by grind only) (by grind only) (by grind only) N
    have he : (786432:Rat)*(4:Rat)^23=(512:Rat)/3*tauEulerFactorRemainderConstant := by decide +kernel
    rw [tauEulerQuadraticBudget,he,tauEulerDerivativeBudget]
    grind only

/-- A single explicit constant works for every finite product length. -/
theorem tauEulerQuadraticBudget_uniform_bound (R : Rat) (hR : 0≤R)
    (hRMax : R≤(1:Rat)/1024) (N : Nat) :
    tauEulerQuadraticBudget R N≤13*tauEulerFactorRemainderConstant := by
  have h := tauEulerQuadraticBudget_geometric_bound R hR hRMax N
  have hv := Rat.mul_nonneg (show (0:Rat)≤8 by decide +kernel) hR
  have hvM := Rat.mul_le_mul_of_nonneg_left hRMax (show (0:Rat)≤8 by decide +kernel)
  have hg := geometric_budget_bound (8*R) hv (Rat.le_trans hvM (by decide +kernel)) N
  have hm := Rat.mul_le_mul_of_nonneg_left hg
    (show 0≤6*tauEulerFactorRemainderConstant by decide +kernel)
  grind only

/-- The actual analytic remainders have a quadratic bound uniform in length. -/
theorem finiteDiscriminantEuler_actual_remainder_uniform_bound (a z : Scalar) (R H : Rat)
    (hR : 0≤R) (hRMax : R≤(1:Rat)/1024) (hH : 0≤H)
    (ha : Small a.val R) (hz : Small z.val R) (hza : Small (sub z.val a.val) H) (N : Nat) :
    Small (DomainFunctions.remainder (finiteDiscriminantEulerMap (N+1)) a trivial
      ((finiteDiscriminantEulerMap_holomorphic (N+1)).derivative a trivial) z trivial)
      (13*tauEulerFactorRemainderConstant*H^2) := by
  have h := finiteDiscriminantEulerRemainder_budget_bound a z R H hR hRMax hH ha hz hza N
  have hm := Rat.mul_le_mul_of_nonneg_right (tauEulerQuadraticBudget_uniform_bound R hR hRMax N)
    (Rat.pow_nonneg hH : 0≤H^2)
  exact Small.congr (finiteDiscriminantEulerRemainder a z (N+1)).property
    (DomainFunctions.remainder_valid _ _ _ _ _ _)
    (equiv_symm (finiteDiscriminantEulerRemainder_actual a z (N+1))) (h.mono hm)

end ComputableAnalysis.ModularForms
