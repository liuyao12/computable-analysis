import ComputableAnalysis.ModularForms.TauFiniteProductDerivative

/-! Uniform finite-product derivative bounds from the literal increment recurrence. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem power_mono (t v : Rat) (ht : 0≤t) (hv : 0≤v) (htv : t≤v) (N : Nat) : t^N≤v^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih ht)
      (Rat.mul_le_mul_of_nonneg_left htv (Rat.pow_nonneg hv))

def tauEulerDerivativeBudget (v : Rat) : Nat → Rat
  | 0 => 0
  | N+1 => tauEulerDerivativeBudget v N+v^N

theorem tauEulerDerivativeBudget_nonnegative (v : Rat) (hv : 0≤v) (N : Nat) : 0≤tauEulerDerivativeBudget v N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih => exact Rat.add_nonneg ih (Rat.pow_nonneg hv)

theorem tauEulerDerivativeBudget_identity (v : Rat) (N : Nat) :
    (1-v)*tauEulerDerivativeBudget v N=1-v^N := by
  induction N with
  | zero => simp only [tauEulerDerivativeBudget,Rat.pow_zero]; grind only
  | succ N ih => rw [tauEulerDerivativeBudget,Rat.pow_succ]; grind only

private theorem budget_bound (v : Rat) (hv : 0≤v) (hvMax : v≤(1:Rat)/2) (N : Nat) :
    tauEulerDerivativeBudget v N≤2 := by
  have hg := tauEulerDerivativeBudget_nonnegative v hv N
  have hi := tauEulerDerivativeBudget_identity v N
  have hp : 0≤v^N := Rat.pow_nonneg hv
  have hm := Rat.mul_le_mul_of_nonneg_right (show (1/2:Rat)≤1-v by grind only) hg
  have hh : (1/2:Rat)*tauEulerDerivativeBudget v N≤1 := by grind only
  have htwo := Rat.mul_le_mul_of_nonneg_left hh (show (0:Rat)≤2 by decide +kernel)
  grind only

theorem finiteDiscriminantEulerSlope_increment_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat)
    (hD : Small (finiteDiscriminantEulerSlope q N).val 2048) :
    Small (sub (finiteDiscriminantEulerSlope q (N+1)).val (finiteDiscriminantEulerSlope q N).val)
      (768*(4*r)^N) := by
  let D := finiteDiscriminantEulerSlope q N
  let F := tauEulerFactorValue q N
  let P := finiteDiscriminantEulerProduct q N
  let G := tauEulerFactorSlope q N
  have ho : one.Valid := ofQComplex_valid _
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hv : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hf := tauEulerFactor_deviation_bound q r hr (Rat.le_trans hrMax (by decide +kernel)) hq N
  have hp := finiteDiscriminantEulerProduct_bound q r hr hrMax hq N
  have hg := tauEulerFactorSlope_geometric_bound q r hr (Rat.le_trans hrMax (by decide +kernel)) hq N
  have hm := Small.mul D.property (sub_valid F.property ho) (show (0:Rat)≤2048 by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg ht)) hD hf
  have hn := Small.mul P.property G.property (show (0:Rat)≤2 by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hv)) hp hg
  have hs := Small.congr (add_valid (mul_valid D.property (sub_valid F.property ho)) (mul_valid P.property G.property))
    (sub_valid (finiteDiscriminantEulerSlope q (N+1)).property D.property)
    (equiv_symm (finiteDiscriminantEulerSlope_increment q N)) (LocalODE.small_add hm hn)
  apply hs.mono
  have htBound := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have hpow := power_mono (2*r) (4*r) ht hv (by grind only) N
  have hprod := Rat.mul_le_mul_of_nonneg_right htBound (Rat.pow_nonneg ht : 0≤(2*r)^N)
  have hpowCoef := Rat.mul_le_mul_of_nonneg_left hpow (show (0:Rat)≤2*(1/1024) by decide +kernel)
  have htail : (2*r)^(N+1)≤(1/512:Rat)*(4*r)^N := by
    rw [Rat.pow_succ]
    have he : (2:Rat)*(1/1024)=1/512 := by decide +kernel
    rw [he] at hprod hpowCoef
    grind only
  have hlarge := Rat.mul_le_mul_of_nonneg_left htail (show (0:Rat)≤196608 by decide +kernel)
  grind only

theorem finiteDiscriminantEulerSlope_budget_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (finiteDiscriminantEulerSlope q N).val (768*tauEulerDerivativeBudget (4*r) N) := by
  have hv : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤4 by decide +kernel)
  induction N with
  | zero => exact Small.zero (show (0:Rat)≤768*0 by decide +kernel)
  | succ N ih =>
    have hb := budget_bound (4*r) hv (Rat.le_trans hmax (by decide +kernel)) N
    have h768 := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤768 by decide +kernel)
    have hD : Small (finiteDiscriminantEulerSlope q N).val 2048 := ih.mono (by grind only)
    have hinc := finiteDiscriminantEulerSlope_increment_bound q r hr hrMax hq N hD
    have hs := LocalODE.small_add hinc ih
    let A := finiteDiscriminantEulerSlope q (N+1)
    let B := finiteDiscriminantEulerSlope q N
    have he : (add (sub A.val B.val) B.val).Equiv A.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (sub_valid A.property B.property) B.property) (hright := A.property)
      let a := ComplexRawQuotient.ofRaw A.val A.property
      let b := ComplexRawQuotient.ofRaw B.val B.property
      change (a-b)+b=a
      grind only
    have hh := Small.congr (add_valid (sub_valid A.property B.property) B.property) A.property he hs
    apply hh.mono
    rw [tauEulerDerivativeBudget]
    grind only

/-- A length-independent bound for the executable whole-product slope. -/
theorem finiteDiscriminantEulerSlope_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (finiteDiscriminantEulerSlope q N).val 2048 := by
  have h := finiteDiscriminantEulerSlope_budget_bound q r hr hrMax hq N
  have hv : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤4 by decide +kernel)
  have hb := budget_bound (4*r) hv (Rat.le_trans hmax (by decide +kernel)) N
  have hh := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤768 by decide +kernel)
  exact h.mono (by grind only)

theorem finiteDiscriminantEulerSlope_increment_geometric_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (finiteDiscriminantEulerSlope q (N+1)).val (finiteDiscriminantEulerSlope q N).val)
      (768*(4*r)^N) :=
  finiteDiscriminantEulerSlope_increment_bound q r hr hrMax hq N
    (finiteDiscriminantEulerSlope_bound q r hr hrMax hq N)

theorem finiteDiscriminantEuler_actual_derivative_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small ((finiteDiscriminantEulerMap_holomorphic N).derivative q trivial).val 2048 :=
  Small.congr (finiteDiscriminantEulerSlope q N).property
    ((finiteDiscriminantEulerMap_holomorphic N).derivative q trivial).property
    (equiv_symm (finiteDiscriminantEulerSlope_actual q N))
    (finiteDiscriminantEulerSlope_bound q r hr hrMax hq N)

end ComputableAnalysis.ModularForms
