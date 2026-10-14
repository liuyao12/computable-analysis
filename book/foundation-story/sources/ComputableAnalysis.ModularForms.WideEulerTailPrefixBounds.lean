import ComputableAnalysis.ModularForms.WideEulerTailFactors
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
private theorem product_deviation_identity (P F : Scalar) :
    (sub (mul P.val F.val) one).Equiv
      (add (add (sub P.val one) (sub F.val one))
        (mul (sub P.val one) (sub F.val one))) := by
  have ho : one.Valid := ofQComplex_valid _
  have hP := sub_valid P.property ho
  have hF := sub_valid F.property ho
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid P.property F.property) ho)
    (hright := add_valid (add_valid hP hF) (mul_valid hP hF))
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  change p*f-1=(p-1)+(f-1)+(p-1)*(f-1)
  grind only

private theorem product_deviation_bound (P F : Scalar) (B D : Rat) (hB : 0≤B) (hD : 0≤D)
    (hP : Small (sub P.val one) B) (hF : Small (sub F.val one) D) :
    Small (sub (mul P.val F.val) one) (B+D+2*B*D) := by
  have ho : one.Valid := ofQComplex_valid _
  have hm := Small.mul (sub_valid P.property ho) (sub_valid F.property ho) hB hD hP hF
  exact Small.congr (add_valid (add_valid (sub_valid P.property ho) (sub_valid F.property ho))
      (mul_valid (sub_valid P.property ho) (sub_valid F.property ho)))
    (sub_valid (mul_valid P.property F.property) ho)
    (equiv_symm (product_deviation_identity P F)) (LocalODE.small_add (LocalODE.small_add hP hF) hm)


private theorem tail_budget_bound (N : Nat) :
    (9/64:Rat)*tauEulerGeometricBudget (1/32) N≤(9/1024:Rat) := by
  have h := Rat.mul_le_mul_of_nonneg_left
    (tauEulerGeometricBudget_bound (1/32) (by decide +kernel) (by decide +kernel) N)
    (show (0:Rat)≤9/64 by decide +kernel)
  exact Rat.le_trans h (by decide +kernel)

/-- Length-independent deviation bound for the actual tail starting at the third factor. -/
theorem wideEulerTailPrefix_deviation_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailPrefix q N).val one)
      ((9/64:Rat)*tauEulerGeometricBudget (1/32) N) := by
  have ho : one.Valid := ofQComplex_valid _
  induction N with
  | zero =>
    exact Small.congr (ofQComplex_valid _) (sub_valid ho ho)
      (equiv_symm (add_neg_equiv one ho)) (Small.zero (by decide +kernel))
  | succ N ih =>
    let P := wideEulerTailPrefix q N
    let F := tauEulerFactorValue q (N+2)
    let B := (9/64:Rat)*tauEulerGeometricBudget (1/32) N
    let D := (3/64:Rat)*((1:Rat)/32)^(N+1)
    have hB : 0≤B := Rat.mul_nonneg (by decide +kernel)
      (tauEulerGeometricBudget_nonnegative (1/32) (by decide +kernel) N)
    have hD : 0≤D := Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel))
    have hBMax : B≤1 := Rat.le_trans (tail_budget_bound N) (by decide +kernel)
    have hresult := product_deviation_bound P F B D hB hD ih (wideEulerTailFactor_deviation q hq N)
    change Small (sub (mul P.val F.val) one) _
    apply hresult.mono
    have hBD := Rat.mul_le_mul_of_nonneg_right hBMax hD
    change B+D+2*B*D≤(9/64:Rat)*(tauEulerGeometricBudget (1/32) N+((1:Rat)/32)^(N+1))
    dsimp only [B,D] at *
    grind only

/-- Uniform bound for every actual finite tail. -/
theorem wideEulerTailPrefix_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (wideEulerTailPrefix q N).val 2 := by
  have h := wideEulerTailPrefix_deviation_bound q hq N
  have hb := tail_budget_bound N
  have ho : Small one 1 := by
    simpa only [LocalODE.power,Rat.pow_zero] using
      LocalODE.power_small zero (ofQComplex_valid _) 0 Rat.le_refl (Small.zero Rat.le_refl) 0
  have he : (add (sub (wideEulerTailPrefix q N).val one) one).Equiv (wideEulerTailPrefix q N).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (wideEulerTailPrefix q N).property (ofQComplex_valid _)) (ofQComplex_valid _))
      (hright := (wideEulerTailPrefix q N).property)
    let P := ComplexRawQuotient.ofRaw (wideEulerTailPrefix q N).val (wideEulerTailPrefix q N).property
    change (P-1)+1=P
    grind only
  exact (Small.congr (add_valid (sub_valid (wideEulerTailPrefix q N).property (ofQComplex_valid _))
    (ofQComplex_valid _)) (wideEulerTailPrefix q N).property he (LocalODE.small_add h ho)).mono (by grind only)

end ComputableAnalysis.ModularForms
