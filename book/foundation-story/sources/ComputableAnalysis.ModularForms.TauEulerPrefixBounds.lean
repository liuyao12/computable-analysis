import ComputableAnalysis.ModularForms.TauEulerFactorBounds

/-! Length-independent bounds for the actual finite discriminant Euler products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def tauEulerGeometricBudget (t : Rat) : Nat → Rat
  | 0 => 0
  | N+1 => tauEulerGeometricBudget t N+t^(N+1)

theorem tauEulerGeometricBudget_nonnegative (t : Rat) (ht : 0≤t) (N : Nat) :
    0≤tauEulerGeometricBudget t N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih => exact Rat.add_nonneg ih (Rat.pow_nonneg ht)

theorem tauEulerGeometricBudget_identity (t : Rat) (N : Nat) :
    (1-t)*tauEulerGeometricBudget t N=t-t^(N+1) := by
  induction N with
  | zero => simp only [tauEulerGeometricBudget,Nat.zero_add,Rat.pow_one]; grind only
  | succ N ih =>
    rw [tauEulerGeometricBudget,Rat.pow_succ]
    grind only

theorem tauEulerGeometricBudget_bound (t : Rat) (ht : 0≤t) (htMax : t≤(1:Rat)/2) (N : Nat) :
    tauEulerGeometricBudget t N≤2*t := by
  have hg := tauEulerGeometricBudget_nonnegative t ht N
  have hid := tauEulerGeometricBudget_identity t N
  have hp : 0≤t^(N+1) := Rat.pow_nonneg ht
  have hmul : (1/2:Rat)*tauEulerGeometricBudget t N≤
      (1-t)*tauEulerGeometricBudget t N :=
    Rat.mul_le_mul_of_nonneg_right (by grind only) hg
  have hle : (1/2:Rat)*tauEulerGeometricBudget t N≤t := by grind only
  have htwo := Rat.mul_le_mul_of_nonneg_left hle (show (0:Rat)≤2 by decide +kernel)
  grind only

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

/-- Finite product deviation, controlled by a geometric sum independent of degree. -/
theorem finiteDiscriminantEulerProduct_deviation_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (finiteDiscriminantEulerProduct q N).val one)
      (144*tauEulerGeometricBudget (2*r) N) := by
  have ho : one.Valid := ofQComplex_valid _
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have htMax : 2*r≤(1:Rat)/2 := Rat.le_trans hmax (by decide +kernel)
  induction N with
  | zero =>
    exact Small.congr (ofQComplex_valid _) (sub_valid ho ho)
      (equiv_symm (add_neg_equiv one ho)) (Small.zero (show (0:Rat)≤144*0 by decide +kernel))
  | succ N ih =>
    let P := finiteDiscriminantEulerProduct q N
    let F : Scalar := ⟨LocalODE.power (sub one (LocalODE.power q.val (N+1))) 24,
      LocalODE.power_valid _ (sub_valid ho (LocalODE.power_valid _ q.property _)) 24⟩
    let B := 144*tauEulerGeometricBudget (2*r) N
    let D := 48*(2*r)^(N+1)
    have hB : 0≤B := Rat.mul_nonneg (by decide +kernel) (tauEulerGeometricBudget_nonnegative _ ht N)
    have hD : 0≤D := Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg ht)
    have hBMax : B≤1 := by
      have hbudget := tauEulerGeometricBudget_bound (2*r) ht htMax N
      have h144 := Rat.mul_le_mul_of_nonneg_left hbudget (show (0:Rat)≤144 by decide +kernel)
      have hr288 := Rat.mul_le_mul_of_nonneg_left hmax (show (0:Rat)≤288 by decide +kernel)
      have hsmall : 288*(2*r)≤1 := Rat.le_trans hr288 (by decide +kernel)
      change 144*tauEulerGeometricBudget (2*r) N≤1
      grind only
    have hf := tauEulerFactor_deviation_bound q r hr
      (Rat.le_trans hrMax (by decide +kernel)) hq N
    have hresult := product_deviation_bound P F B D hB hD ih hf
    change Small (sub (mul P.val F.val) one) _
    apply hresult.mono
    have hBD := Rat.mul_le_mul_of_nonneg_right hBMax hD
    change B+D+2*B*D≤144*(tauEulerGeometricBudget (2*r) N+(2*r)^(N+1))
    dsimp only [B,D] at *
    grind only

/-- A uniform coordinate bound for every actual finite Euler product. -/
theorem finiteDiscriminantEulerProduct_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (finiteDiscriminantEulerProduct q N).val 2 := by
  have h := finiteDiscriminantEulerProduct_deviation_bound q r hr hrMax hq N
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have hb := tauEulerGeometricBudget_bound (2*r) ht (Rat.le_trans hmax (by decide +kernel)) N
  have hb144 := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤144 by decide +kernel)
  have hr288 := Rat.mul_le_mul_of_nonneg_left hmax (show (0:Rat)≤288 by decide +kernel)
  have hBMax : 144*tauEulerGeometricBudget (2*r) N≤1 := by
    have hsmall : 288*(2*r)≤1 := Rat.le_trans hr288 (by decide +kernel)
    grind only
  have ho : Small one 1 := by
    simpa only [LocalODE.power,Rat.pow_zero] using
      LocalODE.power_small zero (ofQComplex_valid _) 0 Rat.le_refl (Small.zero Rat.le_refl) 0
  have he : (add (sub (finiteDiscriminantEulerProduct q N).val one) one).Equiv
      (finiteDiscriminantEulerProduct q N).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (finiteDiscriminantEulerProduct q N).property (ofQComplex_valid _))
        (ofQComplex_valid _)) (hright := (finiteDiscriminantEulerProduct q N).property)
    let p := ComplexRawQuotient.ofRaw (finiteDiscriminantEulerProduct q N).val
      (finiteDiscriminantEulerProduct q N).property
    change (p-1)+1=p
    grind only
  exact (Small.congr (add_valid (sub_valid (finiteDiscriminantEulerProduct q N).property
    (ofQComplex_valid _)) (ofQComplex_valid _)) (finiteDiscriminantEulerProduct q N).property
    he (LocalODE.small_add h ho)).mono (by grind only)

end ComputableAnalysis.ModularForms
