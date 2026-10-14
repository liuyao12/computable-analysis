import ComputableAnalysis.ModularForms.TauEulerPrefixBounds
import ComputableAnalysis.ModularForms.NomeDiscriminantNonvanishing

/-! A checked executable Euler-product value on a small represented nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem budget_difference_nonnegative (t : Rat) (ht : 0≤t) (i N : Nat) (hi : i≤N) :
    0≤tauEulerGeometricBudget t N-tauEulerGeometricBudget t i := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    rw [he]
    grind only
  | succ N ih =>
    by_cases hin : i≤N
    · have hh := ih hin
      have hp : 0≤t^(N+1) := Rat.pow_nonneg ht
      rw [tauEulerGeometricBudget]
      grind only
    · have he : i=N+1 := by omega
      rw [he]
      grind only

private theorem budget_tail_bound (t : Rat) (ht : 0≤t) (htMax : t≤(1:Rat)/2)
    (i N : Nat) (hi : i≤N) :
    tauEulerGeometricBudget t N-tauEulerGeometricBudget t i≤2*t^(i+1) := by
  have hg := budget_difference_nonnegative t ht i N hi
  have hidN := tauEulerGeometricBudget_identity t N
  have hidi := tauEulerGeometricBudget_identity t i
  have hp : 0≤t^(N+1) := Rat.pow_nonneg ht
  have hh := Rat.mul_le_mul_of_nonneg_right
    (show (1/2:Rat)≤1-t by grind only) hg
  have hle : (1/2:Rat)*(tauEulerGeometricBudget t N-tauEulerGeometricBudget t i)≤t^(i+1) := by
    grind only
  have htwo := Rat.mul_le_mul_of_nonneg_left hle (show (0:Rat)≤2 by decide +kernel)
  grind only

private theorem increment_identity (P F : Scalar) :
    (sub (mul P.val F.val) P.val).Equiv (mul P.val (sub F.val one)) := by
  have ho : one.Valid := ofQComplex_valid _
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (mul_valid P.property F.property) P.property)
    (hright := mul_valid P.property (sub_valid F.property ho))
  let p := ComplexRawQuotient.ofRaw P.val P.property
  let f := ComplexRawQuotient.ofRaw F.val F.property
  change p*f-p=p*(f-1)
  grind only

theorem finiteDiscriminantEulerProduct_increment_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (finiteDiscriminantEulerProduct q (N+1)).val
      (finiteDiscriminantEulerProduct q N).val) (192*(2*r)^(N+1)) := by
  let P := finiteDiscriminantEulerProduct q N
  have ho : one.Valid := ofQComplex_valid _
  let F : Scalar := ⟨LocalODE.power (sub one (LocalODE.power q.val (N+1))) 24,
    LocalODE.power_valid _ (sub_valid ho (LocalODE.power_valid _ q.property _)) 24⟩
  have hf := tauEulerFactor_deviation_bound q r hr (Rat.le_trans hrMax (by decide +kernel)) hq N
  have hp := finiteDiscriminantEulerProduct_bound q r hr hrMax hq N
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hd : 0≤48*(2*r)^(N+1) := Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg ht)
  have hm := Small.mul P.property (sub_valid F.property ho) (show (0:Rat)≤2 by decide +kernel) hd hp hf
  have hh := Small.congr (mul_valid P.property (sub_valid F.property ho))
    (sub_valid (mul_valid P.property F.property) P.property)
    (equiv_symm (increment_identity P F)) hm
  change Small (sub (mul P.val F.val) P.val) _
  apply hh.mono
  grind only

private theorem difference_telescope (A B C : Scalar) :
    (add (sub A.val B.val) (sub B.val C.val)).Equiv (sub A.val C.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
    (hright := sub_valid A.property C.property)
  let a := ComplexRawQuotient.ofRaw A.val A.property
  let b := ComplexRawQuotient.ofRaw B.val B.property
  let c := ComplexRawQuotient.ofRaw C.val C.property
  change (a-b)+(b-c)=a-c
  grind only

private theorem difference_budget_bound (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (i N : Nat) (hi : i≤N) :
    Small (sub (finiteDiscriminantEulerProduct q N).val (finiteDiscriminantEulerProduct q i).val)
      (192*(tauEulerGeometricBudget (2*r) N-tauEulerGeometricBudget (2*r) i)) := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    subst i
    have hv := (finiteDiscriminantEulerProduct q 0).property
    exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
      (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))
  | succ N ih =>
    by_cases hin : i≤N
    · let A := finiteDiscriminantEulerProduct q (N+1)
      let B := finiteDiscriminantEulerProduct q N
      let C := finiteDiscriminantEulerProduct q i
      have hh := LocalODE.small_add (finiteDiscriminantEulerProduct_increment_bound q r hr hrMax hq N) (ih hin)
      have hs := Small.congr (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
        (sub_valid A.property C.property) (difference_telescope A B C) hh
      apply hs.mono
      rw [tauEulerGeometricBudget]
      grind only
    · have he : i=N+1 := by omega
      subst i
      have hv := (finiteDiscriminantEulerProduct q (N+1)).property
      exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
        (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))

/-- A geometric Cauchy bound for the actual finite product sequence. -/
theorem finiteDiscriminantEulerProduct_cauchy (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (i N : Nat) (hi : i≤N) :
    Small (sub (finiteDiscriminantEulerProduct q N).val (finiteDiscriminantEulerProduct q i).val)
      (384*(2*r)^(i+1)) := by
  have h := difference_budget_bound q r hr hrMax hq i N hi
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have hb := budget_tail_bound (2*r) ht (Rat.le_trans hmax (by decide +kernel)) i N hi
  have hh := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤192 by decide +kernel)
  apply h.mono
  grind only

def tauEulerProductTail (r : Rat) (N : Nat) : Rat := 384*(2*r)^(N+1)

theorem tauEulerProductTail_shrinks (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/1024) :
    ShrinksToZero (tauEulerProductTail r) := by
  have ht : 0≤2*r := Rat.mul_nonneg (by decide +kernel) hr
  have hC : 0≤96*(2*r) := Rat.mul_nonneg (by decide +kernel) ht
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤2 by decide +kernel)
  have h := LocalODE.tail_bound_shrinks (96*(2*r)) (2*r) hC ht (Rat.le_trans hmax (by decide +kernel))
  have he : (fun N => 4*(96*(2*r))*(2*r)^N)=tauEulerProductTail r := by
    funext N
    unfold tauEulerProductTail
    rw [Rat.pow_succ]
    grind only
  rw [he] at h
  exact h

/-- Executable infinite Euler product with validity proved from finite-prefix errors. -/
def tauEulerProduct (q : Scalar) (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/1024)
    (hq : Small q.val r) : Scalar :=
  ⟨RepresentedCauchySum.value (fun N => (finiteDiscriminantEulerProduct q N).val)
      (fun N => (finiteDiscriminantEulerProduct q N).property) (tauEulerProductTail r),
    RepresentedCauchySum.value_valid _ _ _ (tauEulerProductTail_shrinks r hr hrMax)
      (finiteDiscriminantEulerProduct_cauchy q r hr hrMax hq)⟩

theorem tauEulerProduct_close_prefix (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (tauEulerProduct q r hr hrMax hq).val (finiteDiscriminantEulerProduct q N).val)
      (384*(2*r)^(N+1)) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (finiteDiscriminantEulerProduct_cauchy q r hr hrMax hq) N

theorem tauEulerProduct_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrMax : r≤(1:Rat)/1024) (hsMax : s≤(1:Rat)/1024)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (tauEulerProduct q r hr hrMax hq).val.Equiv (tauEulerProduct w s hs hsMax hw).val := by
  apply RepresentedCauchySum.value_congr _ _ _ _ _ _
    (tauEulerProductTail_shrinks r hr hrMax) (tauEulerProductTail_shrinks s hs hsMax)
    (fun N => Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hr)))
    (fun N => Rat.mul_nonneg (by decide +kernel)
      (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hs)))
    (finiteDiscriminantEulerProduct_cauchy q r hr hrMax hq)
    (finiteDiscriminantEulerProduct_cauchy w s hs hsMax hw)
  exact finiteDiscriminantEulerProduct_congr q w he

theorem tauEulerProduct_near_one (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) :
    Small (sub (tauEulerProduct q r hr hrMax hq).val one) (3/4:Rat) := by
  have h := tauEulerProduct_close_prefix q r hr hrMax hq 0
  simp only [finiteDiscriminantEulerProduct,Nat.zero_add,Rat.pow_one] at h
  have h768 := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤768 by decide +kernel)
  have he : 768*r≤(3/4:Rat) := Rat.le_trans h768 (by decide +kernel)
  apply h.mono
  grind only

theorem tauEulerProduct_nonzero (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) :
    NonzeroBoxSearch.Nonzero (tauEulerProduct q r hr hrMax hq) := by
  let O : Scalar := ⟨one,ofQComplex_valid _⟩
  apply scalar_nonzero_of_small_difference (tauEulerProduct q r hr hrMax hq) O (3/4)
    (tauEulerProduct_near_one q r hr hrMax hq)
  exact scalar_not_small_of_box O (3/4) 0 (Or.inl (by decide +kernel))

end ComputableAnalysis.ModularForms
