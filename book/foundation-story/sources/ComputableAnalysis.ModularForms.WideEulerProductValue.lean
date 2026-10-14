import ComputableAnalysis.ModularForms.WideEulerTailPrefixBounds
import ComputableAnalysis.ModularForms.TauEulerProductLimit
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
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


/-- The actual finite tail increments have a summable uniform majorant. -/
theorem wideEulerTailPrefix_increment_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailPrefix q (N+1)).val (wideEulerTailPrefix q N).val)
      ((3/16:Rat)*((1:Rat)/32)^(N+1)) := by
  let P := wideEulerTailPrefix q N
  let F := tauEulerFactorValue q (N+2)
  have ho : one.Valid := ofQComplex_valid _
  have hf := wideEulerTailFactor_deviation q hq N
  have hp := wideEulerTailPrefix_bound q hq N
  have hd : 0≤(3/64:Rat)*((1:Rat)/32)^(N+1) := Rat.mul_nonneg (by decide +kernel)
    (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel))
  have hm := Small.mul P.property (sub_valid F.property ho) (show (0:Rat)≤2 by decide +kernel) hd hp hf
  have hh := Small.congr (mul_valid P.property (sub_valid F.property ho))
    (sub_valid (mul_valid P.property F.property) P.property) (equiv_symm (increment_identity P F)) hm
  change Small (sub (mul P.val F.val) P.val) _
  exact hh.mono (by grind only)

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

private theorem tail_difference_budget_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (i N : Nat) (hi : i≤N) :
    Small (sub (wideEulerTailPrefix q N).val (wideEulerTailPrefix q i).val)
      ((3/16:Rat)*(tauEulerGeometricBudget ((1:Rat)/32) N-tauEulerGeometricBudget ((1:Rat)/32) i)) := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    subst i
    have hv := (wideEulerTailPrefix q 0).property
    exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
      (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))
  | succ N ih =>
    by_cases hin : i≤N
    · let A := wideEulerTailPrefix q (N+1)
      let B := wideEulerTailPrefix q N
      let C := wideEulerTailPrefix q i
      have hh := LocalODE.small_add (wideEulerTailPrefix_increment_bound q hq N) (ih hin)
      have hs := Small.congr (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
        (sub_valid A.property C.property) (difference_telescope A B C) hh
      apply hs.mono
      rw [tauEulerGeometricBudget]
      grind only
    · have he : i=N+1 := by omega
      subst i
      have hv := (wideEulerTailPrefix q (N+1)).property
      exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
        (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))


/-- Cauchy estimate for every pair of actual finite tails. -/
theorem wideEulerTailPrefix_cauchy (q : Scalar) (hq : Small q.val ((1:Rat)/64))
    (i N : Nat) (hi : i≤N) :
    Small (sub (wideEulerTailPrefix q N).val (wideEulerTailPrefix q i).val)
      ((3/8:Rat)*((1:Rat)/32)^(i+1)) := by
  have h := tail_difference_budget_bound q hq i N hi
  have hb := budget_tail_bound (1/32) (by decide +kernel) (by decide +kernel) i N hi
  have hh := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤3/16 by decide +kernel)
  exact h.mono (by grind only)

/-- Explicit geometric tail schedule for the wider infinite Euler tail. -/
def wideEulerTailError (N : Nat) : Rat := (3/8)*((1:Rat)/32)^(N+1)

theorem wideEulerTailError_shrinks : ShrinksToZero wideEulerTailError := by
  have h := LocalODE.tail_bound_shrinks (3/1024) (1/32)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have he : (fun N : Nat => 4*(3/1024:Rat)*((1:Rat)/32)^N)=wideEulerTailError := by
    funext N
    unfold wideEulerTailError
    rw [Rat.pow_succ]
    grind only
  rw [he] at h
  exact h

/-- Executable limit of the actual Euler tail on the larger disk. -/
def wideEulerTailValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨RepresentedCauchySum.value (fun N => (wideEulerTailPrefix q N).val)
      (fun N => (wideEulerTailPrefix q N).property) wideEulerTailError,
    RepresentedCauchySum.value_valid _ _ _ wideEulerTailError_shrinks (wideEulerTailPrefix_cauchy q hq)⟩

theorem wideEulerTailValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailValue q hq).val (wideEulerTailPrefix q N).val) (wideEulerTailError N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (wideEulerTailPrefix_cauchy q hq) N

/-- The actual wider infinite tail is quantitatively separated from zero. -/
theorem wideEulerTailValue_nonzero (q : Scalar) (hq : Small q.val ((1:Rat)/64)) :
    NonzeroBoxSearch.Nonzero (wideEulerTailValue q hq) := by
  have h := wideEulerTailValue_close_prefix q hq 0
  rw [show wideEulerTailError 0=(3/256:Rat) by decide +kernel] at h
  apply scalar_nonzero_of_small_difference (wideEulerTailValue q hq) oneScalar (3/256) h
  exact scalar_not_small_of_box oneScalar (3/256) 0 (Or.inl (by decide +kernel))

/-- The actual full infinite Euler product, retaining its first two finite factors. -/
def wideEulerProductValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  scalarProduct (finiteDiscriminantEulerProduct q 2) (wideEulerTailValue q hq)

theorem wideEulerProductValue_nonzero (q : Scalar) (hq : Small q.val ((1:Rat)/64)) :
    NonzeroBoxSearch.Nonzero (wideEulerProductValue q hq) :=
  scalar_mul_nonzero (finiteDiscriminantEulerProduct q 2) (wideEulerTailValue q hq)
    (finiteDiscriminantEulerProduct_wide_nonzero q hq 2) (wideEulerTailValue_nonzero q hq)

end ComputableAnalysis.ModularForms
