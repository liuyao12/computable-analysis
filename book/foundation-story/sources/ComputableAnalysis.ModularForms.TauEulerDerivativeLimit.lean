import ComputableAnalysis.ModularForms.TauFiniteDerivativeBounds

/-! A valid executable limit of the actual finite-product slopes.
Identification as the derivative of the infinite product is a separate theorem. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
open DomainFunctions

private theorem budget_difference_nonnegative (v : Rat) (hv : 0≤v) (i N : Nat) (hi : i≤N) :
    0≤tauEulerDerivativeBudget v N-tauEulerDerivativeBudget v i := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    rw [he]
    grind only
  | succ N ih =>
    by_cases hin : i≤N
    · have hh := ih hin
      have hp : 0≤v^N := Rat.pow_nonneg hv
      rw [tauEulerDerivativeBudget]
      grind only
    · have he : i=N+1 := by omega
      rw [he]
      grind only

private theorem budget_tail_bound (v : Rat) (hv : 0≤v) (hvMax : v≤(1:Rat)/2)
    (i N : Nat) (hi : i≤N) :
    tauEulerDerivativeBudget v N-tauEulerDerivativeBudget v i≤2*v^i := by
  have hg := budget_difference_nonnegative v hv i N hi
  have hidN := tauEulerDerivativeBudget_identity v N
  have hidi := tauEulerDerivativeBudget_identity v i
  have hp : 0≤v^N := Rat.pow_nonneg hv
  have hh := Rat.mul_le_mul_of_nonneg_right (show (1/2:Rat)≤1-v by grind only) hg
  have hle : (1/2:Rat)*(tauEulerDerivativeBudget v N-tauEulerDerivativeBudget v i)≤v^i := by
    grind only
  have htwo := Rat.mul_le_mul_of_nonneg_left hle (show (0:Rat)≤2 by decide +kernel)
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
    Small (sub (finiteDiscriminantEulerSlope q N).val (finiteDiscriminantEulerSlope q i).val)
      (768*(tauEulerDerivativeBudget (4*r) N-tauEulerDerivativeBudget (4*r) i)) := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    subst i
    have hv := (finiteDiscriminantEulerSlope q 0).property
    exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
      (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))
  | succ N ih =>
    by_cases hin : i≤N
    · let A := finiteDiscriminantEulerSlope q (N+1)
      let B := finiteDiscriminantEulerSlope q N
      let C := finiteDiscriminantEulerSlope q i
      have hh := LocalODE.small_add
        (finiteDiscriminantEulerSlope_increment_geometric_bound q r hr hrMax hq N) (ih hin)
      have hs := Small.congr (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
        (sub_valid A.property C.property) (difference_telescope A B C) hh
      apply hs.mono
      rw [tauEulerDerivativeBudget]
      grind only
    · have he : i=N+1 := by omega
      subst i
      have hv := (finiteDiscriminantEulerSlope q (N+1)).property
      exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
        (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))

/-- Uniform Cauchy errors for the executable slopes of whole products. -/
theorem finiteDiscriminantEulerSlope_cauchy (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (i N : Nat) (hi : i≤N) :
    Small (sub (finiteDiscriminantEulerSlope q N).val (finiteDiscriminantEulerSlope q i).val)
      (1536*(4*r)^i) := by
  have h := difference_budget_bound q r hr hrMax hq i N hi
  have hv : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤4 by decide +kernel)
  have hb := budget_tail_bound (4*r) hv (Rat.le_trans hmax (by decide +kernel)) i N hi
  have hh := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤768 by decide +kernel)
  apply h.mono
  grind only

def tauEulerDerivativeTail (r : Rat) (N : Nat) : Rat := 1536*(4*r)^N

theorem tauEulerDerivativeTail_shrinks (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/1024) :
    ShrinksToZero (tauEulerDerivativeTail r) := by
  have hv : 0≤4*r := Rat.mul_nonneg (by decide +kernel) hr
  have hmax := Rat.mul_le_mul_of_nonneg_left hrMax (show (0:Rat)≤4 by decide +kernel)
  have h := LocalODE.tail_bound_shrinks 384 (4*r) (by decide +kernel) hv
    (Rat.le_trans hmax (by decide +kernel))
  change ShrinksToZero (fun N => 1536*(4*r)^N)
  simpa only [show (4:Rat)*384=1536 by decide +kernel] using h

/-- An executable derivative candidate with proved validity and shrinking errors. -/
def tauEulerDerivativeValue (q : Scalar) (r : Rat) (hr : 0≤r) (hrMax : r≤(1:Rat)/1024)
    (hq : Small q.val r) : Scalar :=
  ⟨RepresentedCauchySum.value (fun N => (finiteDiscriminantEulerSlope q N).val)
      (fun N => (finiteDiscriminantEulerSlope q N).property) (tauEulerDerivativeTail r),
    RepresentedCauchySum.value_valid _ _ _ (tauEulerDerivativeTail_shrinks r hr hrMax)
      (finiteDiscriminantEulerSlope_cauchy q r hr hrMax hq)⟩

theorem tauEulerDerivativeValue_close_prefix (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (tauEulerDerivativeValue q r hr hrMax hq).val (finiteDiscriminantEulerSlope q N).val)
      (1536*(4*r)^N) :=
  RepresentedCauchySum.value_close_prefix _ _ _
    (finiteDiscriminantEulerSlope_cauchy q r hr hrMax hq) N

theorem tauEulerDerivativeValue_congr (q w : Scalar) (r s : Rat) (hr : 0≤r) (hs : 0≤s)
    (hrMax : r≤(1:Rat)/1024) (hsMax : s≤(1:Rat)/1024)
    (hq : Small q.val r) (hw : Small w.val s) (he : q.val.Equiv w.val) :
    (tauEulerDerivativeValue q r hr hrMax hq).val.Equiv
      (tauEulerDerivativeValue w s hs hsMax hw).val := by
  apply RepresentedCauchySum.value_congr _ _ _ _ _ _
    (tauEulerDerivativeTail_shrinks r hr hrMax) (tauEulerDerivativeTail_shrinks s hs hsMax)
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hr)))
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (Rat.mul_nonneg (by decide +kernel) hs)))
    (finiteDiscriminantEulerSlope_cauchy q r hr hrMax hq)
    (finiteDiscriminantEulerSlope_cauchy w s hs hsMax hw)
  exact finiteDiscriminantEulerSlope_congr q w he

theorem tauEulerDerivativeValue_close_actual_prefix (q : Scalar) (r : Rat) (hr : 0≤r)
    (hrMax : r≤(1:Rat)/1024) (hq : Small q.val r) (N : Nat) :
    Small (sub (tauEulerDerivativeValue q r hr hrMax hq).val
      ((finiteDiscriminantEulerMap_holomorphic N).derivative q trivial).val)
      (1536*(4*r)^N) := by
  let D := tauEulerDerivativeValue q r hr hrMax hq
  let P := finiteDiscriminantEulerSlope q N
  let A := (finiteDiscriminantEulerMap_holomorphic N).derivative q trivial
  exact Small.congr (sub_valid D.property P.property) (sub_valid D.property A.property)
    (FunctionTheory.sub_congr (equiv_refl _ D.property)
      (equiv_symm (finiteDiscriminantEulerSlope_actual q N)))
    (tauEulerDerivativeValue_close_prefix q r hr hrMax hq N)

def tauEulerNomeDerivativeCandidate (q : Scalar) (hq : tauEulerNomeDomain q) : Scalar :=
  tauEulerDerivativeValue q (1/1024) (by decide +kernel) Rat.le_refl
    (LocalODE.interior_bound _ q hq)

theorem tauEulerNomeDerivativeCandidate_continuous :
    Nonempty (ContinuousOn tauEulerNomeDomain tauEulerNomeDerivativeCandidate) := by
  let p := fun N q (_ : tauEulerNomeDomain q) =>
    (finiteDiscriminantEulerMap_holomorphic N).derivative q trivial
  have hp : ∀ N, ContinuousOn tauEulerNomeDomain (p N) := fun N =>
    restrictContinuous (finiteDiscriminantEulerMap_holomorphic N).derivative
      (finiteDiscriminantEulerMap_holomorphic N).continuousDerivative (fun _ _ => trivial)
  exact ⟨continuousOn_of_uniform_prefixes tauEulerNomeDerivativeCandidate p hp
    (tauEulerDerivativeTail (1/1024))
    (tauEulerDerivativeTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl)
    (fun N q hq => tauEulerDerivativeValue_close_actual_prefix q (1/1024) (by decide +kernel)
      Rat.le_refl (LocalODE.interior_bound _ q hq) N)⟩

end ComputableAnalysis.ModularForms
