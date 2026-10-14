import ComputableAnalysis.ModularForms.WideEulerTailDerivativeBounds
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
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

private theorem difference_budget_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (i N : Nat) (hi : i≤N) :
    Small (sub (wideEulerTailSlope q N).val (wideEulerTailSlope q i).val)
      ((3/2:Rat)*(tauEulerDerivativeBudget ((1:Rat)/16) N-tauEulerDerivativeBudget ((1:Rat)/16) i)) := by
  induction N with
  | zero =>
    have he : i=0 := by omega
    subst i
    have hv := (wideEulerTailSlope q 0).property
    exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
      (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))
  | succ N ih =>
    by_cases hin : i≤N
    · let A := wideEulerTailSlope q (N+1)
      let B := wideEulerTailSlope q N
      let C := wideEulerTailSlope q i
      have hh := LocalODE.small_add
        (wideEulerTailSlope_increment_geometric_bound q hq N) (ih hin)
      have hs := Small.congr (add_valid (sub_valid A.property B.property) (sub_valid B.property C.property))
        (sub_valid A.property C.property) (difference_telescope A B C) hh
      apply hs.mono
      rw [tauEulerDerivativeBudget]
      grind only
    · have he : i=N+1 := by omega
      subst i
      have hv := (wideEulerTailSlope q (N+1)).property
      exact Small.congr (ofQComplex_valid _) (sub_valid hv hv)
        (equiv_symm (add_neg_equiv _ hv)) (Small.zero (by grind only))


/-- Actual finite-tail derivatives have uniform geometric Cauchy errors on the wider disk. -/
theorem wideEulerTailSlope_cauchy (q : Scalar) (hq : Small q.val ((1:Rat)/64))
    (i N : Nat) (hi : i≤N) :
    Small (sub (wideEulerTailSlope q N).val (wideEulerTailSlope q i).val)
      (3*((1:Rat)/16)^i) := by
  have h := difference_budget_bound q hq i N hi
  have hb := budget_tail_bound (1/16) (by decide +kernel) (by decide +kernel) i N hi
  have hh := Rat.mul_le_mul_of_nonneg_left hb (show (0:Rat)≤3/2 by decide +kernel)
  exact h.mono (by grind only)

def wideEulerTailDerivativeError (N : Nat) : Rat := 3*((1:Rat)/16)^N

theorem wideEulerTailDerivativeError_shrinks : ShrinksToZero wideEulerTailDerivativeError := by
  have h := LocalODE.tail_bound_shrinks (3/4) (1/16)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  change ShrinksToZero (fun N => 3*((1:Rat)/16)^N)
  simpa only [show (4:Rat)*(3/4)=3 by decide +kernel] using h

/-- Executable limit of actual finite-tail slopes, before identifying the infinite derivative. -/
def wideEulerTailDerivativeValue (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : Scalar :=
  ⟨RepresentedCauchySum.value (fun N => (wideEulerTailSlope q N).val)
      (fun N => (wideEulerTailSlope q N).property) wideEulerTailDerivativeError,
    RepresentedCauchySum.value_valid _ _ _ wideEulerTailDerivativeError_shrinks
      (wideEulerTailSlope_cauchy q hq)⟩

theorem wideEulerTailDerivativeValue_close_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailDerivativeValue q hq).val (wideEulerTailSlope q N).val)
      (wideEulerTailDerivativeError N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (wideEulerTailSlope_cauchy q hq) N

theorem wideEulerTailDerivativeValue_close_actual_prefix (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailDerivativeValue q hq).val
      ((wideEulerTailMap_holomorphic N).derivative q trivial).val) (wideEulerTailDerivativeError N) := by
  let D := wideEulerTailDerivativeValue q hq
  let P := wideEulerTailSlope q N
  let A := (wideEulerTailMap_holomorphic N).derivative q trivial
  exact Small.congr (sub_valid D.property P.property) (sub_valid D.property A.property)
    (FunctionTheory.sub_congr (equiv_refl _ D.property) (equiv_symm (wideEulerTailSlope_actual q N)))
    (wideEulerTailDerivativeValue_close_prefix q hq N)

def wideEulerTailDerivativeCandidate (q : Scalar) (hq : wideLambertFifthDomain q) : Scalar :=
  wideEulerTailDerivativeValue q (LocalODE.interior_bound _ q hq)

/-- The actual finite derivative tails prove continuity of the executable slope limit. -/
theorem wideEulerTailDerivativeCandidate_continuous :
    Nonempty (ContinuousOn wideLambertFifthDomain wideEulerTailDerivativeCandidate) := by
  let p := fun N q (_ : wideLambertFifthDomain q) => (wideEulerTailMap_holomorphic N).derivative q trivial
  have hp : ∀ N, ContinuousOn wideLambertFifthDomain (p N) := fun N =>
    restrictContinuous (wideEulerTailMap_holomorphic N).derivative
      (wideEulerTailMap_holomorphic N).continuousDerivative (fun _ _ => trivial)
  exact ⟨continuousOn_of_uniform_prefixes wideEulerTailDerivativeCandidate p hp wideEulerTailDerivativeError
    wideEulerTailDerivativeError_shrinks
    (fun N q hq => wideEulerTailDerivativeValue_close_actual_prefix q (LocalODE.interior_bound _ q hq) N)⟩


/-- The executable limit of actual wider slopes is representation invariant. -/
theorem wideEulerTailDerivativeValue_congr (q w : Scalar) (hq : Small q.val ((1:Rat)/64))
    (hw : Small w.val ((1:Rat)/64)) (he : q.val.Equiv w.val) :
    (wideEulerTailDerivativeValue q hq).val.Equiv (wideEulerTailDerivativeValue w hw).val := by
  apply RepresentedCauchySum.value_congr _ _ _ _ _ _
    wideEulerTailDerivativeError_shrinks wideEulerTailDerivativeError_shrinks
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/16 by decide +kernel)))
    (fun N => Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/16 by decide +kernel)))
    (wideEulerTailSlope_cauchy q hq) (wideEulerTailSlope_cauchy w hw)
  exact wideEulerTailSlope_congr q w he

end ComputableAnalysis.ModularForms
