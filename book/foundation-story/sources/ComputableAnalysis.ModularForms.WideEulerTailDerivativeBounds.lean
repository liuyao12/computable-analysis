import ComputableAnalysis.ModularForms.WideEulerTailDerivative
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem powers_compare (N : Nat) : ((1:Rat)/32)^N≤((1:Rat)/16)^N := by
  induction N with
  | zero => simp only [Rat.pow_zero]; exact Rat.le_refl
  | succ N ih =>
    rw [Rat.pow_succ,Rat.pow_succ]
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel))
      (Rat.mul_le_mul_of_nonneg_left (show (1:Rat)/32≤1/16 by decide +kernel)
        (Rat.pow_nonneg (show (0:Rat)≤1/16 by decide +kernel)))

/-- A uniform bound on the current slope controls the next actual slope increment. -/
theorem wideEulerTailSlope_increment_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat)
    (hD : Small (wideEulerTailSlope q N).val 2) :
    Small (sub (wideEulerTailSlope q (N+1)).val (wideEulerTailSlope q N).val)
      ((3/2:Rat)*((1:Rat)/16)^N) := by
  let D := wideEulerTailSlope q N
  let F := tauEulerFactorValue q (N+2)
  let P := wideEulerTailPrefix q N
  let G := tauEulerFactorSlope q (N+2)
  have ho : one.Valid := ofQComplex_valid _
  have hf := wideEulerTailFactor_deviation q hq N
  have hp := wideEulerTailPrefix_bound q hq N
  have hg := wideEulerTailFactorSlope_bound q hq N
  have hm := Small.mul D.property (sub_valid F.property ho) (show (0:Rat)≤2 by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/32 by decide +kernel))) hD hf
  have hn := Small.mul P.property G.property (show (0:Rat)≤2 by decide +kernel)
    (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg (show (0:Rat)≤1/16 by decide +kernel))) hp hg
  have hs := Small.congr (add_valid (mul_valid D.property (sub_valid F.property ho)) (mul_valid P.property G.property))
    (sub_valid (wideEulerTailSlope q (N+1)).property D.property)
    (equiv_symm (wideEulerTailSlope_increment q N)) (LocalODE.small_add hm hn)
  have hc := Rat.mul_le_mul_of_nonneg_left (powers_compare N) (show (0:Rat)≤3/512 by decide +kernel)
  have ht : 0≤((1:Rat)/16)^N := Rat.pow_nonneg (by decide +kernel)
  apply hs.mono
  rw [Rat.pow_succ ((1:Rat)/32) N]
  generalize ((1:Rat)/32)^N=A at hc ⊢
  generalize ((1:Rat)/16)^N=B at hc ht ⊢
  grind only

private theorem slope_budget_bound (N : Nat) : tauEulerDerivativeBudget (1/16) N≤(16/15:Rat) := by
  have h := tauEulerDerivativeBudget_identity (1/16) N
  have hp : 0≤((1:Rat)/16)^N := Rat.pow_nonneg (by decide +kernel)
  grind only

/-- Actual finite-tail slopes are bounded independently of the number of factors. -/
theorem wideEulerTailSlope_budget_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (wideEulerTailSlope q N).val ((3/2:Rat)*tauEulerDerivativeBudget (1/16) N) := by
  induction N with
  | zero => exact Small.zero (by decide +kernel)
  | succ N ih =>
    have hb := Rat.mul_le_mul_of_nonneg_left (slope_budget_bound N) (show (0:Rat)≤3/2 by decide +kernel)
    have hD : Small (wideEulerTailSlope q N).val 2 := ih.mono (by grind only)
    have hinc := wideEulerTailSlope_increment_bound q hq N hD
    have hs := LocalODE.small_add hinc ih
    let A := wideEulerTailSlope q (N+1)
    let B := wideEulerTailSlope q N
    have he : (add (sub A.val B.val) B.val).Equiv A.val := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (sub_valid A.property B.property) B.property) (hright := A.property)
      let a := ComplexRawQuotient.ofRaw A.val A.property
      let b := ComplexRawQuotient.ofRaw B.val B.property
      change (a-b)+b=a
      grind only
    apply (Small.congr (add_valid (sub_valid A.property B.property) B.property) A.property he hs).mono
    rw [tauEulerDerivativeBudget]
    grind only

theorem wideEulerTailSlope_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (wideEulerTailSlope q N).val 2 := by
  have h := wideEulerTailSlope_budget_bound q hq N
  have hb := Rat.mul_le_mul_of_nonneg_left (slope_budget_bound N) (show (0:Rat)≤3/2 by decide +kernel)
  exact h.mono (by grind only)

/-- Uniform geometric increments of the actual finite-tail derivatives. -/
theorem wideEulerTailSlope_increment_geometric_bound (q : Scalar) (hq : Small q.val ((1:Rat)/64)) (N : Nat) :
    Small (sub (wideEulerTailSlope q (N+1)).val (wideEulerTailSlope q N).val)
      ((3/2:Rat)*((1:Rat)/16)^N) :=
  wideEulerTailSlope_increment_bound q hq N (wideEulerTailSlope_bound q hq N)

end ComputableAnalysis.ModularForms
