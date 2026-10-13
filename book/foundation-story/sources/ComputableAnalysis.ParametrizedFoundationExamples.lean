import ComputableAnalysis.ParametrizedCalculus
import ComputableAnalysis.ParametrizedComplexContinuity
import ComputableAnalysis.BracketDerivativeExamples
import ComputableAnalysis.AlgebraicFunctions

/-! Concrete applications and failure cases for the parametrized foundation. -/
namespace ComputableAnalysis.ParametrizedFoundationExamples
open RawLimit BracketDerivative BracketContinuity

theorem square_continuous_closed {x : RealRaw} (hx : x.Valid)
    (ha : (RealRaw.ofRat 0).Le x) (hb : x.Le (RealRaw.ofRat 1)) :
    ∃ c, HasContinuousAt (inDomainInterval 0 1) squareOnUnit.rationalValue x c :=
  squareOnUnit_intervalRegular.continuousAt_closed (by decide +kernel) hx ha hb

theorem affine_finite_certificate {a b m c : Rat} {x : RealRaw} (hx : x.Valid)
    (hbracket : ∃ A, Admissible (inDomainInterval a b) x A) :
    HasDerivativeAt (inDomainInterval a b)
      (FunctionOnInterval.exactRat (fun r => m*r+c) a b).rationalValue x (RealRaw.ofRat m) := by
  let G := FunctionOnInterval.exactRat (fun _ => m) a b
  have hG : HasContinuousAt (inDomainInterval a b) G.rationalValue x (RealRaw.ofRat m) := by
    apply BracketContinuity.congr_function
      (BracketContinuity.constant (c := RealRaw.ofRat m) hx (RealRaw.ofRat_valid m) hbracket)
      (fun r _ => G.rationalValue_valid r)
    intro r hr
    have hr' : a ≤ r ∧ r ≤ b := hr
    unfold FunctionOnInterval.rationalValue
    split
    · exact RealRaw.equiv_refl (RealRaw.ofRat m) (RealRaw.ofRat_valid m)
    · rename_i hn
      exact False.elim (hn hr')
  exact (FunctionOnInterval.exactRatAffineDerivative a b m c).toParametrizedDerivative
    (fun _ => by change 0 < (1 : Nat); exact Nat.zero_lt_one) hG

def jump (r : Rat) : RealRaw := RealRaw.ofRat (if r < 0 then -1 else 1)

/-- Full-neighborhood coverage rules out a discontinuity that favorable
one-sided samples could hide. -/
theorem jump_not_continuous (c : RealRaw) :
    ¬ HasContinuousAt (fun _ => True) jump (RealRaw.ofRat 0) c := by
  intro h
  let A := BracketDerivative.enlarged (RealRaw.ofRat 0)
  have hA := BracketDerivative.enlarged_admissible (x := RealRaw.ofRat 0) (RealRaw.ofRat_valid 0)
  obtain ⟨hc,Q,n,m,hn,hm,hC,hCc,cover⟩ := h.2.2.2.2 A hA
  obtain ⟨K,hK⟩ := hC.2.2 ⟨1,by decide +kernel⟩
  have hw := hK K (Nat.le_refl _)
  have hp := BracketDerivative.allowance_pos (n K)
  have hl : (A.compute (n K)).lo < 0 := by
    change (0:Rat)-BracketDerivative.allowance (n K)<0
    grind only
  have bounds := RealRaw.interval_order_of_valid A hA.2.1 (n K)
  have left := cover K (jump (A.compute (n K)).lo)
    ⟨(A.compute (n K)).lo,Rat.le_refl,bounds,rfl⟩
  have right := cover K (jump 0) ⟨0,by change (0:Rat)-BracketDerivative.allowance (n K)≤0; grind only,
    by change (0:Rat)≤0+BracketDerivative.allowance (n K); grind only,rfl⟩
  have lo := left.1 0 0
  have hi := right.2 0 0
  simp only [jump,if_pos hl] at lo
  change (Q (n K) (m K)).lo ≤ -1 at lo
  change 1 ≤ (Q (n K) (m K)).hi at hi
  change (Q (n K) (m K)).hi-(Q (n K) (m K)).lo ≤ 1 at hw
  grind only

end ComputableAnalysis.ParametrizedFoundationExamples
