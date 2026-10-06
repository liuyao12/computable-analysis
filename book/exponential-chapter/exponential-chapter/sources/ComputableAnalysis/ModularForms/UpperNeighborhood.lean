import ComputableAnalysis.ModularForms.ActionComposition
import ComputableAnalysis.RiemannHilbert.DomainFunctions

/-! Executable rational neighborhoods inside the represented upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def positiveImagStage (a : Scalar) (k : Nat) : Bool :=
  decide (0 < (a.val.compute k).lo.im)

theorem positiveImagStage_eventually (a : Scalar) (ha : InUpperHalfPlane a.val) :
    ∃ N, ∀ k, N ≤ k → positiveImagStage a k = true := by
  obtain ⟨N,hN⟩ := ha
  change 0 < (a.val.compute N).lo.im at hN
  refine ⟨N, fun k hk => ?_⟩
  have hn := valid_nestedIn a.property hk
  simp only [positiveImagStage, decide_eq_true_eq]
  have hl := hn.1.2
  grind only

/-- Find a strictly positive lower imaginary endpoint by terminating rational search. -/
def positiveImagIndex (a : Scalar) (ha : InUpperHalfPlane a.val) : Nat :=
  PrecisionSearch.firstFrom (positiveImagStage a) (positiveImagStage_eventually a ha) 0

theorem positiveImagIndex_spec (a : Scalar) (ha : InUpperHalfPlane a.val) :
    0 < (a.val.compute (positiveImagIndex a ha)).lo.im := by
  have h := (PrecisionSearch.firstFrom_spec (positiveImagStage a)
    (positiveImagStage_eventually a ha) 0).2
  simpa only [positiveImagIndex, positiveImagStage, decide_eq_true_eq] using h

/-- Half a positive lower imaginary endpoint is a safe neighborhood radius. -/
def upperRadius (a : Scalar) (ha : InUpperHalfPlane a.val) : QPos :=
  ⟨(a.val.compute (positiveImagIndex a ha)).lo.im / 2,
    by have h := positiveImagIndex_spec a ha; grind only⟩

theorem upperRadius_inside (a : Scalar) (ha : InUpperHalfPlane a.val) (z : Scalar)
    (hs : Small (sub z.val a.val) (upperRadius a ha).val) : InUpperHalfPlane z.val := by
  let N := positiveImagIndex a ha
  let L := (a.val.compute N).lo.im
  have hL : 0 < L := positiveImagIndex_spec a ha
  let eps : QPos := ⟨L/4, by grind only⟩
  obtain ⟨K,hK⟩ := (imagPart_valid z.property).2.2 eps
  let M := max N K
  have hn := valid_nestedIn a.property (Nat.le_max_left N K)
  have hl := hn.1.2
  have hb := hs.2.2.1 0 M
  change -(L/2) ≤ (z.val.compute M).hi.im + -(a.val.compute M).lo.im at hb
  have hw := hK M (Nat.le_max_right N K)
  change (z.val.compute M).hi.im-(z.val.compute M).lo.im ≤ L/4 at hw
  refine ⟨M, ?_⟩
  change 0 < (z.val.compute M).lo.im
  change L ≤ (a.val.compute M).lo.im at hl
  grind only

end ComputableAnalysis.ModularForms
