import ComputableAnalysis.ModularForms.UpperLatticeRegionBounds

/-! Executable discovery of a quantitative lattice region for every upper-half-plane input. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

private def positiveImagGood (z : Scalar) (n : Nat) : Bool := decide (0<(z.val.compute n).lo.im)

private theorem positiveImag_eventually (z : Scalar) (hz : InUpperHalfPlane z.val) :
    ∃ N, ∀ n, N≤n → positiveImagGood z n=true := by
  obtain ⟨N,hN⟩ := hz
  refine ⟨N,?_⟩
  intro n hn
  have hb := ComplexRaw.valid_nestedIn z.property hn
  have hi : (z.val.compute N).lo.im≤(z.val.compute n).lo.im := hb.1.2
  simp only [positiveImagGood,decide_eq_true_eq]
  change 0<(z.val.compute N).lo.im at hN
  grind

def latticeRegionStage (z : Scalar) (hz : InUpperHalfPlane z.val) : Nat :=
  PrecisionSearch.firstFrom (positiveImagGood z) (positiveImag_eventually z hz) 0

theorem latticeRegionStage_positive (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0<(z.val.compute (latticeRegionStage z hz)).lo.im := by
  have h := (PrecisionSearch.firstFrom_spec (positiveImagGood z) (positiveImag_eventually z hz) 0).2
  simpa only [latticeRegionStage,positiveImagGood,decide_eq_true_eq] using h

def latticeRegionWidth (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat :=
  qabs (z.val.compute (latticeRegionStage z hz)).lo.re+
    qabs (z.val.compute (latticeRegionStage z hz)).hi.re+1

def latticeRegionMargin (z : Scalar) (hz : InUpperHalfPlane z.val) : Rat :=
  (z.val.compute (latticeRegionStage z hz)).lo.im/2

theorem latticeRegionWidth_nonnegative (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0≤latticeRegionWidth z hz := by
  have hl := qabs_nonneg (z.val.compute (latticeRegionStage z hz)).lo.re
  have hh := qabs_nonneg (z.val.compute (latticeRegionStage z hz)).hi.re
  unfold latticeRegionWidth
  grind

theorem latticeRegionMargin_positive (z : Scalar) (hz : InUpperHalfPlane z.val) :
    0<latticeRegionMargin z hz := by
  have h := latticeRegionStage_positive z hz
  unfold latticeRegionMargin
  grind

theorem latticeRegionSearch_spec (z : Scalar) (hz : InUpperHalfPlane z.val) :
    LatticeRegionBox z (latticeRegionWidth z hz) (latticeRegionMargin z hz) (latticeRegionStage z hz) := by
  have hpos := latticeRegionStage_positive z hz
  have hl := neg_qabs_le_self (z.val.compute (latticeRegionStage z hz)).lo.re
  have hh := self_le_qabs (z.val.compute (latticeRegionStage z hz)).hi.re
  have hal := qabs_nonneg (z.val.compute (latticeRegionStage z hz)).lo.re
  have hah := qabs_nonneg (z.val.compute (latticeRegionStage z hz)).hi.re
  constructor <;> simp only [latticeRegionWidth,latticeRegionMargin] <;> grind

end ComputableAnalysis.ModularForms
