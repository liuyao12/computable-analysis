import ComputableAnalysis.RiemannHilbert.RelativeLogarithmOffsetBounds

/-! A terminating rational-box search constructs a logarithm-chart center
near every nonzero represented complex value. No finite cover, logarithm
value or local domain membership is assumed in the constructor. -/
namespace ComputableAnalysis.RiemannHilbert.RationalLogarithmAnchor
open ComplexRaw FunctionTheory BoxApproximation NonzeroBoxSearch LocalODE ReciprocalExamples
set_option maxHeartbeats 800000

def tolerance : QPos := ⟨1/64,by decide +kernel⟩
def good (z : Scalar) (eps : QPos) (k : Nat) : Bool :=
  let B := z.val.compute k
  decide (0 < QComplex.normSq B.center ∧
    2*coordinateBound (RationalReciprocal.inverse B.center)*ReciprocalAnchor.radius B ≤ eps.val)

theorem eventually_good (z : Scalar) (hz : Nonzero z) (eps : QPos) :
    ∃ N, ∀ n, N ≤ n → good z eps n = true := by
  obtain ⟨k,hk⟩ := exists_separated z hz
  let d := margin (z.val.compute k)*margin (z.val.compute k)
  have hd : 0 < d := Rat.mul_pos (margin_pos _ hk) (margin_pos _ hk)
  let C := boxCoordinateBound (z.val.compute 0)
  have hC : 0 ≤ C := boxCoordinateBound_nonneg _
  let L := C/d
  have hL : 0 ≤ L := Rat.mul_nonneg hC (Rat.le_of_lt ((Rat.inv_pos).2 hd))
  let eta : QPos := ⟨eps.val/(2*(L+1)),Rat.mul_pos eps.property
    ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) (by grind only)))⟩
  obtain ⟨j,hj⟩ := z.property.2.2 eta
  refine ⟨max k j,?_⟩
  intro n hn
  have hkn : k ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hlower := center_normSq_lower z k n hkn hk
  have hnpos : 0 < QComplex.normSq (z.val.compute n).center := by change d ≤ _ at hlower; grind only
  have hinv := RationalReciprocal.coordinateBound_inverse (z.val.compute n).center C d hC hd hlower (center_bound z n)
  have hwidth := hj n hjn
  have hr : ReciprocalAnchor.radius (z.val.compute n) ≤ eta.val := by unfold ReciprocalAnchor.radius; grind
  have hr0 := ReciprocalAnchor.radius_nonneg (z.val.compute n) (valid_ordered z.property n)
  have hmul := Rat.mul_le_mul_of_nonneg_right hinv hr0
  have hmul2 := Rat.mul_le_mul_of_nonneg_left hr hL
  have heps : eta.val*(2*(L+1))=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt
    (Rat.mul_pos (by decide +kernel) (by grind only)))
  have hle := Rat.mul_le_mul_of_nonneg_right (show L ≤ L+1 by grind only) (Rat.le_of_lt eta.property)
  simp only [good,decide_eq_true_eq]
  exact ⟨hnpos,by change coordinateBound _ * _ ≤ L*ReciprocalAnchor.radius _ at hmul; grind only⟩

def stage (z : Scalar) (hz : Nonzero z) : Nat :=
  PrecisionSearch.firstFrom (good z tolerance) (eventually_good z hz tolerance) 0

theorem stage_spec (z : Scalar) (hz : Nonzero z) :
    0 < QComplex.normSq (z.val.compute (stage z hz)).center ∧
    2*coordinateBound (RationalReciprocal.inverse (z.val.compute (stage z hz)).center)*
      ReciprocalAnchor.radius (z.val.compute (stage z hz)) ≤ tolerance.val := by
  have h := (PrecisionSearch.firstFrom_spec (good z tolerance) (eventually_good z hz tolerance) 0).2
  simpa only [stage,good,decide_eq_true_eq] using h

def center (z : Scalar) (hz : Nonzero z) : QComplex := (z.val.compute (stage z hz)).center
theorem center_normSq_ne_zero (z : Scalar) (hz : Nonzero z) : QComplex.normSq (center z hz) ≠ 0 :=
  Rat.ne_of_gt (stage_spec z hz).1

def centerScalar (z : Scalar) (hz : Nonzero z) : Scalar := rational (center z hz)
theorem center_nonzero (z : Scalar) (hz : Nonzero z) : Nonzero (centerScalar z hz) :=
  rational_nonzero _ (center_normSq_ne_zero z hz)

theorem endpoint_mem (z : Scalar) (hz : Nonzero z) :
    RelativeLogarithm.domain (centerScalar z hz) (center_nonzero z hz) z := by
  let c := center z hz
  let k := stage z hz
  let L := coordinateBound (RationalReciprocal.inverse c)
  let R := ReciprocalAnchor.radius (z.val.compute k)
  have hL : 0 ≤ L := coordinateBound_nonneg _
  have hR : 0 ≤ R := ReciprocalAnchor.radius_nonneg _ (valid_ordered z.property k)
  have herr := center_error z k R hR (by dsimp [R,ReciprocalAnchor.radius]; grind)
    (by dsimp [R,ReciprocalAnchor.radius]; grind)
  have hi : Small (RepresentedReciprocal.inverse (centerScalar z hz) (center_nonzero z hz)).val L :=
    Small.congr (ofQComplex_valid _) (RepresentedReciprocal.inverse (centerScalar z hz) (center_nonzero z hz)).property
      (equiv_symm (rational_inverse c (center_normSq_ne_zero z hz))) (rational_small _)
  exact RelativeLogarithm.domain_of_distance _ _ z L R hL hR hi herr
    (by have hs := (stage_spec z hz).2
        have ht : tolerance.val < LocalLogarithm.radius.val := by decide +kernel
        change 2*L*R ≤ tolerance.val at hs
        grind only)

end ComputableAnalysis.RiemannHilbert.RationalLogarithmAnchor
