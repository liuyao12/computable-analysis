import ComputableAnalysis.RiemannHilbert.RationalReciprocal

/-! The rational normalization used by the represented reciprocal is found
by inspecting boxes. Nonzeroness proves termination; it is not decided. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalAnchor
open ComplexRaw FunctionTheory BoxApproximation NonzeroBoxSearch LocalODE

def radius (B : QBox) : Rat := max B.width B.height

theorem radius_nonneg (B : QBox) (hB : B.Ordered) : 0 ≤ radius B := by
  change B.lo.re ≤ B.hi.re ∧ B.lo.im ≤ B.hi.im at hB
  unfold radius QBox.width QBox.height
  grind

def good (z : Scalar) (k : Nat) : Bool :=
  let B := z.val.compute k
  decide (0 < QComplex.normSq B.center ∧
    2*coordinateBound (RationalReciprocal.inverse B.center)*radius B ≤ (1 : Rat)/8)

theorem eventually_good (z : Scalar) (hz : Nonzero z) :
    ∃ N, ∀ n, N ≤ n → good z n = true := by
  obtain ⟨k,hk⟩ := exists_separated z hz
  let d := margin (z.val.compute k)*margin (z.val.compute k)
  have hd : 0 < d := Rat.mul_pos (margin_pos _ hk) (margin_pos _ hk)
  let C := boxCoordinateBound (z.val.compute 0)
  have hC : 0 ≤ C := boxCoordinateBound_nonneg _
  let L := C/d
  have hL : 0 ≤ L := by
    dsimp [L]
    rw [Rat.div_def]
    exact Rat.mul_nonneg hC (Rat.le_of_lt ((Rat.inv_pos).2 hd))
  let eps : QPos := ⟨1/(16*(L+1)), by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 (Rat.mul_pos (by decide +kernel) (by grind)))⟩
  obtain ⟨j,hj⟩ := z.property.2.2 eps
  refine ⟨max k j, ?_⟩
  intro n hn
  have hkn : k ≤ n := by omega
  have hjn : j ≤ n := by omega
  have hlower := center_normSq_lower z k n hkn hk
  have hnpos : 0 < QComplex.normSq (z.val.compute n).center := by change d ≤ _ at hlower; grind
  have hinv := RationalReciprocal.coordinateBound_inverse (z.val.compute n).center C d
    hC hd hlower (center_bound z n)
  have hwidth := hj n hjn
  have hr : radius (z.val.compute n) ≤ eps.val := by
    unfold radius
    grind
  have hr0 := radius_nonneg (z.val.compute n) (valid_ordered z.property n)
  have hmul := Rat.mul_le_mul_of_nonneg_right hinv hr0
  have hmul2 := Rat.mul_le_mul_of_nonneg_left hr hL
  have heps : 16*(L+1)*eps.val=1 := by
    change 16*(L+1)*(1/(16*(L+1)))=1
    rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel _ (Rat.ne_of_gt (by
      exact Rat.mul_pos (by decide +kernel) (by grind)))]
  have hle := Rat.mul_le_mul_of_nonneg_right (show L ≤ L+1 by grind) (Rat.le_of_lt eps.property)
  simp only [good, decide_eq_true_eq]
  constructor
  · exact hnpos
  · change coordinateBound (RationalReciprocal.inverse (z.val.compute n).center) *
      radius (z.val.compute n) ≤ L * radius (z.val.compute n) at hmul
    grind

def stage (z : Scalar) (hz : Nonzero z) : Nat :=
  PrecisionSearch.firstFrom (good z) (eventually_good z hz) 0

theorem stage_spec (z : Scalar) (hz : Nonzero z) :
    0 < QComplex.normSq (z.val.compute (stage z hz)).center ∧
    2*coordinateBound (RationalReciprocal.inverse (z.val.compute (stage z hz)).center)*
      radius (z.val.compute (stage z hz)) ≤ (1 : Rat)/8 := by
  have h := (PrecisionSearch.firstFrom_spec (good z) (eventually_good z hz) 0).2
  simpa only [stage, good, decide_eq_true_eq] using h

def center (z : Scalar) (hz : Nonzero z) : QComplex := (z.val.compute (stage z hz)).center

def anchor (z : Scalar) (hz : Nonzero z) : Scalar :=
  ⟨ofQComplex (RationalReciprocal.inverse (center z hz)), ofQComplex_valid _⟩

def normalized (z : Scalar) (hz : Nonzero z) : Scalar :=
  ⟨mul (anchor z hz).val z.val, mul_valid (anchor z hz).property z.property⟩

theorem residual (z : Scalar) (hz : Nonzero z) :
    (sub (ofQComplex QComplex.one) (normalized z hz).val).Equiv
      (neg (mul (anchor z hz).val (sub z.val (ofQComplex (center z hz))))) := by
  let a := anchor z hz
  let c := center z hz
  have hunit := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (ofQComplex_valid (RationalReciprocal.inverse c)) (ofQComplex_valid c))
    (hright := ofQComplex_valid QComplex.one) (RationalReciprocal.raw_inverse_mul c
    (Rat.ne_of_gt (stage_spec z hz).1))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (ofQComplex_valid _) (normalized z hz).property)
    (hright := neg_valid (mul_valid a.property (sub_valid z.property (ofQComplex_valid c))))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let C := ComplexRawQuotient.ofRaw (ofQComplex c) (ofQComplex_valid c)
  change A*C=1 at hunit
  change (1 : ScalarAlgebra.Value) + -(A*Z) = -(A*(Z + -C))
  grind

theorem residual_small (z : Scalar) (hz : Nonzero z) :
    Small (sub (ofQComplex QComplex.one) (normalized z hz).val) ((1 : Rat)/8) := by
  let k := stage z hz
  let R := radius (z.val.compute k)
  let a := RationalReciprocal.inverse (center z hz)
  have hR : 0 ≤ R := radius_nonneg _ (valid_ordered z.property k)
  have herr := center_error z k R hR (by dsimp [R, radius]; grind) (by dsimp [R, radius]; grind)
  have hs := SeriesLimitLaws.small_neg (Small.mul
    (ofQComplex_valid a) (sub_valid z.property (ofQComplex_valid (center z hz)))
    (coordinateBound_nonneg a) hR (rational_small a) herr)
  have hm : 2*coordinateBound (RationalReciprocal.inverse (center z hz))*R ≤ (1 : Rat)/8 :=
    (stage_spec z hz).2
  exact Small.congr
    (neg_valid (mul_valid (anchor z hz).property (sub_valid z.property (ofQComplex_valid _))))
    (sub_valid (ofQComplex_valid _) (normalized z hz).property)
    (equiv_symm (residual z hz)) (hs.mono hm)

end ComputableAnalysis.RiemannHilbert.ReciprocalAnchor
