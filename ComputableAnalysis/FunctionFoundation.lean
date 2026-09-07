import ComputableAnalysis.Basic
import ComputableAnalysis.ComplexInterval
import ComputableAnalysis.FunctionDomains
import ComputableAnalysis.Extension
import ComputableAnalysis.ElementaryFunctions
import ComputableAnalysis.AlgebraicFunctions

/-!
# Computable function and representation foundation

This scoped entry point collects rational-domain complex-box functions,
partial real restrictions, interval domains, elementary evaluators, and
representation transport, together with their exact algebra.  A function is
introduced by its computation and domain; continuity or analyticity is added
only when a later theorem needs the corresponding finite certificate.
-/

namespace ComputableAnalysis

/-! The public import deliberately owns only the algebra that combines
explicit complex function computations.  Calculus theorems themselves remain
in their subject modules, which are imported above. -/
/-! Addition has the same representation-transport property as multiplication.
The proof is pointwise rational box arithmetic: overlapping input boxes give
overlapping sums. -/
theorem effectiveComplexRaw_add_equiv
    {z z' w w' : ComplexRaw}
    (hz : z.Valid) (hz' : z'.Valid)
    (hw : w.Valid) (hw' : w'.Valid)
    (hzz' : z.Equiv z') (hww' : w.Equiv w') :
    (ComplexRaw.add z w).Equiv (ComplexRaw.add z' w') := by
  intro n
  have hzz := (ComplexRaw.compareAt_overlap_iff z z' n n).1 (hzz' n)
  have hww := (ComplexRaw.compareAt_overlap_iff w w' n n).1 (hww' n)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z w) (ComplexRaw.add z' w') n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add at *
  simp only [QComplex.le_def] at hzz hww
  constructor
  · constructor <;> grind [Rat.add_assoc]
  · constructor <;> grind [Rat.add_assoc]

/-! The additive identity is also representation transport: adding the
canonical rational zero changes neither coordinate interval.  As with all
function-level identities below, the statement is an equivalence of raw
computations rather than definitional equality. -/
theorem effectiveComplexRaw_zero_add_equiv
    {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.add ComplexRaw.zero z).Equiv z := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add ComplexRaw.zero z) z n n).2
  change QBox.Overlaps
    (QBox.add (ComplexRaw.zero.compute n) (z.compute n)) (z.compute n)
  unfold ComplexRaw.zero ComplexRaw.ofQComplex
    QBox.add QBox.Overlaps QComplex.add
  simp [QComplex.zero, QComplex.le_def]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_add_zero_equiv
    {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.add z ComplexRaw.zero).Equiv z := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z ComplexRaw.zero) z n n).2
  change QBox.Overlaps
    (QBox.add (z.compute n) (ComplexRaw.zero.compute n)) (z.compute n)
  unfold ComplexRaw.zero ComplexRaw.ofQComplex
    QBox.add QBox.Overlaps QComplex.add
  simp [QComplex.zero, QComplex.le_def]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_add_comm_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.add z w).Equiv (ComplexRaw.add w z) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add z w) (ComplexRaw.add w z) n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.add_comm]

theorem effectiveComplexRaw_add_assoc_equiv
    {z w u : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hu : u.Valid) :
    (ComplexRaw.add (ComplexRaw.add z w) u).Equiv
      (ComplexRaw.add z (ComplexRaw.add w u)) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have huorder_re : (u.compute n).lo.re ≤ (u.compute n).hi.re := by
    have h := (hu.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have huorder_im : (u.compute n).lo.im ≤ (u.compute n).hi.im := by
    have h := (hu.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.add (ComplexRaw.add z w) u)
    (ComplexRaw.add z (ComplexRaw.add w u)) n n).2
  unfold ComplexRaw.add QBox.add QBox.Overlaps QComplex.add
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.add_assoc]

theorem effectiveComplexRaw_scaleRat_add_equiv_of_nonneg
    (r : Rat) (hr : 0 <= r) {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.scaleRat r (ComplexRaw.add z w)).Equiv
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) := by
  intro n
  have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
    have h := (hw.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
    have h := (hw.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.scaleRat r (ComplexRaw.add z w))
    (ComplexRaw.add (ComplexRaw.scaleRat r z)
      (ComplexRaw.scaleRat r w)) n n).2
  simp only [ComplexRaw.scaleRat, ComplexRaw.add, QBox.scaleRat,
    QBox.add, if_pos hr]
  change QBox.Overlaps
    { lo := { re := r * ((z.compute n).lo.re + (w.compute n).lo.re),
              im := r * ((z.compute n).lo.im + (w.compute n).lo.im) },
      hi := { re := r * ((z.compute n).hi.re + (w.compute n).hi.re),
              im := r * ((z.compute n).hi.im + (w.compute n).hi.im) } }
    { lo := { re := r * (z.compute n).lo.re + r * (w.compute n).lo.re,
              im := r * (z.compute n).lo.im + r * (w.compute n).lo.im },
      hi := { re := r * (z.compute n).hi.re + r * (w.compute n).hi.re,
              im := r * (z.compute n).hi.im + r * (w.compute n).hi.im } }
  unfold QBox.Overlaps
  have hsum_re : (z.compute n).lo.re + (w.compute n).lo.re ≤
      (z.compute n).hi.re + (w.compute n).hi.re := by
    grind
  have hsum_im : (z.compute n).lo.im + (w.compute n).lo.im ≤
      (z.compute n).hi.im + (w.compute n).hi.im := by
    grind
  have hscaled_re := Rat.mul_le_mul_of_nonneg_left hsum_re hr
  have hscaled_im := Rat.mul_le_mul_of_nonneg_left hsum_im hr
  constructor <;> constructor <;> grind [Rat.mul_add]

theorem effectiveComplexRaw_scaleRat_add_equiv
    (r : Rat) {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.scaleRat r (ComplexRaw.add z w)).Equiv
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) := by
  by_cases hr : 0 <= r
  · exact effectiveComplexRaw_scaleRat_add_equiv_of_nonneg r hr hz hw
  · have hrneg : r < 0 := by grind
    intro n
    have hzorder_re : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
      have h := (hz.1 n).1
      unfold QBox.width at h
      grind [Rat.sub_eq_add_neg]
    have hzorder_im : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
      have h := (hz.1 n).2
      unfold QBox.height at h
      grind [Rat.sub_eq_add_neg]
    have hworder_re : (w.compute n).lo.re ≤ (w.compute n).hi.re := by
      have h := (hw.1 n).1
      unfold QBox.width at h
      grind [Rat.sub_eq_add_neg]
    have hworder_im : (w.compute n).lo.im ≤ (w.compute n).hi.im := by
      have h := (hw.1 n).2
      unfold QBox.height at h
      grind [Rat.sub_eq_add_neg]
    apply (ComplexRaw.compareAt_overlap_iff
      (ComplexRaw.scaleRat r (ComplexRaw.add z w))
      (ComplexRaw.add (ComplexRaw.scaleRat r z)
        (ComplexRaw.scaleRat r w)) n n).2
    simp only [ComplexRaw.scaleRat, ComplexRaw.add, QBox.scaleRat,
      QBox.add, if_neg hr]
    change QBox.Overlaps
      { lo := { re := r * ((z.compute n).hi.re + (w.compute n).hi.re),
                im := r * ((z.compute n).hi.im + (w.compute n).hi.im) },
        hi := { re := r * ((z.compute n).lo.re + (w.compute n).lo.re),
                im := r * ((z.compute n).lo.im + (w.compute n).lo.im) } }
      { lo := { re := r * (z.compute n).hi.re + r * (w.compute n).hi.re,
                im := r * (z.compute n).hi.im + r * (w.compute n).hi.im },
        hi := { re := r * (z.compute n).lo.re + r * (w.compute n).lo.re,
                im := r * (z.compute n).lo.im + r * (w.compute n).lo.im } }
    unfold QBox.Overlaps
    have hsum_re : (z.compute n).lo.re + (w.compute n).lo.re ≤
        (z.compute n).hi.re + (w.compute n).hi.re := by
      grind
    have hsum_im : (z.compute n).lo.im + (w.compute n).lo.im ≤
        (z.compute n).hi.im + (w.compute n).hi.im := by
      grind
    have hscaled_re' := Rat.mul_le_mul_of_nonneg_left hsum_re
      (by grind : 0 ≤ -r)
    have hscaled_im' := Rat.mul_le_mul_of_nonneg_left hsum_im
      (by grind : 0 ≤ -r)
    have hscaled_re : r * ((z.compute n).hi.re + (w.compute n).hi.re) ≤
        r * ((z.compute n).lo.re + (w.compute n).lo.re) := by
      grind [Rat.neg_mul]
    have hscaled_im : r * ((z.compute n).hi.im + (w.compute n).hi.im) ≤
        r * ((z.compute n).lo.im + (w.compute n).lo.im) := by
      grind [Rat.neg_mul]
    constructor <;> constructor <;> grind [Rat.mul_add]

def FunctionRaw.zero : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.zero

def FunctionRaw.one : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.point QComplex.one

def FunctionRaw.constant (c : QComplex) : FunctionRaw where
  domain := fun _ => True
  compute := fun _ _ _ => QBox.point c

theorem FunctionRaw.zero_valid : FunctionRaw.zero.Valid := by
  intro z hz
  change ComplexRaw.zero.Valid
  exact ComplexRaw.ofQComplex_valid QComplex.zero

theorem FunctionRaw.one_valid : FunctionRaw.one.Valid := by
  intro z hz
  change ComplexRaw.ofQComplex QComplex.one |>.Valid
  exact ComplexRaw.ofQComplex_valid QComplex.one

theorem FunctionRaw.constant_valid (c : QComplex) :
    (FunctionRaw.constant c).Valid := by
  intro z hz
  change (ComplexRaw.ofQComplex c).Valid
  exact ComplexRaw.ofQComplex_valid c

theorem FunctionRaw.constant_agreeOnCommonDomain (c : QComplex) :
    (FunctionRaw.constant c).AgreeOnCommonDomain
      (FunctionRaw.constant c) := by
  intro z hleft hright
  exact ComplexRaw.equiv_refl
    ((FunctionRaw.constant c).evalRaw z hleft)
    (FunctionRaw.constant_valid c z hleft)

theorem effectiveMulRealInterval_one_overlap {a b : Rat} (hab : a <= b) :
    QInterval.Overlaps
      (QBox.mulRealInterval a b 1 1)
      ({ lo := a, hi := b } : QInterval) := by
  by_cases ha : 0 <= a
  · have heq := QBox.mulRealInterval_of_nonneg ha hab
      (by native_decide : (0 : Rat) <= 1)
      (by native_decide : (1 : Rat) <= 1)
    rw [heq]
    simp [QInterval.Overlaps]
    exact hab
  · have hault : a < 0 := by grind
    by_cases hb : b <= 0
    · unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind
    · have hbpos : 0 < b := by grind
      unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind

theorem effectiveMulRealInterval_zero {a b : Rat} :
    QBox.mulRealInterval a b 0 0 = ({ lo := 0, hi := 0 } : QInterval) := by
  unfold QBox.mulRealInterval min4 max4 minRat maxRat2
  simp

theorem effectiveMulRealInterval_zero_left {a b : Rat} :
    QBox.mulRealInterval 0 0 a b = ({ lo := 0, hi := 0 } : QInterval) := by
  unfold QBox.mulRealInterval min4 max4 minRat maxRat2
  simp

theorem effectiveMulRealInterval_one_left_overlap {a b : Rat} (hab : a <= b) :
    QInterval.Overlaps
      (QBox.mulRealInterval 1 1 a b)
      ({ lo := a, hi := b } : QInterval) := by
  by_cases ha : 0 <= a
  · have heq := QBox.mulRealInterval_of_nonneg
      (by native_decide : (0 : Rat) <= 1)
      (by native_decide : (1 : Rat) <= 1) ha hab
    rw [heq]
    simp [QInterval.Overlaps]
    exact hab
  · have hault : a < 0 := by grind
    by_cases hb : b <= 0
    · unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind
    · have hbpos : 0 < b := by grind
      unfold QBox.mulRealInterval min4 max4 minRat maxRat2
      simp only [QInterval.Overlaps]
      constructor <;> grind

theorem effectiveComplexRaw_mul_one_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul z ComplexRaw.one).Equiv z := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hreal := effectiveMulRealInterval_one_overlap hzre
  have himag := effectiveMulRealInterval_one_overlap hzim
  have hreal' :
      (QBox.mulRealInterval (z.compute n).lo.re (z.compute n).hi.re 1 1).lo ≤
        (z.compute n).hi.re /\
      (z.compute n).lo.re ≤
        (QBox.mulRealInterval (z.compute n).lo.re (z.compute n).hi.re 1 1).hi := by
    simpa [QInterval.Overlaps] using hreal
  have himag' :
      (QBox.mulRealInterval (z.compute n).lo.im (z.compute n).hi.im 1 1).lo ≤
        (z.compute n).hi.im /\
      (z.compute n).lo.im ≤
        (QBox.mulRealInterval (z.compute n).lo.im (z.compute n).hi.im 1 1).hi := by
    simpa [QInterval.Overlaps] using himag
  have hzeroRe := effectiveMulRealInterval_zero
      (a := (z.compute n).lo.im) (b := (z.compute n).hi.im)
  have hzeroIm := effectiveMulRealInterval_zero
      (a := (z.compute n).lo.re) (b := (z.compute n).hi.re)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z ComplexRaw.one) z n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (QBox.point QComplex.one)) (z.compute n)
  simp [QBox.mul, QBox.point, QComplex.one, hzeroRe, hzeroIm]
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hreal_lo := hreal'.1
  have hreal_hi := hreal'.2
  have himag_lo := himag'.1
  have himag_hi := himag'.2
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_one_mul_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul ComplexRaw.one z).Equiv z := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  have hreal0 := effectiveMulRealInterval_one_left_overlap hzre
  have himag0 := effectiveMulRealInterval_one_left_overlap hzim
  have hreal :
      (QBox.mulRealInterval 1 1 (z.compute n).lo.re
        (z.compute n).hi.re).lo ≤ (z.compute n).hi.re /\
      (z.compute n).lo.re ≤
        (QBox.mulRealInterval 1 1 (z.compute n).lo.re
          (z.compute n).hi.re).hi := by
    simpa [QInterval.Overlaps] using hreal0
  have himag :
      (QBox.mulRealInterval 1 1 (z.compute n).lo.im
        (z.compute n).hi.im).lo ≤ (z.compute n).hi.im /\
      (z.compute n).lo.im ≤
        (QBox.mulRealInterval 1 1 (z.compute n).lo.im
          (z.compute n).hi.im).hi := by
    simpa [QInterval.Overlaps] using himag0
  have hzeroRe := effectiveMulRealInterval_zero_left
      (a := (z.compute n).lo.im) (b := (z.compute n).hi.im)
  have hzeroIm := effectiveMulRealInterval_zero_left
      (a := (z.compute n).lo.re) (b := (z.compute n).hi.re)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul ComplexRaw.one z) z n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.point QComplex.one) (z.compute n)) (z.compute n)
  simp [QBox.mul, QBox.point, QComplex.one, hzeroRe, hzeroIm]
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hreal_lo := hreal.1
  have hreal_hi := hreal.2
  have himag_lo := himag.1
  have himag_hi := himag.2
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_mul_zero_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul z ComplexRaw.zero).Equiv ComplexRaw.zero := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z ComplexRaw.zero) ComplexRaw.zero n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (QBox.point QComplex.zero))
    (QBox.point QComplex.zero)
  simp [QBox.mul, QBox.point, QComplex.zero,
    effectiveMulRealInterval_zero, QInterval.Overlaps]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_zero_mul_equiv {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.mul ComplexRaw.zero z).Equiv ComplexRaw.zero := by
  intro n
  have hzre : (z.compute n).lo.re ≤ (z.compute n).hi.re := by
    have h := (hz.1 n).1
    unfold QBox.width at h
    grind [Rat.sub_eq_add_neg]
  have hzim : (z.compute n).lo.im ≤ (z.compute n).hi.im := by
    have h := (hz.1 n).2
    unfold QBox.height at h
    grind [Rat.sub_eq_add_neg]
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul ComplexRaw.zero z) ComplexRaw.zero n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.point QComplex.zero) (z.compute n))
    (QBox.point QComplex.zero)
  simp [QBox.mul, QBox.point, QComplex.zero,
    effectiveMulRealInterval_zero_left, QInterval.Overlaps]
  constructor <;> constructor <;> grind

theorem effectiveComplexRaw_mul_comm_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul z w).Equiv (ComplexRaw.mul w z) := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z w) (ComplexRaw.mul w z) n n).2
  change QBox.Overlaps
    (QBox.mul (z.compute n) (w.compute n))
    (QBox.mul (w.compute n) (z.compute n))
  unfold QBox.mul QBox.Overlaps QBox.mulRealInterval
    min4 max4 minRat maxRat2
  simp only [QComplex.le_def]
  constructor <;> constructor <;> grind [Rat.mul_comm]

theorem effectiveComplexRaw_mul_assoc_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul (ComplexRaw.mul z w) v).Equiv
      (ComplexRaw.mul z (ComplexRaw.mul w v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hwv := QBox.mul_contains hy.1 hy.2 hu.1 hu.2
  have hleft := QBox.mul_contains hzw.1 hzw.2 hu.1 hu.2
  have hright := QBox.mul_contains hx.1 hx.2 hwv.1 hwv.2
  have hassoc : QComplex.mul (QComplex.mul x y) u =
      QComplex.mul x (QComplex.mul y u) := by
    exact QComplex.mul_assoc_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.mul z w) v)
    (ComplexRaw.mul z (ComplexRaw.mul w v)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.mul A B) C)
    (QBox.mul A (QBox.mul B C))
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  have hre := congrArg QComplex.re hassoc
  have him := congrArg QComplex.im hassoc
  have hrightReLo : (QBox.mul A (QBox.mul B C)).lo.re <=
      (QComplex.mul (QComplex.mul x y) u).re := by
    rw [hre]
    exact hright.1.1
  have hrightReHi : (QComplex.mul (QComplex.mul x y) u).re <=
      (QBox.mul A (QBox.mul B C)).hi.re := by
    rw [hre]
    exact hright.2.1
  have hleftReHi : (QComplex.mul (QComplex.mul x y) u).re <=
      (QBox.mul (QBox.mul A B) C).hi.re := by
    exact hleft.2.1
  have hrightImLo : (QBox.mul A (QBox.mul B C)).lo.im <=
      (QComplex.mul (QComplex.mul x y) u).im := by
    rw [him]
    exact hright.1.2
  have hrightImHi : (QComplex.mul (QComplex.mul x y) u).im <=
      (QBox.mul A (QBox.mul B C)).hi.im := by
    rw [him]
    exact hright.2.2
  have hleftImHi : (QComplex.mul (QComplex.mul x y) u).im <=
      (QBox.mul (QBox.mul A B) C).hi.im := by
    exact hleft.2.2
  exact ⟨⟨Rat.le_trans hleft.1.1 hrightReHi,
    Rat.le_trans hleft.1.2 hrightImHi⟩,
    ⟨Rat.le_trans hrightReLo hleftReHi,
      Rat.le_trans hrightImLo hleftImHi⟩⟩

theorem QBox.overlaps_of_common_point {A B : QBox} {z : QComplex}
    (hA : A.lo <= z /\ z <= A.hi)
    (hB : B.lo <= z /\ z <= B.hi) :
    A.Overlaps B := by
  unfold QBox.Overlaps
  simp only [QComplex.le_def]
  exact ⟨⟨Rat.le_trans hA.1.1 hB.2.1,
    Rat.le_trans hA.1.2 hB.2.2⟩,
    ⟨Rat.le_trans hB.1.1 hA.2.1,
      Rat.le_trans hB.1.2 hA.2.2⟩⟩

theorem QBox.neg_contains {A : QBox} {z : QComplex}
    (hA : A.lo <= z /\ z <= A.hi) :
    (QBox.neg A).lo <= QComplex.neg z /\
      QComplex.neg z <= (QBox.neg A).hi := by
  unfold QBox.neg QComplex.neg
  simp only [QComplex.le_def]
  exact ⟨⟨Rat.neg_le_neg hA.2.1, Rat.neg_le_neg hA.2.2⟩,
    ⟨Rat.neg_le_neg hA.1.1, Rat.neg_le_neg hA.1.2⟩⟩

theorem effectiveComplexRaw_mul_neg_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul z (ComplexRaw.neg w)).Equiv
      (ComplexRaw.neg (ComplexRaw.mul z w)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let x := A.center
  let y := B.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hny := QBox.neg_contains hy
  have hleft := QBox.mul_contains hx.1 hx.2 hny.1 hny.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hright := QBox.neg_contains hzw
  have hidentity : QComplex.mul x (QComplex.neg y) =
      QComplex.neg (QComplex.mul x y) := by
    exact QComplex.mul_neg_cert x y
  have hright' : (QBox.neg (QBox.mul A B)).lo <=
      QComplex.mul x (QComplex.neg y) /\
      QComplex.mul x (QComplex.neg y) <=
        (QBox.neg (QBox.mul A B)).hi := by
    rw [hidentity]
    exact hright
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z (ComplexRaw.neg w))
    (ComplexRaw.neg (ComplexRaw.mul z w)) n n).2
  change QBox.Overlaps
    (QBox.mul A (QBox.neg B))
    (QBox.neg (QBox.mul A B))
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_neg_mul_equiv
    {z w : ComplexRaw} (hz : z.Valid) (hw : w.Valid) :
    (ComplexRaw.mul (ComplexRaw.neg z) w).Equiv
      (ComplexRaw.neg (ComplexRaw.mul z w)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let x := A.center
  let y := B.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hnx := QBox.neg_contains hx
  have hleft := QBox.mul_contains hnx.1 hnx.2 hy.1 hy.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hright := QBox.neg_contains hzw
  have hidentity : QComplex.mul (QComplex.neg x) y =
      QComplex.neg (QComplex.mul x y) := by
    exact QComplex.neg_mul_cert x y
  have hright' : (QBox.neg (QBox.mul A B)).lo <=
      QComplex.mul (QComplex.neg x) y /\
      QComplex.mul (QComplex.neg x) y <=
        (QBox.neg (QBox.mul A B)).hi := by
    rw [hidentity]
    exact hright
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.neg z) w)
    (ComplexRaw.neg (ComplexRaw.mul z w)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.neg A) B)
    (QBox.neg (QBox.mul A B))
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_mul_add_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul z (ComplexRaw.add w v)).Equiv
      (ComplexRaw.add (ComplexRaw.mul z w) (ComplexRaw.mul z v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hyu := QBox.add_contains hy.1 hy.2 hu.1 hu.2
  have hleft := QBox.mul_contains hx.1 hx.2 hyu.1 hyu.2
  have hzw := QBox.mul_contains hx.1 hx.2 hy.1 hy.2
  have hzv := QBox.mul_contains hx.1 hx.2 hu.1 hu.2
  have hright := QBox.add_contains hzw.1 hzw.2 hzv.1 hzv.2
  have hidentity : QComplex.mul x (QComplex.add y u) =
      QComplex.add (QComplex.mul x y) (QComplex.mul x u) := by
    exact QComplex.mul_add_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul z (ComplexRaw.add w v))
    (ComplexRaw.add (ComplexRaw.mul z w) (ComplexRaw.mul z v)) n n).2
  change QBox.Overlaps
    (QBox.mul A (QBox.add B C))
    (QBox.add (QBox.mul A B) (QBox.mul A C))
  have hright' : (QBox.add (QBox.mul A B) (QBox.mul A C)).lo <=
      QComplex.mul x (QComplex.add y u) /\
      QComplex.mul x (QComplex.add y u) <=
        (QBox.add (QBox.mul A B) (QBox.mul A C)).hi := by
    rw [hidentity]
    exact hright
  exact QBox.overlaps_of_common_point hleft hright'

theorem effectiveComplexRaw_add_mul_equiv
    {z w v : ComplexRaw} (hz : z.Valid) (hw : w.Valid) (hv : v.Valid) :
    (ComplexRaw.mul (ComplexRaw.add z w) v).Equiv
      (ComplexRaw.add (ComplexRaw.mul z v) (ComplexRaw.mul w v)) := by
  intro n
  let A := z.compute n
  let B := w.compute n
  let C := v.compute n
  let x := A.center
  let y := B.center
  let u := C.center
  have hx : A.lo <= x /\ x <= A.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hz n)
  have hy : B.lo <= y /\ y <= B.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hw n)
  have hu : C.lo <= u /\ u <= C.hi := by
    exact QBox.center_mem (ComplexRaw.valid_ordered hv n)
  have hxy := QBox.add_contains hx.1 hx.2 hy.1 hy.2
  have hleft := QBox.mul_contains hxy.1 hxy.2 hu.1 hu.2
  have hzv := QBox.mul_contains hx.1 hx.2 hu.1 hu.2
  have hwv := QBox.mul_contains hy.1 hy.2 hu.1 hu.2
  have hright := QBox.add_contains hzv.1 hzv.2 hwv.1 hwv.2
  have hidentity : QComplex.mul (QComplex.add x y) u =
      QComplex.add (QComplex.mul x u) (QComplex.mul y u) := by
    exact QComplex.add_mul_cert x y u
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.mul (ComplexRaw.add z w) v)
    (ComplexRaw.add (ComplexRaw.mul z v) (ComplexRaw.mul w v)) n n).2
  change QBox.Overlaps
    (QBox.mul (QBox.add A B) C)
    (QBox.add (QBox.mul A C) (QBox.mul B C))
  have hright' : (QBox.add (QBox.mul A C) (QBox.mul B C)).lo <=
      QComplex.mul (QComplex.add x y) u /\
      QComplex.mul (QComplex.add x y) u <=
        (QBox.add (QBox.mul A C) (QBox.mul B C)).hi := by
    rw [hidentity]
    exact hright
  exact QBox.overlaps_of_common_point hleft hright'

/-! Negation is the interval-reversing operation needed to assemble signed
linear combinations from the order-preserving nonnegative scaling primitive. -/
theorem effectiveComplexRaw_neg_equiv
    {z w : ComplexRaw}
    (hzw : z.Equiv w) :
    (ComplexRaw.neg z).Equiv (ComplexRaw.neg w) := by
  intro n
  have hover := (ComplexRaw.compareAt_overlap_iff z w n n).1 (hzw n)
  apply (ComplexRaw.compareAt_overlap_iff
    (ComplexRaw.neg z) (ComplexRaw.neg w) n n).2
  change QBox.Overlaps
    { lo := { re := -(z.compute n).hi.re, im := -(z.compute n).hi.im },
      hi := { re := -(z.compute n).lo.re, im := -(z.compute n).lo.im } }
    { lo := { re := -(w.compute n).hi.re, im := -(w.compute n).hi.im },
      hi := { re := -(w.compute n).lo.re, im := -(w.compute n).lo.im } }
  unfold QBox.Overlaps at hover ⊢
  simp only [QComplex.le_def] at hover ⊢
  constructor <;> constructor <;> grind [Rat.neg_le_neg]

def FunctionRaw.add (f g : FunctionRaw) : FunctionRaw where
  domain := fun z => f.domain z /\ g.domain z
  compute := fun z hz n =>
    QBox.add (f.compute z hz.1 n) (g.compute z hz.2 n)

theorem FunctionRaw.add_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.add f g).Valid := by
  intro z hz
  have hadd : (ComplexRaw.add (f.evalRaw z hz.1)
      (g.evalRaw z hz.2)).Valid :=
    ComplexRaw.add_valid (hf z hz.1) (hg z hz.2)
  change (ComplexRaw.add (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid at hadd
  change (ComplexRaw.add (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid
  exact hadd

theorem FunctionRaw.add_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.add f g).AgreeOnCommonDomain
      (FunctionRaw.add f' g') := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (f'.evalRaw z hright.1)
      (g'.evalRaw z hright.2))
  exact effectiveComplexRaw_add_equiv
    (hf z hleft.1) (hf' z hright.1)
    (hg z hleft.2) (hg' z hright.2)
    (hff z hleft.1 hright.1)
    (hgg z hleft.2 hright.2)

theorem FunctionRaw.zero_add_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.add FunctionRaw.zero f).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.add
    (FunctionRaw.zero.evalRaw z hleft.1)
    (f.evalRaw z hleft.2)).Equiv (f.evalRaw z hright)
  exact effectiveComplexRaw_zero_add_equiv (hf z hright)

theorem FunctionRaw.add_zero_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.add f FunctionRaw.zero).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.add
    (f.evalRaw z hleft.1)
    (FunctionRaw.zero.evalRaw z hleft.2)).Equiv (f.evalRaw z hright)
  exact effectiveComplexRaw_add_zero_equiv (hf z hright)

theorem FunctionRaw.add_comm_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.add f g).AgreeOnCommonDomain
      (FunctionRaw.add g f) := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (g.evalRaw z hright.1)
      (f.evalRaw z hright.2))
  exact effectiveComplexRaw_add_comm_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.add_assoc_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.add (FunctionRaw.add f g) h).AgreeOnCommonDomain
      (FunctionRaw.add f (FunctionRaw.add g h)) := by
  intro z hleft hright
  change (ComplexRaw.add
      (ComplexRaw.add (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add (f.evalRaw z hright.1)
      (ComplexRaw.add (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_add_assoc_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

def FunctionRaw.sum : List FunctionRaw → FunctionRaw
  | [] => FunctionRaw.zero
  | f :: fs => FunctionRaw.add f (FunctionRaw.sum fs)

theorem FunctionRaw.sum_valid
    (fs : List FunctionRaw)
    (hfs : ∀ f, f ∈ fs → f.Valid) :
    (FunctionRaw.sum fs).Valid := by
  induction fs with
  | nil => exact FunctionRaw.zero_valid
  | cons f fs ih =>
    exact FunctionRaw.add_valid (hfs f (by simp))
      (ih (fun g hg => hfs g (by simp [hg])))

theorem FunctionRaw.zero_agreeOnCommonDomain :
    FunctionRaw.zero.AgreeOnCommonDomain FunctionRaw.zero := by
  intro z _ _
  exact ComplexRaw.equiv_refl ComplexRaw.zero
    (ComplexRaw.ofQComplex_valid QComplex.zero)

def FunctionRaw.AgreeList : List FunctionRaw → List FunctionRaw → Prop
  | [], [] => True
  | f :: fs, g :: gs =>
      f.AgreeOnCommonDomain g ∧ FunctionRaw.AgreeList fs gs
  | _, _ => False

theorem FunctionRaw.sum_agreeOnCommonDomain
    {fs gs : List FunctionRaw}
    (hfs : ∀ f, f ∈ fs → f.Valid)
    (hgs : ∀ g, g ∈ gs → g.Valid)
    (hpair : FunctionRaw.AgreeList fs gs) :
    (FunctionRaw.sum fs).AgreeOnCommonDomain
      (FunctionRaw.sum gs) := by
  induction fs generalizing gs with
  | nil =>
    cases gs with
    | nil => exact FunctionRaw.zero_agreeOnCommonDomain
    | cons g gs => simp [FunctionRaw.AgreeList] at hpair
  | cons f fs ih =>
    cases gs with
    | nil => simp [FunctionRaw.AgreeList] at hpair
    | cons g gs =>
      rcases hpair with ⟨hfg, htail⟩
      exact FunctionRaw.add_agreeOnCommonDomain
        (hfs f (by simp))
        (hgs g (by simp))
        (FunctionRaw.sum_valid fs (fun x hx => hfs x (by simp [hx])))
        (FunctionRaw.sum_valid gs (fun x hx => hgs x (by simp [hx])))
        hfg
        (ih
          (fun x hx => hfs x (by simp [hx]))
            (fun x hx => hgs x (by simp [hx]))
            htail)

def FunctionRaw.neg (f : FunctionRaw) : FunctionRaw where
  domain := f.domain
  compute := fun z hz n => QBox.neg (f.compute z hz n)

theorem FunctionRaw.neg_valid
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.neg f).Valid := by
  intro z hz
  have hneg : (ComplexRaw.neg (f.evalRaw z hz)).Valid :=
    ComplexRaw.neg_valid (hf z hz)
  change (ComplexRaw.neg (f.evalRaw z hz)).Valid at hneg
  change (ComplexRaw.neg (f.evalRaw z hz)).Valid
  exact hneg

theorem FunctionRaw.neg_agreeOnCommonDomain
    {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.neg f).AgreeOnCommonDomain (FunctionRaw.neg g) := by
  intro z hfz hgz
  change (ComplexRaw.neg (f.evalRaw z hfz)).Equiv
    (ComplexRaw.neg (g.evalRaw z hgz))
  exact effectiveComplexRaw_neg_equiv (hfg z hfz hgz)

/-! Nonnegative rational scaling is the order-preserving scalar operation on
complex raw functions.  Negative scaling is intentionally assembled from
negation plus this primitive, so interval reversal stays explicit. -/
def FunctionRaw.scaleRat (r : Rat) (f : FunctionRaw) : FunctionRaw where
  domain := f.domain
  compute := fun z hz n => QBox.scaleRat r (f.compute z hz n)

theorem FunctionRaw.scaleRat_add_agreeOnCommonDomain_of_nonneg
    {r : Rat} (hr : 0 <= r) {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.scaleRat r (FunctionRaw.add f g)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.scaleRat r f)
        (FunctionRaw.scaleRat r g)) := by
  intro z hleft hright
  change (ComplexRaw.scaleRat r
      (ComplexRaw.add (f.evalRaw z hleft.1)
        (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.scaleRat r (f.evalRaw z hright.1))
      (ComplexRaw.scaleRat r (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_scaleRat_add_equiv_of_nonneg r hr
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.scaleRat_add_agreeOnCommonDomain
    {r : Rat} {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.scaleRat r (FunctionRaw.add f g)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.scaleRat r f)
        (FunctionRaw.scaleRat r g)) := by
  intro z hleft hright
  change (ComplexRaw.scaleRat r
      (ComplexRaw.add (f.evalRaw z hleft.1)
        (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.scaleRat r (f.evalRaw z hright.1))
      (ComplexRaw.scaleRat r (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_scaleRat_add_equiv r
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.scaleRat_valid_of_nonneg
    {r : Rat} (hr : 0 <= r) {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.scaleRat r f).Valid := by
  intro z hz
  have hscaled : (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid :=
    ComplexRaw.scaleRat_valid_of_nonneg hr (hf z hz)
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid at hscaled
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid
  exact hscaled

theorem FunctionRaw.scaleRat_agreeOnCommonDomain_of_nonneg
    {r : Rat} (hr : 0 <= r)
    {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.scaleRat r f).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r g) := by
  intro z hfz hgz
  change (ComplexRaw.scaleRat r (f.evalRaw z hfz)).Equiv
    (ComplexRaw.scaleRat r (g.evalRaw z hgz))
  exact ComplexRaw.scaleRat_equiv_of_nonneg hr
    (hfg z hfz hgz)

private theorem effectiveComplexRaw_scaleRat_neg_eq
    {r : Rat} (hr : r < 0) (z : ComplexRaw) :
    ∀ n, (ComplexRaw.scaleRat r z).compute n =
      (ComplexRaw.neg (ComplexRaw.scaleRat (-r) z)).compute n := by
  cases z with
  | mk compute rate =>
    intro n
    have hrnot : ¬ 0 <= r := by grind
    have hrpos : 0 <= -r := by grind
    simp only [ComplexRaw.scaleRat, ComplexRaw.neg, QBox.scaleRat,
      if_neg hrnot, if_pos hrpos]
    congr 1 <;> simp [Rat.neg_mul]

theorem effectiveComplexRaw_scaleRat_valid
    {r : Rat} {z : ComplexRaw} (hz : z.Valid) :
    (ComplexRaw.scaleRat r z).Valid := by
  by_cases hr : 0 <= r
  · exact ComplexRaw.scaleRat_valid_of_nonneg hr hz
  · have hrlt : r < 0 := by grind
    have hrnonneg : 0 <= -r := by grind
    have hcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt z
    have hneg : (ComplexRaw.neg (ComplexRaw.scaleRat (-r) z)).Valid :=
      ComplexRaw.neg_valid
        (ComplexRaw.scaleRat_valid_of_nonneg hrnonneg hz)
    change ComplexRaw.ValidCompute (ComplexRaw.scaleRat r z).compute
    rw [funext hcompute]
    exact hneg

theorem effectiveComplexRaw_scaleRat_equiv
    {r : Rat} {z w : ComplexRaw} (hzw : z.Equiv w) :
    (ComplexRaw.scaleRat r z).Equiv (ComplexRaw.scaleRat r w) := by
  by_cases hr : 0 <= r
  · exact ComplexRaw.scaleRat_equiv_of_nonneg hr hzw
  · have hrlt : r < 0 := by grind
    have hrnonneg : 0 <= -r := by grind
    have hzcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt z
    have hwcompute := effectiveComplexRaw_scaleRat_neg_eq hrlt w
    intro n
    have hneg := effectiveComplexRaw_neg_equiv
      (ComplexRaw.scaleRat_equiv_of_nonneg hrnonneg hzw) n
    change ComplexRaw.compareBoxes
      ((ComplexRaw.scaleRat r z).compute n)
      ((ComplexRaw.scaleRat r w).compute n) =
      ComplexRaw.CompareAt.overlap
    rw [hzcompute n, hwcompute n]
    exact hneg

theorem FunctionRaw.scaleRat_valid
    {r : Rat} {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.scaleRat r f).Valid := by
  intro z hz
  have hscaled : (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid :=
    effectiveComplexRaw_scaleRat_valid (hf z hz)
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid at hscaled
  change (ComplexRaw.scaleRat r (f.evalRaw z hz)).Valid
  exact hscaled

theorem FunctionRaw.scaleRat_agreeOnCommonDomain
    {r : Rat} {f g : FunctionRaw}
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.scaleRat r f).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r g) := by
  intro z hfz hgz
  change (ComplexRaw.scaleRat r (f.evalRaw z hfz)).Equiv
    (ComplexRaw.scaleRat r (g.evalRaw z hgz))
  exact effectiveComplexRaw_scaleRat_equiv (hfg z hfz hgz)

def FunctionRaw.linearCombination : List (Rat × FunctionRaw) → FunctionRaw :=
  fun terms =>
    FunctionRaw.sum
      (terms.map (fun term => FunctionRaw.scaleRat term.1 term.2))

theorem FunctionRaw.linearCombination_valid
    (terms : List (Rat × FunctionRaw))
    (hterms : ∀ term, term ∈ terms → term.2.Valid) :
    (FunctionRaw.linearCombination terms).Valid := by
  apply FunctionRaw.sum_valid
  intro f hf
  obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hf
  exact FunctionRaw.scaleRat_valid (hterms term hterm)

/-! Subtraction is assembled from the already certified addition and
negation operations.  No separate interval-arithmetic theorem is needed. -/
def FunctionRaw.sub (f g : FunctionRaw) : FunctionRaw :=
  FunctionRaw.add f (FunctionRaw.neg g)

theorem FunctionRaw.sub_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.sub f g).Valid := by
  exact FunctionRaw.add_valid hf (FunctionRaw.neg_valid hg)

theorem FunctionRaw.sub_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.sub f g).AgreeOnCommonDomain
      (FunctionRaw.sub f' g') := by
  intro z hleft hright
  change (ComplexRaw.add (f.evalRaw z hleft.1)
      (ComplexRaw.neg (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.add (f'.evalRaw z hright.1)
      (ComplexRaw.neg (g'.evalRaw z hright.2)))
  exact effectiveComplexRaw_add_equiv
    (hf z hleft.1) (hf' z hright.1)
    (ComplexRaw.neg_valid (hg z hleft.2))
    (ComplexRaw.neg_valid (hg' z hright.2))
    (hff z hleft.1 hright.1)
    (effectiveComplexRaw_neg_equiv (hgg z hleft.2 hright.2))

/-! The abstract function handle exposes the same certified operations as its
preferred raw representative.  Alternative evaluators remain explicit data
which can be attached with `ComplexFunction.withAlternative`. -/
def ComplexFunction.zero : ComplexFunction :=
  ComplexFunction.ofRaw FunctionRaw.zero FunctionRaw.zero_valid

def ComplexFunction.one : ComplexFunction :=
  ComplexFunction.ofRaw FunctionRaw.one FunctionRaw.one_valid

def ComplexFunction.add (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.add f.preferred g.preferred)
    (FunctionRaw.add_valid f.valid g.valid)

theorem ComplexFunction.zero_add_representation_agrees_preferred
    (f : ComplexFunction) :
    (ComplexFunction.add ComplexFunction.zero f).preferred.AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.add FunctionRaw.zero f.preferred).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.zero_add_agreeOnCommonDomain f.valid

theorem ComplexFunction.add_zero_representation_agrees_preferred
    (f : ComplexFunction) :
    (ComplexFunction.add f ComplexFunction.zero).preferred.AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.add f.preferred FunctionRaw.zero).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.add_zero_agreeOnCommonDomain f.valid

theorem ComplexFunction.add_comm_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.add f g).preferred.AgreeOnCommonDomain
      (ComplexFunction.add g f).preferred := by
  change (FunctionRaw.add f.preferred g.preferred).AgreeOnCommonDomain
    (FunctionRaw.add g.preferred f.preferred)
  exact FunctionRaw.add_comm_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.add_assoc_representation_agrees_preferred
    (f g h : ComplexFunction) :
    ((ComplexFunction.add (ComplexFunction.add f g) h).preferred).AgreeOnCommonDomain
      (ComplexFunction.add f (ComplexFunction.add g h)).preferred := by
  change (FunctionRaw.add (FunctionRaw.add f.preferred g.preferred)
      h.preferred).AgreeOnCommonDomain
    (FunctionRaw.add f.preferred (FunctionRaw.add g.preferred h.preferred))
  exact FunctionRaw.add_assoc_agreeOnCommonDomain f.valid g.valid h.valid

def ComplexFunction.neg (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.neg f.preferred)
    (FunctionRaw.neg_valid f.valid)

def ComplexFunction.scaleRat (r : Rat) (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.scaleRat r f.preferred)
    (FunctionRaw.scaleRat_valid f.valid)

theorem ComplexFunction.scaleRat_add_representation_agrees_preferred_of_nonneg
    (r : Rat) (hr : 0 <= r) (f g : ComplexFunction) :
    ((ComplexFunction.scaleRat r (ComplexFunction.add f g)).preferred).AgreeOnCommonDomain
      ((ComplexFunction.add (ComplexFunction.scaleRat r f)
        (ComplexFunction.scaleRat r g)).preferred) := by
  change (FunctionRaw.scaleRat r (FunctionRaw.add f.preferred g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.scaleRat r f.preferred)
      (FunctionRaw.scaleRat r g.preferred))
  exact FunctionRaw.scaleRat_add_agreeOnCommonDomain_of_nonneg hr
    f.valid g.valid

theorem ComplexFunction.scaleRat_add_representation_agrees_preferred
    (r : Rat) (f g : ComplexFunction) :
    ((ComplexFunction.scaleRat r (ComplexFunction.add f g)).preferred).AgreeOnCommonDomain
      ((ComplexFunction.add (ComplexFunction.scaleRat r f)
        (ComplexFunction.scaleRat r g)).preferred) := by
  change (FunctionRaw.scaleRat r (FunctionRaw.add f.preferred g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.scaleRat r f.preferred)
      (FunctionRaw.scaleRat r g.preferred))
  exact FunctionRaw.scaleRat_add_agreeOnCommonDomain f.valid g.valid

def ComplexFunction.sub (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.sub f.preferred g.preferred)
    (FunctionRaw.sub_valid f.valid g.valid)

def ComplexFunction.sum (fs : List ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.sum (fs.map (fun f => f.preferred)))
    (FunctionRaw.sum_valid _ (by
      intro raw hraw
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hraw
      exact f.valid))

theorem ComplexFunction.sum_representation_agrees_preferred
    {fs : List ComplexFunction} {alternatives : List FunctionRaw}
    (halt : ∀ raw, raw ∈ alternatives → raw.Valid)
    (hpair : FunctionRaw.AgreeList alternatives
      (fs.map (fun f => f.preferred))) :
    (FunctionRaw.sum alternatives).AgreeOnCommonDomain
      (FunctionRaw.sum (fs.map (fun f => f.preferred))) := by
  apply FunctionRaw.sum_agreeOnCommonDomain
  · exact halt
  · intro raw hraw
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hraw
    exact f.valid
  · exact hpair

def ComplexFunction.linearCombination
    (terms : List (Rat × ComplexFunction)) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.linearCombination
      (terms.map (fun term => (term.1, term.2.preferred))))
    (FunctionRaw.linearCombination_valid _ (by
      intro term hterm
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hterm
      exact original.2.valid))

theorem ComplexFunction.linearCombination_representation_agrees_preferred
    {terms : List (Rat × ComplexFunction)}
    {alternatives : List (Rat × FunctionRaw)}
    (halt : ∀ term, term ∈ alternatives → term.2.Valid)
    (hpair : FunctionRaw.AgreeList
      (alternatives.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2))
      (terms.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2.preferred))) :
    (FunctionRaw.linearCombination alternatives).AgreeOnCommonDomain
      (FunctionRaw.linearCombination
        (terms.map (fun term => (term.1, term.2.preferred)))) := by
  have hsum :
      (FunctionRaw.sum
        (alternatives.map (fun term =>
          FunctionRaw.scaleRat term.1 term.2))).AgreeOnCommonDomain
        (FunctionRaw.sum
          (terms.map (fun term =>
            FunctionRaw.scaleRat term.1 term.2.preferred))) := by
    apply FunctionRaw.sum_agreeOnCommonDomain
    · intro raw hraw
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hraw
      exact FunctionRaw.scaleRat_valid (halt term hterm)
    · intro raw hraw
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp hraw
      exact FunctionRaw.scaleRat_valid term.2.valid
    · exact hpair
  have hmap :
      (terms.map (fun term => (term.1, term.2.preferred))).map
          (fun term => FunctionRaw.scaleRat term.1 term.2) =
        terms.map (fun term =>
          FunctionRaw.scaleRat term.1 term.2.preferred) := by
    simp [List.map_map]
  unfold FunctionRaw.linearCombination
  rw [hmap]
  exact hsum

def ComplexFunction.linearCombination_withAlternative
    {terms : List (Rat × ComplexFunction)}
    {alternatives : List (Rat × FunctionRaw)}
    (halt : ∀ term, term ∈ alternatives → term.2.Valid)
    (hpair : FunctionRaw.AgreeList
      (alternatives.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2))
      (terms.map (fun term =>
        FunctionRaw.scaleRat term.1 term.2.preferred))) : ComplexFunction :=
  ComplexFunction.withAlternative
    (ComplexFunction.linearCombination terms)
    (FunctionRaw.linearCombination alternatives)
    (FunctionRaw.linearCombination_valid alternatives halt)
    (FunctionRaw.agreeOnCommonDomain_symm
      (ComplexFunction.linearCombination_representation_agrees_preferred
        halt hpair))

theorem ComplexFunction.add_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.add rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.add f.preferred g.preferred) := by
  exact FunctionRaw.add_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

theorem ComplexFunction.neg_representation_agrees_preferred
    {f : ComplexFunction} (rf : ComplexFunction.Representation f) :
    (FunctionRaw.neg rf.raw).AgreeOnCommonDomain
      (FunctionRaw.neg f.preferred) := by
  exact FunctionRaw.neg_agreeOnCommonDomain rf.agrees

theorem ComplexFunction.scaleRat_representation_agrees_preferred
    {r : Rat} {f : ComplexFunction}
    (rf : ComplexFunction.Representation f) :
    (FunctionRaw.scaleRat r rf.raw).AgreeOnCommonDomain
      (FunctionRaw.scaleRat r f.preferred) := by
  exact FunctionRaw.scaleRat_agreeOnCommonDomain rf.agrees

theorem ComplexFunction.sub_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.sub rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.sub f.preferred g.preferred) := by
  exact FunctionRaw.sub_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

/-! Function-level representation equivalence records the same domain and a
pointwise raw-real equivalence.  This is the lightweight bridge needed when a
later proof switches between two certified implementations of one function. -/
def RealFunRaw.EquivOn (f g : RealFunRaw) : Prop :=
  f.domain = g.domain /\
    ∀ x, f.domain x ->
      ({ compute := f.compute x } : RealRaw).Equiv
        ({ compute := g.compute x } : RealRaw)

theorem RealFunRaw.equivOn_refl (f : RealFunRaw) (hf : f.Valid) :
    f.EquivOn f := by
  constructor
  · rfl
  · intro x hx
    exact RealRaw.equiv_refl { compute := f.compute x } (hf x hx)

theorem RealFunRaw.equivOn_symm {f g : RealFunRaw}
    (hfg : f.EquivOn g) : g.EquivOn f := by
  constructor
  · exact hfg.1.symm
  · intro x hx
    exact RealRaw.equiv_symm (hfg.2 x (hfg.1.symm ▸ hx))

theorem RealFunRaw.equivOn_trans {f g h : RealFunRaw}
    (hf : f.Valid) (hg : g.Valid) (hh : h.Valid)
    (hfg : f.EquivOn g) (hgh : g.EquivOn h) :
    f.EquivOn h := by
  constructor
  · exact hfg.1.trans hgh.1
  · intro x hx
    let F : RealRaw := { compute := f.compute x }
    let G : RealRaw := { compute := g.compute x }
    let H : RealRaw := { compute := h.compute x }
    have hF : F.Valid := by
      simpa [F, RealRaw.Valid, RealFunRaw.applyCompute] using hf x hx
    have hG : G.Valid := by
      simpa [G, RealRaw.Valid, RealFunRaw.applyCompute] using
        hg x (hfg.1 ▸ hx)
    have hH : H.Valid := by
      simpa [H, RealRaw.Valid, RealFunRaw.applyCompute] using
        hh x (hgh.1 ▸ (hfg.1 ▸ hx))
    exact RealRaw.equiv_trans hF hG hH
      (hfg.2 x hx) (hgh.2 x (hfg.1 ▸ hx))

theorem effectiveRealFunRaw_mul_equivOn
    {f f' g g' : RealFunRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.EquivOn f') (hgg : g.EquivOn g') :
    (RealFunRaw.mul f g).EquivOn (RealFunRaw.mul f' g') := by
  constructor
  · funext x
    simp only [RealFunRaw.mul]
    rw [hff.1, hgg.1]
  · intro x hx
    have hfx : f.domain x := hx.1
    have hgx : g.domain x := hx.2
    let X : RealRaw := { compute := f.compute x }
    let X' : RealRaw := { compute := f'.compute x }
    let Y : RealRaw := { compute := g.compute x }
    let Y' : RealRaw := { compute := g'.compute x }
    have hX : X.Valid := by
      simpa [X, RealRaw.Valid, RealFunRaw.applyCompute] using hf x hfx
    have hX' : X'.Valid := by
      simpa [X', RealRaw.Valid, RealFunRaw.applyCompute] using hf' x (hff.1 ▸ hfx)
    have hY : Y.Valid := by
      simpa [Y, RealRaw.Valid, RealFunRaw.applyCompute] using hg x hgx
    have hY' : Y'.Valid := by
      simpa [Y', RealRaw.Valid, RealFunRaw.applyCompute] using hg' x (hgg.1 ▸ hgx)
    change (X * Y).Equiv (X' * Y')
    exact RealRaw.mul_equiv hX hX' hY hY'
      (hff.2 x hfx) (hgg.2 x hgx)

/-! Complex-valued raw functions have the same constructive product closure.
The domain is the intersection of the two input domains, and the output box
is the rational four-corner product of the two certified complex boxes. -/
def FunctionRaw.mul (f g : FunctionRaw) : FunctionRaw where
  domain := fun z => f.domain z /\ g.domain z
  compute := fun z hz n =>
    QBox.mul (f.compute z hz.1 n) (g.compute z hz.2 n)

theorem FunctionRaw.mul_valid
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f g).Valid := by
  intro z hz
  have hproduct : (ComplexRaw.mul (f.evalRaw z hz.1)
      (g.evalRaw z hz.2)).Valid :=
    ComplexRaw.mul_valid (hf z hz.1) (hg z hz.2)
  change (ComplexRaw.mul (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid at hproduct
  change (ComplexRaw.mul (f.evalRaw z hz.1)
    (g.evalRaw z hz.2)).Valid
  exact hproduct

theorem FunctionRaw.mul_agreeOnCommonDomain
    {f f' g g' : FunctionRaw}
    (hf : f.Valid) (hf' : f'.Valid)
    (hg : g.Valid) (hg' : g'.Valid)
    (hff : f.AgreeOnCommonDomain f')
    (hgg : g.AgreeOnCommonDomain g') :
    (FunctionRaw.mul f g).AgreeOnCommonDomain
      (FunctionRaw.mul f' g') := by
  intro z hleft hright
  let F := f.evalRaw z hleft.1
  let F' := f'.evalRaw z hright.1
  let G := g.evalRaw z hleft.2
  let G' := g'.evalRaw z hright.2
  change (ComplexRaw.mul F G).Equiv (ComplexRaw.mul F' G')
  exact ComplexRaw.mul_equiv
    (hf z hleft.1) (hf' z hright.1)
    (hg z hleft.2) (hg' z hright.2)
    (hff z hleft.1 hright.1)
    (hgg z hleft.2 hright.2)

theorem FunctionRaw.mul_one_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul f FunctionRaw.one).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (FunctionRaw.one.evalRaw z hleft.2)).Equiv
    (f.evalRaw z hright)
  exact effectiveComplexRaw_mul_one_equiv (hf z hleft.1)

theorem FunctionRaw.one_mul_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul FunctionRaw.one f).AgreeOnCommonDomain f := by
  intro z hleft hright
  change (ComplexRaw.mul (FunctionRaw.one.evalRaw z hleft.1)
      (f.evalRaw z hleft.2)).Equiv
    (f.evalRaw z hright)
  exact effectiveComplexRaw_one_mul_equiv (hf z hleft.2)

theorem FunctionRaw.mul_zero_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul f FunctionRaw.zero).AgreeOnCommonDomain
      FunctionRaw.zero := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (FunctionRaw.zero.evalRaw z hleft.2)).Equiv
    (FunctionRaw.zero.evalRaw z hright)
  exact effectiveComplexRaw_mul_zero_equiv (hf z hleft.1)

theorem FunctionRaw.zero_mul_agreeOnCommonDomain
    {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.mul FunctionRaw.zero f).AgreeOnCommonDomain
      FunctionRaw.zero := by
  intro z hleft hright
  change (ComplexRaw.mul (FunctionRaw.zero.evalRaw z hleft.1)
      (f.evalRaw z hleft.2)).Equiv
    (FunctionRaw.zero.evalRaw z hright)
  exact effectiveComplexRaw_zero_mul_equiv (hf z hleft.2)

theorem FunctionRaw.mul_comm_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f g).AgreeOnCommonDomain
      (FunctionRaw.mul g f) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.mul (g.evalRaw z hright.1)
      (f.evalRaw z hright.2))
  exact effectiveComplexRaw_mul_comm_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.mul_assoc_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul (FunctionRaw.mul f g) h).AgreeOnCommonDomain
      (FunctionRaw.mul f (FunctionRaw.mul g h)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.mul (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.mul (f.evalRaw z hright.1)
      (ComplexRaw.mul (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_mul_assoc_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

def FunctionRaw.pow (f : FunctionRaw) : Nat -> FunctionRaw
  | 0 => FunctionRaw.one
  | n + 1 => FunctionRaw.mul (FunctionRaw.pow f n) f

theorem FunctionRaw.pow_valid {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.pow f n).Valid := by
  induction n with
  | zero => exact FunctionRaw.one_valid
  | succ n ih => exact FunctionRaw.mul_valid ih hf

theorem FunctionRaw.one_agreeOnCommonDomain :
    FunctionRaw.one.AgreeOnCommonDomain FunctionRaw.one := by
  intro z hleft hright
  exact ComplexRaw.equiv_refl
    (FunctionRaw.one.evalRaw z hleft)
    (FunctionRaw.one_valid z hleft)

theorem FunctionRaw.pow_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid)
    (hfg : f.AgreeOnCommonDomain g) (n : Nat) :
    (FunctionRaw.pow f n).AgreeOnCommonDomain
      (FunctionRaw.pow g n) := by
  induction n with
  | zero => exact FunctionRaw.one_agreeOnCommonDomain
  | succ n ih =>
    exact FunctionRaw.mul_agreeOnCommonDomain
      (FunctionRaw.pow_valid hf) (FunctionRaw.pow_valid hg) hf hg ih hfg

theorem FunctionRaw.mul_add_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul f (FunctionRaw.add g h)).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.mul f g) (FunctionRaw.mul f h)) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (ComplexRaw.add (g.evalRaw z hleft.2.1)
        (h.evalRaw z hleft.2.2))).Equiv
    (ComplexRaw.add
      (ComplexRaw.mul (f.evalRaw z hright.1.1)
        (g.evalRaw z hright.1.2))
      (ComplexRaw.mul (f.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_mul_add_equiv
    (hf z hleft.1) (hg z hleft.2.1) (hh z hleft.2.2)

theorem FunctionRaw.add_mul_agreeOnCommonDomain
    {f g h : FunctionRaw} (hf : f.Valid) (hg : g.Valid) (hh : h.Valid) :
    (FunctionRaw.mul (FunctionRaw.add f g) h).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.mul f h) (FunctionRaw.mul g h)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.add (f.evalRaw z hleft.1.1)
        (g.evalRaw z hleft.1.2))
      (h.evalRaw z hleft.2)).Equiv
    (ComplexRaw.add
      (ComplexRaw.mul (f.evalRaw z hright.1.1)
        (h.evalRaw z hright.1.2))
      (ComplexRaw.mul (g.evalRaw z hright.2.1)
        (h.evalRaw z hright.2.2)))
  exact effectiveComplexRaw_add_mul_equiv
    (hf z hleft.1.1) (hg z hleft.1.2) (hh z hleft.2)

theorem FunctionRaw.mul_neg_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul f (FunctionRaw.neg g)).AgreeOnCommonDomain
      (FunctionRaw.neg (FunctionRaw.mul f g)) := by
  intro z hleft hright
  change (ComplexRaw.mul (f.evalRaw z hleft.1)
      (ComplexRaw.neg (g.evalRaw z hleft.2))).Equiv
    (ComplexRaw.neg (ComplexRaw.mul (f.evalRaw z hright.1)
      (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_mul_neg_equiv
    (hf z hleft.1) (hg z hleft.2)

theorem FunctionRaw.neg_mul_agreeOnCommonDomain
    {f g : FunctionRaw} (hf : f.Valid) (hg : g.Valid) :
    (FunctionRaw.mul (FunctionRaw.neg f) g).AgreeOnCommonDomain
      (FunctionRaw.neg (FunctionRaw.mul f g)) := by
  intro z hleft hright
  change (ComplexRaw.mul
      (ComplexRaw.neg (f.evalRaw z hleft.1))
      (g.evalRaw z hleft.2)).Equiv
    (ComplexRaw.neg (ComplexRaw.mul (f.evalRaw z hright.1)
      (g.evalRaw z hright.2)))
  exact effectiveComplexRaw_neg_mul_equiv
    (hf z hleft.1) (hg z hleft.2)

def FunctionRaw.polynomial (coeffs : List QComplex) (f : FunctionRaw) : FunctionRaw :=
  coeffs.foldr
    (fun c acc => FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f acc))
    FunctionRaw.zero

theorem FunctionRaw.polynomial_compute
    (coeffs : List QComplex) {f : FunctionRaw} {z : QComplex}
    (hz : f.domain z) (n : Nat)
    (h : (FunctionRaw.polynomial coeffs f).domain z) :
    (FunctionRaw.polynomial coeffs f).compute z h n =
      QBox.evalPoly coeffs (f.compute z hz n) := by
  induction coeffs with
  | nil => rfl
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).compute z h n =
      QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n) (QBox.evalPoly cs (f.compute z hz n)))
    change QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n)
          ((FunctionRaw.polynomial cs f).compute z _ n)) =
      QBox.add (QBox.point c)
        (QBox.mul (f.compute z hz n) (QBox.evalPoly cs (f.compute z hz n)))
    rw [ih]

theorem FunctionRaw.polynomial_valid
    (coeffs : List QComplex) {f : FunctionRaw} (hf : f.Valid) :
    (FunctionRaw.polynomial coeffs f).Valid := by
  induction coeffs with
  | nil => exact FunctionRaw.zero_valid
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).Valid
    exact FunctionRaw.add_valid (FunctionRaw.constant_valid c)
      (FunctionRaw.mul_valid hf ih)

theorem FunctionRaw.polynomial_agreeOnCommonDomain
    (coeffs : List QComplex) {f g : FunctionRaw}
    (hf : f.Valid) (hg : g.Valid)
    (hfg : f.AgreeOnCommonDomain g) :
    (FunctionRaw.polynomial coeffs f).AgreeOnCommonDomain
      (FunctionRaw.polynomial coeffs g) := by
  induction coeffs with
  | nil => exact FunctionRaw.zero_agreeOnCommonDomain
  | cons c cs ih =>
    change (FunctionRaw.add (FunctionRaw.constant c)
      (FunctionRaw.mul f (FunctionRaw.polynomial cs f))).AgreeOnCommonDomain
      (FunctionRaw.add (FunctionRaw.constant c)
        (FunctionRaw.mul g (FunctionRaw.polynomial cs g)))
    exact FunctionRaw.add_agreeOnCommonDomain
      (FunctionRaw.constant_valid c) (FunctionRaw.constant_valid c)
      (FunctionRaw.mul_valid hf (FunctionRaw.polynomial_valid cs hf))
      (FunctionRaw.mul_valid hg (FunctionRaw.polynomial_valid cs hg))
      (FunctionRaw.constant_agreeOnCommonDomain c)
      (FunctionRaw.mul_agreeOnCommonDomain (f := f) (f' := g)
        (g := FunctionRaw.polynomial cs f)
        (g' := FunctionRaw.polynomial cs g) hf hg
        (FunctionRaw.polynomial_valid cs hf)
        (FunctionRaw.polynomial_valid cs hg)
        hfg ih)

/-! The abstract complex-function API exposes the certified product only
after the raw product closure has been established.  This keeps the handle
layer honest: multiplication carries the intersection domain and inherits
validity from the four-corner rational box product. -/
def ComplexFunction.mul (f g : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.mul f.preferred g.preferred)
    (FunctionRaw.mul_valid f.valid g.valid)

def ComplexFunction.pow (f : ComplexFunction) (n : Nat) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.pow f.preferred n)
    (FunctionRaw.pow_valid f.valid)

def ComplexFunction.constant (c : QComplex) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.constant c)
    (FunctionRaw.constant_valid c)

def ComplexFunction.polynomial
    (coeffs : List QComplex) (f : ComplexFunction) : ComplexFunction :=
  ComplexFunction.ofRaw
    (FunctionRaw.polynomial coeffs f.preferred)
    (FunctionRaw.polynomial_valid coeffs f.valid)

theorem ComplexFunction.mul_one_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul f ComplexFunction.one).preferred).AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.mul f.preferred FunctionRaw.one).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.mul_one_agreeOnCommonDomain f.valid

theorem ComplexFunction.one_mul_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul ComplexFunction.one f).preferred).AgreeOnCommonDomain
      f.preferred := by
  change (FunctionRaw.mul FunctionRaw.one f.preferred).AgreeOnCommonDomain
    f.preferred
  exact FunctionRaw.one_mul_agreeOnCommonDomain f.valid

theorem ComplexFunction.mul_zero_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul f ComplexFunction.zero).preferred).AgreeOnCommonDomain
      ComplexFunction.zero.preferred := by
  change (FunctionRaw.mul f.preferred FunctionRaw.zero).AgreeOnCommonDomain
    FunctionRaw.zero
  exact FunctionRaw.mul_zero_agreeOnCommonDomain f.valid

theorem ComplexFunction.zero_mul_representation_agrees_preferred
    (f : ComplexFunction) :
    ((ComplexFunction.mul ComplexFunction.zero f).preferred).AgreeOnCommonDomain
      ComplexFunction.zero.preferred := by
  change (FunctionRaw.mul FunctionRaw.zero f.preferred).AgreeOnCommonDomain
    FunctionRaw.zero
  exact FunctionRaw.zero_mul_agreeOnCommonDomain f.valid

theorem ComplexFunction.mul_comm_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul f g).preferred.AgreeOnCommonDomain
      (ComplexFunction.mul g f).preferred := by
  change (FunctionRaw.mul f.preferred g.preferred).AgreeOnCommonDomain
    (FunctionRaw.mul g.preferred f.preferred)
  exact FunctionRaw.mul_comm_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.mul_assoc_representation_agrees_preferred
    (f g h : ComplexFunction) :
    ((ComplexFunction.mul (ComplexFunction.mul f g) h).preferred).AgreeOnCommonDomain
      (ComplexFunction.mul f (ComplexFunction.mul g h)).preferred := by
  change (FunctionRaw.mul (FunctionRaw.mul f.preferred g.preferred)
      h.preferred).AgreeOnCommonDomain
    (FunctionRaw.mul f.preferred (FunctionRaw.mul g.preferred h.preferred))
  exact FunctionRaw.mul_assoc_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.mul_add_representation_agrees_preferred
    (f g h : ComplexFunction) :
    (ComplexFunction.mul f (ComplexFunction.add g h)).preferred.AgreeOnCommonDomain
      (ComplexFunction.add (ComplexFunction.mul f g)
        (ComplexFunction.mul f h)).preferred := by
  change (FunctionRaw.mul f.preferred
      (FunctionRaw.add g.preferred h.preferred)).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.mul f.preferred g.preferred)
      (FunctionRaw.mul f.preferred h.preferred))
  exact FunctionRaw.mul_add_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.add_mul_representation_agrees_preferred
    (f g h : ComplexFunction) :
    (ComplexFunction.mul (ComplexFunction.add f g) h).preferred.AgreeOnCommonDomain
      (ComplexFunction.add (ComplexFunction.mul f h)
        (ComplexFunction.mul g h)).preferred := by
  change (FunctionRaw.mul
      (FunctionRaw.add f.preferred g.preferred) h.preferred).AgreeOnCommonDomain
    (FunctionRaw.add (FunctionRaw.mul f.preferred h.preferred)
      (FunctionRaw.mul g.preferred h.preferred))
  exact FunctionRaw.add_mul_agreeOnCommonDomain f.valid g.valid h.valid

theorem ComplexFunction.mul_representation_agrees_preferred
    {f g : ComplexFunction}
    (rf : ComplexFunction.Representation f)
    (rg : ComplexFunction.Representation g) :
    (FunctionRaw.mul rf.raw rg.raw).AgreeOnCommonDomain
      (FunctionRaw.mul f.preferred g.preferred) := by
  exact FunctionRaw.mul_agreeOnCommonDomain
    rf.valid f.valid rg.valid g.valid rf.agrees rg.agrees

theorem ComplexFunction.pow_representation_agrees_preferred
    {f : ComplexFunction} (rf : ComplexFunction.Representation f) (n : Nat) :
    (FunctionRaw.pow rf.raw n).AgreeOnCommonDomain
      (FunctionRaw.pow f.preferred n) := by
  exact FunctionRaw.pow_agreeOnCommonDomain
    rf.valid f.valid rf.agrees n

theorem ComplexFunction.polynomial_representation_agrees_preferred
    {f : ComplexFunction} (coeffs : List QComplex)
    (rf : ComplexFunction.Representation f) :
    (FunctionRaw.polynomial coeffs rf.raw).AgreeOnCommonDomain
      (FunctionRaw.polynomial coeffs f.preferred) := by
  exact FunctionRaw.polynomial_agreeOnCommonDomain
    coeffs rf.valid f.valid rf.agrees

theorem ComplexFunction.mul_neg_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul f (ComplexFunction.neg g)).preferred.AgreeOnCommonDomain
      (ComplexFunction.neg (ComplexFunction.mul f g)).preferred := by
  change (FunctionRaw.mul f.preferred (FunctionRaw.neg g.preferred)).AgreeOnCommonDomain
    (FunctionRaw.neg (FunctionRaw.mul f.preferred g.preferred))
  exact FunctionRaw.mul_neg_agreeOnCommonDomain f.valid g.valid

theorem ComplexFunction.neg_mul_representation_agrees_preferred
    (f g : ComplexFunction) :
    (ComplexFunction.mul (ComplexFunction.neg f) g).preferred.AgreeOnCommonDomain
      (ComplexFunction.neg (ComplexFunction.mul f g)).preferred := by
  change (FunctionRaw.mul (FunctionRaw.neg f.preferred) g.preferred).AgreeOnCommonDomain
    (FunctionRaw.neg (FunctionRaw.mul f.preferred g.preferred))
  exact FunctionRaw.neg_mul_agreeOnCommonDomain f.valid g.valid


end ComputableAnalysis
