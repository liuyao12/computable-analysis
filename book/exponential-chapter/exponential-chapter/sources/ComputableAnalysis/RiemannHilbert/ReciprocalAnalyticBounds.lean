import ComputableAnalysis.RiemannHilbert.ReciprocalDifference

/-! Quantitative first-difference, quadratic-remainder, and derivative
continuity estimates for the actual represented reciprocal. -/
namespace ComputableAnalysis.RiemannHilbert.ReciprocalAnalyticBounds
open ComplexRaw FunctionTheory NonzeroBoxSearch RepresentedReciprocal ReciprocalLocalBounds

def quadraticConstant (a : Scalar) (ha : Nonzero a) : Rat :=
  128*bound a ha*bound a ha*bound a ha

def derivativeConstant (a : Scalar) (ha : Nonzero a) : Rat :=
  576*bound a ha*bound a ha*bound a ha

theorem quadraticConstant_nonneg (a : Scalar) (ha : Nonzero a) : 0 ≤ quadraticConstant a ha :=
  Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (bound_pos a ha)))
    (Rat.le_of_lt (bound_pos a ha))) (Rat.le_of_lt (bound_pos a ha))

theorem derivativeConstant_nonneg (a : Scalar) (ha : Nonzero a) : 0 ≤ derivativeConstant a ha :=
  Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (bound_pos a ha)))
    (Rat.le_of_lt (bound_pos a ha))) (Rat.le_of_lt (bound_pos a ha))

theorem difference_bound (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) (H : QPos)
    (hH : H.val ≤ (radius a ha).val) (hza : Small (sub z.val a.val) H.val) :
    Small (sub (inverse z hz).val (inverse a ha).val) (32*bound a ha*bound a ha*H.val) := by
  let B := bound a ha
  have hB : 0 ≤ B := Rat.le_of_lt (bound_pos a ha)
  have hS := inverse_bound a ha z hz (hza.mono hH)
  have hfirst := Small.mul (inverse a ha).property (sub_valid z.property a.property)
    hB (Rat.le_of_lt H.property) (inverse_small a ha) hza
  have hs := SeriesLimitLaws.small_neg (Small.mul
    (mul_valid (inverse a ha).property (sub_valid z.property a.property)) (inverse z hz).property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) (Rat.le_of_lt H.property))
    (Rat.mul_nonneg (by decide +kernel) hB) hfirst hS)
  have he : 2*(2*B*H.val)*(8*B) = 32*B*B*H.val := by grind
  change Small _ (2*(2*B*H.val)*(8*B)) at hs
  rw [he] at hs
  exact Small.congr
    (neg_valid (mul_valid (mul_valid (inverse a ha).property (sub_valid z.property a.property))
      (inverse z hz).property))
    (sub_valid (inverse z hz).property (inverse a ha).property)
    (equiv_symm (ReciprocalDifference.difference a z ha hz)) hs

theorem remainder_bound (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) (H : QPos)
    (hH : H.val ≤ (radius a ha).val) (hza : Small (sub z.val a.val) H.val) :
    Small (sub (sub (inverse z hz).val (inverse a ha).val)
      (mul (ReciprocalDifference.derivative a ha).val (sub z.val a.val)))
      (quadraticConstant a ha*H.val*H.val) := by
  let B := bound a ha
  let r := inverse a ha
  let s := inverse z hz
  let d := sub z.val a.val
  have hB : 0 ≤ B := Rat.le_of_lt (bound_pos a ha)
  have hH0 : 0 ≤ H.val := Rat.le_of_lt H.property
  have hS := inverse_bound a ha z hz (hza.mono hH)
  have hR2 := Small.mul r.property r.property hB hB (inverse_small a ha) (inverse_small a ha)
  have hD2 := Small.mul (sub_valid z.property a.property) (sub_valid z.property a.property) hH0 hH0 hza hza
  have hr0 : 0 ≤ 2*B*B := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB
  have hd0 : 0 ≤ 2*H.val*H.val := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hH0) hH0
  have hfirst := Small.mul (mul_valid r.property r.property) (mul_valid (sub_valid z.property a.property)
    (sub_valid z.property a.property)) hr0 hd0 hR2 hD2
  have hs := Small.mul (mul_valid (mul_valid r.property r.property)
    (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) s.property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hr0) hd0)
    (Rat.mul_nonneg (by decide +kernel) hB) hfirst hS
  have he : 2*(2*(2*B*B)*(2*H.val*H.val))*(8*B) =
      quadraticConstant a ha*H.val*H.val := by unfold quadraticConstant; change _ = 128*B*B*B*H.val*H.val; grind
  change Small _ (2*(2*(2*B*B)*(2*H.val*H.val))*(8*B)) at hs
  rw [he] at hs
  exact Small.congr
    (mul_valid (mul_valid (mul_valid r.property r.property)
      (mul_valid (sub_valid z.property a.property) (sub_valid z.property a.property))) s.property)
    (sub_valid (sub_valid s.property r.property)
      (mul_valid (ReciprocalDifference.derivative a ha).property (sub_valid z.property a.property)))
    (equiv_symm (ReciprocalDifference.remainder a z ha hz)) hs

theorem derivative_difference_bound (a z : Scalar) (ha : Nonzero a) (hz : Nonzero z) (H : QPos)
    (hH : H.val ≤ (radius a ha).val) (hza : Small (sub z.val a.val) H.val) :
    Small (sub (ReciprocalDifference.derivative z hz).val (ReciprocalDifference.derivative a ha).val)
      (derivativeConstant a ha*H.val) := by
  let B := bound a ha
  have hB : 0 ≤ B := Rat.le_of_lt (bound_pos a ha)
  have hS := inverse_bound a ha z hz (hza.mono hH)
  have hsum := LocalODE.small_add hS (inverse_small a ha)
  have hd := difference_bound a z ha hz H hH hza
  have hs := SeriesLimitLaws.small_neg (Small.mul
    (add_valid (inverse z hz).property (inverse a ha).property)
    (sub_valid (inverse z hz).property (inverse a ha).property)
    (Rat.add_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB)
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hB) hB) (Rat.le_of_lt H.property))
    hsum hd)
  have he : 2*(8*B+B)*(32*B*B*H.val) = derivativeConstant a ha*H.val := by
    unfold derivativeConstant; change _ = 576*B*B*B*H.val; grind
  change Small _ (2*(8*B+B)*(32*B*B*H.val)) at hs
  rw [he] at hs
  exact Small.congr
    (neg_valid (mul_valid (add_valid (inverse z hz).property (inverse a ha).property)
      (sub_valid (inverse z hz).property (inverse a ha).property)))
    (sub_valid (ReciprocalDifference.derivative z hz).property (ReciprocalDifference.derivative a ha).property)
    (equiv_symm (ReciprocalDifference.derivative_difference a z ha hz)) hs

def precision (C : Rat) (hC : 0 ≤ C) (eps : QPos) : QPos :=
  ⟨eps.val/(C+1), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by grind))⟩

theorem precision_estimate (C : Rat) (hC : 0 ≤ C) (eps H : QPos)
    (hH : H.val ≤ (precision C hC eps).val) : C*H.val ≤ eps.val := by
  have he : (C+1)*(precision C hC eps).val=eps.val := by
    change (C+1)*(eps.val/(C+1))=eps.val
    rw [Rat.div_def]
    have hinv := Rat.mul_inv_cancel (C+1) (Rat.ne_of_gt (show 0<C+1 by grind))
    grind
  have hm := Rat.mul_le_mul_of_nonneg_left hH (show 0≤C+1 by grind)
  have hH0 := H.property
  grind

def delta (a : Scalar) (ha : Nonzero a) (C : Rat) (hC : 0 ≤ C) (eps : QPos) : QPos :=
  ⟨min (radius a ha).val (precision C hC eps).val, by
    have h1 := (radius a ha).property
    have h2 := (precision C hC eps).property
    grind⟩

theorem delta_radius (a : Scalar) (ha : Nonzero a) (C : Rat) (hC : 0 ≤ C) (eps : QPos) :
    (delta a ha C hC eps).val ≤ (radius a ha).val := by unfold delta; grind

theorem delta_precision (a : Scalar) (ha : Nonzero a) (C : Rat) (hC : 0 ≤ C) (eps : QPos) :
    (delta a ha C hC eps).val ≤ (precision C hC eps).val := by unfold delta; grind

end ComputableAnalysis.RiemannHilbert.ReciprocalAnalyticBounds
