import ComputableAnalysis.Differential

/-!
# Rational interval quotients

This module packages the finite sign split for the quotient of two symmetric
rational boxes.  It is the reusable endpoint calculation behind analytic
derivative certificates whose function and derivative values are both
enclosed by a common-radius interval algorithm.
-/

namespace ComputableAnalysis

namespace QInterval

/-- The symmetric rational interval with the displayed center and radius. -/
def around (center radius : Rat) : QInterval :=
  { lo := center - radius, hi := center + radius }

/-- For a positive rational step, a rational bound for the center secant,
the quotient width, and the derivative width yield a literal `NearAt`
certificate for symmetric interval boxes. -/
theorem around_differenceQuotient_near_around_of_pos
    (c0 c1 d r h E : Rat) (eps : QPos)
    (hpos : 0 < h) (hr : 0 <= r)
    (herror : qabs ((c1 - c0) / h - d) <= E)
    (hbudget : E + 2 * r / h + r <= eps.val)
    (hquotientWidth : 4 * r / h <= eps.val)
    (hderivativeWidth : 2 * r <= eps.val) :
    (differenceQuotient (around c1 r) (around c0 r) h).NearAt
      (around d r) eps := by
  have hh : h ≠ 0 := Rat.ne_of_gt hpos
  have hinvpos : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have htwoRdiv : 0 <= 2 * r / h := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hr)
      (Rat.le_of_lt ((Rat.inv_pos).2 hpos))
  have hEeps : E <= eps.val := by
    grind [Rat.sub_eq_add_neg]
  let q : Rat := (c1 - c0) / h
  have hupper : q - d <= E := by
    dsimp [q]
    exact Rat.le_trans (self_le_qabs _) herror
  have hlower : d - q <= E := by
    dsimp [q]
    calc
      d - (c1 - c0) / h = -((c1 - c0) / h - d) := by
        grind [Rat.sub_eq_add_neg]
      _ <= qabs (-((c1 - c0) / h - d)) := self_le_qabs _
      _ = qabs ((c1 - c0) / h - d) := qabs_neg _
      _ <= E := herror
  have hlo : (1 / h) * ((c1 - r) - (c0 + r)) = q - 2 * r / h := by
    dsimp [q]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hhi : (1 / h) * ((c1 + r) - (c0 - r)) = q + 2 * r / h := by
    dsimp [q]
    rw [Rat.div_def, Rat.div_def]
    have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  unfold NearAt differenceQuotient divRat sub scaleRat around width
  rw [if_pos hinvpos]
  dsimp
  change
    (1 / h) * ((c1 - r) - (c0 + r)) <= d + r + eps.val /\
      d - r <= (1 / h) * ((c1 + r) - (c0 - r)) + eps.val /\
      (1 / h) * ((c1 + r) - (c0 - r)) -
        (1 / h) * ((c1 - r) - (c0 + r)) <= eps.val /\
      d + r - (d - r) <= eps.val
  rw [hlo, hhi]
  have hqlo : q - 2 * r / h <= q := by grind
  have hqhi : q <= q + 2 * r / h := by grind
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  constructor
  · grind [Rat.sub_eq_add_neg]
  · grind [Rat.sub_eq_add_neg]

/-- The symmetric interval quotient certificate is independent of the sign
of its nonzero rational step. -/
theorem around_differenceQuotient_near_around
    (c0 c1 d r h E : Rat) (eps : QPos)
    (hh : h ≠ 0) (hr : 0 <= r)
    (herror : qabs ((c1 - c0) / h - d) <= E)
    (hbudget : E + 2 * r / qabs h + r <= eps.val)
    (hquotientWidth : 4 * r / qabs h <= eps.val)
    (hderivativeWidth : 2 * r <= eps.val) :
    (differenceQuotient (around c1 r) (around c0 r) h).NearAt
      (around d r) eps := by
  by_cases hpos : 0 < h
  · have hqabs : qabs h = h := qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)
    rw [hqabs] at hbudget hquotientWidth
    exact around_differenceQuotient_near_around_of_pos
      c0 c1 d r h E eps hpos hr herror hbudget hquotientWidth
      hderivativeWidth
  · have hneg : h < 0 := by grind
    have hkpos : 0 < -h := by grind
    have hqabs : qabs h = -h := qabs_eq_neg_of_nonpos (Rat.le_of_lt hneg)
    rw [hqabs] at hbudget hquotientWidth
    have hnegInv : (-h)⁻¹ = -h⁻¹ := by
      have hnegmul : (-h) * (-h⁻¹) = 1 := by
        have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
        grind [Rat.mul_assoc, Rat.mul_comm]
      calc
        (-h)⁻¹ = (-h)⁻¹ * 1 := by grind
        _ = (-h)⁻¹ * ((-h) * (-h⁻¹)) := by rw [hnegmul]
        _ = ((-h)⁻¹ * (-h)) * (-h⁻¹) := by
          grind [Rat.mul_assoc]
        _ = 1 * (-h⁻¹) := by
          rw [Rat.inv_mul_cancel (-h) (by grind)]
        _ = -h⁻¹ := by rw [Rat.one_mul]
    have hquotient : (c0 - c1) / (-h) = (c1 - c0) / h := by
      rw [Rat.div_def, Rat.div_def, hnegInv]
      grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]
    have herror' : qabs ((c0 - c1) / (-h) - d) <= E := by
      rw [hquotient]
      exact herror
    have hreverse := differenceQuotient_reverse_of_pos
      (A := around c0 r) (B := around c1 r) (h := -h) hkpos
    have hdouble : -(-h) = h := by grind
    rw [hdouble] at hreverse
    rw [hreverse]
    exact around_differenceQuotient_near_around_of_pos
      c1 c0 d r (-h) E eps hkpos hr herror' hbudget hquotientWidth
      hderivativeWidth

end QInterval

end ComputableAnalysis
