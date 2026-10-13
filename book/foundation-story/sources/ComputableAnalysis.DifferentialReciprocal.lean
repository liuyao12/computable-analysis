import ComputableAnalysis.FinitePolynomialCalculus

/-!
# Effective reciprocal differentiation on a positive rational chart

The logarithm regression previously certified `(1/x)' = -1/x^2` only on
`[1,2]`.  This module records the chart-local fact needed by time changes and
other quotient calculations: any rational interval `[a,b]` with `0 < a` has
the same two-sided finite-difference certificate.

Everything is exact rational algebra.  The secant remainder is

`h / (x^2 * (x+h))`,

and positivity of the chart bounds its absolute coefficient by `1/a^3`.
-/

namespace ComputableAnalysis

namespace FinitePolynomial

namespace CenteredSecantDerivativeBound

/-- Translate a centered secant certificate to the corresponding function of
the local coordinate. -/
def shifted {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) :
    SecantDerivativeBound C
      (fun y => f (y + basepoint))
      (fun y => df (y + basepoint)) where
  errorCoefficient := F.errorCoefficient
  errorCoefficient_nonneg := F.errorCoefficient_nonneg
  error_bound := by
    intro y h hh hy hyh
    have hF := F.error_bound (y + basepoint) h hh (by
      simpa [Rat.add_sub_cancel] using hy) (by
      have heq : y + basepoint + h - basepoint = y + h := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [heq]
      exact hyh)
    simpa [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm] using hF

/-- Centered quantitative secant bounds are closed under rational scaling. -/
def scaleRat (r : Rat) {basepoint C : Rat} {f df : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df) :
    CenteredSecantDerivativeBound basepoint C
      (fun x => r * f x) (fun x => r * df x) := by
  let S := F.shifted.scaleRat r
  refine
    { errorCoefficient := S.errorCoefficient
      errorCoefficient_nonneg := S.errorCoefficient_nonneg
      error_bound := ?_ }
  intro x h hh hx hxh
  have hS := S.error_bound (x - basepoint) h hh hx (by
    have heq : x - basepoint + h = x + h - basepoint := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hxh)
  dsimp [S, shifted] at hS
  have hbase : x - basepoint + basepoint = x := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hstep : x - basepoint + h + basepoint = x + h := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  rw [hbase, hstep] at hS
  exact hS

/-- Centered quantitative secant bounds inherit the finite product rule from
the symmetric local-coordinate implementation. -/
def mul {basepoint C : Rat} {f df g dg : Rat -> Rat}
    (F : CenteredSecantDerivativeBound basepoint C f df)
    (G : CenteredSecantDerivativeBound basepoint C g dg)
    (fMajorant dfMajorant gMajorant dgMajorant : Rat)
    (hfMajorant : forall x, qabs (x - basepoint) <= C ->
      qabs (f x) <= fMajorant)
    (hdfMajorant : forall x, qabs (x - basepoint) <= C ->
      qabs (df x) <= dfMajorant)
    (hgMajorant : forall x, qabs (x - basepoint) <= C ->
      qabs (g x) <= gMajorant)
    (hdgMajorant : forall x, qabs (x - basepoint) <= C ->
      qabs (dg x) <= dgMajorant)
    (hC0 : 0 <= C) (hf0 : 0 <= fMajorant) (hdf0 : 0 <= dfMajorant)
    (hg0 : 0 <= gMajorant) (hdg0 : 0 <= dgMajorant) :
    CenteredSecantDerivativeBound basepoint C
      (fun x => f x * g x)
      (fun x => f x * dg x + g x * df x) := by
  have hfshift : forall y, qabs y <= C ->
      qabs (f (y + basepoint)) <= fMajorant := by
    intro y hy
    apply hfMajorant
    have heq : y + basepoint - basepoint = y := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hy
  have hdfshift : forall y, qabs y <= C ->
      qabs (df (y + basepoint)) <= dfMajorant := by
    intro y hy
    apply hdfMajorant
    have heq : y + basepoint - basepoint = y := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hy
  have hgshift : forall y, qabs y <= C ->
      qabs (g (y + basepoint)) <= gMajorant := by
    intro y hy
    apply hgMajorant
    have heq : y + basepoint - basepoint = y := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hy
  have hdgshift : forall y, qabs y <= C ->
      qabs (dg (y + basepoint)) <= dgMajorant := by
    intro y hy
    apply hdgMajorant
    have heq : y + basepoint - basepoint = y := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hy
  let P := F.shifted.mul G.shifted
    fMajorant dfMajorant gMajorant dgMajorant
    hfshift hdfshift hgshift hdgshift
    hC0 hf0 hdf0 hg0 hdg0
  refine
    { errorCoefficient := P.errorCoefficient
      errorCoefficient_nonneg := P.errorCoefficient_nonneg
      error_bound := ?_ }
  intro x h hh hx hxh
  have hP := P.error_bound (x - basepoint) h hh hx (by
    have heq : x - basepoint + h = x + h - basepoint := by
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
    rw [heq]
    exact hxh)
  dsimp [P, shifted] at hP
  have hbase : x - basepoint + basepoint = x := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  have hstep : x - basepoint + h + basepoint = x + h := by
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
  rw [hbase, hstep] at hP
  exact hP

end CenteredSecantDerivativeBound

/-- The explicit error coefficient for reciprocal differentiation on a chart
whose positive lower endpoint is `a`. -/
def positiveReciprocalErrorCoefficient (a : Rat) : Rat :=
  1 / a ^ 3

theorem positiveReciprocalErrorCoefficient_nonneg
    {a : Rat} (ha : 0 < a) :
    0 <= positiveReciprocalErrorCoefficient a := by
  unfold positiveReciprocalErrorCoefficient
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by native_decide)
    (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos ha)))

/-- Quantitative reciprocal secant bound on an arbitrary positive rational
interval.  The centered box is exactly `[a,b]`. -/
def positiveReciprocalCenteredSecantBound
    (a b : Rat) (ha : 0 < a) (hab : a <= b) :
    CenteredSecantDerivativeBound ((a + b) / 2) ((b - a) / 2)
      (fun x => 1 / x) (fun x => -(1 / x ^ 2)) := by
  refine
    { errorCoefficient := positiveReciprocalErrorCoefficient a
      errorCoefficient_nonneg :=
        positiveReciprocalErrorCoefficient_nonneg ha
      error_bound := ?_ }
  intro x h hh hx hxh
  have hCnonneg : 0 <= (b - a) / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
  have hxneg := neg_qabs_le_self (x - (a + b) / 2)
  have hxpos := self_le_qabs (x - (a + b) / 2)
  have hxhneg := neg_qabs_le_self (x + h - (a + b) / 2)
  have hxhpos := self_le_qabs (x + h - (a + b) / 2)
  have hxlo : a <= x := by grind
  have hxhi : x <= b := by grind
  have hxhlo : a <= x + h := by grind
  have hxhhi : x + h <= b := by grind
  have hxpositive : 0 < x := by grind
  have hxhpositive : 0 < x + h := by grind
  have hxne : x ≠ 0 := Rat.ne_of_gt hxpositive
  have hxhne : x + h ≠ 0 := Rat.ne_of_gt hxhpositive
  have hdenpos : 0 < x ^ 2 * (x + h) :=
    Rat.mul_pos (Rat.pow_pos hxpositive) hxhpositive
  have hapos : 0 < a ^ 3 := Rat.pow_pos ha
  have hxsq : a ^ 2 <= x ^ 2 := by
    rw [show a ^ 2 = a * a by simp [Rat.pow_succ],
      show x ^ 2 = x * x by simp [Rat.pow_succ]]
    calc
      a * a <= x * a := Rat.mul_le_mul_of_nonneg_right hxlo
        (Rat.le_of_lt ha)
      _ <= x * x := Rat.mul_le_mul_of_nonneg_left hxlo
        (Rat.le_of_lt hxpositive)
  have hdenlower : a ^ 3 <= x ^ 2 * (x + h) := by
    rw [show a ^ 3 = a ^ 2 * a by simp [Rat.pow_succ]]
    calc
      a ^ 2 * a <= x ^ 2 * a := Rat.mul_le_mul_of_nonneg_right hxsq
        (Rat.le_of_lt ha)
      _ <= x ^ 2 * (x + h) := Rat.mul_le_mul_of_nonneg_left hxhlo
        (Rat.le_of_lt (Rat.pow_pos hxpositive))
  have hinvnonneg : 0 <= (x ^ 2 * (x + h))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  have hinvle : (x ^ 2 * (x + h))⁻¹ <= (a ^ 3)⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := x ^ 2 * (x + h))
    · rw [Rat.inv_mul_cancel _ (Rat.ne_of_gt hdenpos)]
      have hainvnonneg : 0 <= (a ^ 3)⁻¹ :=
        Rat.le_of_lt ((Rat.inv_pos).2 hapos)
      have hscaled := Rat.mul_le_mul_of_nonneg_left hdenlower hainvnonneg
      have hacancel : (a ^ 3)⁻¹ * a ^ 3 = 1 :=
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hapos)
      calc
        1 = (a ^ 3)⁻¹ * a ^ 3 := hacancel.symm
        _ <= (a ^ 3)⁻¹ * (x ^ 2 * (x + h)) := hscaled
    · exact hdenpos
  have hrewrite :
      ((1 / (x + h) - 1 / x) / h - -(1 / x ^ 2)) =
        h * (x ^ 2 * (x + h))⁻¹ := by
    rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def,
      Rat.inv_mul_rev]
    have hxinv : x * x⁻¹ = 1 := Rat.mul_inv_cancel x hxne
    have hxinv' : x⁻¹ * x = 1 := Rat.inv_mul_cancel x hxne
    have hxh_inv : (x + h) * (x + h)⁻¹ = 1 :=
      Rat.mul_inv_cancel (x + h) hxhne
    have hxh_inv' : (x + h)⁻¹ * (x + h) = 1 :=
      Rat.inv_mul_cancel (x + h) hxhne
    have h_inv : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hh
    have h_inv' : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hh
    have hx2rewrite : (x ^ 2)⁻¹ = x⁻¹ * x⁻¹ := by
      simp [Rat.pow_succ, Rat.inv_mul_rev]
    rw [hx2rewrite]
    simp only [Rat.one_mul]
    grind [Rat.mul_inv_cancel, Rat.inv_mul_cancel,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul,
      Rat.sub_eq_add_neg]
  rw [hrewrite, qabs_mul, qabs_eq_self_of_nonneg hinvnonneg]
  unfold positiveReciprocalErrorCoefficient
  rw [Rat.div_def, Rat.one_mul]
  exact Rat.mul_le_mul_of_nonneg_left hinvle (qabs_nonneg h)

/-- Full two-sided represented derivative `(1/x)' = -1/x^2` on every
positive rational interval. -/
def positiveReciprocal_hasDerivativeOnInterval
    (a b : Rat) (ha : 0 < a) (hab : a <= b) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat (fun x => 1 / x) a b)
      (FunctionOnInterval.exactRat (fun x => -(1 / x ^ 2)) a b) := by
  let D := positiveReciprocalCenteredSecantBound a b ha hab
  apply D.toHasDerivativeOnInterval a b
  · grind
  · grind

private theorem inv_antitone_of_pos
    {a b : Rat} (ha : 0 < a) (hab : a <= b) : b⁻¹ <= a⁻¹ := by
  have hb : 0 < b := by grind
  apply Rat.le_of_mul_le_mul_right (c := b)
  · rw [Rat.inv_mul_cancel b (Rat.ne_of_gt hb)]
    have hainvnonneg : 0 <= a⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 ha)
    have hscaled := Rat.mul_le_mul_of_nonneg_left hab hainvnonneg
    have hacancel : a⁻¹ * a = 1 :=
      Rat.inv_mul_cancel a (Rat.ne_of_gt ha)
    calc
      1 = a⁻¹ * a := hacancel.symm
      _ <= a⁻¹ * b := hscaled
  · exact hb

theorem positiveReciprocal_value_bound
    {a x : Rat} (ha : 0 < a) (hax : a <= x) :
    qabs (1 / x) <= 1 / a := by
  have hx : 0 < x := by grind
  have hinvnonneg : 0 <= x⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 hx)
  rw [Rat.div_def, Rat.one_mul, qabs_eq_self_of_nonneg hinvnonneg]
  simpa [Rat.div_def, Rat.one_mul] using inv_antitone_of_pos ha hax

theorem positiveReciprocalDerivative_value_bound
    {a x : Rat} (ha : 0 < a) (hax : a <= x) :
    qabs (-(1 / x ^ 2)) <= 1 / a ^ 2 := by
  have hx : 0 < x := by grind
  have hsq : a ^ 2 <= x ^ 2 := by
    rw [show a ^ 2 = a * a by simp [Rat.pow_succ],
      show x ^ 2 = x * x by simp [Rat.pow_succ]]
    calc
      a * a <= x * a := Rat.mul_le_mul_of_nonneg_right hax
        (Rat.le_of_lt ha)
      _ <= x * x := Rat.mul_le_mul_of_nonneg_left hax
        (Rat.le_of_lt hx)
  have hinvnonneg : 0 <= (x ^ 2)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos hx))
  rw [qabs_neg, Rat.div_def, Rat.one_mul,
    qabs_eq_self_of_nonneg hinvnonneg, Rat.div_def, Rat.one_mul]
  exact inv_antitone_of_pos (Rat.pow_pos ha) hsq

/-- The rational physical-time coordinate associated with inverse scale
`q`: `t(q)=1/(4*q^2)`. -/
def inverseSquareTimeOn (a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun q => 1 / (4 * q ^ 2)) a b

/-- Exact derivative target for the inverse-square time coordinate. -/
def inverseSquareTimeDerivativeOn (a b : Rat) : FunctionOnInterval :=
  FunctionOnInterval.exactRat (fun q => -(1 / (2 * q ^ 3))) a b

/-- Quantitative centered secant bound for `t(q)=1/(4*q^2)`, assembled from
the positive reciprocal certificate, its centered product rule, and rational
scaling. -/
def inverseSquareTimeCenteredSecantBound
    (a b : Rat) (ha : 0 < a) (hab : a <= b) :
    CenteredSecantDerivativeBound ((a + b) / 2) ((b - a) / 2)
      (fun q => 1 / (4 * q ^ 2))
      (fun q => -(1 / (2 * q ^ 3))) := by
  let R := positiveReciprocalCenteredSecantBound a b ha hab
  have hC : 0 <= (b - a) / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by grind)
      (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
  have hf0 : 0 <= 1 / a := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 ha))
  have hdf0 : 0 <= 1 / a ^ 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos ha)))
  have hlower : forall q,
      qabs (q - (a + b) / 2) <= (b - a) / 2 -> a <= q := by
    intro q hq
    have hneg := neg_qabs_le_self (q - (a + b) / 2)
    grind
  let P := R.mul R (1 / a) (1 / a ^ 2) (1 / a) (1 / a ^ 2)
    (fun q hq => positiveReciprocal_value_bound ha (hlower q hq))
    (fun q hq => positiveReciprocalDerivative_value_bound ha (hlower q hq))
    (fun q hq => positiveReciprocal_value_bound ha (hlower q hq))
    (fun q hq => positiveReciprocalDerivative_value_bound ha (hlower q hq))
    hC hf0 hdf0 hf0 hdf0
  let S := P.scaleRat (1 / 4)
  have hsource :
      (fun q : Rat => (1 / 4) * ((1 / q) * (1 / q))) =
        (fun q => 1 / (4 * q ^ 2)) := by
    funext q
    simp only [Rat.div_def, Rat.one_mul]
    rw [Rat.inv_mul_rev]
    have hq2 : (q ^ 2)⁻¹ = q⁻¹ * q⁻¹ := by
      simp [Rat.pow_succ, Rat.inv_mul_rev]
    rw [hq2]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hderivative :
      (fun q : Rat => (1 / 4) *
        ((1 / q) * (-(1 / q ^ 2)) +
          (1 / q) * (-(1 / q ^ 2)))) =
        (fun q => -(1 / (2 * q ^ 3))) := by
    funext q
    simp only [Rat.div_def, Rat.one_mul]
    rw [Rat.inv_mul_rev]
    have hq2 : (q ^ 2)⁻¹ = q⁻¹ * q⁻¹ := by
      simp [Rat.pow_succ, Rat.inv_mul_rev]
    have hq3 : (q ^ 3)⁻¹ = q⁻¹ * q⁻¹ * q⁻¹ := by
      simp [Rat.pow_succ, Rat.inv_mul_rev, Rat.mul_assoc]
    rw [hq2, hq3]
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_add, Rat.add_mul]
  rw [hsource, hderivative] at S
  exact S

/-- Full two-sided derivative certificate
`d(1/(4*q^2))/dq = -1/(2*q^3)` on any positive rational scale chart. -/
def inverseSquareTime_hasDerivativeOnInterval
    (a b : Rat) (ha : 0 < a) (hab : a <= b) :
    HasDerivativeOnInterval
      (inverseSquareTimeOn a b) (inverseSquareTimeDerivativeOn a b) := by
  let D := inverseSquareTimeCenteredSecantBound a b ha hab
  simpa [inverseSquareTimeOn, inverseSquareTimeDerivativeOn] using
    D.toHasDerivativeOnInterval a b (by grind) (by grind)

end FinitePolynomial

end ComputableAnalysis
