import ComputableAnalysis.FTA.Direction
import ComputableAnalysis.FTA.Inverse

/-! The rational power directions extend to arbitrary represented complex
coefficients. Exact order and finite linear identities do the lifting; no
choice of a rational value equal to an irrational coefficient is made. -/
namespace ComputableAnalysis.RepresentedPolynomial
open ComputableCoefficient

private def scaled (r : Rat) (v : Value) : Value where
  real := Real.ofRaw (RealRaw.scaleRat r v.real.preferred) (RealRaw.scaleRat_valid v.real.valid)
  sample := fun s => r * v.sample s
  observation := v.observation
  encloses := by
    intro n m hnm s hs
    have hv := v.encloses n m hnm s hs
    change (RealRaw.scaleRatCompute r v.real.preferred n).lo ≤ _ ∧
      _ ≤ (RealRaw.scaleRatCompute r v.real.preferred n).hi
    unfold RealRaw.scaleRatCompute
    split
    · exact ⟨Rat.mul_le_mul_of_nonneg_left hv.1 ‹0 ≤ r›, Rat.mul_le_mul_of_nonneg_left hv.2 ‹0 ≤ r›⟩
    · have hr : r < 0 := by grind
      have hl := Rat.mul_le_mul_of_nonneg_left hv.2 (show 0 ≤ -r by grind)
      have hh := Rat.mul_le_mul_of_nonneg_left hv.1 (show 0 ≤ -r by grind)
      constructor <;> dsimp [Real.compute] at * <;> grind

private def linear (x y : Real) (d : QComplex) : Value :=
  Value.add (scaled d.re (.parameter x)) (scaled (-d.im) (.parameter y))

private def Nonnegative (v : Value) : Prop := RealRaw.zero.Le v.real.preferred

private theorem vtrans {a b c : Value}
    (hab : a.real.preferred.Equiv b.real.preferred)
    (hbc : b.real.preferred.Equiv c.real.preferred) :
    a.real.preferred.Equiv c.real.preferred :=
  RealRaw.equiv_trans a.real.valid b.real.valid c.real.valid hab hbc

private theorem veq (a b : Value) (h : ∀ s, a.sample s = b.sample s) :
    a.real.preferred.Equiv b.real.preferred :=
  Value.equiv_of_samples a b 0 (fun _ _ s _ => h s)

private theorem nonnegative_congr {a b : Value}
    (h : a.real.preferred.Equiv b.real.preferred) (ha : Nonnegative a) : Nonnegative b :=
  RealRaw.le_trans a.real.valid ha (RealRaw.le_of_equiv a.real.valid b.real.valid h)

private theorem nonnegative_add {a b : Value} (ha : Nonnegative a) (hb : Nonnegative b) :
    Nonnegative (Value.add a b) := by
  intro n m
  have h1 : 0 ≤ (a.real.compute m).hi := ha 0 m
  have h2 : 0 ≤ (b.real.compute m).hi := hb 0 m
  exact Rat.add_nonneg h1 h2

private theorem nonnegative_scaled_negative {r : Rat} (hr : r < 0) (v : Value)
    (hv : Nonnegative (scaled r v)) : v.real.preferred.Le RealRaw.zero := by
  intro n m
  have hn := hv 0 n
  change 0 ≤ (RealRaw.scaleRatCompute r v.real.preferred n).hi at hn
  unfold RealRaw.scaleRatCompute at hn
  rw [if_neg (show ¬ 0 ≤ r by grind)] at hn
  change 0 ≤ r * (v.real.compute n).lo at hn
  change (v.real.compute n).lo ≤ 0
  by_cases h : (v.real.compute n).lo ≤ 0
  · exact h
  · have hp : 0 < (v.real.compute n).lo := by grind
    have hm := Rat.mul_lt_mul_of_pos_right hr hp
    grind

private theorem nonnegative_scaled_positive {r : Rat} (hr : 0 < r) (v : Value)
    (hv : Nonnegative (scaled r v)) : Nonnegative v := by
  intro n m
  have hm := hv 0 m
  change 0 ≤ (RealRaw.scaleRatCompute r v.real.preferred m).hi at hm
  unfold RealRaw.scaleRatCompute at hm
  rw [if_pos (Rat.le_of_lt hr)] at hm
  change 0 ≤ r * (v.real.compute m).hi at hm
  change 0 ≤ (v.real.compute m).hi
  by_cases h : 0 ≤ (v.real.compute m).hi
  · exact h
  · have hn : (v.real.compute m).hi < 0 := by grind
    have hp := Rat.mul_lt_mul_of_pos_left hn hr
    grind

private theorem linear_sum_conj (x y : Real) (d : QComplex) :
    (Value.add (linear x y d) (linear x y (QComplex.conj d))).real.preferred.Equiv
      (scaled (2*d.re) (.parameter x)).real.preferred := by
  apply veq
  intro s
  change (d.re*s x+(-d.im)*s y)+(d.re*s x+(-(-d.im))*s y)=(2*d.re)*s x
  grind

private theorem linear_first_zero (x y : Real) (hx : x.preferred.Equiv RealRaw.zero) (d : QComplex) :
    (linear x y d).real.preferred.Equiv (scaled (-d.im) (.parameter y)).real.preferred := by
  have hs : (scaled d.re (.parameter x)).real.preferred.Equiv (Value.rational 0).real.preferred := by
    have h1 : (scaled d.re (.parameter x)).real.preferred.Equiv
        (scaled d.re (.rational 0)).real.preferred := RealRaw.scaleRat_equiv hx
    have h2 : (scaled d.re (.rational 0)).real.preferred.Equiv (Value.rational 0).real.preferred := by
      apply veq
      intro s
      change d.re*0=0
      grind
    exact vtrans h1 h2
  have ha : (linear x y d).real.preferred.Equiv
      (Value.add (.rational 0) (scaled (-d.im) (.parameter y))).real.preferred :=
    RealRaw.add_equiv (scaled d.re (.parameter x)).real.valid (Value.rational 0).real.valid
      (scaled (-d.im) (.parameter y)).real.valid (scaled (-d.im) (.parameter y)).real.valid
      hs (RealRaw.equiv_refl _ (scaled (-d.im) (.parameter y)).real.valid)
  exact RealRaw.equiv_trans (linear x y d).real.valid
    (Value.add (.rational 0) (scaled (-d.im) (.parameter y))).real.valid
    (scaled (-d.im) (.parameter y)).real.valid ha
    (RealRaw.zero_add_equiv (scaled (-d.im) (.parameter y)).real.valid)

private theorem linear_product_equiv (c : ComplexCert) (d : QComplex) :
    (linear (realCoordinate c) (imagCoordinate c) d).real.preferred.Equiv
      (mul c (ofQComplex d)).raw.realPart := by
  intro n
  let s : Real → Rat := fun a => (a.compute n).lo
  have hv := (linear (realCoordinate c) (imagCoordinate c) d).encloses n n
    (by simp [linear, scaled, Value.add, Value.parameter]) s (samples_lower n)
  have hp := QBox.mul_contains (QComplex.le_refl (c.raw.compute n).lo)
    (ComplexRaw.valid_ordered c.valid n) (A := c.raw.compute n)
    (B := QBox.point d) (QComplex.le_refl d) (QComplex.le_refl d)
  have he : (linear (realCoordinate c) (imagCoordinate c) d).sample s =
      (QComplex.mul (c.raw.compute n).lo d).re := by
    change d.re*(c.raw.compute n).lo.re+(-d.im)*(c.raw.compute n).lo.im =
      (c.raw.compute n).lo.re*d.re-(c.raw.compute n).lo.im*d.im
    grind
  rw [he] at hv
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨Rat.le_trans hv.1 hp.2.1, Rat.le_trans hp.1.1 hv.2⟩

private theorem qpow_one (k : Nat) : QComplex.pow QComplex.one k = QComplex.one := by
  induction k with
  | zero => rfl
  | succ k ih => rw [QComplex.pow, ih, QComplex.one_mul_cert]

private theorem qpow_conj (d : QComplex) (k : Nat) :
    QComplex.pow (QComplex.conj d) k = QComplex.conj (QComplex.pow d k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [QComplex.pow, ih, QComplex.pow, QComplex.conj_mul]

/-- Every nonzero represented complex coefficient admits a rational negative
power direction. Negativity is exact raw-real strict order, witnessed by a
finite upper endpoint below zero. -/
theorem exists_represented_negative_direction (c : ComplexCert)
    (hc : ¬ c.raw.Equiv zero.raw) (k : Nat) (hk : 0 < k) :
    ∃ d : QComplex, (mul c (ofQComplex (QComplex.pow d k))).raw.realPart.Neg := by
  classical
  apply Classical.byContradiction
  intro hnone
  let x := realCoordinate c
  let y := imagCoordinate c
  have hall : ∀ d : QComplex, Nonnegative (linear x y (QComplex.pow d k)) := by
    intro d
    have hnon : RealRaw.zero.Le (mul c (ofQComplex (QComplex.pow d k))).raw.realPart := by
      intro n m
      change 0 ≤ ((mul c (ofQComplex (QComplex.pow d k))).raw.compute m).hi.re
      by_cases h : 0 ≤ ((mul c (ofQComplex (QComplex.pow d k))).raw.compute m).hi.re
      · exact h
      · exact False.elim (hnone ⟨d, m, by change ((mul c (ofQComplex (QComplex.pow d k))).raw.compute m).hi.re < 0; grind⟩)
    exact RealRaw.le_trans (ComplexRaw.realPart_valid (mul c (ofQComplex (QComplex.pow d k))).valid)
      hnon (RealRaw.le_of_equiv (ComplexRaw.realPart_valid (mul c (ofQComplex (QComplex.pow d k))).valid)
        (linear x y (QComplex.pow d k)).real.valid (RealRaw.equiv_symm (linear_product_equiv c _)))
  have hx : Nonnegative (.parameter x) := by
    have h := hall QComplex.one
    rw [qpow_one] at h
    apply nonnegative_congr (a := linear x y QComplex.one) ?_ h
    apply veq
    intro s
    change 1*s x+(-0)*s y=s x
    grind
  obtain ⟨d, hd⟩ := PolynomialDirection.exists_power_negative_real k hk
  have hsum := nonnegative_add (hall d) (hall (QComplex.conj d))
  rw [qpow_conj] at hsum
  have hscaled := nonnegative_congr (linear_sum_conj x y (QComplex.pow d k)) hsum
  have hxle := nonnegative_scaled_negative (show 2*(QComplex.pow d k).re < 0 by grind) (.parameter x) hscaled
  have hx0 : x.preferred.Equiv RealRaw.zero := RealRaw.equiv_of_le_of_ge hxle hx
  let e : QComplex := { re := 1, im := PolynomialDirection.smallStep k }
  have he : 0 < (QComplex.pow e k).im := PolynomialDirection.smallStep_power_im_pos k hk
  have hyneg := nonnegative_congr (linear_first_zero x y hx0 (QComplex.pow e k)) (hall e)
  have hyle := nonnegative_scaled_negative (show -(QComplex.pow e k).im < 0 by grind) (.parameter y) hyneg
  have hconj := hall (QComplex.conj e)
  rw [qpow_conj] at hconj
  have hypos := nonnegative_congr (linear_first_zero x y hx0 (QComplex.conj (QComplex.pow e k))) hconj
  have hy : Nonnegative (.parameter y) :=
    nonnegative_scaled_positive (show 0 < -(QComplex.conj (QComplex.pow e k)).im by change 0 < -(-(QComplex.pow e k).im); grind)
      (.parameter y) hypos
  have hy0 : y.preferred.Equiv RealRaw.zero := RealRaw.equiv_of_le_of_ge hyle hy
  apply hc
  intro n
  have hxr := (RealRaw.compareAt_overlap_iff _ _ n n).1 (hx0 n)
  have hyr := (RealRaw.compareAt_overlap_iff _ _ n n).1 (hy0 n)
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  exact ⟨⟨hxr.1, hyr.1⟩, ⟨hxr.2, hyr.2⟩⟩

end ComputableAnalysis.RepresentedPolynomial
