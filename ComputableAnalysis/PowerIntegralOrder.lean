import ComputableAnalysis.BinomialPowerOrder
import ComputableAnalysis.IntegralConstantComparison

namespace ComputableAnalysis
open Integral FormalPowerSeries BinomialPower BinomialPower.Global

namespace RealRaw

theorem mul_nonneg_value {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (hx : (ofRat 0).Le X) (hy : (ofRat 0).Le Y) : (ofRat 0).Le (mul X Y) := by
  intro i j
  have point {I : QInterval} (ho : I.lo ≤ I.hi) (hi : 0 ≤ I.hi) :
      ∃ t : Rat, 0 ≤ t ∧ I.lo ≤ t ∧ t ≤ I.hi := by
    by_cases h : 0 ≤ I.lo
    · exact ⟨I.lo,h,Rat.le_refl,ho⟩
    · exact ⟨0,Rat.le_refl,by grind,hi⟩
  obtain ⟨x,hx0,hxl,hxh⟩ := point (interval_order_of_valid _ hX j) (hx 0 j)
  obtain ⟨y,hy0,hyl,hyh⟩ := point (interval_order_of_valid _ hY j) (hy 0 j)
  have h := (QBox.mulRealInterval_contains hxl hxh hyl hyh).2
  exact Rat.le_trans (Rat.mul_nonneg hx0 hy0) h

theorem le_of_sub_nonneg {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (h : (ofRat 0).Le (sub X Y)) : Y.Le X := by
  intro i j
  let n := max i j
  have hh := h 0 n
  have hxi := (hX.2.1 j n (Nat.le_max_right _ _)).2.2
  have hyi := (hY.2.1 i n (Nat.le_max_left _ _)).1
  change 0 ≤ (X.compute n).hi-(Y.compute n).lo at hh
  grind only
end RealRaw

namespace BinomialPower.Global

theorem integral_nonneg (p : Real) {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (RealRaw.ofRat 0).Le (canonicalIntegral p a b ha hab hb) := by
  apply (canonicalIntegral_hasIntegral p ha hab hb).nonneg
  intro x hx n
  change a ≤ x ∧ x ≤ b at hx
  exact canonical_nonneg p (Rat.le_trans ha hx.1) (by grind) 0 n

/-- Nonnegative exponent powers decrease as the binomial coordinate increases. -/
theorem canonical_antitone (p : Real) (hp : (RealRaw.ofRat 2).Le p.preferred)
    {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    (canonicalValue p b).Le (canonicalValue p a) := by
  let q := lowerParameter p
  let I := canonicalIntegral q a b ha hab hb
  let D := RealRaw.sub q.preferred (RealRaw.ofRat 1)
  have hI := canonicalIntegral_hasIntegral q ha hab hb
  have hD := RealRaw.sub_valid q.valid (RealRaw.ofRat_valid 1)
  have hnD : (RealRaw.ofRat 0).Le D := by
    intro i j
    have h := hp i j
    change 2 ≤ (p.compute j).hi at h
    change 0 ≤ ((p.compute j).hi-1)-1
    grind only
  have hnon := RealRaw.mul_nonneg_value hD hI.valid hnD (integral_nonneg q ha hab hb)
  have hclosed := canonicalIntegral_closedForm q ha hab hb
  have hVa := canonicalValue_valid (shiftParameter q) ha (by grind)
  have hVb := canonicalValue_valid (shiftParameter q) (Rat.le_trans ha hab) hb
  have hsub := RealRaw.le_trans (RealRaw.mul_valid hD hI.valid) hnon
    (RealRaw.le_of_equiv (RealRaw.mul_valid hD hI.valid) (RealRaw.sub_valid hVa hVb) hclosed)
  have horder := RealRaw.le_of_sub_nonneg hVa hVb hsub
  have hea := canonicalValue_equiv (shift_lower_equiv p) ha (by grind : a < 1)
  have heb := canonicalValue_equiv (shift_lower_equiv p) (Rat.le_trans ha hab) hb
  have hpa := canonicalValue_valid p ha (by grind)
  have hpb := canonicalValue_valid p (Rat.le_trans ha hab) hb
  exact RealRaw.le_trans hVb (RealRaw.le_of_equiv hpb hVb (RealRaw.equiv_symm heb))
    (RealRaw.le_trans hVa horder (RealRaw.le_of_equiv hVa hpa hea))

end BinomialPower.Global
namespace PowerIntegral

theorem infinityValue_shift (p : Real) {x : Rat} (hx : 1 ≤ x) :
    (canonicalValue (shiftParameter (shiftParameter p)) (1-x⁻¹)).Equiv (infinityValue p x) := by
  have hi := inverse_unit_bounds hx
  have hz0 : 0 ≤ 1-x⁻¹ := by grind
  have hz1 : 1-x⁻¹ < 1 := by grind
  have he1 := canonical_shift (shiftParameter p) hz0 hz1
  have he2 := RealRaw.scaleRat_equiv (r := x⁻¹) (canonical_shift p hz0 hz1)
  have hid : 1-(1-x⁻¹)=x⁻¹ := by grind only
  rw [hid] at he1 he2
  have hv := canonicalValue_valid p hz0 hz1
  have hw := canonicalValue_valid (shiftParameter p) hz0 hz1
  have hz := canonicalValue_valid (shiftParameter (shiftParameter p)) hz0 hz1
  exact RealRaw.equiv_trans hz (RealRaw.scaleRat_valid hw) (infinityValue_valid p hx) he1
    (RealRaw.equiv_trans (RealRaw.scaleRat_valid hw) (RealRaw.scaleRat_valid (RealRaw.scaleRat_valid hv))
      (infinityValue_valid p hx) he2
      (RealRaw.scaleRat_scaleRat_equiv_of_nonneg x⁻¹ x⁻¹ (Rat.le_of_lt hi.1) (Rat.le_of_lt hi.1) _ hv))

theorem infinity_nonneg (p : Real) {x : Rat} (hx : 1 ≤ x) :
    (RealRaw.ofRat 0).Le (infinityValue p x) := by
  have hi := inverse_unit_bounds hx
  intro i j
  have hn := canonical_nonneg p (show 0 ≤ 1-x⁻¹ by grind) (show 1-x⁻¹ < 1 by grind) i j
  have hr := Rat.mul_nonneg (Rat.le_of_lt hi.1) (Rat.le_of_lt hi.1)
  simp only [infinityValue,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
  exact Rat.mul_nonneg hr hn

/-- The monotonicity needed for the integral test is proved for the independent
power evaluator, rather than assumed in its definition. -/
theorem infinity_antitone (p : Real) (hp : (RealRaw.ofRat 0).Le p.preferred)
    {x y : Rat} (hx : 1 ≤ x) (hxy : x ≤ y) :
    (infinityValue p y).Le (infinityValue p x) := by
  let q := shiftParameter (shiftParameter p)
  have hq : (RealRaw.ofRat 2).Le q.preferred := by
    intro i j
    have h := hp i j
    change 0 ≤ (p.compute j).hi at h
    change 2 ≤ ((p.compute j).hi+1)+1
    grind only
  have hxi := inverse_unit_bounds hx
  have hyi := inverse_unit_bounds (Rat.le_trans hx hxy)
  have hg := inverse_gap hx hxy
  have hx0 : 0 ≤ 1-x⁻¹ := by grind
  have hy0 : 0 ≤ 1-y⁻¹ := by grind
  have hx1 : 1-x⁻¹ < 1 := by grind
  have hy1 : 1-y⁻¹ < 1 := by grind
  have horder := canonical_antitone q hq hx0 (show 1-x⁻¹ ≤ 1-y⁻¹ by grind) hy1
  have hvx := canonicalValue_valid q hx0 hx1
  have hvy := canonicalValue_valid q hy0 hy1
  exact RealRaw.le_trans hvy
    (RealRaw.le_of_equiv (infinityValue_valid p (Rat.le_trans hx hxy)) hvy
      (RealRaw.equiv_symm (infinityValue_shift p (Rat.le_trans hx hxy))))
    (RealRaw.le_trans hvx horder (RealRaw.le_of_equiv hvx (infinityValue_valid p hx) (infinityValue_shift p hx)))

theorem infinityCompact_bounds (p : Real) (hp : (RealRaw.ofRat 0).Le p.preferred)
    {a b : Rat} (ha : 1 ≤ a) (hab : a ≤ b) :
    (RealRaw.scaleRat (b-a) (infinityValue p b)).Le (infinityCompact p a b ha hab) ∧
    (infinityCompact p a b ha hab).Le (RealRaw.scaleRat (b-a) (infinityValue p a)) := by
  have hI := infinityCompact_hasIntegral p ha hab
  exact ⟨hI.lower_real hab (fun x hax hxb => infinity_antitone p hp (Rat.le_trans ha hax) hxb),
    hI.upper_real hab (fun x hax _ => infinity_antitone p hp ha hax)⟩

end PowerIntegral
end ComputableAnalysis
