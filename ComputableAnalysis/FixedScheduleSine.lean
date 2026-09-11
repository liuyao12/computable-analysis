import ComputableAnalysis.RotationTaylorBridge

/-!
# A fixed-schedule derivative of the factorial sine evaluator

The derivative reads only sine outputs at x and x plus or minus 1/(n+1),
at prescribed stage n. There is no precision search. A fixed quadratic
correction supplies secant brackets. Cosine occurs in the proof, not in
the algorithm. This is the factorial radian-coordinate representation;
identification with the geometric angle representation is separate.
-/

namespace ComputableAnalysis
namespace FixedSchedule

/-- Finite intersections with no numerical stopping condition. -/
def intersectPrefix (B : Nat -> QInterval) : Nat -> QInterval
  | 0 => B 0
  | n + 1 => QInterval.intersection (intersectPrefix B n) (B (n + 1))

def prefixRaw (B : Nat -> QInterval) : RealRaw where
  compute := intersectPrefix B

theorem prefix_subset_current (B : Nat -> QInterval) (n : Nat) :
    (B n).ContainsInterval (intersectPrefix B n) := by
  cases n with
  | zero => exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ n =>
      change (B (n+1)).lo <= max (intersectPrefix B n).lo (B (n+1)).lo ∧
        min (intersectPrefix B n).hi (B (n+1)).hi <= (B (n+1)).hi
      constructor <;> grind

theorem prefix_contains (B : Nat -> QInterval) (A : RealRaw)
    (hA : A.Valid)
    (hB : ∀ n, (B n).ContainsInterval (A.compute n)) (n : Nat) :
    (intersectPrefix B n).ContainsInterval (A.compute n) := by
  induction n with
  | zero => exact hB 0
  | succ n ih =>
      have hn := hA.2.1 n (n+1) (Nat.le_succ n)
      have hb := hB (n+1)
      change (intersectPrefix B n).lo <= (A.compute n).lo ∧
        (A.compute n).hi <= (intersectPrefix B n).hi at ih
      change (B (n+1)).lo <= (A.compute (n+1)).lo ∧
        (A.compute (n+1)).hi <= (B (n+1)).hi at hb
      change max (intersectPrefix B n).lo (B (n+1)).lo <= (A.compute (n+1)).lo ∧
        (A.compute (n+1)).hi <= min (intersectPrefix B n).hi (B (n+1)).hi
      constructor <;> grind

theorem prefix_nested (B : Nat -> QInterval) {n m : Nat} (hnm : n <= m) :
    (intersectPrefix B n).ContainsInterval (intersectPrefix B m) := by
  induction m with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      exact ⟨Rat.le_refl, Rat.le_refl⟩
  | succ m ih =>
      by_cases heq : n = m+1
      · subst n
        exact ⟨Rat.le_refl, Rat.le_refl⟩
      · have hold := ih (by omega)
        change (intersectPrefix B n).lo <= (intersectPrefix B m).lo ∧
          (intersectPrefix B m).hi <= (intersectPrefix B n).hi at hold
        change (intersectPrefix B n).lo <= max (intersectPrefix B m).lo (B (m+1)).lo ∧
          min (intersectPrefix B m).hi (B (m+1)).hi <= (intersectPrefix B n).hi
        constructor <;> grind

theorem prefix_width_le (B : Nat -> QInterval) (n : Nat) :
    (intersectPrefix B n).width <= (B n).width := by
  have h := prefix_subset_current B n
  unfold QInterval.ContainsInterval QInterval.width at *
  grind

theorem prefix_valid (B : Nat -> QInterval) (A : RealRaw)
    (hA : A.Valid) (hB : ∀ n, (B n).ContainsInterval (A.compute n))
    (hwidth : RealRaw.WidthsShrinkToZero B) : (prefixRaw B).Valid := by
  have hordered (n : Nat) : (intersectPrefix B n).lo <= (intersectPrefix B n).hi := by
    have hc := prefix_contains B A hA hB n
    have ha := RealRaw.interval_order_of_valid A hA n
    unfold QInterval.ContainsInterval at hc
    grind
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <= (intersectPrefix B n).width
    unfold QInterval.width
    have ho := hordered n
    grind
  · intro n m hnm
    have hn := prefix_nested B hnm
    exact ⟨hn.1, hordered m, hn.2⟩
  · intro eps
    obtain ⟨N, hN⟩ := hwidth eps
    exact ⟨N, fun n hn => Rat.le_trans (prefix_width_le B n) (hN n hn)⟩

theorem prefix_equiv (B : Nat -> QInterval) (A : RealRaw)
    (hA : A.Valid) (hB : ∀ n, (B n).ContainsInterval (A.compute n)) :
    (prefixRaw B).Equiv A := by
  intro n
  apply (RealRaw.compareAt_overlap_iff (prefixRaw B) A n n).2
  have hc := prefix_contains B A hA hB n
  have ho := RealRaw.interval_order_of_valid A hA n
  exact ⟨Rat.le_trans hc.1 ho, Rat.le_trans ho hc.2⟩

/-- Bounds are proved about this schedule, not supplied as stopping criteria. -/
def step (n : Nat) : Rat := 1 / ((n+1 : Nat) : Rat)

theorem step_pos (n : Nat) : 0 < step n := by
  unfold step
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos n))

theorem step_le_one (n : Nat) : step n <= 1 := by
  have hp : 0 < ((n+1 : Nat) : Rat) := (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hone : (1 : Rat) <= ((n+1 : Nat) : Rat) := by
    exact_mod_cast (show 1 <= n+1 by omega)
  have hc := Rat.inv_mul_cancel ((n+1 : Nat) : Rat) (Rat.ne_of_gt hp)
  apply Rat.le_of_mul_le_mul_right (c := ((n+1 : Nat) : Rat))
  · unfold step
    simpa only [Rat.div_def, Rat.one_mul, hc] using hone
  · exact hp

open RotationSeries

def sine (x : Rat) : RealRaw := (uniformRotationExpRaw x).imagPart
def cosine (x : Rat) : RealRaw := (uniformRotationExpRaw x).realPart

theorem cosine_valid (x : Rat) (hx : qabs x <= 2) : (cosine x).Valid :=
  ComplexRaw.realPart_valid (uniformRotationExpRaw_valid x hx)

theorem sine_valid (x : Rat) (hx : qabs x <= 2) : (sine x).Valid :=
  ComplexRaw.imagPart_valid (uniformRotationExpRaw_valid x hx)

private theorem radius_nonneg (n : Nat) : 0 <= uniformRotationTailRadius n := by
  unfold uniformRotationTailRadius uniformRotationTailMagnitude
  exact Rat.mul_nonneg (by decide)
    (RationalMajorant.factorialTailTerm_nonneg (by decide) _)

private theorem half_pow_add (m n : Nat) :
    ((1 : Rat)/2)^(m+n) = ((1 : Rat)/2)^m * ((1 : Rat)/2)^n := by
  induction n with
  | zero => simp [Rat.pow_zero, Rat.mul_one]
  | succ n ih =>
      rw [show m+(n+1) = (m+n)+1 by omega, Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc]

/-- The factorial boxes already have more precision than 1/(n+1)^2. -/
theorem radius_le_step_sq (n : Nat) :
    uniformRotationTailRadius n <= step n * step n := by
  have hs : uniformRotationTailStart = 5 := by decide
  have ht : uniformRotationTailTerms n = 10 + 2*n := by
    unfold uniformRotationTailTerms
    rw [hs]
    omega
  have hg := RationalMajorant.factorialTailTerm_le_geometric_from_start
    (C := (2 : Rat)) (N := 10) (by decide) (by native_decide) (2*n)
  have hcoef : 4 * RationalMajorant.factorialTailTerm 2 10 <= 1 := by native_decide
  have hpow0 : 0 <= ((1 : Rat)/2)^(2*n) := Rat.pow_nonneg (by native_decide)
  have hmajor := RationalMajorant.half_pow_le_one_div_succ n
  have hhalf0 : 0 <= ((1 : Rat)/2)^n := Rat.pow_nonneg (by native_decide)
  have hp0 : 0 <= step n := Rat.le_of_lt (step_pos n)
  change ((1 : Rat)/2)^n <= step n at hmajor
  have hsquare : ((1 : Rat)/2)^(2*n) <= step n * step n := by
    rw [show 2*n = n+n by omega, half_pow_add]
    exact Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_right hmajor hhalf0)
      (Rat.mul_le_mul_of_nonneg_left hmajor hp0)
  unfold uniformRotationTailRadius uniformRotationTailMagnitude
  rw [ht]
  calc
    4 * RationalMajorant.factorialTailTerm 2 (10+2*n) <=
        4 * (RationalMajorant.factorialTailTerm 2 10 * ((1 : Rat)/2)^(2*n)) :=
          Rat.mul_le_mul_of_nonneg_left hg (by decide)
    _ = (4 * RationalMajorant.factorialTailTerm 2 10) * ((1 : Rat)/2)^(2*n) := by
      grind [Rat.mul_assoc]
    _ <= 1 * ((1 : Rat)/2)^(2*n) :=
      Rat.mul_le_mul_of_nonneg_right hcoef hpow0
    _ <= step n * step n := by simpa [Rat.one_mul] using hsquare

/-- Secants for sine + 50*x^2, after subtracting 100*x.
Only sine is evaluated; both schedules are fixed in advance. -/
def sineBracket (x : Rat) (n : Nat) : QInterval :=
  let h := step n
  let F := (sine x).compute n
  let L := (sine (x-h)).compute n
  let R := (sine (x+h)).compute n
  { lo := (F.lo-L.hi)/h - 50*h,
    hi := (R.hi-F.lo)/h + 50*h }

def sineDerivative (x : Rat) : RealRaw := prefixRaw (sineBracket x)

private theorem shifted_domain {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    qabs x <= 2 ∧ qabs (x-step n) <= 2 ∧ qabs (x+step n) <= 2 := by
  have hp0 := Rat.le_of_lt (step_pos n)
  have hp1 := step_le_one n
  have habs : qabs (step n) = step n := qabs_eq_self_of_nonneg hp0
  have hm := qabs_sub_le x (step n)
  have ha := qabs_add_le x (step n)
  rw [habs] at hm ha
  exact ⟨by grind, by grind, by grind⟩

private theorem center_secants {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    qabs (((uniformRotationCenter x n).im -
      (uniformRotationCenter (x-step n) n).im)/step n -
      (uniformRotationCenter x n).re) <= 50*step n ∧
    qabs (((uniformRotationCenter (x+step n) n).im -
      (uniformRotationCenter x n).im)/step n -
      (uniformRotationCenter x n).re) <= 50*step n := by
  have hd := shifted_domain hx n
  have hp := step_pos n
  have hne := Rat.ne_of_gt hp
  have habs := qabs_eq_self_of_nonneg (Rat.le_of_lt hp)
  have hcancel : x-step n+step n = x := by grind
  have hback := uniformRotationSinCenter_secant_error_le_thirty_four
    (x := x-step n) (h := step n) hne hd.2.1 (by simpa only [hcancel] using hd.1) n
  have hforward := uniformRotationSinCenter_secant_error_le_thirty_four
    (x := x) (h := step n) hne hd.1 hd.2.2 n
  have hcos := (uniformRotationCenter_input_lipschitz
    (x-step n) x hd.2.1 hd.1 n).1
  rw [hcancel, habs] at hback
  rw [habs] at hforward
  have hdiff : x-step n-x = -(step n) := by grind
  rw [hdiff, qabs_neg, habs] at hcos
  constructor
  · have hid :
      ((uniformRotationCenter x n).im - (uniformRotationCenter (x-step n) n).im)/step n -
        (uniformRotationCenter x n).re =
      (((uniformRotationCenter x n).im - (uniformRotationCenter (x-step n) n).im)/step n -
        (uniformRotationCenter (x-step n) n).re) +
      ((uniformRotationCenter (x-step n) n).re - (uniformRotationCenter x n).re) := by grind
    rw [hid]
    have ht := qabs_add_le
      (((uniformRotationCenter x n).im - (uniformRotationCenter (x-step n) n).im)/step n -
        (uniformRotationCenter (x-step n) n).re)
      ((uniformRotationCenter (x-step n) n).re - (uniformRotationCenter x n).re)
    grind
  · grind

private theorem bracket_arithmetic (a b c d r h : Rat)
    (hr : 0 <= r) (hp : 0 < h) (hsmall : h <= 1)
    (hl : qabs ((b-a)/h-d) <= 50*h)
    (hu : qabs ((c-b)/h-d) <= 50*h) :
    let I : QInterval :=
      { lo := ((b-r)-(a+r))/h - 50*h,
        hi := ((c+r)-(b-r))/h + 50*h }
    I.ContainsInterval { lo := d-r, hi := d+r } ∧
      I.width <= 200*h+4*r/h := by
  have hli := Rat.le_trans (self_le_qabs _) hl
  have hll := Rat.le_trans (Rat.neg_le_neg hl) (neg_qabs_le_self _)
  have hui := Rat.le_trans (self_le_qabs _) hu
  have hul := Rat.le_trans (Rat.neg_le_neg hu) (neg_qabs_le_self _)
  have hc := Rat.inv_mul_cancel h (Rat.ne_of_gt hp)
  have hd : r <= 2*r/h := by
    apply Rat.le_of_mul_le_mul_right (c := h)
    · have hm := Rat.mul_le_mul_of_nonneg_left hsmall hr
      have htwo : r*h <= 2*r := by grind [Rat.mul_one]
      simpa only [Rat.div_def, Rat.mul_assoc, hc, Rat.mul_one] using htwo
    · exact hp
  dsimp only [QInterval.ContainsInterval, QInterval.width]
  simp only [Rat.div_def] at *
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  · grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem sineBracket_contains_cosine {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    (sineBracket x n).ContainsInterval ((cosine x).compute n) := by
  have hs := center_secants hx n
  exact (bracket_arithmetic
    (uniformRotationCenter (x-step n) n).im
    (uniformRotationCenter x n).im
    (uniformRotationCenter (x+step n) n).im
    (uniformRotationCenter x n).re
    (uniformRotationTailRadius n) (step n)
    (radius_nonneg n) (step_pos n) (step_le_one n) hs.1 hs.2).1

theorem sineBracket_width_le {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    (sineBracket x n).width <= 204 / ((n+1 : Nat) : Rat) := by
  have hs := center_secants hx n
  have hw := (bracket_arithmetic
    (uniformRotationCenter (x-step n) n).im
    (uniformRotationCenter x n).im
    (uniformRotationCenter (x+step n) n).im
    (uniformRotationCenter x n).re
    (uniformRotationTailRadius n) (step n)
    (radius_nonneg n) (step_pos n) (step_le_one n) hs.1 hs.2).2
  change (sineBracket x n).width <= 200*step n + 4*uniformRotationTailRadius n/step n at hw
  have hrr := radius_le_step_sq n
  have hi0 : 0 <= (step n)⁻¹ := Rat.le_of_lt ((Rat.inv_pos).2 (step_pos n))
  have hrdiv := Rat.mul_le_mul_of_nonneg_right hrr hi0
  have hc := Rat.mul_inv_cancel (step n) (Rat.ne_of_gt (step_pos n))
  have heq : 204 / ((n+1 : Nat) : Rat) = 204*step n := by
    unfold step
    rw [Rat.div_def, Rat.div_def, Rat.one_mul]
  rw [heq]
  rw [Rat.div_def] at hw
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_one]

theorem sineDerivative_valid {x : Rat} (hx : qabs x <= 1) :
    (sineDerivative x).Valid := by
  apply prefix_valid (sineBracket x) (cosine x)
    (cosine_valid x (by grind)) (sineBracket_contains_cosine hx)
  exact shrinksToZero_of_natOverSuccBound (C := 204) (sineBracket_width_le hx)

theorem sineDerivative_equiv_cosine {x : Rat} (hx : qabs x <= 1) :
    (sineDerivative x).Equiv (cosine x) :=
  prefix_equiv (sineBracket x) (cosine x)
    (cosine_valid x (by grind)) (sineBracket_contains_cosine hx)

theorem sineDerivative_width_le {x : Rat} (hx : qabs x <= 1) (n : Nat) :
    ((sineDerivative x).compute n).width <= 204 / ((n+1 : Nat) : Rat) :=
  Rat.le_trans (prefix_width_le (sineBracket x) n) (sineBracket_width_le hx n)

/-- Literal comparison of rational endpoints at arbitrary stages. -/
theorem sineDerivative_output_overlap {x : Rat} (hx : qabs x <= 1) (n m : Nat) :
    QInterval.Overlaps ((sineDerivative x).compute n) ((cosine x).compute m) :=
  (RealRaw.compareAt_overlap_iff (sineDerivative x) (cosine x) n m).1
    (RealRaw.allStagesOverlap_of_equiv (sineDerivative_valid hx)
      (cosine_valid x (by grind)) (sineDerivative_equiv_cosine hx) n m)

end FixedSchedule
end ComputableAnalysis
