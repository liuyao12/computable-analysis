import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteExponentialTaylor
import ComputableAnalysis.ExpProofs

/-!
# Finite Gaussian integral prefixes

This is the bounded, finite layer of the Gaussian route.  The integrand is the
even Taylor prefix for `exp (-x^2)`, and each monomial is integrated exactly
over `[-radius,radius]`.  It is not yet an improper integral over the line.
-/

namespace ComputableAnalysis

def gaussianEvenIntegralPrefix (terms : Nat) (radius : Rat) : Rat :=
  (List.range terms).foldl
    (fun acc k =>
      acc + 2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)) 0

theorem gaussianEvenIntegralPrefix_zero (radius : Rat) :
    gaussianEvenIntegralPrefix 0 radius = 0 := by
  rfl

/- The finite Gaussian prefix is integrated term by term.  This recurrence is
   the algebraic interface used by any later tail certificate; it does not
   assert an improper integral or invoke a completed real number. -/
theorem gaussianEvenIntegralPrefix_succ (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius =
      gaussianEvenIntegralPrefix terms radius +
        2 * FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms *
          radius ^ (2 * terms + 1) / ((2 * terms + 1 : Nat) : Rat) := by
  unfold gaussianEvenIntegralPrefix
  rw [List.range_succ]
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem gaussianEvenIntegralPrefix_term_difference (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius -
        gaussianEvenIntegralPrefix terms radius =
      2 * FormalPowerSeries.expCoeff terms * (-1 : Rat) ^ terms *
        radius ^ (2 * terms + 1) / ((2 * terms + 1 : Nat) : Rat) := by
  rw [gaussianEvenIntegralPrefix_succ]
  grind

def gaussianEvenIntegralTerm (k : Nat) (radius : Rat) : Rat :=
  2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
    radius ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)

def gaussianEvenIntegralTailMajorant (radius : Rat) (start : Nat) : Nat → Rat
  | 0 => 0
  | terms + 1 =>
      gaussianEvenIntegralTailMajorant radius start terms +
        qabs (gaussianEvenIntegralTerm (start + terms) radius)

theorem gaussianEvenIntegralPrefix_succ_eq_term (terms : Nat) (radius : Rat) :
    gaussianEvenIntegralPrefix (terms + 1) radius =
      gaussianEvenIntegralPrefix terms radius +
        gaussianEvenIntegralTerm terms radius := by
  rw [gaussianEvenIntegralPrefix_succ]
  rfl

theorem gaussianEvenIntegralPrefix_remainder_abs_le
    (radius : Rat) (start terms : Nat) :
    qabs (gaussianEvenIntegralPrefix (start + terms) radius -
      gaussianEvenIntegralPrefix start radius) <=
      gaussianEvenIntegralTailMajorant radius start terms := by
  induction terms with
  | zero =>
      simp only [gaussianEvenIntegralTailMajorant, Nat.zero_eq, Nat.add_zero,
        Rat.sub_self]
      exact Rat.le_refl
  | succ terms ih =>
      rw [gaussianEvenIntegralTailMajorant]
      have hstep :
          gaussianEvenIntegralPrefix (start + (terms + 1)) radius =
            gaussianEvenIntegralPrefix (start + terms) radius +
              gaussianEvenIntegralTerm (start + terms) radius := by
        have hindex : start + (terms + 1) = (start + terms) + 1 := by omega
        rw [hindex, gaussianEvenIntegralPrefix_succ_eq_term]
      rw [hstep]
      have hrewrite :
          gaussianEvenIntegralPrefix (start + terms) radius +
              gaussianEvenIntegralTerm (start + terms) radius -
            gaussianEvenIntegralPrefix start radius =
            (gaussianEvenIntegralPrefix (start + terms) radius -
              gaussianEvenIntegralPrefix start radius) +
              gaussianEvenIntegralTerm (start + terms) radius := by
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      rw [hrewrite]
      exact Rat.le_trans
        (qabs_add_le _ _)
        (rat_add_le_add ih Rat.le_refl)

/- Package the finite Gaussian prefix together with its explicit rational tail
   allowance.  This is the interval-valued object consumed by later bounded
   or improper Gaussian constructions; no infinite integral is asserted here. -/
def gaussianEvenIntegralPrefix_interval
    (radius : Rat) (start terms : Nat) : QInterval :=
  { lo := gaussianEvenIntegralPrefix start radius -
      gaussianEvenIntegralTailMajorant radius start terms,
    hi := gaussianEvenIntegralPrefix start radius +
      gaussianEvenIntegralTailMajorant radius start terms }

theorem gaussianEvenIntegralPrefix_interval_contains
    (radius : Rat) (start terms : Nat) :
    (gaussianEvenIntegralPrefix_interval radius start terms).lo <=
        gaussianEvenIntegralPrefix (start + terms) radius /\
      gaussianEvenIntegralPrefix (start + terms) radius <=
        (gaussianEvenIntegralPrefix_interval radius start terms).hi := by
  have h := gaussianEvenIntegralPrefix_remainder_abs_le radius start terms
  unfold gaussianEvenIntegralPrefix_interval
  constructor
  · have hneg := neg_qabs_le_self
      (gaussianEvenIntegralPrefix (start + terms) radius -
        gaussianEvenIntegralPrefix start radius)
    have hlow := Rat.le_trans (Rat.neg_le_neg h) hneg
    grind [Rat.sub_eq_add_neg]
  · have hupper := self_le_qabs
      (gaussianEvenIntegralPrefix (start + terms) radius -
        gaussianEvenIntegralPrefix start radius)
    have hupp := Rat.le_trans hupper h
    grind [Rat.sub_eq_add_neg]

theorem gaussianEvenIntegralPrefix_interval_width
    (radius : Rat) (start terms : Nat) :
    (gaussianEvenIntegralPrefix_interval radius start terms).width =
      2 * gaussianEvenIntegralTailMajorant radius start terms := by
  unfold gaussianEvenIntegralPrefix_interval QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem gaussianEvenIntegralPrefix_interval_ordered
    (radius : Rat) (start terms : Nat) :
    (gaussianEvenIntegralPrefix_interval radius start terms).lo <=
      (gaussianEvenIntegralPrefix_interval radius start terms).hi := by
  unfold gaussianEvenIntegralPrefix_interval
  have hnonneg : 0 <= gaussianEvenIntegralTailMajorant radius start terms := by
    induction terms with
    | zero =>
        simp [gaussianEvenIntegralTailMajorant]
    | succ terms ih =>
        rw [gaussianEvenIntegralTailMajorant]
        exact Rat.add_nonneg ih (qabs_nonneg _)
  grind [Rat.sub_eq_add_neg]

theorem gaussianEvenIntegralTailMajorant_mono
    (radius : Rat) (start : Nat) :
    forall terms₁ terms₂,
      terms₁ <= terms₂ ->
        gaussianEvenIntegralTailMajorant radius start terms₁ <=
          gaussianEvenIntegralTailMajorant radius start terms₂ := by
  intro terms₁ terms₂ hterms
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hterms
  induction extra with
  | zero =>
      simp
  | succ extra ih =>
      rw [show terms₁ + (extra + 1) = (terms₁ + extra) + 1 by omega,
        gaussianEvenIntegralTailMajorant]
      calc
        gaussianEvenIntegralTailMajorant radius start terms₁ <=
            gaussianEvenIntegralTailMajorant radius start (terms₁ + extra) :=
              ih (by omega)
        _ <= gaussianEvenIntegralTailMajorant radius start (terms₁ + extra) +
            qabs (gaussianEvenIntegralTerm
              (start + (terms₁ + extra)) radius) := by
          grind [qabs_nonneg]

theorem gaussianEvenIntegralPrefix_interval_contains_future
    (radius : Rat) (start terms₁ terms₂ : Nat) (hterms : terms₁ <= terms₂) :
    (gaussianEvenIntegralPrefix_interval radius start terms₂).ContainsInterval
      (gaussianEvenIntegralPrefix_interval radius start terms₁) := by
  have htail := gaussianEvenIntegralTailMajorant_mono radius start
    terms₁ terms₂ hterms
  unfold gaussianEvenIntegralPrefix_interval QInterval.ContainsInterval
  constructor <;> grind

theorem gaussianEvenIntegralPrefix_stage_four :
    gaussianEvenIntegralPrefix 4 1 = 52 / 35 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_six :
    gaussianEvenIntegralPrefix 6 1 = 31049 / 20790 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_eight :
    gaussianEvenIntegralPrefix 8 1 = 1009219 / 675675 := by
  native_decide

/-! Higher exact checkpoints keep the bounded Gaussian computation auditable
as the factorial prefix is extended. -/
theorem gaussianEvenIntegralPrefix_stage_ten :
    gaussianEvenIntegralPrefix 10 1 = 31293917807 / 20951330400 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_twelve :
    gaussianEvenIntegralPrefix 12 1 =
      15114962544323 / 10119492583200 := by
  native_decide

theorem gaussianEvenIntegralPrefix_stage_twelve_minus_ten :
    gaussianEvenIntegralPrefix 12 1 - gaussianEvenIntegralPrefix 10 1 =
      29 / 1204988400 := by
  rw [gaussianEvenIntegralPrefix_stage_twelve,
    gaussianEvenIntegralPrefix_stage_ten]
  native_decide

/-! A finite tensor-product evaluator for the two-dimensional Gaussian.  Each
factor is a rational Taylor prefix for `exp (-x^2)`; the weighted sum is the
rectangle computation, so no Fubini or measure theorem is involved. -/
def gaussianTaylorPointPrefix (terms : Nat) (x : Rat) : Rat :=
  FinitePolynomial.taylorPrefix FormalPowerSeries.expCoeff terms (-(x * x))

def gaussianTaylorProductIntegralSum (terms : Nat)
    (xs ys : List (Rat × Rat)) : Rat :=
  finiteProductIntegralSum2D xs ys
    (gaussianTaylorPointPrefix terms)
    (gaussianTaylorPointPrefix terms)

theorem gaussianTaylorProductIntegralSum_factorized
    (terms : Nat) (xs ys : List (Rat × Rat)) :
    gaussianTaylorProductIntegralSum terms xs ys =
      (xs.map (fun cell => cell.2 * gaussianTaylorPointPrefix terms cell.1)).foldl
          (fun acc value => acc + value) 0 *
        (ys.map (fun cell => cell.2 * gaussianTaylorPointPrefix terms cell.1)).foldl
          (fun acc value => acc + value) 0 := by
  exact finiteProductIntegralSum2D_factorized xs ys
    (gaussianTaylorPointPrefix terms)
    (gaussianTaylorPointPrefix terms)

/-! A concrete four-cell-per-axis computation over `[-1,1]^2`.  The value is
the exact rational output of the finite evaluator, not the value of an
improper Gaussian integral. -/
theorem gaussianTaylorProductIntegralSum_stage_four_unit_square :
    gaussianTaylorProductIntegralSum 4
      [(-1, 1 / 2), (-1 / 2, 1 / 2), (0, 1 / 2), (1 / 2, 1 / 2)]
      [(-1, 1 / 2), (-1 / 2, 1 / 2), (0, 1 / 2), (1 / 2, 1 / 2)] =
      34225 / 16384 := by
  native_decide

/-! The same construction in three coordinates uses the general nested
rectangle sum.  The factorization is finite algebra, so it is available before
any limiting or measure-theoretic argument. -/
def gaussianTaylorProductIntegralNestedSum3D (terms : Nat)
    (xs ys zs : List (Rat × Rat)) : Rat :=
  finiteProductIntegralNestedSum
    [xs, ys, zs]
    [gaussianTaylorPointPrefix terms,
      gaussianTaylorPointPrefix terms,
      gaussianTaylorPointPrefix terms]

theorem gaussianTaylorProductIntegralNestedSum3D_factorized
    (terms : Nat) (xs ys zs : List (Rat × Rat)) :
    gaussianTaylorProductIntegralNestedSum3D terms xs ys zs =
      (xs.map (fun cell => cell.2 * gaussianTaylorPointPrefix terms cell.1)).foldl
          (fun acc value => acc + value) 0 *
        (ys.map (fun cell => cell.2 * gaussianTaylorPointPrefix terms cell.1)).foldl
          (fun acc value => acc + value) 0 *
        (zs.map (fun cell => cell.2 * gaussianTaylorPointPrefix terms cell.1)).foldl
          (fun acc value => acc + value) 0 := by
  unfold gaussianTaylorProductIntegralNestedSum3D
  rw [finiteProductIntegralNestedSum_factorized]
  rw [finiteProductIntegralSum_eq_factorProduct]
  simp only [finiteProductIntegralFactorProduct, Rat.mul_one]
  grind [Rat.mul_assoc]

theorem gaussianTaylorProductIntegralNestedSum3D_stage_four_unit_cube :
    gaussianTaylorProductIntegralNestedSum3D 4
      [(-1, 1 / 2), (-1 / 2, 1 / 2), (0, 1 / 2), (1 / 2, 1 / 2)]
      [(-1, 1 / 2), (-1 / 2, 1 / 2), (0, 1 / 2), (1 / 2, 1 / 2)]
      [(-1, 1 / 2), (-1 / 2, 1 / 2), (0, 1 / 2), (1 / 2, 1 / 2)] =
      6331625 / 2097152 := by
  native_decide

/-! The same Gaussian rectangle evaluator is available in arbitrary finite
dimension.  The axes are carried as a list rather than being hard-coded to
two or three coordinates; the factor list is generated from that same list,
so the construction cannot silently lose or add a coordinate. -/

def gaussianTaylorProductIntegralNestedSum
    (terms : Nat) (axes : List (List (Rat × Rat))) : Rat :=
  finiteProductIntegralNestedSum axes
    (axes.map (fun _ => gaussianTaylorPointPrefix terms))

theorem gaussianTaylorProductIntegralNestedSum_factorized
    (terms : Nat) (axes : List (List (Rat × Rat))) :
    gaussianTaylorProductIntegralNestedSum terms axes =
      finiteProductIntegralFactorProduct axes
        (axes.map (fun _ => gaussianTaylorPointPrefix terms)) := by
  unfold gaussianTaylorProductIntegralNestedSum
  rw [finiteProductIntegralNestedSum_factorized]
  exact finiteProductIntegralSum_eq_factorProduct axes
    (axes.map (fun _ => gaussianTaylorPointPrefix terms))

theorem gaussianTaylorProductIntegralNestedSum_nonneg
    (terms : Nat) (axes : List (List (Rat × Rat)))
    (hwidth : forall cells, cells ∈ axes ->
      forall cell, cell ∈ cells -> 0 <= cell.2)
    (hfactor : forall x : Rat, 0 <= gaussianTaylorPointPrefix terms x) :
    0 <= gaussianTaylorProductIntegralNestedSum terms axes := by
  unfold gaussianTaylorProductIntegralNestedSum
  apply finiteProductIntegralNestedSum_nonneg axes
    (axes.map (fun _ => gaussianTaylorPointPrefix terms)) hwidth
  intro factor hfactor_mem x
  rcases List.mem_map.1 hfactor_mem with ⟨cells, hcells, rfl⟩
  exact hfactor x

theorem gaussianEvenIntegralPrefix_stage_six_minus_four :
    gaussianEvenIntegralPrefix 6 1 - gaussianEvenIntegralPrefix 4 1 =
      23 / 2970 := by
  rw [gaussianEvenIntegralPrefix_stage_six,
    gaussianEvenIntegralPrefix_stage_four]
  native_decide

theorem gaussianEvenIntegralPrefix_stage_four_nonnegative :
    0 <= gaussianEvenIntegralPrefix 4 1 := by
  rw [gaussianEvenIntegralPrefix_stage_four]
  native_decide

/-! A finite reciprocal-square tail, suitable for transporting a supplied
pointwise Gaussian domination certificate. -/

def reciprocalSquareTailPartial (cutoff : Rat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      reciprocalSquareTailPartial cutoff terms +
        1 / (cutoff + (terms + 1 : Nat)) ^ 2

theorem reciprocalSquareTailPartial_succ (cutoff : Rat) (terms : Nat) :
    reciprocalSquareTailPartial cutoff (terms + 1) =
      reciprocalSquareTailPartial cutoff terms +
        1 / (cutoff + (terms + 1 : Nat)) ^ 2 := by
  rfl

theorem reciprocalSquareTailPartial_nonneg
    (cutoff : Rat) (hcutoff : 0 <= cutoff) :
    forall terms, 0 <= reciprocalSquareTailPartial cutoff terms := by
  intro terms
  induction terms with
  | zero =>
      exact Rat.le_refl
  | succ terms ih =>
      rw [reciprocalSquareTailPartial_succ]
      apply Rat.add_nonneg ih
      have hden : 0 < cutoff + (terms + 1 : Nat) := by
        have hnat : 0 < (terms + 1 : Nat) := by omega
        have hcast : 0 < ((terms + 1 : Nat) : Rat) :=
          (Rat.natCast_pos).2 hnat
        grind
      rw [Rat.div_def]
      exact Rat.mul_nonneg (by native_decide)
        (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos hden)))

theorem reciprocalSquareTailPartial_succ_le
    (cutoff : Rat) (hcutoff : 0 <= cutoff) (terms : Nat) :
    reciprocalSquareTailPartial cutoff terms ≤
      reciprocalSquareTailPartial cutoff (terms + 1) := by
  rw [reciprocalSquareTailPartial_succ]
  have hden : 0 < cutoff + (terms + 1 : Nat) := by
    have hnat : 0 < (terms + 1 : Nat) := by omega
    have hcast : 0 < ((terms + 1 : Nat) : Rat) :=
      (Rat.natCast_pos).2 hnat
    grind
  have hterm : 0 ≤ 1 / (cutoff + (terms + 1 : Nat)) ^ 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.pow_pos hden)))
  grind

theorem reciprocalSquareTailPartial_mono
    (cutoff : Rat) (hcutoff : 0 <= cutoff) :
    forall m n, m ≤ n ->
      reciprocalSquareTailPartial cutoff m ≤
        reciprocalSquareTailPartial cutoff n := by
  intro m n hmn
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Rat.le_refl
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · exact Rat.le_trans (ih hmn')
          (reciprocalSquareTailPartial_succ_le cutoff hcutoff n)
      · have hm : m = n + 1 := by omega
        subst m
        exact Rat.le_refl

theorem reciprocalSquareTailPartial_pos
    (cutoff : Rat) (hcutoff : 0 <= cutoff) (terms : Nat) :
    0 < reciprocalSquareTailPartial cutoff (terms + 1) := by
  rw [reciprocalSquareTailPartial_succ]
  have hprefix := reciprocalSquareTailPartial_nonneg cutoff hcutoff terms
  have hden : 0 < cutoff + (terms + 1 : Nat) := by
    have hnat : 0 < (terms + 1 : Nat) := by omega
    have hcast : 0 < ((terms + 1 : Nat) : Rat) :=
      (Rat.natCast_pos).2 hnat
    grind
  have hterm : 0 < 1 / (cutoff + (terms + 1 : Nat)) ^ 2 := by
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 (Rat.pow_pos hden))
  grind

theorem reciprocalSquareTailPartial_stage_four :
    reciprocalSquareTailPartial 1 4 = 1669 / 3600 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_four_below_one :
    reciprocalSquareTailPartial 1 4 < 1 := by
  rw [reciprocalSquareTailPartial_stage_four]
  native_decide

theorem reciprocalSquareTailPartial_stage_six :
    reciprocalSquareTailPartial 1 6 = 90281 / 176400 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_eight :
    reciprocalSquareTailPartial 1 8 = 3427741 / 6350400 := by
  native_decide

theorem reciprocalSquareTailPartial_stage_eight_below_one :
    reciprocalSquareTailPartial 1 8 < 1 := by
  rw [reciprocalSquareTailPartial_stage_eight]
  native_decide

/-! A concrete pointwise Gaussian tail witness from the project's certified
power-series exponential box. -/

theorem expPowerSeries_neg_four_stage_twenty_upper :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 := by
  native_decide

theorem expPowerSeries_neg_nine_stage_twenty_upper :
    ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 := by
  native_decide

theorem expPowerSeries_neg_sixteen_stage_twenty_upper :
    ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  native_decide

theorem expPowerSeries_neg_twenty_five_stage_twenty_upper :
    ((expPowerSeries (-25 : Rat)).compute 20).hi <= 1 / 25 := by
  native_decide

theorem gaussianTailPointLadder_stage_twenty :
    ((expPowerSeries (-4 : Rat)).compute 20).hi <= 1 / 4 /\
      ((expPowerSeries (-9 : Rat)).compute 20).hi <= 1 / 9 /\
      ((expPowerSeries (-16 : Rat)).compute 20).hi <= 1 / 16 := by
  exact ⟨expPowerSeries_neg_four_stage_twenty_upper,
    expPowerSeries_neg_nine_stage_twenty_upper,
    expPowerSeries_neg_sixteen_stage_twenty_upper⟩

def gaussianTailBoxUpper (x : Rat) (stage : Nat) : Rat :=
  ((expPowerSeries (-(x * x))).compute stage).hi

theorem gaussianTailBoxUpper_stage_twenty_ladder :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_ladder_four :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_ladder_eight :
    gaussianTailBoxUpper 2 20 <= 1 / 4 /\
      gaussianTailBoxUpper 3 20 <= 1 / 9 /\
      gaussianTailBoxUpper 4 20 <= 1 / 16 /\
      gaussianTailBoxUpper 5 20 <= 1 / 25 /\
      gaussianTailBoxUpper 6 100 <= 1 / 36 /\
      gaussianTailBoxUpper 7 100 <= 1 / 49 /\
      gaussianTailBoxUpper 8 100 <= 1 / 64 := by
  native_decide

theorem gaussianTailBoxUpper_stage_twenty_three_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 <= 61 / 144 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder
  grind

theorem gaussianTailBoxUpper_stage_twenty_four_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 <=
      1669 / 3600 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_four
  grind

theorem gaussianTailBoxUpper_stage_twenty_eight_point_sum :
    gaussianTailBoxUpper 2 20 + gaussianTailBoxUpper 3 20 +
        gaussianTailBoxUpper 4 20 + gaussianTailBoxUpper 5 20 +
        gaussianTailBoxUpper 6 100 + gaussianTailBoxUpper 7 100 +
        gaussianTailBoxUpper 8 100 <= 3349341 / 6350400 := by
  have h := gaussianTailBoxUpper_stage_twenty_ladder_eight
  grind

theorem gaussianTailBoxUpper_stage_two_hundred_nine_ten_ladder :
    gaussianTailBoxUpper 9 200 <= 1 / 81 /\
      gaussianTailBoxUpper 10 200 <= 1 / 100 := by
  native_decide

theorem gaussianTailBoxUpper_stage_two_hundred_nine_ten_sum :
    gaussianTailBoxUpper 9 200 + gaussianTailBoxUpper 10 200 <=
      181 / 8100 := by
  have h := gaussianTailBoxUpper_stage_two_hundred_nine_ten_ladder
  grind

end ComputableAnalysis
