import ComputableAnalysis.FiniteNBallVolume
import ComputableAnalysis.FiniteExponentialTaylor
import ComputableAnalysis.ExpProofs
import ComputableAnalysis.Series

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

/- The alternating-series adapter is the point where a bounded Gaussian
   computation becomes a `RealRaw`.  The two analytic obligations are kept
   explicit: monotonicity of the integrated term magnitudes and their
   potential-infinity modulus. -/
def gaussianEvenIntegralAlternatingRaw (radius : Rat)
    (hdecreasing : forall k, qabs (gaussianEvenIntegralTerm (k + 1) radius) <=
      qabs (gaussianEvenIntegralTerm k radius))
    (hshrinks : ShrinksToZero
      (fun k => qabs (gaussianEvenIntegralTerm k radius))) :
    Series.AlternatingRaw where
  term := fun k => qabs (gaussianEvenIntegralTerm k radius)
  term_nonneg := fun k => qabs_nonneg _
  term_decreasing := hdecreasing
  term_shrinks := hshrinks

theorem gaussianEvenIntegralAlternatingRaw_valid (radius : Rat)
    (hdecreasing : forall k, qabs (gaussianEvenIntegralTerm (k + 1) radius) <=
      qabs (gaussianEvenIntegralTerm k radius))
    (hshrinks : ShrinksToZero
      (fun k => qabs (gaussianEvenIntegralTerm k radius))) :
    (gaussianEvenIntegralAlternatingRaw radius hdecreasing hshrinks).toRealRaw.Valid := by
  exact (gaussianEvenIntegralAlternatingRaw radius hdecreasing hshrinks).toRealRaw_valid

/- The extra factor in a Gaussian integral term is controlled by the same
   factorial majorant as the exponential series.  Keeping the radius and its
   square bound explicit makes this usable for bounded, finite-stage Gaussian
   convergence without introducing an improper integral. -/
theorem gaussianEvenIntegralTerm_abs_le_factorialTailTerm
    {C radius : Rat} (hr : 0 <= radius) (hC : 0 <= C)
    (hR : radius * radius <= C) (k : Nat) :
    qabs (gaussianEvenIntegralTerm k radius) <=
      2 * radius * RationalMajorant.factorialTailTerm C k := by
  have hden : 1 <= ((2 * k + 1 : Nat) : Rat) := by
    have hk : (0 : Rat) <= (k : Rat) := Rat.natCast_nonneg
    grind
  unfold gaussianEvenIntegralTerm
  rw [Rat.div_def, qabs_mul]
  have hdenpos : 0 < ((2 * k + 1 : Nat) : Rat) := by
    grind
  have hinv0 : 0 <= (((2 * k + 1 : Nat) : Rat)⁻¹) :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdenpos)
  rw [qabs_eq_self_of_nonneg hinv0]
  have hnumer :
      qabs (2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1)) <=
        2 * radius * RationalMajorant.factorialTailTerm C k := by
    rw [qabs_mul, qabs_mul, qabs_mul,
      qabs_eq_self_of_nonneg (by native_decide : (0 : Rat) <= 2)]
    have hsign : qabs ((-1 : Rat) ^ k) = 1 := by
      rw [RationalMajorant.qabs_pow_eq_pow_qabs]
      have hone : qabs (-1 : Rat) = 1 := by native_decide
      rw [hone]
      let rec honepow : ∀ n : Nat, (1 : Rat) ^ n = 1
        | 0 => by native_decide
        | n + 1 => by
            rw [Rat.pow_succ, honepow n]
            native_decide
      exact honepow k
    rw [hsign]
    simp only [Rat.mul_one, RationalMajorant.qabs_pow_eq_pow_qabs]
    have hrabs : qabs radius = radius := qabs_eq_self_of_nonneg hr
    rw [hrabs]
    let rec hpow_even : ∀ n : Nat, radius ^ (2 * n) = (radius * radius) ^ n
      | 0 => by simp [Rat.pow_zero]
      | n + 1 => by
          rw [show 2 * (n + 1) = (2 * n) + 2 by omega,
            Rat.pow_succ, Rat.pow_succ, hpow_even n]
          grind [Rat.mul_assoc, Rat.mul_comm]
    rw [show 2 * k + 1 = (2 * k) + 1 by rfl, Rat.pow_succ, hpow_even]
    have hRabs : qabs (radius * radius) <= C := by
      calc
        qabs (radius * radius) = radius * radius := by
          rw [qabs_mul]
          rw [qabs_eq_self_of_nonneg hr]
        _ <= C := hR
    have hpow : (radius * radius) ^ k <= C ^ k := by
      have := RationalMajorant.qabs_pow_le_pow hC hRabs k
      rw [RationalMajorant.qabs_pow_eq_pow_qabs] at this
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hr hr)] at this
      exact this
    have hcoef : 0 <= FormalPowerSeries.expCoeff k := by
      unfold FormalPowerSeries.expCoeff
      rw [Rat.div_def, Rat.one_mul]
      exact Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos k))
    have hterm :
        FormalPowerSeries.expCoeff k * (radius * radius) ^ k <=
          RationalMajorant.factorialTailTerm C k := by
      calc
        FormalPowerSeries.expCoeff k * (radius * radius) ^ k <=
            FormalPowerSeries.expCoeff k * C ^ k :=
          Rat.mul_le_mul_of_nonneg_left hpow hcoef
        _ = RationalMajorant.factorialTailTerm C k := by
          unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
    have hcoefabs : qabs (FormalPowerSeries.expCoeff k) =
        FormalPowerSeries.expCoeff k := qabs_eq_self_of_nonneg hcoef
    calc
      2 * qabs (FormalPowerSeries.expCoeff k) *
          ((radius * radius) ^ k * radius) =
          2 * radius * (FormalPowerSeries.expCoeff k *
            (radius * radius) ^ k) := by
            rw [hcoefabs]
            grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= 2 * radius * RationalMajorant.factorialTailTerm C k :=
        Rat.mul_le_mul_of_nonneg_left hterm
          (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hr)
  have htarget : 0 <=
      2 * radius * RationalMajorant.factorialTailTerm C k := by
    exact Rat.mul_nonneg (Rat.mul_nonneg (by native_decide) hr)
      (RationalMajorant.factorialTailTerm_nonneg hC k)
  have hscaled :
      qabs (2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1)) <=
        (2 * radius * RationalMajorant.factorialTailTerm C k) *
          ((2 * k + 1 : Nat) : Rat) := by
    have hmul := Rat.mul_le_mul_of_nonneg_right hden htarget
    calc
      qabs (2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
          radius ^ (2 * k + 1)) <=
          2 * radius * RationalMajorant.factorialTailTerm C k := hnumer
      _ <= (2 * radius * RationalMajorant.factorialTailTerm C k) *
          ((2 * k + 1 : Nat) : Rat) := by
        simpa [Rat.mul_comm] using hmul
  have hmul := Rat.mul_le_mul_of_nonneg_right hscaled hinv0
  calc
    qabs (2 * FormalPowerSeries.expCoeff k * (-1 : Rat) ^ k *
        radius ^ (2 * k + 1)) * ((2 * k + 1 : Nat) : Rat)⁻¹ <=
        (2 * radius * RationalMajorant.factorialTailTerm C k) *
          ((2 * k + 1 : Nat) : Rat) * ((2 * k + 1 : Nat) : Rat)⁻¹ := hmul
    _ = 2 * radius * RationalMajorant.factorialTailTerm C k := by
      rw [Rat.mul_assoc, Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)]
      simp

/- For nonnegative radius, the absolute integrated term has the expected
   factorial form.  This equality exposes the ratio used by the alternating
   series certificate, rather than hiding it in an inequality. -/
theorem gaussianEvenIntegralTerm_abs_eq_scaled_factorialTailTerm
    {radius : Rat} (hr : 0 <= radius) (k : Nat) :
    qabs (gaussianEvenIntegralTerm k radius) =
      2 * radius * RationalMajorant.factorialTailTerm (radius * radius) k /
        ((2 * k + 1 : Nat) : Rat) := by
  have hdenpos : 0 < ((2 * k + 1 : Nat) : Rat) := by grind
  have hcoef : 0 <= FormalPowerSeries.expCoeff k := by
    unfold FormalPowerSeries.expCoeff
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt ((Rat.inv_pos).2 (RationalMajorant.factorialRat_pos k))
  have hsign : qabs ((-1 : Rat) ^ k) = 1 := by
    rw [RationalMajorant.qabs_pow_eq_pow_qabs]
    have hone : qabs (-1 : Rat) = 1 := by native_decide
    rw [hone]
    let rec honepow : ∀ n : Nat, (1 : Rat) ^ n = 1
      | 0 => by native_decide
      | n + 1 => by
          rw [Rat.pow_succ, honepow n]
          native_decide
    exact honepow k
  let rec hpow_even : ∀ n : Nat, radius ^ (2 * n) = (radius * radius) ^ n
    | 0 => by simp [Rat.pow_zero]
    | n + 1 => by
        rw [show 2 * (n + 1) = (2 * n) + 2 by omega,
          Rat.pow_succ, Rat.pow_succ, hpow_even n, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  unfold gaussianEvenIntegralTerm
  rw [Rat.div_def, qabs_mul, qabs_mul, qabs_mul, qabs_mul,
    qabs_eq_self_of_nonneg (by native_decide : (0 : Rat) <= 2), hsign]
  rw [Rat.mul_one, RationalMajorant.qabs_pow_eq_pow_qabs,
    qabs_eq_self_of_nonneg hr]
  rw [show 2 * k + 1 = (2 * k) + 1 by rfl, Rat.pow_succ, hpow_even k]
  have hdeninv : qabs (((2 * k + 1 : Nat) : Rat)⁻¹) =
      ((2 * k + 1 : Nat) : Rat)⁻¹ :=
    qabs_eq_self_of_nonneg (Rat.le_of_lt ((Rat.inv_pos).2 hdenpos))
  have hcoefabs : qabs (FormalPowerSeries.expCoeff k) =
      FormalPowerSeries.expCoeff k := qabs_eq_self_of_nonneg hcoef
  rw [hdeninv]
  rw [hcoefabs]
  unfold FormalPowerSeries.expCoeff RationalMajorant.factorialTailTerm
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianEvenIntegralTerm_abs_decreasing
    {radius : Rat} (hr : 0 <= radius) (hradiusSq : radius * radius <= 1)
    (k : Nat) :
    qabs (gaussianEvenIntegralTerm (k + 1) radius) <=
      qabs (gaussianEvenIntegralTerm k radius) := by
  rw [gaussianEvenIntegralTerm_abs_eq_scaled_factorialTailTerm hr,
    gaussianEvenIntegralTerm_abs_eq_scaled_factorialTailTerm hr,
    RationalMajorant.factorialTailTerm_succ]
  let C : Rat := radius * radius
  let T : Rat := RationalMajorant.factorialTailTerm C k
  let d₁ : Rat := ((2 * k + 1 : Nat) : Rat)
  let d₂ : Rat := ((2 * (k + 1) + 1 : Nat) : Rat)
  have hC : 0 <= C := by
    dsimp [C]
    exact Rat.mul_nonneg hr hr
  have hT : 0 <= T := by
    dsimp [T]
    exact RationalMajorant.factorialTailTerm_nonneg hC k
  have hscale : 0 <= 2 * radius :=
    Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hr
  have hd₁ : 0 < d₁ := by
    dsimp [d₁]
    exact (Rat.natCast_pos).2 (by omega)
  have hd₂ : 0 < d₂ := by
    dsimp [d₂]
    exact (Rat.natCast_pos).2 (by omega)
  have hratio : C / ((k + 1 : Nat) : Rat) <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := ((k + 1 : Nat) : Rat))
    · rw [Rat.div_def, Rat.mul_assoc,
        Rat.inv_mul_cancel _ (Rat.ne_of_gt (by exact_mod_cast (Nat.succ_pos k)))]
      calc
        C * 1 = C := by simp
        _ <= 1 := by simpa [C] using hradiusSq
        _ <= ((k + 1 : Nat) : Rat) := by exact_mod_cast (by omega)
        _ = 1 * ((k + 1 : Nat) : Rat) := by simp
    · exact (Rat.natCast_pos).2 (Nat.succ_pos k)
  have hden : d₂⁻¹ <= d₁⁻¹ := by
    apply Rat.le_of_mul_le_mul_right (c := d₁ * d₂)
    · calc
        d₂⁻¹ * (d₁ * d₂) = d₁ := by
          rw [show d₂⁻¹ * (d₁ * d₂) = d₁ * (d₂⁻¹ * d₂) by
            grind [Rat.mul_assoc, Rat.mul_comm]]
          rw [Rat.inv_mul_cancel d₂ (Rat.ne_of_gt hd₂)]
          simp
        _ <= d₂ := by
          dsimp [d₁, d₂]
          exact_mod_cast (by omega)
        _ = d₁⁻¹ * (d₁ * d₂) := by
          rw [show d₁⁻¹ * (d₁ * d₂) = d₂ * (d₁⁻¹ * d₁) by
            grind [Rat.mul_assoc, Rat.mul_comm]]
          rw [Rat.inv_mul_cancel d₁ (Rat.ne_of_gt hd₁)]
          simp
    · exact Rat.mul_pos hd₁ hd₂
  have hfirst : T * (C / ((k + 1 : Nat) : Rat)) <= T := by
    calc
      T * (C / ((k + 1 : Nat) : Rat)) <= T * 1 :=
        Rat.mul_le_mul_of_nonneg_left hratio hT
      _ = T := by simp
  have hsecond : 2 * radius * T / d₂ <= 2 * radius * T / d₁ := by
    rw [Rat.div_def, Rat.div_def]
    exact Rat.mul_le_mul_of_nonneg_left hden
      (Rat.mul_nonneg hscale hT)
  calc
    2 * radius * (T * (C / ((k + 1 : Nat) : Rat))) / d₂ <=
        2 * radius * T / d₂ := by
      rw [Rat.div_def, Rat.div_def]
      apply Rat.mul_le_mul_of_nonneg_right
      · exact Rat.mul_le_mul_of_nonneg_left hfirst hscale
      · exact Rat.le_of_lt ((Rat.inv_pos).2 hd₂)
    _ <= 2 * radius * T / d₁ := hsecond

theorem gaussianEvenIntegralTerm_abs_shrinks_unit_radius
    {radius : Rat} (hr : 0 <= radius) (hradius : radius <= 1)
    (hradiusSq : radius * radius <= 1) :
    ShrinksToZero (fun k => qabs (gaussianEvenIntegralTerm k radius)) := by
  intro eps
  let C : Rat := radius * radius
  let start : Nat := RationalMajorant.factorialTailStart C
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
  let shift : Nat := RationalMajorant.halfDecayShift
    (2 * RationalMajorant.factorialTailTerm C start) half
  refine ⟨start + shift, ?_⟩
  intro k hk
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
  have hC : 0 <= C := by
    dsimp [C]
    exact Rat.mul_nonneg hr hr
  have hstart := RationalMajorant.factorialTailStart_satisfies C
  have hgeom := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC hstart (shift + d)
  have hpow : ((1 : Rat) / 2) ^ (shift + d) <=
      ((1 : Rat) / 2) ^ shift :=
    Series.halfPow_add_le_left shift d
  have hbound : RationalMajorant.factorialTailTerm C start *
      ((1 : Rat) / 2) ^ shift <= half.val := by
    have hspec := RationalMajorant.halfDecayShift_spec
      (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2)
        (RationalMajorant.factorialTailTerm_nonneg hC start)) half
    have hsmall : RationalMajorant.factorialTailTerm C start *
        ((1 : Rat) / 2) ^ shift <=
        2 * RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ shift := by
      exact Rat.mul_le_mul_of_nonneg_right
        (by grind [RationalMajorant.factorialTailTerm_nonneg hC start])
        (Rat.pow_nonneg (by native_decide))
    exact Rat.le_trans hsmall (by simpa [shift] using hspec)
  have hterm : RationalMajorant.factorialTailTerm C (start + shift + d) <=
      half.val := by
    calc
      RationalMajorant.factorialTailTerm C (start + shift + d) <=
          RationalMajorant.factorialTailTerm C start *
            ((1 : Rat) / 2) ^ (shift + d) := by
        simpa [Nat.add_assoc] using hgeom
      _ <= RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ shift := by
        exact Rat.mul_le_mul_of_nonneg_left hpow
          (RationalMajorant.factorialTailTerm_nonneg hC start)
      _ <= half.val := hbound
  have hterm' : qabs (gaussianEvenIntegralTerm k radius) <= eps.val := by
    rw [gaussianEvenIntegralTerm_abs_eq_scaled_factorialTailTerm hr]
    have hden : 0 <= ((2 * k + 1 : Nat) : Rat)⁻¹ := by
      exact Rat.le_of_lt ((Rat.inv_pos).2 (by grind))
    have hCk : 0 <= RationalMajorant.factorialTailTerm C k :=
      RationalMajorant.factorialTailTerm_nonneg hC k
    have hfactorial_k : RationalMajorant.factorialTailTerm C k <= half.val := by
      simpa [C, start, shift, hd, Nat.add_assoc] using hterm
    have hscaled := Rat.mul_le_mul_of_nonneg_left hfactorial_k
      (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hr)
    have hrad := Rat.mul_le_mul_of_nonneg_left hradius
      (RationalMajorant.factorialTailTerm_nonneg hC k)
    have hfinal : 2 * radius *
        RationalMajorant.factorialTailTerm C k <=
        2 * RationalMajorant.factorialTailTerm C k := by
      have htwo := Rat.mul_le_mul_of_nonneg_left hrad
        (by native_decide : (0 : Rat) <= 2)
      have htwo' : 2 * (radius *
          RationalMajorant.factorialTailTerm C k) <=
          2 * RationalMajorant.factorialTailTerm C k := by
        calc
          2 * (radius * RationalMajorant.factorialTailTerm C k) =
              2 * (RationalMajorant.factorialTailTerm C k * radius) := by
                grind [Rat.mul_comm]
          _ <= 2 * (RationalMajorant.factorialTailTerm C k * 1) := htwo
          _ = 2 * RationalMajorant.factorialTailTerm C k := by simp
      calc
        2 * radius * RationalMajorant.factorialTailTerm C k =
            radius * (2 * RationalMajorant.factorialTailTerm C k) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ = 2 * (radius * RationalMajorant.factorialTailTerm C k) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= 2 * RationalMajorant.factorialTailTerm C k := htwo'
    have hdenle : 2 * radius *
        RationalMajorant.factorialTailTerm C k /
          ((2 * k + 1 : Nat) : Rat) <=
        2 * radius * RationalMajorant.factorialTailTerm C k := by
      have hX : 0 <= 2 * radius *
          RationalMajorant.factorialTailTerm C k :=
        Rat.mul_nonneg
          (Rat.mul_nonneg (by native_decide : (0 : Rat) <= 2) hr) hCk
      have hdge : 1 <= ((2 * k + 1 : Nat) : Rat) := by grind
      apply Rat.le_of_mul_le_mul_right
        (c := ((2 * k + 1 : Nat) : Rat))
      · rw [Rat.div_def, Rat.mul_assoc,
          Rat.inv_mul_cancel _ (Rat.ne_of_gt (by grind)), Rat.mul_one]
        simpa using Rat.mul_le_mul_of_nonneg_left hdge hX
      · exact (Rat.natCast_pos).2 (by omega)
    have hhalf : 2 * half.val = eps.val := by
      dsimp [half]
      rw [Rat.div_def]
      grind
    have hscaled2 := Rat.mul_le_mul_of_nonneg_left hfactorial_k
      (by native_decide : (0 : Rat) <= 2)
    rw [hhalf] at hscaled2
    exact Rat.le_trans hdenle (Rat.le_trans hfinal hscaled2)
  exact hterm'

/- The bounded Gaussian is now a certified alternating `RealRaw`: all proof
   obligations are discharged by the preceding rational ratio and factorial
   modulus lemmas. -/
def gaussianEvenIntegralUnitRadiusAlternatingRaw
    {radius : Rat} (hr : 0 <= radius) (hradius : radius <= 1)
    (hradiusSq : radius * radius <= 1) : Series.AlternatingRaw :=
  gaussianEvenIntegralAlternatingRaw radius
    (fun k => gaussianEvenIntegralTerm_abs_decreasing hr hradiusSq k)
    (gaussianEvenIntegralTerm_abs_shrinks_unit_radius hr hradius hradiusSq)

theorem gaussianEvenIntegralUnitRadiusAlternatingRaw_valid
    {radius : Rat} (hr : 0 <= radius) (hradius : radius <= 1)
    (hradiusSq : radius * radius <= 1) :
    (gaussianEvenIntegralUnitRadiusAlternatingRaw hr hradius hradiusSq).toRealRaw.Valid := by
  exact (gaussianEvenIntegralUnitRadiusAlternatingRaw hr hradius hradiusSq).toRealRaw_valid

def gaussianEvenIntegralTailMajorant (radius : Rat) (start : Nat) : Nat → Rat
  | 0 => 0
  | terms + 1 =>
      gaussianEvenIntegralTailMajorant radius start terms +
        qabs (gaussianEvenIntegralTerm (start + terms) radius)

/- The whole finite Gaussian tail is bounded by the corresponding finite
   factorial majorant.  This is the finite-stage bridge from the integrated
   even exponential series to the existing computable tail machinery. -/
theorem gaussianEvenIntegralTailMajorant_le_factorialTailPartial
    {C radius : Rat} (hr : 0 <= radius) (hC : 0 <= C)
    (hR : radius * radius <= C) (start terms : Nat) :
    gaussianEvenIntegralTailMajorant radius start terms <=
      2 * radius * RationalMajorant.factorialTailPartial C start terms := by
  induction terms with
  | zero =>
      simp [gaussianEvenIntegralTailMajorant,
        RationalMajorant.factorialTailPartial]
  | succ terms ih =>
      rw [gaussianEvenIntegralTailMajorant,
        RationalMajorant.factorialTailPartial]
      have hterm := gaussianEvenIntegralTerm_abs_le_factorialTailTerm
        (C := C) (radius := radius) hr hC hR (start + terms)
      have hadd := rat_add_le_add ih hterm
      simpa [Rat.mul_add, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm,
        Nat.add_comm] using hadd

/- On the unit radius range, halve the requested budget before calling the
   factorial modulus; the integrated Gaussian's factor `2 * radius` then fits
   inside the original epsilon. -/
def gaussianEvenIntegralUnitRadiusStage (eps : QPos) : Nat :=
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
  RationalMajorant.factorialTailStart 1 +
    RationalMajorant.halfDecayShift
      (2 * RationalMajorant.factorialTailTerm 1
        (RationalMajorant.factorialTailStart 1)) half

theorem gaussianEvenIntegralTailMajorant_unit_radius_le_eps
    {radius : Rat} (hr : 0 <= radius) (hradius : radius <= 1)
    (hradiusSq : radius * radius <= 1)
    (eps : QPos) (terms : Nat) :
    gaussianEvenIntegralTailMajorant radius
      (gaussianEvenIntegralUnitRadiusStage eps) terms <= eps.val := by
  let half : QPos := ⟨eps.val / 2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property
      ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
  let start : Nat := RationalMajorant.factorialTailStart 1 +
    RationalMajorant.halfDecayShift
      (2 * RationalMajorant.factorialTailTerm 1
        (RationalMajorant.factorialTailStart 1)) half
  have hbound := gaussianEvenIntegralTailMajorant_le_factorialTailPartial
    (C := 1) (radius := radius) hr (by native_decide) hradiusSq start terms
  have hpartial : 0 <= RationalMajorant.factorialTailPartial 1 start terms := by
    have hmono := RationalMajorant.factorialTailPartial_mono
      (C := 1) (N := start) (by native_decide) 0 terms (Nat.zero_le terms)
    simpa [RationalMajorant.factorialTailPartial] using hmono
  have hscaled : 2 * radius *
      RationalMajorant.factorialTailPartial 1 start terms <=
      2 * RationalMajorant.factorialTailPartial 1 start terms := by
    have hrad := Rat.mul_le_mul_of_nonneg_right hradius hpartial
    have htwo := Rat.mul_le_mul_of_nonneg_left hrad (by native_decide : (0 : Rat) <= 2)
    simpa [Rat.mul_assoc] using htwo
  have hfactorial := RationalMajorant.factorialTailPartial_shifted_le_eps
    (C := 1) (by native_decide) half terms
  have hfactorialScaled := Rat.mul_le_mul_of_nonneg_left hfactorial
    (by native_decide : (0 : Rat) <= 2)
  have hhalf : 2 * half.val = eps.val := by
    dsimp [half]
    rw [Rat.div_def]
    grind
  dsimp [start] at hbound ⊢
  rw [hhalf] at hfactorialScaled
  exact Rat.le_trans (Rat.le_trans hbound hscaled) hfactorialScaled

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

theorem reciprocalSquareTerm_le_telescopeStep
    {cutoff : Rat} (hcutoff : 0 < cutoff) (n : Nat) :
    1 / (cutoff + (n + 1 : Nat)) ^ 2 <=
      1 / (cutoff + (n : Nat)) -
        1 / (cutoff + (n + 1 : Nat)) := by
  let M : Rat := cutoff + (n : Nat)
  let S : Rat := cutoff + (n + 1 : Nat)
  have hMpos : 0 < M := by
    dsimp [M]
    have hn : 0 <= ((n : Nat) : Rat) := Rat.natCast_nonneg
    grind
  have hSpos : 0 < S := by
    dsimp [S]
    have hn : 0 <= ((n + 1 : Nat) : Rat) := Rat.natCast_nonneg
    grind
  have hMne : M ≠ 0 := Rat.ne_of_gt hMpos
  have hSne : S ≠ 0 := Rat.ne_of_gt hSpos
  have hSSne : S * S ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hSpos hSpos)
  have hMS : M <= S := by
    dsimp [M, S]
    have hn : (n : Rat) <= (n + 1 : Rat) := by exact_mod_cast (Nat.le_succ n)
    grind
  apply Rat.le_of_mul_le_mul_right (c := (S * S) * M)
  · rw [show (cutoff + (n + 1 : Nat)) ^ 2 = S * S by
      dsimp [S]
      rw [Rat.pow_succ, Rat.pow_succ]
      simp [Rat.mul_assoc]]
    calc
      (1 / (S * S)) * ((S * S) * M) = M := by
        rw [Rat.div_def]
        have hcancel : (S * S) * (S * S)⁻¹ = 1 :=
          Rat.mul_inv_cancel (S * S) hSSne
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= S := hMS
      _ = (1 / M - 1 / S) * ((S * S) * M) := by
        rw [Rat.div_def, Rat.div_def]
        have hMcancel : M * M⁻¹ = 1 := Rat.mul_inv_cancel M hMne
        have hScancel : S * S⁻¹ = 1 := Rat.mul_inv_cancel S hSne
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
          Rat.mul_assoc, Rat.mul_comm]
  · exact Rat.mul_pos (Rat.mul_pos hSpos hSpos) hMpos

theorem reciprocalSquareTailPartial_le_telescoping
    {cutoff : Rat} (hcutoff : 0 < cutoff) (terms : Nat) :
    reciprocalSquareTailPartial cutoff terms <=
      1 / cutoff - 1 / (cutoff + (terms : Nat)) := by
  induction terms with
  | zero =>
      simp [reciprocalSquareTailPartial, Rat.add_zero, Rat.sub_self]
  | succ terms ih =>
      rw [reciprocalSquareTailPartial]
      have hstep := reciprocalSquareTerm_le_telescopeStep hcutoff terms
      have hadd := rat_add_le_add ih hstep
      calc
        reciprocalSquareTailPartial cutoff terms +
            1 / (cutoff + (terms + 1 : Nat)) ^ 2 <=
            (1 / cutoff - 1 / (cutoff + (terms : Nat))) +
              (1 / (cutoff + (terms : Nat)) -
                1 / (cutoff + (terms + 1 : Nat))) := hadd
        _ = 1 / cutoff - 1 / (cutoff + (terms + 1 : Nat)) := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem reciprocalSquareTailPartial_le_inv_cutoff
    {cutoff : Rat} (hcutoff : 0 < cutoff) (terms : Nat) :
    reciprocalSquareTailPartial cutoff terms <= 1 / cutoff := by
  have htel := reciprocalSquareTailPartial_le_telescoping hcutoff terms
  have hpos : 0 < cutoff + (terms : Nat) := by
    have hn : 0 <= ((terms : Nat) : Rat) := Rat.natCast_nonneg
    grind
  have hnonneg : 0 <= 1 / (cutoff + (terms : Nat)) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by native_decide)
      (Rat.le_of_lt ((Rat.inv_pos).2 hpos))
  grind [Rat.sub_eq_add_neg]

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

/- A finite shell sum of certified pointwise Gaussian upper boxes.  The shell
   is deliberately indexed by rational sample points; no cell at infinity is
   introduced by the definition. -/
def gaussianTailBoxUpperPartial (cutoff : Rat) (stage : Nat) : Nat -> Rat
  | 0 => 0
  | terms + 1 =>
      gaussianTailBoxUpperPartial cutoff stage terms +
        gaussianTailBoxUpper (cutoff + (terms + 1 : Nat)) stage

theorem gaussianTailBoxUpperPartial_le_reciprocalSquareTailPartial
    {cutoff : Rat} (hcutoff : 0 <= cutoff) (stage terms : Nat)
    (hdom : forall n : Nat,
      gaussianTailBoxUpper (cutoff + (n + 1 : Nat)) stage <=
        1 / (cutoff + (n + 1 : Nat)) ^ 2) :
    gaussianTailBoxUpperPartial cutoff stage terms <=
      reciprocalSquareTailPartial cutoff terms := by
  induction terms with
  | zero =>
      rfl
  | succ terms ih =>
      rw [gaussianTailBoxUpperPartial, reciprocalSquareTailPartial]
      exact rat_add_le_add ih (hdom terms)

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
