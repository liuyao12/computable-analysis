import ComputableAnalysis.GeometricSeriesCalculus
import ComputableAnalysis.FiniteSecantIntegralOrder
import ComputableAnalysis.IntegerPowerIntegral

/-! Compact integral witnesses for supplied geometrically bounded series.
Only finite polynomial order and explicit geometric errors are used. -/
namespace ComputableAnalysis.FormalPowerSeries
open Integral FinitePolynomial

/-- Coefficients obtained by integrating a supplied series, normalized at zero. -/
def integralCoefficient (c : Coeffs) : Coeffs
  | 0 => 0
  | k+1 => c k/((k : Rat)+1)

theorem integralCoefficient_bound {c : Coeffs} {M : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k) (k : Nat) :
    qabs (integralCoefficient c k) ≤ (2*M)*((1 : Rat)/2)^k := by
  cases k with
  | zero => simp only [integralCoefficient, Rat.pow_zero, Rat.mul_one, qabs_eq_self_of_nonneg (Rat.le_refl : (0 : Rat) ≤ 0)]; grind
  | succ k =>
    have hk := Rat.natCast_nonneg (a := k)
    have hinv := Rat.inv_pos.mpr (show 0 < (k : Rat)+1 by grind)
    have hcan := Rat.mul_inv_cancel ((k : Rat)+1) (by grind)
    have hi : ((k : Rat)+1)⁻¹ ≤ 1 := by
      have := Rat.mul_nonneg hk (Rat.le_of_lt hinv)
      grind only
    have h := Rat.mul_le_mul_of_nonneg_left hi (qabs_nonneg (c k))
    rw [integralCoefficient, Rat.div_def, qabs_mul,
      qabs_eq_self_of_nonneg (Rat.le_of_lt hinv), Rat.pow_succ]
    have hh := hc k
    grind only

theorem integral_prefix (c : Coeffs) (x : Rat) (n : Nat) :
    sumBelow (fun k => integralCoefficient c k*x^k) (n+1) =
      integratedTaylorPrefix c n x := by
  induction n with
  | zero => simp [sumBelow_succ, integralCoefficient, integratedTaylorPrefix]; grind
  | succ n ih =>
    rw [sumBelow_succ, ih, integralCoefficient, integratedTaylorPrefix]
    simp only [Rat.natCast_add, Rat.div_def]
    grind only

theorem polynomial_prefix (c : Coeffs) (x : Rat) (n : Nat) :
    sumBelow (fun k => c k*x^k) n = taylorDerivativePrefix c n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumBelow_succ, taylorDerivativePrefix, ih]

/-- The independently evaluated integrand on a compact subinterval of `[0,1]`. -/
def geometricFunction (c : Coeffs) (M a b : Rat) (hM : 0 ≤ M)
    (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hb : b ≤ 1) : FunctionOnInterval where
  raw := { definedAt := fun x => a ≤ x ∧ x ≤ b
           compute := fun x _ => (geometricRaw c M x).compute }
  lower := a
  upper := b
  defined_on := fun _ h => h
  valid_on := by
    intro x hx
    apply geometricRaw_valid hM (R := 1/2) (by decide +kernel) hc
    rw [qabs_eq_self_of_nonneg (Rat.le_trans ha hx.1)]
    have := Rat.le_trans hx.2 hb
    grind

/-- Endpoint difference of the integrated series, with its own stage boxes. -/
def geometricIntegral (c : Coeffs) (M a b : Rat) : RealRaw :=
  RealRaw.sub (geometricRaw (integralCoefficient c) (2*M) b)
    (geometricRaw (integralCoefficient c) (2*M) a)

theorem geometricIntegral_valid {c : Coeffs} {M a b : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (geometricIntegral c M a b).Valid := by
  apply RealRaw.sub_valid
  all_goals
    apply geometricRaw_valid (by grind : 0 ≤ 2*M) (R := 1/2) (by decide +kernel)
      (integralCoefficient_bound hM hc)
    rw [qabs_eq_self_of_nonneg (by grind)]
    grind

private theorem sum_shift (P : RationalPartition a b) (v : Nat → Rat) (e : Rat) :
    rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k+e)) P.pieces =
      rectangleSum (fun k => (P.point (k+1)-P.point k)*v k) P.pieces+(b-a)*e := by
  have h (n : Nat) :
      rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k+e)) n =
      rectangleSum (fun k => (P.point (k+1)-P.point k)*v k) n+
        (P.point n-P.point 0)*e := by
    induction n with
    | zero => simp only [rectangleSum]; grind
    | succ n ih => simp only [rectangleSum, ih]; grind only
  simpa only [P.left_endpoint, P.right_endpoint] using h P.pieces

/-- Every finite rectangle bound encloses the integrated series. The error
is removed by rational separation, after proving the finite polynomial bound. -/
theorem geometricIntegral_bounds {c : Coeffs} {M a b : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∀ B : Bounds (geometricFunction c M a b hM hc ha hb),
      B.Encloses (geometricIntegral c M a b) := by
  intro B stage
  have finite (n : Nat) :
      B.lowerSum-(b-a)*(2*M*((1 : Rat)/2)^n) ≤
        integratedTaylorPrefix c n b-integratedTaylorPrefix c n a ∧
      integratedTaylorPrefix c n b-integratedTaylorPrefix c n a ≤
        B.upperSum+(b-a)*(2*M*((1 : Rat)/2)^n) := by
    let e := 2*M*((1 : Rat)/2)^n
    let D : Bounds (FunctionOnInterval.exactRat (taylorDerivativePrefix c n) a b) :=
      { partition := B.partition
        lower := fun k => B.lower k-e
        upper := fun k => B.upper k+e
        lower_le := by
          intro k hk x hx j
          have h := B.lower_le k hk x hx n
          change B.lower k ≤ sumBelow (fun k => c k*x^k) n+e at h
          rw [polynomial_prefix] at h
          change B.lower k-e ≤ taylorDerivativePrefix c n x
          grind only
        upper_ge := by
          intro k hk x hx j
          have h := B.upper_ge k hk x hx n
          change sumBelow (fun k => c k*x^k) n-e ≤ B.upper k at h
          rw [polynomial_prefix] at h
          change taylorDerivativePrefix c n x ≤ B.upper k+e
          grind only }
    have ord := (integratedTaylorPrefixSecantBound 1 c (by decide) n).exactCellOrder
    have ord' : ExactCellOrderPreservation (taylorDerivativePrefix c n)
        (fun u v => integratedTaylorPrefix c n v-integratedTaylorPrefix c n u) a b :=
      { lower_const := fun hu huv hv hf => ord.lower_const (Rat.le_trans ha hu) huv (Rat.le_trans hv hb) hf
        upper_const := fun hu huv hv hf => ord.upper_const (Rat.le_trans ha hu) huv (Rat.le_trans hv hb) hf }
    have h := ord'.encloses D 0
    have hl : D.lowerSum = B.lowerSum-(b-a)*e := by
      change rectangleSum (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k-e)) _ = _
      have hs := sum_shift B.partition B.lower (-e)
      have he : (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k-e)) =
          (fun k => (B.partition.point (k+1)-B.partition.point k)*(B.lower k+(-e))) := by funext k; grind only
      rw [he, hs]
      change B.lowerSum+(b-a)*(-e) = B.lowerSum-(b-a)*e
      grind only
    have hu : D.upperSum = B.upperSum+(b-a)*e := sum_shift B.partition B.upper e
    rw [hl,hu] at h
    exact h
  have future (n : Nat) (hn : stage ≤ n) :
      ((geometricIntegral c M a b).compute stage).lo ≤
        integratedTaylorPrefix c n b-integratedTaylorPrefix c n a ∧
      integratedTaylorPrefix c n b-integratedTaylorPrefix c n a ≤
        ((geometricIntegral c M a b).compute stage).hi := by
    have hxbox (x : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :=
      geometricRaw_contains_prefix (c := integralCoefficient c) (by grind : 0 ≤ 2*M)
        (R := 1/2) (by decide +kernel) (integralCoefficient_bound hM hc)
        (x := x) (by rw [qabs_eq_self_of_nonneg hx0]; grind : (1 : Rat)/2*qabs x ≤ 1/2)
        (show stage ≤ n+1 by omega)
    have h1 := hxbox a ha (by grind)
    have h2 := hxbox b (by grind) hb
    rw [integral_prefix] at h1 h2
    change _-_ ≤ _ ∧ _ ≤ _-_
    grind only
  have herr : 0 ≤ (b-a)*(2*M) := Rat.mul_nonneg (by grind) (by grind)
  constructor
  · by_cases h : B.lowerSum ≤ ((geometricIntegral c M a b).compute stage).hi
    · exact h
    exfalso
    let eps : QPos := ⟨(B.lowerSum-((geometricIntegral c M a b).compute stage).hi)/2, by grind⟩
    let N := RationalMajorant.halfDecayShift ((b-a)*(2*M)) eps
    have hsmall := RationalMajorant.halfDecayShift_spec herr eps
    have hn := half_pow_antitone (Nat.le_max_left N stage)
    have hmul := Rat.mul_le_mul_of_nonneg_left hn herr
    have hfin := (finite (max N stage)).1
    have hfur := (future (max N stage) (Nat.le_max_right _ _)).2
    dsimp [eps] at hsmall
    change (b-a)*(2*M)*((1 : Rat)/2)^N ≤ _ at hsmall
    grind only
  · by_cases h : ((geometricIntegral c M a b).compute stage).lo ≤ B.upperSum
    · exact h
    exfalso
    let eps : QPos := ⟨(((geometricIntegral c M a b).compute stage).lo-B.upperSum)/2, by grind⟩
    let N := RationalMajorant.halfDecayShift ((b-a)*(2*M)) eps
    have hsmall := RationalMajorant.halfDecayShift_spec herr eps
    have hn := half_pow_antitone (Nat.le_max_left N stage)
    have hmul := Rat.mul_le_mul_of_nonneg_left hn herr
    have hfin := (finite (max N stage)).2
    have hfur := (future (max N stage) (Nat.le_max_right _ _)).1
    dsimp [eps] at hsmall
    change (b-a)*(2*M)*((1 : Rat)/2)^N ≤ _ at hsmall
    grind only

private theorem power_lipschitz_unit (k : Nat) {x y : Rat}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    qabs (y^k-x^k) ≤ (k : Rat)*(y-x) := by
  cases k with
  | zero => simp [Rat.pow_zero, qabs]; grind
  | succ k =>
    have hd := IntegerPowerIntegral.power_difference k x y
    have hm := IntegerPowerIntegral.power_mono (k+1) hx hxy
    have hs := (IntegerPowerIntegral.slope_bounds k hx hxy).2
    have hp := IntegerPowerIntegral.power_mono k (show 0 ≤ y by grind) hy
    have hone (j : Nat) : (1 : Rat)^j=1 := by
      induction j with
      | zero => rfl
      | succ j ih => rw [Rat.pow_succ, ih, Rat.mul_one]
    rw [hone] at hp
    have hkp : 0 ≤ (k : Rat)+1 := by have := Rat.natCast_nonneg (a := k); grind
    have h1 := Rat.mul_le_mul_of_nonneg_left hp hkp
    have h2 := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans hs (by simpa using h1)) (show 0 ≤ y-x by grind)
    rw [qabs_eq_self_of_nonneg (show 0 ≤ y^(k+1)-x^(k+1) by grind), hd]
    simp only [Rat.natCast_add]
    grind only

def polynomialLip (c : Coeffs) : Nat → Rat
  | 0 => 0
  | n+1 => polynomialLip c n+qabs (c n)*(n : Rat)

theorem polynomialLip_nonneg (c : Coeffs) (n : Nat) : 0 ≤ polynomialLip c n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
    have := Rat.mul_nonneg (qabs_nonneg (c n)) (Rat.natCast_nonneg (a := n))
    unfold polynomialLip
    grind only

theorem polynomial_lipschitz (c : Coeffs) (n : Nat) {x y : Rat}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    qabs (sumBelow (fun k => c k*y^k) n-sumBelow (fun k => c k*x^k) n) ≤
      polynomialLip c n*(y-x) := by
  induction n with
  | zero => simp [sumBelow, polynomialLip, qabs]; grind
  | succ n ih =>
    have hp := Rat.mul_le_mul_of_nonneg_left (power_lipschitz_unit n hx hxy hy) (qabs_nonneg (c n))
    rw [← qabs_mul] at hp
    have ht := qabs_add_le
      (sumBelow (fun k => c k*y^k) n-sumBelow (fun k => c k*x^k) n) (c n*(y^n-x^n))
    rw [show (sumBelow (fun k => c k*y^k) n-sumBelow (fun k => c k*x^k) n)+c n*(y^n-x^n)=
      sumBelow (fun k => c k*y^k) (n+1)-sumBelow (fun k => c k*x^k) (n+1) by
        rw [sumBelow_succ,sumBelow_succ]; grind only] at ht
    rw [polynomialLip]
    grind only

/-- Explicit finite rectangles: a polynomial value at the left endpoint,
its finite Lipschitz error across the cell, and the geometric evaluation tail. -/
def geometricBounds (c : Coeffs) (M a b : Rat) (hM : 0 ≤ M)
    (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n N : Nat) (hN : 0 < N) :
    Bounds (geometricFunction c M a b hM hc ha hb) where
  partition := RationalPartition.uniform a b N hN hab
  lower k := sumBelow (fun j => c j*(leftPoint a b N k)^j) n-
    (2*M*((1 : Rat)/2)^n+polynomialLip c n*mesh a b N)
  upper k := sumBelow (fun j => c j*(leftPoint a b N k)^j) n+
    (2*M*((1 : Rat)/2)^n+polynomialLip c n*mesh a b N)
  lower_le := by
    intro k hk x hx j
    let P := RationalPartition.uniform a b N hN hab
    have hc0 := (P.cell k hk).lower_mem
    have hc1 := (P.cell k hk).upper_mem
    have he := polynomial_lipschitz c n (x := leftPoint a b N k) (y := x)
      (Rat.le_trans ha hc0) hx.1 (Rat.le_trans hx.2 (Rat.le_trans hc1 hb))
    have hm : x-leftPoint a b N k ≤ mesh a b N := by
      have hh := leftPoint_step a b N k
      have hxupper : x ≤ leftPoint a b N (k+1) := hx.2
      grind only
    have hl := Rat.mul_le_mul_of_nonneg_left hm (polynomialLip_nonneg c n)
    have hv := (geometricFunction c M a b hM hc ha hb).valid_on x
      ((P.cell k hk).contains_inDomain hx)
    have ho := (RealRaw.compareAt_overlap_iff _ _ n j).1 (RealRaw.allStagesOverlap_refl _ hv n j)
    have hn := neg_qabs_le_self (sumBelow (fun k => c k*x^k) n-sumBelow (fun j => c j*(leftPoint a b N k)^j) n)
    change _ ≤ ((geometricRaw c M x).compute j).hi
    change ((geometricRaw c M x).compute n).Overlaps ((geometricRaw c M x).compute j) at ho
    dsimp [geometricRaw, QInterval.Overlaps] at ho ⊢
    grind only
  upper_ge := by
    intro k hk x hx j
    let P := RationalPartition.uniform a b N hN hab
    have hc0 := (P.cell k hk).lower_mem
    have hc1 := (P.cell k hk).upper_mem
    have he := polynomial_lipschitz c n (x := leftPoint a b N k) (y := x)
      (Rat.le_trans ha hc0) hx.1 (Rat.le_trans hx.2 (Rat.le_trans hc1 hb))
    have hm : x-leftPoint a b N k ≤ mesh a b N := by
      have hh := leftPoint_step a b N k
      have hxupper : x ≤ leftPoint a b N (k+1) := hx.2
      grind only
    have hl := Rat.mul_le_mul_of_nonneg_left hm (polynomialLip_nonneg c n)
    have hv := (geometricFunction c M a b hM hc ha hb).valid_on x
      ((P.cell k hk).contains_inDomain hx)
    have ho := (RealRaw.compareAt_overlap_iff _ _ n j).1 (RealRaw.allStagesOverlap_refl _ hv n j)
    have hn := self_le_qabs (sumBelow (fun k => c k*x^k) n-sumBelow (fun j => c j*(leftPoint a b N k)^j) n)
    change ((geometricRaw c M x).compute j).lo ≤ _
    change ((geometricRaw c M x).compute n).Overlaps ((geometricRaw c M x).compute j) at ho
    dsimp [geometricRaw, QInterval.Overlaps] at ho ⊢
    grind only

theorem geometricBounds_gap (c : Coeffs) (M a b : Rat) (hM : 0 ≤ M)
    (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (n N : Nat) (hN : 0 < N) :
    (geometricBounds c M a b hM hc ha hab hb n N hN).upperSum-
      (geometricBounds c M a b hM hc ha hab hb n N hN).lowerSum =
      2*(b-a)*(2*M*((1 : Rat)/2)^n+polynomialLip c n*mesh a b N) := by
  let P := RationalPartition.uniform a b N hN hab
  let v := fun k => sumBelow (fun j => c j*(leftPoint a b N k)^j) n
  let e := 2*M*((1 : Rat)/2)^n+polynomialLip c n*mesh a b N
  have hh := sum_shift P v e
  have hl := sum_shift P v (-e)
  have he : (fun k => (P.point (k+1)-P.point k)*(v k-e)) =
      (fun k => (P.point (k+1)-P.point k)*(v k+(-e))) := by funext k; grind only
  change rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k+e)) P.pieces-
    rectangleSum (fun k => (P.point (k+1)-P.point k)*(v k-e)) P.pieces = 2*(b-a)*e
  rw [he,hh,hl]
  grind only

/-- The algorithm supplies arbitrarily tight bounds; this is a construction,
not an assumed membership condition on the eventual integral. -/
theorem geometricFunction_tight {c : Coeffs} {M a b : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasTightBounds (geometricFunction c M a b hM hc ha hb) := by
  intro eps
  have hhalf : 0 < eps.val/2 := by have := eps.property; grind
  let n := RationalMajorant.halfDecayShift (4*(b-a)*M) ⟨_,hhalf⟩
  have hC : 0 ≤ 4*(b-a)*M := Rat.mul_nonneg (by grind) hM
  have hn := RationalMajorant.halfDecayShift_spec hC ⟨_,hhalf⟩
  let L := 2*(b-a)*polynomialLip c n*(b-a)
  have hL : 0 ≤ L := Rat.mul_nonneg
    (Rat.mul_nonneg (by grind) (polynomialLip_nonneg c n)) (by grind)
  have htol : 0 < eps.val/(2*(L+1)) := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))
  obtain ⟨N,hN⟩ := shrinksToZero_of_natOverSuccBound (C := 1)
    (width := fun j => 1/((j+1 : Nat) : Rat)) (fun _ => Rat.le_refl) ⟨_,htol⟩
  refine ⟨geometricBounds c M a b hM hc ha hab hb n (N+1) (by omega), ?_⟩
  rw [geometricBounds_gap]
  have hsmall := hN N (Nat.le_refl _)
  have hprod := Rat.mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 2*(L+1) by grind)
  have hcan := Rat.mul_inv_cancel (2*(L+1)) (by grind)
  have hni : 0 ≤ (((N+1 : Nat) : Rat)⁻¹) := Rat.le_of_lt
    (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega)))
  simp only [Rat.div_def, Rat.one_mul] at hprod
  have hcanc : eps.val*(2*(L+1))⁻¹*(2*(L+1))=eps.val := by grind only
  rw [hcanc] at hprod
  have hmesh : mesh a b (N+1) = (b-a)*(((N+1 : Nat) : Rat)⁻¹) := by
    simp only [mesh, if_neg (show N+1 ≠ 0 by omega), Rat.div_def]
  rw [hmesh]
  change 4*(b-a)*M*((1 : Rat)/2)^n ≤ eps.val/2 at hn
  have hfinal : 2*(b-a)*(2*M*((1 : Rat)/2)^n+
      polynomialLip c n*((b-a)*(((N+1 : Nat) : Rat)⁻¹))) =
      4*(b-a)*M*((1 : Rat)/2)^n+L*(((N+1 : Nat) : Rat)⁻¹) := by dsimp [L]; grind only
  rw [hfinal]
  grind only

/-- Actual compact integral existence for this supplied series computation. -/
theorem geometricIntegral_hasIntegral {c : Coeffs} {M a b : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/2)^k)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    HasIntegral (geometricFunction c M a b hM hc ha hb) (geometricIntegral c M a b) :=
  ⟨geometricIntegral_valid hM hc ha hab hb, geometricIntegral_bounds hM hc ha hab hb,
    geometricFunction_tight hM hc ha hab hb⟩

end ComputableAnalysis.FormalPowerSeries
