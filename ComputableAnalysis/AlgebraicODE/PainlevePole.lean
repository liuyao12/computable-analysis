import ComputableAnalysis.AlgebraicODE.PainleveLaurent
import ComputableAnalysis.CauchyProductEstimate

/-! Computed local pole charts for Painlevé I in a scaled rational coordinate.
The regular factor and both derivatives are valid interval algorithms. -/
namespace ComputableAnalysis.AlgebraicODE.Painleve.Pole
open FormalPowerSeries

def radius (p q : Rat) : Rat := 1/(64*Laurent.growthBound p q)

theorem radius_pos (p q : Rat) : 0 < radius p q := by
  have hR := Laurent.growthBound_ge_one p q
  unfold radius
  rw [Rat.div_def]
  exact Rat.mul_pos (by decide) (Rat.inv_pos.mpr (by grind))

def coefficients (p q : Rat) (n : Nat) : Rat := Laurent.coeff p q n * radius p q ^ n

theorem coefficient_bound (p q : Rat) (n : Nat) :
    qabs (coefficients p q n) ≤ ((1 : Rat)/64)^n := by
  have hR := Laurent.growthBound_ge_one p q
  have hr := radius_pos p q
  have h := Rat.mul_le_mul_of_nonneg_right (Laurent.coeff_growth p q n)
    (Rat.pow_nonneg (n := n) (Rat.le_of_lt hr))
  have he : Laurent.growthBound p q * radius p q=1/64 := by
    unfold radius
    rw [Rat.div_def, Rat.inv_mul_rev]
    have hc := Rat.mul_inv_cancel (Laurent.growthBound p q) (by grind)
    grind
  unfold coefficients
  rw [qabs_mul, qabs_eq_self_of_nonneg (Rat.pow_nonneg (Rat.le_of_lt hr))]
  rw [pow_product, he] at h
  exact h

theorem first_coefficient_bound (p q : Rat) (n : Nat) :
    qabs (coefficientShift (coefficients p q) n) ≤ ((1 : Rat)/32)^n := by
  have h := coefficientShift_unit_growth (by decide +kernel : (0 : Rat) ≤ 1/64)
    (by decide +kernel) (coefficient_bound p q) n
  simpa only [show (2 : Rat)*(1/64)=1/32 by decide +kernel] using h

theorem second_coefficient_bound (p q : Rat) (n : Nat) :
    qabs (coefficientShift (coefficientShift (coefficients p q)) n) ≤ ((1 : Rat)/16)^n := by
  have h := coefficientShift_unit_growth (by decide +kernel : (0 : Rat) ≤ 1/32)
    (by decide +kernel) (first_coefficient_bound p q) n
  simpa only [show (2 : Rat)*(1/32)=1/16 by decide +kernel] using h

theorem coefficients_rapid (p q : Rat) (n : Nat) :
    qabs (coefficients p q n) ≤ 1*((1 : Rat)/8)^n := by
  rw [Rat.one_mul]
  exact Rat.le_trans (coefficient_bound p q n)
    (pow_base_mono (by decide +kernel) (by decide +kernel) n)

theorem first_coefficients_rapid (p q : Rat) (n : Nat) :
    qabs (coefficientShift (coefficients p q) n) ≤ 1*((1 : Rat)/8)^n := by
  rw [Rat.one_mul]
  exact Rat.le_trans (first_coefficient_bound p q n)
    (pow_base_mono (by decide +kernel) (by decide +kernel) n)

def factor (p q t : Rat) : RealRaw := geometricRaw (coefficients p q) 1 t
def firstDerivative (p q t : Rat) : RealRaw := geometricRaw (coefficientShift (coefficients p q)) 1 t
def secondDerivative (p q t : Rat) : RealRaw :=
  geometricRaw (coefficientShift (coefficientShift (coefficients p q))) 1 t

theorem factor_valid (p q t : Rat) (ht : qabs t ≤ 1) : (factor p q t).Valid :=
  geometricRaw_rapid_valid (by decide) (coefficients_rapid p q) ht

theorem firstDerivative_valid (p q t : Rat) (ht : qabs t ≤ 1) : (firstDerivative p q t).Valid :=
  geometricRaw_rapid_valid (by decide) (first_coefficients_rapid p q) ht

theorem secondDerivative_valid (p q t : Rat) (ht : qabs t ≤ 1) : (secondDerivative p q t).Valid :=
  geometricRaw_coefficientShift_valid (by decide) (first_coefficients_rapid p q) ht

/-- First derivative of the actual interval-valued factor, measured on
all samples from sufficiently refined boxes. -/
theorem factor_derivative (p q : Rat) (eps : QPos) {t h v w d : Rat} {n : Nat}
    (hh : h ≠ 0) (ht : qabs t ≤ 1) (hth : qabs (t+h) ≤ 1)
    (hsmall : qabs h ≤ (derivativeRadius 1 (by decide) eps).val)
    (hn : derivativeStage 1 eps h ≤ n)
    (hv : InBox v ((factor p q t).compute n))
    (hw : InBox w ((factor p q (t+h)).compute n))
    (hd : InBox d ((firstDerivative p q t).compute n)) :
    qabs (w-v-h*d) ≤ eps.val*qabs h :=
  geometricRaw_hasBoxDerivative (by decide) (coefficients_rapid p q) eps hh ht hth hsmall hn hv hw hd

/-- The second derivative is also certified by finite differences. -/
theorem factor_secondDerivative (p q : Rat) (eps : QPos) {t h v w d : Rat} {n : Nat}
    (hh : h ≠ 0) (ht : qabs t ≤ 1) (hth : qabs (t+h) ≤ 1)
    (hsmall : qabs h ≤ (derivativeRadius 1 (by decide) eps).val)
    (hn : derivativeStage 1 eps h ≤ n)
    (hv : InBox v ((firstDerivative p q t).compute n))
    (hw : InBox w ((firstDerivative p q (t+h)).compute n))
    (hd : InBox d ((secondDerivative p q t).compute n)) :
    qabs (w-v-h*d) ≤ eps.val*qabs h :=
  geometricRaw_hasBoxDerivative (by decide) (first_coefficients_rapid p q) eps hh ht hth hsmall hn hv hw hd

def forcingCoefficient (p r : Rat) (n : Nat) : Rat :=
  if n=4 then p*r^4 else if n=5 then r^5 else 0

theorem coefficient_equation (p q : Rat) (n : Nat) :
    shiftedSecondEuler (-2) (coefficients p q) n =
      6*cauchyProduct (coefficients p q) (coefficients p q) n+
        forcingCoefficient p (radius p q) n := by
  have hr := Laurent.coeff_isSolution p q n
  unfold Laurent.residual at hr
  have hm := cauchy_terms (Laurent.coeff p q) (Laurent.coeff p q) (radius p q) n
  change cauchyProduct (coefficients p q) (coefficients p q) n = _ at hm
  have hf : (if 4 ≤ n then Laurent.forcing p (n-4) else 0)*radius p q^n =
      forcingCoefficient p (radius p q) n := by
    by_cases hn : n<6
    · have hc : n=0 ∨ n=1 ∨ n=2 ∨ n=3 ∨ n=4 ∨ n=5 := by omega
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [Laurent.forcing, ofPolynomial, forcingCoefficient]
    · have hz : Laurent.forcing p (n-4)=0 := by
        unfold Laurent.forcing ofPolynomial
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [if_pos (by omega), hz]
      simp [forcingCoefficient, show n≠4 by omega, show n≠5 by omega]
  rw [hm, ← hf]
  unfold shiftedSecondEuler coefficients at *
  grind

theorem forcing_prefix (p r t : Rat) {N : Nat} (hN : 6 ≤ N) :
    sumBelow (fun k => forcingCoefficient p r k*t^k) N = p*r^4*t^4+r^5*t^5 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction m with
  | zero => simp [sumBelow_succ, forcingCoefficient]; grind
  | succ m ih =>
      rw [show 6+(m+1)=(6+m)+1 by omega, sumBelow_succ, ih (by omega)]
      simp [forcingCoefficient, show 6+m≠4 by omega, show 6+m≠5 by omega]; grind

theorem scaled_jet_prefix (c : Coeffs) (t : Rat) (n : Nat) :
    t^2*sumBelow (fun k => coefficientShift (coefficientShift c) k*t^k) n-
      4*t*sumBelow (fun k => coefficientShift c k*t^k) (n+1)+
      6*sumBelow (fun k => c k*t^k) (n+2) =
      sumBelow (fun k => shiftedSecondEuler (-2) c k*t^k) (n+2) := by
  induction n with
  | zero =>
      simp [sumBelow_succ, coefficientShift, shiftedSecondEuler, Rat.pow_succ]
      grind
  | succ n ih =>
      simp only [sumBelow_succ, coefficientShift, shiftedSecondEuler,
        Rat.pow_succ, Rat.natCast_add] at ih ⊢
      grind

theorem finite_equation (p q t : Rat) {n : Nat} (hn : 4 ≤ n) :
    t^2*sumBelow (fun k => coefficientShift (coefficientShift (coefficients p q)) k*t^k) n-
      4*t*sumBelow (fun k => coefficientShift (coefficients p q) k*t^k) (n+1)+
      6*sumBelow (fun k => coefficients p q k*t^k) (n+2)-
      6*sumBelow (fun k => cauchyProduct (coefficients p q) (coefficients p q) k*t^k) (n+2)-
      (p*radius p q^4*t^4+radius p q^5*t^5) = 0 := by
  rw [scaled_jet_prefix]
  have he : (fun k => shiftedSecondEuler (-2) (coefficients p q) k*t^k) =
      (fun k => 6*(cauchyProduct (coefficients p q) (coefficients p q) k*t^k)+
        forcingCoefficient p (radius p q) k*t^k) := by
    funext k
    rw [coefficient_equation]
    grind
  rw [he, sumBelow_add, sumBelow_mul, forcing_prefix p (radius p q) t (by omega)]
  grind

theorem second_coefficients_rapid (p q : Rat) (n : Nat) :
    qabs (coefficientShift (coefficientShift (coefficients p q)) n) ≤ 1*((1 : Rat)/8)^n := by
  rw [Rat.one_mul]
  exact Rat.le_trans (second_coefficient_bound p q n)
    (pow_base_mono (by decide +kernel) (by decide +kernel) n)

private theorem prefix_inBox {c : Coeffs} {t : Rat}
    (hc : ∀ n, qabs (c n) ≤ 1*((1 : Rat)/8)^n) (ht : qabs t ≤ 1)
    {n N : Nat} (hn : n ≤ N) :
    InBox (sumBelow (fun k => c k*t^k) N) ((geometricRaw c 1 t).compute n) :=
  geometricRaw_contains_prefix (by decide) (by decide +kernel) hc (by grind) hn

private theorem sample_bound {V : RealRaw} (hV : V.Valid)
    (h0 : V.compute 0=⟨-2,2⟩) {n : Nat} {v : Rat} (hv : InBox v (V.compute n)) :
    qabs v ≤ 2 := by
  have hn := hV.2.1 0 n (Nat.zero_le n)
  rw [h0] at hn
  unfold InBox at hv
  apply qabs_le_of_neg_le_le <;> grind

private theorem raw_zero_box (c : Coeffs) (t : Rat) :
    (geometricRaw c 1 t).compute 0=⟨-2,2⟩ := by
  simp [geometricRaw, sumBelow_zero]
  congr 1 <;> decide +kernel

private theorem terms_bound {c : Coeffs} {t : Rat}
    (hc : ∀ n, qabs (c n) ≤ 1*((1 : Rat)/8)^n) (ht : qabs t ≤ 1) (n : Nat) :
    qabs (c n*t^n) ≤ 1*((1 : Rat)/8)^n := by
  have hp : qabs (t^n) ≤ 1 := by
    clear hc
    induction n with
    | zero => simp [qabs]; decide
    | succ n ih =>
        rw [Rat.pow_succ, qabs_mul]
        have h := Rat.mul_le_mul_of_nonneg_left ht (qabs_nonneg (t^n))
        grind
  have h1 := Rat.mul_le_mul_of_nonneg_left hp (qabs_nonneg (c n))
  rw [qabs_mul]
  have h2 := hc n
  grind

private theorem residual_stability {t u v w U V W F delta eta : Rat}
    (ht : qabs t ≤ 1) (hu : qabs u ≤ 2) (hU : qabs U ≤ 2)
    (_hd : 0 ≤ delta)
    (hdu : qabs (u-U) ≤ delta) (hdv : qabs (v-V) ≤ delta) (hdw : qabs (w-W) ≤ delta)
    (he : qabs (t^2*W-4*t*V+6*U-6*U^2-F) ≤ eta) :
    qabs (t^2*w-4*t*v+6*u-6*u^2-F) ≤ 35*delta+eta := by
  have hs : qabs (u^2-U^2) ≤ 4*delta := by
    have hf : u^2-U^2=(u-U)*(u+U) := by simp [Rat.pow_succ]; grind
    rw [hf, qabs_mul]
    have hsum := qabs_add_le u U
    have hm1 := Rat.mul_le_mul_of_nonneg_left (show qabs (u+U) ≤ 4 by grind)
      (qabs_nonneg (u-U))
    have hm2 := Rat.mul_le_mul_of_nonneg_right hdu (show (0 : Rat) ≤ 4 by decide)
    grind
  have hwp : qabs (t^2*(w-W)) ≤ delta := by
    rw [qabs_mul]
    have htp : qabs (t^2) ≤ 1 := by
      simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul, qabs_mul]
      have h := Rat.mul_le_mul_of_nonneg_right ht (qabs_nonneg t)
      grind
    have h1 := Rat.mul_le_mul_of_nonneg_right htp (qabs_nonneg (w-W))
    grind
  have hvp : qabs (4*t*(v-V)) ≤ 4*delta := by
    rw [qabs_mul, qabs_mul, show qabs (4 : Rat)=4 by decide +kernel]
    have h1 := Rat.mul_le_mul_of_nonneg_right ht (qabs_nonneg (v-V))
    grind
  have hup : qabs (6*(u-U)) ≤ 6*delta := by
    rw [qabs_mul, show qabs (6 : Rat)=6 by decide +kernel]
    grind
  have hsp : qabs (6*(u^2-U^2)) ≤ 24*delta := by
    rw [qabs_mul, show qabs (6 : Rat)=6 by decide +kernel]
    grind
  have h1 := qabs_sub_le (t^2*(w-W)) (4*t*(v-V))
  have h2 := qabs_add_le (t^2*(w-W)-4*t*(v-V)) (6*(u-U))
  have h3 := qabs_sub_le (t^2*(w-W)-4*t*(v-V)+6*(u-U)) (6*(u^2-U^2))
  have h4 := qabs_add_le (t^2*(w-W)-4*t*(v-V)+6*(u-U)-6*(u^2-U^2))
    (t^2*W-4*t*V+6*U-6*U^2-F)
  have hid : (t^2*(w-W)-4*t*(v-V)+6*(u-U)-6*(u^2-U^2))+
      (t^2*W-4*t*V+6*U-6*U^2-F)=t^2*w-4*t*v+6*u-6*u^2-F := by grind
  rw [hid] at h4
  grind only

/-- The actual computed factor and derivatives satisfy the regularized
Painlevé equation with a uniform, explicit error at every stage. -/
theorem equation_error (p q : Rat) {t u v w : Rat} (ht : qabs t ≤ 1) (n : Nat)
    (hu : InBox u ((factor p q t).compute n))
    (hv : InBox v ((firstDerivative p q t).compute n))
    (hw : InBox w ((secondDerivative p q t).compute n)) :
    qabs (t^2*w-4*t*v+6*u-6*u^2-
      (p*radius p q^4*t^4+radius p q^5*t^5)) ≤ 146*((1 : Rat)/2)^n := by
  let c := coefficients p q
  let P := sumBelow (fun k => c k*t^k) (n+6)
  let D := sumBelow (fun k => coefficientShift c k*t^k) (n+5)
  let E := sumBelow (fun k => coefficientShift (coefficientShift c) k*t^k) (n+4)
  have hP : InBox P ((factor p q t).compute n) :=
    prefix_inBox (coefficients_rapid p q) ht (by omega)
  have hD : InBox D ((firstDerivative p q t).compute n) :=
    prefix_inBox (first_coefficients_rapid p q) ht (by omega)
  have hE : InBox E ((secondDerivative p q t).compute n) :=
    prefix_inBox (second_coefficients_rapid p q) ht (by omega)
  have hdu := inBox_distance hu hP
  have hdv := inBox_distance hv hD
  have hdw := inBox_distance hw hE
  change _ ≤ ((geometricRaw _ 1 t).compute n).width at hdu hdv hdw
  rw [geometricRaw_width] at hdu hdv hdw
  have hu2 := sample_bound (factor_valid p q t ht) (raw_zero_box _ _) hu
  have hP2 := sample_bound (factor_valid p q t ht) (raw_zero_box _ _) hP
  have hprod := cauchy_prefix_error (M := 1) (by decide)
    (terms_bound (coefficients_rapid p q) ht) (terms_bound (coefficients_rapid p q) ht) (n+6)
  have heq : cauchyProduct (fun j => coefficients p q j*t^j) (fun j => coefficients p q j*t^j)=
      (fun k => cauchyProduct c c k*t^k) := by funext k; exact cauchy_terms c c t k
  rw [heq] at hprod
  have hfinite := finite_equation p q t (n := n+4) (by omega)
  change t^2*E-4*t*D+6*P-6*sumBelow (fun k => cauchyProduct c c k*t^k) (n+6)-
    (p*radius p q^4*t^4+radius p q^5*t^5)=0 at hfinite
  have herr : qabs (t^2*E-4*t*D+6*P-6*P^2-
      (p*radius p q^4*t^4+radius p q^5*t^5)) ≤ 6*((1 : Rat)/2)^n := by
    have hid : t^2*E-4*t*D+6*P-6*P^2-(p*radius p q^4*t^4+radius p q^5*t^5) =
        -6*(P*P-sumBelow (fun k => cauchyProduct c c k*t^k) (n+6)) := by
      simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
      grind
    rw [hid, qabs_mul, show qabs (-6 : Rat)=6 by decide +kernel]
    have hp := half_pow_antitone (show n ≤ n+6 by omega)
    change qabs (P*P-_) ≤ _ at hprod
    grind
  have h := residual_stability ht hu2 hP2
    (Rat.mul_nonneg (by decide : (0 : Rat) ≤ 4) (Rat.pow_nonneg (n := n) (by decide +kernel : (0 : Rat) ≤ 1/2)))
    (by simpa only [show (4 : Rat)*1=4 by decide +kernel] using hdu)
    (by simpa only [show (4 : Rat)*1=4 by decide +kernel] using hdv)
    (by simpa only [show (4 : Rat)*1=4 by decide +kernel] using hdw) herr
  grind only

/-- Every positive rational error request has a computed ODE precision. -/
theorem equation (p q : Rat) (eps : QPos) {t u v w : Rat} (ht : qabs t ≤ 1)
    {n : Nat} (hn : RationalMajorant.halfDecayShift 146 eps ≤ n)
    (hu : InBox u ((factor p q t).compute n))
    (hv : InBox v ((firstDerivative p q t).compute n))
    (hw : InBox w ((secondDerivative p q t).compute n)) :
    qabs (t^2*w-4*t*v+6*u-6*u^2-
      (p*radius p q^4*t^4+radius p q^5*t^5)) ≤ eps.val := by
  have h1 := equation_error p q ht n hu hv hw
  have h2 := Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hn) (by decide : (0 : Rat) ≤ 146)
  exact Rat.le_trans h1 (Rat.le_trans h2 (RationalMajorant.halfDecayShift_spec (by decide) eps))

/-- The actual factor boxes stay away from zero, uniformly in both parameters. -/
theorem factor_two (p q t : Rat) :
    (factor p q t).compute 2 = ⟨1/2, 3/2⟩ := by
  have h0 : Laurent.coeff p q 0 = 1 := by rw [Laurent.coeff]
  have h1 : Laurent.coeff p q 1 = 0 := by rw [Laurent.coeff]
  simp [factor, geometricRaw, sumBelow_succ, coefficients, h0, h1, Rat.pow_succ]
  decide +kernel

theorem factor_bounds (p q : Rat) {t : Rat} (ht : qabs t ≤ 1)
    {n : Nat} (hn : 2 ≤ n) :
    1/2 ≤ ((factor p q t).compute n).lo ∧
      ((factor p q t).compute n).hi ≤ 3/2 := by
  have h := (factor_valid p q t ht).2.1 2 n hn
  rw [factor_two] at h
  exact ⟨h.1, h.2.2⟩

/-- Reconstruction at `x=p+radius*poleCoordinate`, away from the pole. -/
def value (p q t : Rat) : RealRaw :=
  RealRaw.scaleRat (1/(radius p q*t)^2) (factor p q t)

theorem value_valid (p q : Rat) {t : Rat} (ht : qabs t ≤ 1) :
    (value p q t).Valid := RealRaw.scaleRat_valid (factor_valid p q t ht)

/-- Two-sided order-two pole bounds, on every sufficiently refined box. -/
theorem double_pole_bounds (p q : Rat) {t : Rat} (ht : qabs t ≤ 1)
    (ht0 : t ≠ 0) {n : Nat} (hn : 2 ≤ n) :
    1/2 ≤ (radius p q*t)^2 * ((value p q t).compute n).lo ∧
      (radius p q*t)^2 * ((value p q t).compute n).hi ≤ 3/2 := by
  have hr := radius_pos p q
  have hr0 : radius p q ≠ 0 := Rat.ne_of_gt hr
  have hri := Rat.mul_inv_cancel (radius p q) hr0
  have hz : (radius p q*t)^2 ≠ 0 := by
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind only
  have hp : 0 ≤ (radius p q*t)^2 := by
    simpa only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] using
      rat_square_nonneg_basic (radius p q*t)
  have hi : 0 ≤ 1/(radius p q*t)^2 := by
    rw [Rat.div_def, Rat.one_mul]
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.lt_of_le_of_ne hp (Ne.symm hz)))
  have hc := Rat.mul_inv_cancel ((radius p q*t)^2) hz
  have hb := factor_bounds p q ht hn
  simp only [value, RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos hi]
  simp only [Rat.div_def, Rat.one_mul, ← Rat.mul_assoc, hc, Rat.one_mul] at *
  exact hb

/-- Exact change of jet coordinates for the original equation `y''=6y²+x`.
Derivative certificates above are for the regular factor in the `t` coordinate. -/
theorem original_equation_identity (p r t u v w : Rat) (hr : r ≠ 0) (ht : t ≠ 0) :
    r^4*t^4 * ((t^2*w-4*t*v+6*u)/(r^4*t^4) -
      6*(u/(r^2*t^2))^2-(p+r*t)) =
    t^2*w-4*t*v+6*u-6*u^2-(p*r^4*t^4+r^5*t^5) := by
  have h2 : r^2*t^2 ≠ 0 := by
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind
  have h4 : r^4*t^4 ≠ 0 := by
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind
  have hc2 := Rat.mul_inv_cancel (r^2*t^2) h2
  have hc4 := Rat.mul_inv_cancel (r^4*t^4) h4
  simp only [Rat.div_def, Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at *
  grind only

end ComputableAnalysis.AlgebraicODE.Painleve.Pole
