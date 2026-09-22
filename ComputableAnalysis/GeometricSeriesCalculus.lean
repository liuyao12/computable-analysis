import ComputableAnalysis.GeometricPowerSeries

/-! Finite-difference semantics for rapidly convergent rational series. -/
namespace ComputableAnalysis.FormalPowerSeries
open FinitePolynomial

theorem pow_product (a b : Rat) (n : Nat) : a^n*b^n=(a*b)^n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Rat.pow_succ]; grind

theorem nat_succ_le_two_pow (n : Nat) : ((n+1 : Nat) : Rat) ≤ (2 : Rat)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : (1 : Rat) ≤ ((n+1 : Nat) : Rat) := by exact_mod_cast (by omega : 1 ≤ n+1)
      simp only [Rat.pow_succ, Rat.natCast_add] at *
      grind

/-- Differentiation of coefficients preserves an explicit geometric bound.
The analytic finite-difference theorem below is a separate statement. -/
theorem coefficientShift_growth {c : Coeffs} {M R : Rat}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hc : ∀ n, qabs (c n) ≤ M*R^n) (n : Nat) :
    qabs (coefficientShift c n) ≤ (M*R)*(2*R)^n := by
  have hn : (0 : Rat) ≤ ((n+1 : Nat) : Rat) := Rat.natCast_nonneg
  have h1 := Rat.mul_le_mul_of_nonneg_left (hc (n+1)) hn
  have h2 := Rat.mul_le_mul_of_nonneg_right (nat_succ_le_two_pow n)
    (Rat.mul_nonneg hM (Rat.pow_nonneg (n := n+1) hR))
  unfold coefficientShift
  rw [qabs_mul, qabs_eq_self_of_nonneg hn]
  rw [Rat.pow_succ] at h1 h2
  rw [← pow_product]
  grind

theorem pow_base_mono {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (n : Nat) : a^n ≤ b^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have h1 := Rat.mul_le_mul_of_nonneg_right ih ha
      have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (n := n) (by grind : 0 ≤ b))
      grind

theorem coefficientShift_unit_growth {c : Coeffs} {R : Rat}
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (hc : ∀ n, qabs (c n) ≤ R^n) (n : Nat) :
    qabs (coefficientShift c n) ≤ (2*R)^n := by
  have h := coefficientShift_growth (M := 1) (by decide) hR
    (by intro k; simpa using hc k) n
  have hs := Rat.mul_le_mul_of_nonneg_right hR1
    (Rat.pow_nonneg (n := n) (show 0 ≤ 2*R by grind))
  simp only [Rat.one_mul] at h hs
  exact Rat.le_trans h hs

private theorem error_unit_bound (n : Nat) : powerSecantErrorBound 1 n ≤ (4 : Rat)^n := by
  induction n with
  | zero => simp [powerSecantErrorBound]; decide
  | succ n ih =>
      have hn := nat_succ_le_two_pow n
      have ht : (2 : Rat)^n ≤ (4 : Rat)^n := by
        clear ih hn
        induction n with
        | zero => simp
        | succ n ih =>
            have hp : 0 ≤ (4 : Rat)^n := Rat.pow_nonneg (by decide)
            simp only [Rat.pow_succ]
            grind
      have hp : 0 ≤ (4 : Rat)^n := Rat.pow_nonneg (by decide)
      have hone : (1 : Rat)^n=1 := by
        clear ih hn ht hp
        induction n with
        | zero => rfl
        | succ n ih => rw [Rat.pow_succ, ih]; decide +kernel
      simp only [powerSecantErrorBound, hone, Rat.mul_one, Rat.one_mul, Rat.pow_succ]
      simp only [Rat.natCast_add] at hn
      grind

theorem sum_half (n : Nat) :
    sumBelow (fun k => ((1 : Rat)/2)^k) n = 2-2*((1 : Rat)/2)^n := by
  induction n with
  | zero => simp; grind
  | succ n ih => rw [sumBelow_succ, ih, Rat.pow_succ]; grind

theorem sumBelow_le {f g : Nat → Rat} {n : Nat}
    (h : ∀ k, k<n → f k ≤ g k) : sumBelow f n ≤ sumBelow g n := by
  induction n with
  | zero => exact Rat.le_refl
  | succ n ih =>
      rw [sumBelow_succ, sumBelow_succ]
      have := ih (fun k hk => h k (by omega))
      have := h n (by omega)
      grind

theorem abs_sumBelow_le (f : Nat → Rat) (n : Nat) :
    qabs (sumBelow f n) ≤ sumBelow (fun k => qabs (f k)) n := by
  induction n with
  | zero => simp [qabs]
  | succ n ih =>
      rw [sumBelow_succ, sumBelow_succ]
      have := qabs_add_le (sumBelow f n) (f n)
      grind

/-- All finite polynomials share one secant error bound. This uniformity
is what permits their boxed series to inherit a genuine derivative. -/
theorem prefix_secant_bound {c : Coeffs} {M x h : Rat}
    (hM : 0 ≤ M) (hc : ∀ n, qabs (c n) ≤ M*((1 : Rat)/8)^n)
    (hh : h ≠ 0) (hx : qabs x ≤ 1) (hxh : qabs (x+h) ≤ 1) (N : Nat) :
    qabs ((sumBelow (fun k => c k*(x+h)^k) N-sumBelow (fun k => c k*x^k) N)/h-
      sumBelow (fun k => c k*powerDerivative x k) N) ≤ 2*M*qabs h := by
  have he : (sumBelow (fun k => c k*(x+h)^k) N-sumBelow (fun k => c k*x^k) N)/h-
      sumBelow (fun k => c k*powerDerivative x k) N =
      sumBelow (fun k => c k*(((x+h)^k-x^k)/h-powerDerivative x k)) N := by
    induction N with
    | zero => simp; grind
    | succ n ih => simp only [sumBelow_succ, Rat.div_def] at *; grind
  rw [he]
  apply Rat.le_trans (abs_sumBelow_le _ N)
  have ht (k : Nat) : qabs (c k*(((x+h)^k-x^k)/h-powerDerivative x k)) ≤
      M*qabs h*((1 : Rat)/2)^k := by
    have hpow := qabs_power_differenceQuotient_sub_derivative_le hh
      (by decide : (0 : Rat) ≤ 1) (by decide : (1 : Rat) ≤ 1) hx hxh k
    have h1 := Rat.mul_le_mul_of_nonneg_left hpow (qabs_nonneg (c k))
    have h2 := Rat.mul_le_mul_of_nonneg_right (hc k)
      (Rat.mul_nonneg (qabs_nonneg h) (powerSecantErrorBound_nonneg (by decide : (0 : Rat) ≤ 1) k))
    have h3 := Rat.mul_le_mul_of_nonneg_left (error_unit_bound k)
      (Rat.mul_nonneg (Rat.mul_nonneg hM (Rat.pow_nonneg (n := k) (by decide +kernel : (0 : Rat) ≤ 1/8)))
        (qabs_nonneg h))
    have hp : ((1 : Rat)/8)^k*4^k=((1 : Rat)/2)^k := by
      rw [pow_product, show (1 : Rat)/8*4=1/2 by decide +kernel]
    rw [qabs_mul]
    have hrewrite : M*((1 : Rat)/8)^k*qabs h*4^k = M*qabs h*((1 : Rat)/2)^k := by
      rw [← hp]; grind
    rw [hrewrite] at h3
    grind only
  have hs := sumBelow_le (fun k (_ : k<N) => ht k)
  rw [sumBelow_mul, sum_half] at hs
  have hp := Rat.mul_nonneg (Rat.mul_nonneg hM (qabs_nonneg h))
    (Rat.pow_nonneg (n := N) (by decide +kernel : (0 : Rat) ≤ 1/2))
  grind

theorem geometricRaw_rapid_valid {c : Coeffs} {M x : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/8)^k)
    (hx : qabs x ≤ 1) : (geometricRaw c M x).Valid :=
  geometricRaw_valid hM (by decide +kernel) hc (by grind)

theorem geometricRaw_coefficientShift_valid {c : Coeffs} {M x : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/8)^k)
    (hx : qabs x ≤ 1) : (geometricRaw (coefficientShift c) M x).Valid := by
  apply geometricRaw_valid hM (R := 1/4) (by decide +kernel) ?_ (by grind)
  intro n
  have h := coefficientShift_growth hM (by decide +kernel : (0 : Rat) ≤ 1/8) hc n
  rw [show (2 : Rat)*(1/8)=1/4 by decide +kernel] at h
  have hm : M*(1/8) ≤ M := by grind
  exact Rat.le_trans h (Rat.mul_le_mul_of_nonneg_right hm
    (Rat.pow_nonneg (n := n) (by decide +kernel)))

theorem sumBelow_head (f : Nat → Rat) (n : Nat) :
    sumBelow f (n+1)=f 0+sumBelow (fun k => f (k+1)) n := by
  induction n with
  | zero => rw [show 1=0+1 by rfl, sumBelow_succ]; simp; grind
  | succ n ih => rw [sumBelow_succ, ih, sumBelow_succ]; grind

theorem prefix_derivative_shift (c : Coeffs) (x : Rat) (n : Nat) :
    sumBelow (fun k => c k*powerDerivative x k) (n+1) =
      sumBelow (fun k => coefficientShift c k*x^k) n := by
  rw [sumBelow_head]
  simp only [show powerDerivative x 0=0 by rfl, Rat.mul_zero, Rat.zero_add]
  apply sumBelow_congr
  intro k _
  rw [powerDerivative_succ]
  unfold coefficientShift
  grind

/-- Membership in a computed scalar box, with no chosen real point. -/
def InBox (v : Rat) (I : QInterval) : Prop := I.lo ≤ v ∧ v ≤ I.hi

theorem inBox_distance {v w : Rat} {I : QInterval}
    (hv : InBox v I) (hw : InBox w I) : qabs (v-w) ≤ I.width := by
  apply qabs_le_of_neg_le_le <;> unfold InBox QInterval.width at * <;> grind

/-- A literal finite-stage derivative estimate, before choosing a precision.
Its residual is measured on arbitrary samples from the actual output boxes. -/
theorem geometricRaw_derivative_error {c : Coeffs} {M x h v w d : Rat} {n : Nat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/8)^k)
    (hh : h ≠ 0) (hx : qabs x ≤ 1) (hxh : qabs (x+h) ≤ 1)
    (hv : InBox v ((geometricRaw c M x).compute n))
    (hw : InBox w ((geometricRaw c M (x+h)).compute n))
    (hd : InBox d ((geometricRaw (coefficientShift c) M x).compute n)) :
    qabs (w-v-h*d) ≤ 2*M*qabs h*qabs h+(8*M+4*M*qabs h)*((1 : Rat)/2)^n := by
  let P := fun t => sumBelow (fun k => c k*t^k) (n+1)
  let D := sumBelow (fun k => coefficientShift c k*x^k) n
  have hsample (t z : Rat) (ht : qabs t ≤ 1)
      (hz : InBox z ((geometricRaw c M t).compute n)) :
      qabs (z-P t) ≤ 4*M*((1 : Rat)/2)^n := by
    have hm := geometricRaw_contains_prefix hM (by decide +kernel : (0 : Rat) ≤ 1/8)
      hc (x := t) (by grind) (Nat.le_succ n)
    have he := inBox_distance hz hm
    rw [geometricRaw_width] at he
    exact he
  have hv' := hsample x v hx hv
  have hw' := hsample (x+h) w hxh hw
  have hd' : qabs (d-D) ≤ 4*M*((1 : Rat)/2)^n := by
    have hcenter : InBox D ((geometricRaw (coefficientShift c) M x).compute n) := by
      have ht := Rat.mul_nonneg (show 0 ≤ 2*M by grind)
        (Rat.pow_nonneg (n := n) (by decide +kernel : (0 : Rat) ≤ 1/2))
      unfold InBox geometricRaw
      change _ ≤ D ∧ D ≤ _
      dsimp [D] at *
      grind
    have he := inBox_distance hd hcenter
    rwa [geometricRaw_width] at he
  have hs := prefix_secant_bound hM hc hh hx hxh (n+1)
  rw [prefix_derivative_shift] at hs
  change qabs ((P (x+h)-P x)/h-D) ≤ 2*M*qabs h at hs
  have hm := Rat.mul_le_mul_of_nonneg_left hs (qabs_nonneg h)
  rw [← qabs_mul] at hm
  have he : h*((P (x+h)-P x)/h-D)=P (x+h)-P x-h*D := by
    have := mul_div_cancel_left (a := h) (b := P (x+h)-P x) hh
    grind
  rw [he] at hm
  have hde := Rat.mul_le_mul_of_nonneg_left hd' (qabs_nonneg h)
  rw [← qabs_mul] at hde
  have h1 := qabs_sub_le (w-P (x+h)) (v-P x)
  have h2 := qabs_sub_le ((w-P (x+h))-(v-P x)) (h*(d-D))
  have h3 := qabs_add_le (((w-P (x+h))-(v-P x))-h*(d-D)) (P (x+h)-P x-h*D)
  have hid : (((w-P (x+h))-(v-P x))-h*(d-D))+(P (x+h)-P x-h*D) = w-v-h*d := by grind
  rw [hid] at h3
  grind only

/-- Positive derivative step size, computed directly from the requested error. -/
def derivativeRadius (M : Rat) (hM : 0 ≤ M) (eps : QPos) : QPos :=
  ⟨eps.val/(4*(M+1)), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))⟩

def derivativeStage (M : Rat) (eps : QPos) (h : Rat) : Nat :=
  if hh : h ≠ 0 then RationalMajorant.halfDecayShift (8*M+4*M*qabs h)
    ⟨eps.val*qabs h/2, by
      rw [Rat.div_def]
      exact Rat.mul_pos (Rat.mul_pos eps.property (qabs_pos_of_ne hh))
        (Rat.inv_pos.mpr (by decide))⟩ else 0

/-- The boxed series has a genuine effective derivative on the unit interval.
All radii and precision stages are executable rational computations. -/
theorem geometricRaw_hasBoxDerivative {c : Coeffs} {M x h v w d : Rat}
    (hM : 0 ≤ M) (hc : ∀ k, qabs (c k) ≤ M*((1 : Rat)/8)^k)
    (eps : QPos) {n : Nat} (hh : h ≠ 0)
    (hx : qabs x ≤ 1) (hxh : qabs (x+h) ≤ 1)
    (hsmall : qabs h ≤ (derivativeRadius M hM eps).val)
    (hn : derivativeStage M eps h ≤ n)
    (hv : InBox v ((geometricRaw c M x).compute n))
    (hw : InBox w ((geometricRaw c M (x+h)).compute n))
    (hd : InBox d ((geometricRaw (coefficientShift c) M x).compute n)) :
    qabs (w-v-h*d) ≤ eps.val*qabs h := by
  have he := geometricRaw_derivative_error hM hc hh hx hxh hv hw hd
  have hC : 0 ≤ 8*M+4*M*qabs h := by
    have := Rat.mul_nonneg hM (qabs_nonneg h)
    grind
  let tol : QPos := ⟨eps.val*qabs h/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos (Rat.mul_pos eps.property (qabs_pos_of_ne hh))
      (Rat.inv_pos.mpr (by decide))⟩
  have ht := RationalMajorant.halfDecayShift_spec hC tol
  have hn' : RationalMajorant.halfDecayShift (8*M+4*M*qabs h) tol ≤ n := by
    simpa only [derivativeStage, dif_pos hh] using hn
  have hp := Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hn') hC
  have hb : (8*M+4*M*qabs h)*((1 : Rat)/2)^n ≤ eps.val*qabs h/2 :=
    Rat.le_trans hp ht
  have hcancel : (4*(M+1))*(derivativeRadius M hM eps).val=eps.val :=
    mul_div_cancel_left (by grind : 4*(M+1) ≠ 0)
  have hs := Rat.mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4*(M+1) by grind)
  rw [hcancel] at hs
  have hs' := Rat.mul_le_mul_of_nonneg_right hs (qabs_nonneg h)
  have hsq := Rat.mul_nonneg (qabs_nonneg h) (qabs_nonneg h)
  clear hc hv hw hd hn hn' ht hp hsmall
  grind only

end ComputableAnalysis.FormalPowerSeries
