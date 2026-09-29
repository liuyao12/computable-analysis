import ComputableAnalysis.PowerImproperAtZero
import ComputableAnalysis.ReciprocalPolynomialIntegral

/-! Reciprocal-power integrals on the positive half-line above one. The
reciprocal chart is justified first for finite polynomials, then by uniform
rational bounds for arbitrary represented exponents. -/
namespace ComputableAnalysis.PowerIntegral
open FormalPowerSeries ZetaReal Integral FinitePolynomial BinomialPower BinomialPower.Global

/-- The independent reciprocal chart for `x^(-p)` on `1 ≤ x`:
`x^(-2) (1-(1-1/x))^(p-2)`. -/
def infinityValue (p : Real) (x : Rat) : RealRaw :=
  RealRaw.scaleRat (x⁻¹*x⁻¹) (canonicalValue p (1-x⁻¹))

theorem infinityValue_valid (p : Real) {x : Rat} (hx : 1 ≤ x) : (infinityValue p x).Valid := by
  have hi := inverse_unit_bounds hx
  exact RealRaw.scaleRat_valid (canonicalValue_valid p (by grind) (by grind))

def infinityFunction (p : Real) (a b : Rat) (ha : 1 ≤ a) : FunctionOnInterval :=
  onInterval (infinityValue p) a b (fun x hx => infinityValue_valid p (Rat.le_trans ha hx.1))

def infinityCompact (p : Real) (a b : Rat) (ha : 1 ≤ a) (hab : a ≤ b) : RealRaw :=
  canonicalIntegral p (1-a⁻¹) (1-b⁻¹)
    (by have := inverse_unit_bounds ha; grind)
    (by have := inverse_gap ha hab; grind)
    (by have := inverse_unit_bounds (Rat.le_trans ha hab); grind)

private theorem scale_within {X : RealRaw} {v e r : Rat}
    (h : Within X (RealRaw.ofRat v) e) (hr : 0 ≤ r) (hr1 : r ≤ 1) (he : 0 ≤ e) :
    Within (RealRaw.scaleRat r X) (RealRaw.ofRat (r*v)) e := by
  intro i j
  have hh := h i j
  have h1 := Rat.mul_le_mul_of_nonneg_left hh.1 hr
  have h2 := Rat.mul_le_mul_of_nonneg_left hh.2 hr
  have h3 := Rat.mul_le_mul_of_nonneg_right hr1 he
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
  change r*(X.compute i).lo ≤ r*v+e ∧ r*v ≤ r*(X.compute i).hi+e
  change r*(X.compute i).lo ≤ r*(v+e) at h1
  change r*v ≤ r*((X.compute i).hi+e) at h2
  constructor <;> grind only

/-- Constructed compact witnesses for every represented exponent, with no
assumed substitution or improper-limit law. -/
theorem infinityCompact_hasIntegral (p : Real) {a b : Rat} (ha : 1 ≤ a) (hab : a ≤ b) :
    HasIntegral (infinityFunction p a b ha) (infinityCompact p a b ha hab) := by
  have hai := inverse_unit_bounds ha
  have hbi := inverse_unit_bounds (Rat.le_trans ha hab)
  have habi := inverse_gap ha hab
  let A := chart p (1-b⁻¹) (by grind) (by grind)
  have hp := chart_bounds p (1-b⁻¹) (by grind) (by grind)
  have hv := A.integral_valid hp (show 0 ≤ 1-a⁻¹ by grind)
    (show 1-a⁻¹ ≤ 1-b⁻¹ by grind) (Rat.le_refl)
  apply hasIntegral_of_uniform_approximation
    (g := fun n x => RealRaw.ofRat (x⁻¹*x⁻¹*taylorDerivativePrefix (coefficient (A.parameter p n)) (A.cutoff n) (1-x⁻¹)))
    (hg := fun _ _ _ => RealRaw.ofRat_valid _)
    (J := fun n => RealRaw.ofRat (A.integralPolynomial p (1-a⁻¹) (1-b⁻¹) n))
    (e := fun n => 2*((1 : Rat)/2)^n) hab hv
  · intro n
    exact (reciprocal_polynomial_hasIntegral (coefficient (A.parameter p n)) (A.cutoff n) ha hab).exactRat_onInterval
  · exact GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 2)
  · intro n x hx
    have hxi := inverse_unit_bounds (Rat.le_trans ha hx.1)
    have hxb := inverse_gap (Rat.le_trans ha hx.1) hx.2
    have hx0 : 0 ≤ 1-x⁻¹ := by grind
    have hxA : 1-x⁻¹ ≤ A.radius := by change 1-x⁻¹ ≤ 1-b⁻¹; grind
    have hraw := A.value_valid hp hx0 hxA
    have hnear := (GeometricSequence.raw_within hraw n).congr_left
      (canonicalValue_valid p hx0 (by grind)) hraw (canonicalValue_agrees A hp hx0 hxA)
    have hs := scale_within hnear (Rat.mul_nonneg (Rat.le_of_lt hxi.1) (Rat.le_of_lt hxi.1))
      (show x⁻¹*x⁻¹ ≤ 1 by
        have h := Rat.mul_le_mul_of_nonneg_left hxi.2 (Rat.le_of_lt hxi.1)
        grind only)
      (show 0 ≤ 2*((1 : Rat)/2)^n by have := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := n); grind)
    change Within (infinityValue p x) (RealRaw.ofRat (x⁻¹*x⁻¹*powerPolynomial (A.parameter p n) (A.cutoff n) (1-x⁻¹))) _ at hs
    unfold powerPolynomial at hs
    rw [polynomial_prefix] at hs
    exact hs
  · intro n
    exact GeometricSequence.raw_within hv n

def infinityEndpoint (p : Real) (x : Rat) : RealRaw := canonicalValue (shiftParameter p) (1-x⁻¹)

theorem infinityCompact_closedForm (p : Real) {a b : Rat} (ha : 1 ≤ a) (hab : a ≤ b) :
    (RealRaw.mul (RealRaw.sub p.preferred (RealRaw.ofRat 1)) (infinityCompact p a b ha hab)).Equiv
      (RealRaw.sub (infinityEndpoint p a) (infinityEndpoint p b)) :=
  canonicalIntegral_closedForm p
    (by have := inverse_unit_bounds ha; grind) (by have := inverse_gap ha hab; grind)
    (by have := inverse_unit_bounds (Rat.le_trans ha hab); grind)

def infinityIntegral (p : Real) (hp : AboveOne p) : RealRaw := endpointTotal p hp

def infinityCutoff (p : Real) (j : Nat) : Rat := (endpointCutoff (endpointM p) j)⁻¹

theorem infinityCutoff_ge (p : Real) (j : Nat) : 1 ≤ infinityCutoff p j := by
  have ha := endpointCutoff_bounds (endpointM p) j
  have h := IntegerPowerIntegral.inverse_antitone ha.1 ha.2
  rw [show (1 : Rat)⁻¹=1 by decide +kernel] at h
  exact h

def infinityExhaustion (p : Real) (j : Nat) : FunctionOnInterval :=
  infinityFunction p 1 (infinityCutoff p j) (Rat.le_refl)

theorem infinity_compact (p : Real) (j : Nat) :
    HasIntegral (infinityExhaustion p j)
      (infinityCompact p 1 (infinityCutoff p j) (Rat.le_refl) (infinityCutoff_ge p j)) :=
  infinityCompact_hasIntegral p (Rat.le_refl) (infinityCutoff_ge p j)

theorem infinity_tail (p : Real) (hp : AboveOne p) (j : Nat) :
    Within (infinityIntegral p hp)
      (infinityCompact p 1 (infinityCutoff p j) (Rat.le_refl) (infinityCutoff_ge p j))
      (endpointError (endpointQ p hp) (endpointM p) j) := by
  have h := endpointTotal_within p hp j
  simpa only [infinityIntegral,infinityCompact,infinityCutoff,show (1 : Rat)⁻¹=1 by decide +kernel,
    show (1 : Rat)-1=0 by decide +kernel,Rat.inv_inv] using h

/-- Exact improper integral `1/(p-1)` on the supplied exhaustion of `[1,∞)`. -/
theorem infinity_hasIntegralLimit (p : Real) (hp : AboveOne p) :
    HasIntegralLimit (infinityExhaustion p) (infinityIntegral p hp) := by
  refine ⟨endpointTotal_valid p hp,fun j => ⟨_,infinity_compact p j⟩,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := endpointError_shrinks (endpointQ p hp) (endpointM p) eps
  refine ⟨N,fun j hj J hJ => ?_⟩
  have hc := infinity_compact p j
  have h := ((infinity_tail p hp j).symm.congr_left hJ.valid hc.valid (hJ.unique hc)).symm
  have he := hN j hj
  intro n m
  have hh := h n m
  constructor <;> grind only

/-- The finite upper endpoints eventually exceed any supplied positive bound. -/
theorem infinity_exhausts (p : Real) (R : QPos) :
    ∃ N, ∀ n, N ≤ n → R.val ≤ infinityCutoff p n := by
  let e : QPos := ⟨R.val⁻¹,Rat.inv_pos.mpr R.property⟩
  obtain ⟨N,hN⟩ := endpointCutoff_shrinks (endpointM p) e
  refine ⟨N,fun n hn => ?_⟩
  have h := IntegerPowerIntegral.inverse_antitone (endpointCutoff_bounds (endpointM p) n).1 (hN n hn)
  change (R.val⁻¹)⁻¹ ≤ _ at h
  rw [Rat.inv_inv] at h
  exact h

theorem infinityValue_equiv {p q : Real} (heq : p.Equiv q) {x : Rat} (hx : 1 ≤ x) :
    (infinityValue p x).Equiv (infinityValue q x) := by
  have hi := inverse_unit_bounds hx
  exact RealRaw.scaleRat_equiv (canonicalValue_equiv heq (by grind) (by grind))

theorem infinityIntegral_equiv {p q : Real} (hp : AboveOne p) (hq : AboveOne q) (heq : p.Equiv q) :
    (infinityIntegral p hp).Equiv (infinityIntegral q hq) := by
  apply RealRaw.positiveInv_equiv_names (RealRaw.sub_valid p.valid (RealRaw.ofRat_valid 1))
    (RealRaw.sub_valid q.valid (RealRaw.ofRat_valid 1))
    (RealRaw.sub_equiv p.valid q.valid (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 1)
      heq (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1)))
  · change 0 < (p.compute (separationStage p hp)).lo-1
    have := separationStage_spec p hp
    grind only
  · change 0 < (q.compute (separationStage q hq)).lo-1
    have := separationStage_spec q hq
    grind only

end ComputableAnalysis.PowerIntegral
