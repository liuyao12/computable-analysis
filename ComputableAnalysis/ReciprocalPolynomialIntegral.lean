import ComputableAnalysis.LocalIntegralOrder
import ComputableAnalysis.PolynomialIntegralWitness
import ComputableAnalysis.LipschitzRectangleBounds

/-! Reciprocal substitution for finite polynomial integrals, proved directly
on the positive segment by local rational error estimates. -/
namespace ComputableAnalysis.FormalPowerSeries
open Integral FinitePolynomial

theorem inverse_unit_bounds {x : Rat} (hx : 1 ≤ x) : 0 < x⁻¹ ∧ x⁻¹ ≤ 1 := by
  have hp : 0 < x := by grind
  have h := IntegerPowerIntegral.inverse_antitone (a := 1) (by decide) hx
  have h1 : (1 : Rat)⁻¹=1 := by decide +kernel
  rw [h1] at h
  exact ⟨Rat.inv_pos.mpr hp,h⟩

theorem inverse_gap {u v : Rat} (hu : 1 ≤ u) (huv : u ≤ v) :
    u⁻¹-v⁻¹=(v-u)*u⁻¹*v⁻¹ ∧ 0 ≤ u⁻¹-v⁻¹ ∧ u⁻¹-v⁻¹ ≤ v-u := by
  have hu' := inverse_unit_bounds hu
  have hv' := inverse_unit_bounds (Rat.le_trans hu huv)
  have hcu := Rat.mul_inv_cancel u (by grind)
  have hcv := Rat.mul_inv_cancel v (by grind)
  have he : u⁻¹-v⁻¹=(v-u)*u⁻¹*v⁻¹ := by grind only
  have hnon := Rat.mul_nonneg (Rat.mul_nonneg (show 0 ≤ v-u by grind) (Rat.le_of_lt hu'.1)) (Rat.le_of_lt hv'.1)
  have h1 := Rat.mul_le_mul_of_nonneg_left hu'.2 (show 0 ≤ v-u by grind)
  have h2 := Rat.mul_le_mul_of_nonneg_left hv'.2
    (Rat.mul_nonneg (show 0 ≤ v-u by grind) (Rat.le_of_lt hu'.1))
  exact ⟨he,by grind only,by grind only⟩

theorem secant_local_error {F f : Rat → Rat} (D : SecantDerivativeBound 1 F f)
    {y z : Rat} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z ≤ 1) :
    qabs (F z-F y-(z-y)*f y) ≤ (z-y)*(z-y)*D.errorCoefficient := by
  by_cases he : y=z
  · subst z
    have hid : F y-F y-(y-y)*f y=0 := by grind only
    rw [hid,qabs_eq_self_of_nonneg (by decide : (0 : Rat) ≤ 0)]
    grind only
  have hd : 0 < z-y := by grind
  have h := D.error_bound y (z-y) (Rat.ne_of_gt hd)
    (by rw [qabs_eq_self_of_nonneg hy]; grind)
    (by rw [show y+(z-y)=z by grind only,qabs_eq_self_of_nonneg (by grind : 0 ≤ z)]; exact hz)
  rw [show y+(z-y)=z by grind only,qabs_eq_self_of_nonneg (Rat.le_of_lt hd)] at h
  have hm := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hd)
  have hi := Rat.inv_mul_cancel (z-y) (Rat.ne_of_gt hd)
  have hid : ((F z-F y)/(z-y)-f y)*(z-y)=F z-F y-(z-y)*f y := by
    rw [Rat.div_def,Rat.sub_eq_add_neg,Rat.add_mul,Rat.mul_assoc,hi,Rat.mul_one]
    grind only
  have habs := congrArg qabs hid
  rw [qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hd)] at habs
  grind only

/-- Local error for `J(1-1/x)` with derivative `P(1-1/x)/x²`. -/
theorem reciprocal_local_error {F f : Rat → Rat} (D : SecantDerivativeBound 1 F f)
    {B u v : Rat} (hB : 0 ≤ B) (hf : ∀ y, 0 ≤ y → y ≤ 1 → qabs (f y) ≤ B)
    (hu : 1 ≤ u) (huv : u ≤ v) :
    qabs (F (1-v⁻¹)-F (1-u⁻¹)-(v-u)*(u⁻¹*u⁻¹*f (1-u⁻¹))) ≤
      (v-u)*(v-u)*(D.errorCoefficient+B) := by
  have hui := inverse_unit_bounds hu
  have hvi := inverse_unit_bounds (Rat.le_trans hu huv)
  have hg := inverse_gap hu huv
  have hy : 0 ≤ 1-u⁻¹ := by grind
  have hz : 1-v⁻¹ ≤ 1 := by grind
  have he := secant_local_error D hy (show 1-u⁻¹ ≤ 1-v⁻¹ by grind) hz
  have hbound := hf (1-u⁻¹) hy (by grind)
  have hd : 0 ≤ v-u := by grind
  have hprod := Rat.mul_nonneg (Rat.le_of_lt hui.1) (Rat.le_of_lt hui.1)
  have hp1 := Rat.mul_le_mul_of_nonneg_left hui.2 (Rat.le_of_lt hui.1)
  have hp2 : u⁻¹*u⁻¹*v⁻¹ ≤ 1 := by
    have h := Rat.mul_le_mul_of_nonneg_left hvi.2 hprod
    grind only
  have hc : 0 ≤ (v-u)*(v-u)*u⁻¹*u⁻¹*v⁻¹ :=
    Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg hd hd) (Rat.le_of_lt hui.1))
      (Rat.le_of_lt hui.1)) (Rat.le_of_lt hvi.1)
  have hb1 := Rat.mul_le_mul_of_nonneg_left hbound hc
  have hb2 := Rat.mul_le_mul_of_nonneg_left hp2 (Rat.mul_nonneg (Rat.mul_nonneg hd hd) hB)
  have herr : qabs ((v-u)*(v-u)*u⁻¹*u⁻¹*v⁻¹*f (1-u⁻¹)) ≤ (v-u)*(v-u)*B := by
    rw [qabs_mul,qabs_eq_self_of_nonneg hc]
    grind only
  have hsq1 := Rat.mul_le_mul_of_nonneg_left hg.2.2 hg.2.1
  have hsq2 := Rat.mul_le_mul_of_nonneg_right hg.2.2 hd
  have hsq : (u⁻¹-v⁻¹)*(u⁻¹-v⁻¹) ≤ (v-u)*(v-u) := by grind only
  have hsqE := Rat.mul_le_mul_of_nonneg_right hsq D.errorCoefficient_nonneg
  have hid : F (1-v⁻¹)-F (1-u⁻¹)-(v-u)*(u⁻¹*u⁻¹*f (1-u⁻¹)) =
      (F (1-v⁻¹)-F (1-u⁻¹)-((1-v⁻¹)-(1-u⁻¹))*f (1-u⁻¹))-
        (v-u)*(v-u)*u⁻¹*u⁻¹*v⁻¹*f (1-u⁻¹) := by
    have hcu := Rat.mul_inv_cancel u (by grind)
    have hcv := Rat.mul_inv_cancel v (by grind)
    grind only
  rw [hid]
  have htri := qabs_sub_le (F (1-v⁻¹)-F (1-u⁻¹)-((1-v⁻¹)-(1-u⁻¹))*f (1-u⁻¹))
    ((v-u)*(v-u)*u⁻¹*u⁻¹*v⁻¹*f (1-u⁻¹))
  rw [show (1-v⁻¹)-(1-u⁻¹)=u⁻¹-v⁻¹ by grind only] at he
  grind only

/-- A finite polynomial bound on the unit interval. -/
def polynomialBound (c : Coeffs) (K : Nat) : Rat := sumBelow (fun k => qabs (c k)) K

theorem polynomialBound_nonneg (c : Coeffs) (K : Nat) : 0 ≤ polynomialBound c K := by
  induction K with
  | zero => exact Rat.le_refl
  | succ K ih =>
    unfold polynomialBound at *
    rw [sumBelow_succ]
    have := qabs_nonneg (c K)
    grind only

theorem polynomial_unit_bound (c : Coeffs) (K : Nat) {x : Rat} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    qabs (taylorDerivativePrefix c K x) ≤ polynomialBound c K := by
  rw [← polynomial_prefix]
  apply Rat.le_trans (abs_sumBelow_le _ K)
  apply sumBelow_le
  intro k _
  have hp := Rat.pow_nonneg hx (n := k)
  have unit (j : Nat) : x^j ≤ 1 := by
    induction j with
    | zero => rw [Rat.pow_zero]; exact Rat.le_refl
    | succ j ih =>
      rw [Rat.pow_succ]
      have h := Rat.mul_le_mul_of_nonneg_right ih hx
      grind only
  have hp1 := unit k
  rw [qabs_mul,qabs_eq_self_of_nonneg hp]
  have h := Rat.mul_le_mul_of_nonneg_left hp1 (qabs_nonneg (c k))
  grind only

theorem reciprocal_lipschitz {f : Rat → Rat} {B L u v : Rat} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hf : ∀ y, 0 ≤ y → y ≤ 1 → qabs (f y) ≤ B)
    (hlip : ∀ y z, 0 ≤ y → y ≤ z → z ≤ 1 → qabs (f z-f y) ≤ L*(z-y))
    (hu : 1 ≤ u) (huv : u ≤ v) :
    qabs (v⁻¹*v⁻¹*f (1-v⁻¹)-u⁻¹*u⁻¹*f (1-u⁻¹)) ≤ (L+2*B)*(v-u) := by
  have hui := inverse_unit_bounds hu
  have hvi := inverse_unit_bounds (Rat.le_trans hu huv)
  have hg := inverse_gap hu huv
  have hl := hlip (1-u⁻¹) (1-v⁻¹) (by grind) (by grind) (by grind)
  have hb := hf (1-u⁻¹) (by grind) (by grind)
  have hd : 0 ≤ v-u := by grind
  have hvsq := Rat.mul_nonneg (Rat.le_of_lt hvi.1) (Rat.le_of_lt hvi.1)
  have hv1 := Rat.mul_le_mul_of_nonneg_left hvi.2 (Rat.le_of_lt hvi.1)
  have h1 := Rat.mul_le_mul_of_nonneg_left hg.2.2 hL
  have h2 := Rat.mul_le_mul_of_nonneg_left hl hvsq
  have h3 := Rat.mul_le_mul_of_nonneg_right (show v⁻¹*v⁻¹ ≤ 1 by grind) (Rat.mul_nonneg hL hd)
  have hs0 := Rat.mul_nonneg hg.2.1 (show 0 ≤ u⁻¹+v⁻¹ by grind)
  have hs1 := Rat.mul_le_mul_of_nonneg_right hg.2.2 (show 0 ≤ u⁻¹+v⁻¹ by grind)
  have hs2 := Rat.mul_le_mul_of_nonneg_left (show u⁻¹+v⁻¹ ≤ 2 by grind) hd
  have hs : 0 ≤ u⁻¹*u⁻¹-v⁻¹*v⁻¹ ∧ u⁻¹*u⁻¹-v⁻¹*v⁻¹ ≤ 2*(v-u) := by grind only
  have h4 := Rat.mul_le_mul_of_nonneg_left hb hs.1
  have h5 := Rat.mul_le_mul_of_nonneg_right hs.2 hB
  have hid : v⁻¹*v⁻¹*f (1-v⁻¹)-u⁻¹*u⁻¹*f (1-u⁻¹)=
      v⁻¹*v⁻¹*(f (1-v⁻¹)-f (1-u⁻¹))-(u⁻¹*u⁻¹-v⁻¹*v⁻¹)*f (1-u⁻¹) := by grind only
  rw [hid]
  have ht := qabs_sub_le (v⁻¹*v⁻¹*(f (1-v⁻¹)-f (1-u⁻¹))) ((u⁻¹*u⁻¹-v⁻¹*v⁻¹)*f (1-u⁻¹))
  simp only [qabs_mul,qabs_eq_self_of_nonneg (Rat.le_of_lt hvi.1),qabs_eq_self_of_nonneg hs.1] at ht
  rw [show (1-v⁻¹)-(1-u⁻¹)=u⁻¹-v⁻¹ by grind only] at hl h2
  have h6 := Rat.mul_le_mul_of_nonneg_left h1 hvsq
  grind only

/-- Actual compact rational-function integrals obtained by reciprocal
substitution, including the whole segment's domain evidence. -/
theorem reciprocal_polynomial_hasIntegral (c : Coeffs) (K : Nat) {a b : Rat}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    HasIntegral (FunctionOnInterval.exactRat (fun x => x⁻¹*x⁻¹*taylorDerivativePrefix c K (1-x⁻¹)) a b)
      (RealRaw.ofRat (integratedTaylorPrefix c K (1-b⁻¹)-integratedTaylorPrefix c K (1-a⁻¹))) := by
  let D := integratedTaylorPrefixSecantBound 1 c (by decide) K
  have hB := polynomialBound_nonneg c K
  have hL := polynomialLip_nonneg c K
  have horder := exactCellOrder_of_local_error (a := a) (b := b)
    (F := fun x => integratedTaylorPrefix c K (1-x⁻¹))
    (f := fun x => x⁻¹*x⁻¹*taylorDerivativePrefix c K (1-x⁻¹))
    (E := D.errorCoefficient+polynomialBound c K)
    (by have := D.errorCoefficient_nonneg; grind)
    (fun u v hu huv _ => reciprocal_local_error D hB (fun _ hx hx1 => polynomial_unit_bound c K hx hx1)
      (Rat.le_trans ha hu) huv)
  apply horder.hasIntegral
  apply lipschitz_tight _ a b (polynomialLip c K+2*polynomialBound c K) hab (by grind)
  intro u v hau huv _
  apply reciprocal_lipschitz hB hL (fun _ hx hx1 => polynomial_unit_bound c K hx hx1)
    (fun y z hy hyz hz => ?_) (Rat.le_trans ha hau) huv
  simpa only [polynomial_prefix] using polynomial_lipschitz c K hy hyz hz

end ComputableAnalysis.FormalPowerSeries
