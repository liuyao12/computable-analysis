import ComputableAnalysis.FinitePolynomialCalculus

/-!
# Integral order from quantitative finite differences

A secant certificate gives exact integral order by finite midpoint subdivision.
The error is divided by two at each subdivision. Rational separation and an
explicit shrinking bound remove the error; no completed real is used.
-/
namespace ComputableAnalysis
namespace FinitePolynomial
namespace SecantDerivativeBound

private theorem lower_dyadic {F f : Rat → Rat}
    (D : SecantDerivativeBound 1 F f) (n : Nat) {p r c : Rat}
    (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (hc : ∀ x, p ≤ x → x ≤ r → c ≤ f x) :
    (r-p)*c - (r-p)*(r-p)*D.errorCoefficient*((1:Rat)/2)^n ≤ F r-F p := by
  induction n generalizing p r with
  | zero =>
      by_cases heq : p = r
      · subst r; grind
      have hd : 0 < r-p := by grind
      have h := D.error_bound p (r-p) (Rat.ne_of_gt hd)
        (by rw [qabs_eq_self_of_nonneg hp]; grind)
        (by rw [show p+(r-p)=r by grind, qabs_eq_self_of_nonneg (by grind)]; exact hr)
      rw [show p+(r-p)=r by grind, qabs_eq_self_of_nonneg (Rat.le_of_lt hd)] at h
      have hneg := neg_qabs_le_self (((F r-F p)/(r-p))-f p)
      have hl : f p - (F r-F p)/(r-p) ≤ (r-p)*D.errorCoefficient := by grind
      have hm := Rat.mul_le_mul_of_nonneg_right hl (Rat.le_of_lt hd)
      have hcancel := Rat.inv_mul_cancel (r-p) (Rat.ne_of_gt hd)
      have hcp := hc p (Rat.le_refl) hpr
      have hcm := Rat.mul_le_mul_of_nonneg_left hcp (Rat.le_of_lt hd)
      simp only [Rat.pow_zero, Rat.mul_one]
      have he : (f p - (F r-F p)/(r-p))*(r-p) =
          (r-p)*f p - (F r-F p) := by
        simp only [Rat.div_def, Rat.sub_eq_add_neg, Rat.add_mul,
          Rat.neg_mul, Rat.mul_assoc]
        grind [Rat.mul_comm]
      rw [he] at hm
      have he2 : (r-p)*D.errorCoefficient*(r-p) =
          (r-p)*(r-p)*D.errorCoefficient := by grind
      rw [he2] at hm
      grind
  | succ n ih =>
      have hmid0 : 0 ≤ (p+r)/2 := by grind
      have hpm : p ≤ (p+r)/2 := by grind
      have hmr : (p+r)/2 ≤ r := by grind
      have hmid1 : (p+r)/2 ≤ 1 := by grind
      have hl := ih hp hpm hmid1 (fun x hx hy => hc x hx (Rat.le_trans hy hmr))
      have hu := ih hmid0 hmr hr (fun x hx hy => hc x (Rat.le_trans hpm hx) hy)
      rw [Rat.pow_succ]
      grind

/-- Integrating a pointwise lower bound using finite secant error estimates. -/
theorem integral_lower {F f : Rat → Rat}
    (D : SecantDerivativeBound 1 F f) {p r c : Rat}
    (hp : 0 ≤ p) (hpr : p ≤ r) (hr : r ≤ 1)
    (hc : ∀ x, p ≤ x → x ≤ r → c ≤ f x) :
    (r-p)*c ≤ F r-F p := by
  let E := (r-p)*(r-p)*D.errorCoefficient
  have hE : 0 ≤ E := Rat.mul_nonneg
    (Rat.mul_nonneg (by grind) (by grind)) D.errorCoefficient_nonneg
  by_cases hgoal : (r-p)*c ≤ F r-F p
  · exact hgoal
  have hnot := hgoal
  have hgap : 0 < ((r-p)*c - (F r-F p))/2 := by grind
  let eps : QPos := ⟨_, hgap⟩
  let N := RationalMajorant.halfDecayShift E eps
  have he := RationalMajorant.halfDecayShift_spec hE eps
  have hb := lower_dyadic D N hp hpr hr hc
  change E*((1:Rat)/2)^N ≤ ((r-p)*c - (F r-F p))/2 at he
  dsimp [E] at he
  grind

/-- Exact cell-order preservation for every quantitative primitive certificate. -/
theorem exactCellOrder {F f : Rat → Rat} (D : SecantDerivativeBound 1 F f) :
    Integral.ExactCellOrderPreservation f (fun p r => F r-F p) 0 1 := by
  constructor
  · intro p r c hp hpr hr hc
    exact D.integral_lower hp hpr hr (fun x hx hy => hc hx hy)
  · intro p r c hp hpr hr hc
    have h := (D.scaleRat (-1)).integral_lower (c := -c) hp hpr hr
      (fun x hx hy => by have := hc hx hy; grind)
    grind

end SecantDerivativeBound
end FinitePolynomial
end ComputableAnalysis
