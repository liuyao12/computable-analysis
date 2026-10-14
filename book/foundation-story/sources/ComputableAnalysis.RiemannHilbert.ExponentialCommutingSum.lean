import ComputableAnalysis.RiemannHilbert.ExponentialAddition

/-! The exponential of a sum of commuting represented operators. The
constructed product has a proved uniform ODE remainder, and global
constant-ODE uniqueness compares it with the independent entire series. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}
set_option maxHeartbeats 2000000

def sumResidue (A B : ValueMap (Fiber n) (Fiber n)) := ValueMap.sum A B

theorem sumResidue_linear (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) :
    IsLinear (sumResidue A B) := ValueMap.sum_linear A B hA hB

theorem values_commute_of_residues (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (z w : Scalar) (x : Fiber n) :
    (value A hA z).eval ((value B hB w).eval x) ≈ (value B hB w).eval ((value A hA z).eval x) :=
  Setoid.symm (value_intertwines A hA A hA (value B hB w) (value_linear B hB w)
    (fun y => Setoid.symm (value_intertwines B hB B hB A hA hAB w y)) z x)

def commutingProductField (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (R : QPos) :=
  composeFields (discField B hB R) (discField A hA R) (fun _ hz => hz)

def commutingProductSlope (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B) (R : QPos) :=
  compositionSlope (discField B hB R) (discSlope B hB R) (discField A hA R) (discSlope A hA R) (fun _ hz => hz)

theorem commutingProductSlope_ode (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (R : QPos) (z : Scalar) (hz : interior R.val z) :
    (commutingProductSlope A B hA hB R z hz).Equiv
      ((commutingProductField A B hA hB R z hz).followedBy (sumResidue A B)) := by
  intro x
  exact Fiber.add_congr (Setoid.refl _)
    (Setoid.symm (value_intertwines A hA A hA B hB (fun y => Setoid.symm (hAB y)) z ((value B hB z).eval x)))

def commutingProductDelta (A B : ValueMap (Fiber n) (Fiber n)) (R : QPos) : QPos → QPos :=
  productDelta (discValueBound A R) (discDerivativeBound A R) (discValueBound B R) (discDerivativeBound B R)
    (discValueBound_nonneg A R) (discDerivativeBound_nonneg A R)
    (discValueBound_nonneg B R) (discDerivativeBound_nonneg B R) (discDelta B R) (discDelta A R)

theorem commutingProduct_uniform_remainder (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (R : QPos)
    (eps H : QPos) (w z : Scalar) (hw : interior R.val w) (hz : interior R.val z)
    (hH : H.val ≤ (commutingProductDelta A B R eps).val) (hzw : Small (sub z.val w.val) H.val)
    (C : Rat) (hC : 0 ≤ C) (x : Fiber n) (hx : CoordinateBound x C) :
    CoordinateBound (UniformSegment.remainder (fun _ _ => sumResidue A B)
      (fun v hv => (commutingProductField A B hA hB R v hv).eval x) w z hw hz) ((eps.val*H.val)*C) := by
  have hs := compose_uniform_remainder (discField B hB R) (discSlope B hB R)
    (discField A hA R) (discSlope A hA R) (fun z _ => value_linear A hA z)
    (discValueBound A R) (discDerivativeBound A R) (discValueBound B R) (discDerivativeBound B R)
    (discValueBound_nonneg A R) (discDerivativeBound_nonneg A R)
    (discValueBound_nonneg B R) (discDerivativeBound_nonneg B R)
    (discField_bound A hA R) (discSlope_bound A hA R)
    (discField_bound B hB R) (discSlope_bound B hB R)
    (discDelta B R) (discDelta A R) (disc_uniform_remainder B hB R) (disc_uniform_remainder A hA R)
    eps H w z hw hz hH hzw C hC x hx
  exact bound_congr (Fiber.sub_congr (Setoid.refl _)
    (Fiber.scale_congr (equiv_refl _ (sub_valid z.property w.property))
      (commutingProductSlope_ode A B hA hB hAB R w hw x))) hs

/-- The independent entire evaluators obey the commuting-residue sum law
at every represented parameter, with no operator smallness restriction. -/
theorem value_commuting_sum (A B : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A) (hB : IsLinear B)
    (hAB : ∀ x, A.eval (B.eval x) ≈ B.eval (A.eval x)) (z : Scalar) (x : Fiber n) :
    (value (sumResidue A B) (sumResidue_linear A B hA hB) z).eval x ≈
      (value A hA z).eval ((value B hB z).eval x) := by
  let S := sumResidue A B
  have hS := sumResidue_linear A B hA hB
  let R := pointRadius z
  let p : Scalar := ⟨zero,ofQComplex_valid _⟩
  let C := LocalSystem.initialBound x
  have hC := LocalSystem.initialBound_nonneg x
  let f : UniformSegment.Field (n := n) (interior R.val) := fun v _ => (value S hS v).eval x
  let g : UniformSegment.Field (n := n) (interior R.val) := fun v hv => (commutingProductField A B hA hB R v hv).eval x
  have hfrem : ∀ (eps H : QPos) w v hw hv,
      H.val ≤ (discDelta S R (inputError C hC eps)).val → Small (sub v.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => S) f w v hw hv) (eps.val*H.val) := by
    intro eps H w v hw hv hH hvw
    have hs := disc_uniform_remainder S hS R (inputError C hC eps) H w v hw hv hH hvw C hC x (LocalSystem.initialBound_valid x)
    have hb := Rat.mul_le_mul_of_nonneg_right (inputError_bound C hC eps) (Rat.le_of_lt H.property)
    intro i
    exact (hs i).mono (by grind)
  have hgrem : ∀ (eps H : QPos) w v hw hv,
      H.val ≤ (commutingProductDelta A B R (inputError C hC eps)).val → Small (sub v.val w.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => S) g w v hw hv) (eps.val*H.val) := by
    intro eps H w v hw hv hH hvw
    have hs := commutingProduct_uniform_remainder A B hA hB hAB R (inputError C hC eps) H w v hw hv hH hvw
      C hC x (LocalSystem.initialBound_valid x)
    have hb := Rat.mul_le_mul_of_nonneg_right (inputError_bound C hC eps) (Rat.le_of_lt H.property)
    intro i
    exact (hs i).mono (by grind)
  have hi : g p (interior_zero R.val R.property) ≈ x :=
    Setoid.trans ((value A hA p).congr (value_initial B hB x)) (value_initial A hA x)
  exact constant_ode_equal_on_disc S hS R p z (interior_zero R.val R.property) (pointRadius_inside z) f g
    (discValueBound S R*C) (discValueBound A R*(discValueBound B R*C))
    (Rat.mul_nonneg (discValueBound_nonneg S R) hC)
    (Rat.mul_nonneg (discValueBound_nonneg A R) (Rat.mul_nonneg (discValueBound_nonneg B R) hC))
    (fun w v _ _ hwv => value_congr S S hS hS (fun _ => Setoid.refl _) w v hwv x x (Setoid.refl _))
    (fun w v _ _ hwv => value_congr A A hA hA (fun _ => Setoid.refl _) w v hwv _ _
      (value_congr B B hB hB (fun _ => Setoid.refl _) w v hwv x x (Setoid.refl _)))
    (Setoid.trans (value_initial S hS x) (Setoid.symm hi))
    (fun v hv => discField_bound S hS R v hv C hC x (LocalSystem.initialBound_valid x))
    (fun v hv => discField_bound A hA R v hv (discValueBound B R*C)
      (Rat.mul_nonneg (discValueBound_nonneg B R) hC) _
      (discField_bound B hB R v hv C hC x (LocalSystem.initialBound_valid x)))
    (fun eps => discDelta S R (inputError C hC eps))
    (fun eps => commutingProductDelta A B R (inputError C hC eps)) hfrem hgrem

end ComputableAnalysis.RiemannHilbert.MatrixExponential
