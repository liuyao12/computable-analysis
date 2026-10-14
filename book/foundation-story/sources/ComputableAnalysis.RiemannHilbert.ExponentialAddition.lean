import ComputableAnalysis.RiemannHilbert.ExponentialODEUniqueness

/-! The exact addition law for the entire represented matrix exponential.
All disc sizes and error shares are constructed internally. Translation
preserves the proved remainder, and global constant-ODE uniqueness identifies
the translated solution with the product solution. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE LinearField
variable {n : Nat}
set_option maxHeartbeats 2000000

def translateRadius (w : Scalar) (R : QPos) : QPos :=
  ⟨LocalODE.initialBound w.val+R.val+1, by have := LocalODE.initialBound_nonneg w.val; have := R.property; grind⟩

theorem translate_disc_mem (w : Scalar) (R : QPos) (z : Scalar) (hz : interior R.val z) :
    interior (translateRadius w R).val (Centered.translate w z) :=
  ⟨LocalODE.initialBound w.val+R.val,
    Rat.add_nonneg (LocalODE.initialBound_nonneg w.val) (Rat.le_of_lt R.property),
    by dsimp [translateRadius]; grind,
    small_add (LocalODE.initialBound_valid w.val w.property) (interior_bound R.val z hz)⟩

/-- Exponentiation turns addition of arbitrary represented parameters into
composition, with no smallness, rational-input, or caller-chosen disc. -/
theorem value_add (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z w : Scalar) (x : Fiber n) :
    (value A hA (Centered.translate w z)).eval x ≈
      (value A hA z).eval ((value A hA w).eval x) := by
  let R := pointRadius z
  let S := translateRadius w R
  let p : Scalar := ⟨zero, ofQComplex_valid _⟩
  let y := (value A hA w).eval x
  let E := LocalSystem.initialBound x
  let F := LocalSystem.initialBound y
  have hE := LocalSystem.initialBound_nonneg x
  have hF := LocalSystem.initialBound_nonneg y
  let f : UniformSegment.Field (n := n) (interior R.val) := fun v _ => (value A hA (Centered.translate w v)).eval x
  let g : UniformSegment.Field (n := n) (interior R.val) := fun v _ => (value A hA v).eval y
  have hfrem : ∀ (eps H : QPos) a v ha hv,
      H.val ≤ (discDelta A S (inputError E hE eps)).val → Small (sub v.val a.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => A) f a v ha hv) (eps.val*H.val) := by
    intro eps H a v ha hv hH hva
    have ht : Small (sub (Centered.translate w v).val (Centered.translate w a).val) H.val :=
      Small.congr (sub_valid v.property a.property)
        (sub_valid (Centered.translate w v).property (Centered.translate w a).property)
        (equiv_symm (Centered.translate_difference w a v)) hva
    have hs := disc_uniform_remainder A hA S (inputError E hE eps) H
      (Centered.translate w a) (Centered.translate w v) (translate_disc_mem w R a ha) (translate_disc_mem w R v hv)
      hH ht E hE x (LocalSystem.initialBound_valid x)
    have he : operatorRemainder (discField A hA S) (discSlope A hA S)
        (Centered.translate w a) (Centered.translate w v) (translate_disc_mem w R a ha) (translate_disc_mem w R v hv) x ≈
        UniformSegment.remainder (fun _ _ => A) f a v ha hv :=
      Fiber.sub_congr (Setoid.refl _)
        (Fiber.scale_congr (Centered.translate_difference w a v) (Setoid.refl _))
    have hh := Rat.mul_le_mul_of_nonneg_right (inputError_bound E hE eps) (Rat.le_of_lt H.property)
    intro i
    exact ((bound_congr he hs) i).mono (by grind)
  have hgrem : ∀ (eps H : QPos) a v ha hv,
      H.val ≤ (discDelta A R (inputError F hF eps)).val → Small (sub v.val a.val) H.val →
      CoordinateBound (UniformSegment.remainder (fun _ _ => A) g a v ha hv) (eps.val*H.val) := by
    intro eps H a v ha hv hH hva
    have hs := disc_uniform_remainder A hA R (inputError F hF eps) H a v ha hv hH hva F hF y
      (LocalSystem.initialBound_valid y)
    have hh := Rat.mul_le_mul_of_nonneg_right (inputError_bound F hF eps) (Rat.le_of_lt H.property)
    intro i
    exact (hs i).mono (by grind)
  exact constant_ode_equal_on_disc A hA R p z (interior_zero R.val R.property) (pointRadius_inside z)
    f g (discValueBound A S*E) (discValueBound A R*F)
    (Rat.mul_nonneg (discValueBound_nonneg A S) hE) (Rat.mul_nonneg (discValueBound_nonneg A R) hF)
    (fun a v _ _ hav => value_congr A A hA hA (fun _ => Setoid.refl _) _ _
      (add_equiv (equiv_refl _ w.property) hav) x x (Setoid.refl _))
    (fun a v _ _ hav => value_congr A A hA hA (fun _ => Setoid.refl _) a v hav y y (Setoid.refl _))
    (Setoid.trans (value_congr A A hA hA (fun _ => Setoid.refl _) (Centered.translate w p) w
      (Centered.translate_zero w) x x (Setoid.refl _)) (Setoid.symm (value_initial A hA y)))
    (fun v hv => discField_bound A hA S _ (translate_disc_mem w R v hv) E hE x (LocalSystem.initialBound_valid x))
    (fun v hv => discField_bound A hA R v hv F hF y (LocalSystem.initialBound_valid y))
    (fun eps => discDelta A S (inputError E hE eps)) (fun eps => discDelta A R (inputError F hF eps)) hfrem hgrem

theorem values_commute (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z w : Scalar) (x : Fiber n) :
    (value A hA z).eval ((value A hA w).eval x) ≈
      (value A hA w).eval ((value A hA z).eval x) :=
  Setoid.trans (Setoid.symm (value_add A hA z w x))
    (Setoid.trans (value_congr A A hA hA (fun _ => Setoid.refl _) _ _
      (add_comm_equiv _ _ w.property z.property) x x (Setoid.refl _)) (value_add A hA w z x))

/-- Negating the represented parameter agrees with exponentiating the
negative residue. Both sides are actual entire series evaluators. -/
theorem value_negative_parameter (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (z : Scalar) :
    (value A hA ⟨neg z.val, neg_valid z.property⟩).Equiv
      (value (negativeOperator A) (negativeOperator_linear A hA) z) := by
  intro x
  let v : Scalar := ⟨neg z.val, neg_valid z.property⟩
  have hsum : (Centered.translate v z).val.Equiv zero :=
    equiv_trans (Centered.translate v z).property (add_valid z.property v.property) (ofQComplex_valid _)
      (add_comm_equiv _ _ v.property z.property) (add_neg_equiv _ z.property)
  have he : (value A hA z).eval ((value A hA v).eval x) ≈ x :=
    Setoid.trans (Setoid.symm (value_add A hA z v x))
      (Setoid.trans (value_congr A A hA hA (fun _ => Setoid.refl _) _ ⟨zero, ofQComplex_valid _⟩
        hsum x x (Setoid.refl _)) (value_initial A hA x))
  exact (frame A hA z).toValueIso.forward_reflects
    (Setoid.trans he (Setoid.symm (value_after_negative A hA z x)))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
