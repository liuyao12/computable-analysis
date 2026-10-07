import ComputableAnalysis.ModularForms.GeometricEulerExponentialProduct

/-! A fixed bound on actual exponential products along every geometric mesh. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def geometricExponentialPrefixBound : Rat :=
  4*exponentialQuadraticConstant geometricFactorRadius+3

theorem geometricExponentialPrefixBound_nonnegative : 0 ≤ geometricExponentialPrefixBound := by
  have hc := exponentialQuadraticConstant_nonnegative geometricFactorRadius
  have hm := Rat.mul_nonneg (show (0:Rat)≤4 by decide) hc
  unfold geometricExponentialPrefixBound
  grind only

theorem geometricMeshAngle_prefix_bounds (N k : Nat) (hk : k ≤ N+1) :
    0 ≤ geometricMeshAngle N k ∧ geometricMeshAngle N k ≤ 2 := by
  have hb := geometricMeshAngle_bounds N k
  have hc : (k:Rat) ≤ ((N+1:Nat):Rat) := by exact_mod_cast hk
  have hm := Rat.mul_le_mul_of_nonneg_right hc (Rat.le_of_lt (geometricMeshStep_positive N))
  have hi := geometricMeshStep_identity N
  constructor
  · exact hb.1
  · grind only

theorem geometricMeshAngleScalar_small (N k : Nat) (hk : k ≤ N+1) :
    Small (geometricMeshAngleScalar N k).val 2 := by
  obtain ⟨hl,hu⟩ := geometricMeshAngle_prefix_bounds N k hk
  refine ⟨?_,?_,?_,?_⟩
  · intro n m; change (-2:Rat) ≤ 0; decide
  · intro n m; change (0:Rat) ≤ 2; decide
  · intro n m; change -2 ≤ geometricMeshAngle N k; grind only
  · intro n m; exact hu

theorem geometricExponentialProduct_small (N k : Nat) (hk : k ≤ N+1) :
    Small (geometricExponentialProduct N k) geometricExponentialPrefixBound := by
  let z := geometricMeshAngleScalar N k
  let e := (entireExponentialValue z).val
  let l := add (ofQComplex QComplex.one) z.val
  have hz := geometricMeshAngleScalar_small N k hk
  have hchart : (exponentialChart geometricFactorRadius).domain z :=
    ⟨2,by decide,by decide,hz⟩
  have hr := entireExponential_linear_error geometricFactorRadius z hchart 2 (by decide) hz
  have hone : Small (ofQComplex QComplex.one) 1 := by
    refine ⟨?_,?_,?_,?_⟩
    · intro n m; change (-1:Rat) ≤ 1; decide
    · intro n m; change (1:Rat) ≤ 1; decide
    · intro n m; change (-1:Rat) ≤ 0; decide
    · intro n m; change (0:Rat) ≤ 1; decide
  have hl : Small l 3 := by
    have hb := LocalODE.small_add hone hz
    have hc : (1:Rat)+2=3 := by decide +kernel
    rw [hc] at hb
    exact hb
  have he : (add (sub e l) l).Equiv e := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid (entireExponentialValue z).property
        (add_valid (ofQComplex_valid _) z.property)) (add_valid (ofQComplex_valid _) z.property))
      (hright := (entireExponentialValue z).property)
    change (ComplexRawQuotient.ofRaw e (entireExponentialValue z).property +
      -ComplexRawQuotient.ofRaw l (add_valid (ofQComplex_valid _) z.property)) +
      ComplexRawQuotient.ofRaw l (add_valid (ofQComplex_valid _) z.property) =
      ComplexRawQuotient.ofRaw e (entireExponentialValue z).property
    grind only
  have hb := LocalODE.small_add hr hl
  have hval := Small.congr
    (add_valid (sub_valid (entireExponentialValue z).property (add_valid (ofQComplex_valid _) z.property))
      (add_valid (ofQComplex_valid _) z.property)) (entireExponentialValue z).property he hb
  have hconst : exponentialQuadraticConstant geometricFactorRadius*(2:Rat)^2+3=
      geometricExponentialPrefixBound := by
    unfold geometricExponentialPrefixBound
    simp only [Rat.pow_succ,Rat.pow_zero]
    grind only
  rw [hconst] at hval
  exact Small.congr (entireExponentialValue z).property (geometricExponentialProduct_valid N k)
    (equiv_symm (geometricExponentialProduct_angle N k)) hval

end ComputableAnalysis.ModularForms
