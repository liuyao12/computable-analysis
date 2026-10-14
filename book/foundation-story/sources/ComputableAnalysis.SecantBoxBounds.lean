import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
import ComputableAnalysis.ParametrizedComplexContinuity
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.ContourSegmentBisection

/-! Computed complex secants and balanced rational separation bounds. -/
namespace ComputableAnalysis.RiemannHilbert.DomainFunctions
open ComplexRaw FunctionTheory BoxApproximation NonzeroBoxSearch

/-- A nonzero displacement has rational upper bounds for itself and its
computed reciprocal whose product is bounded by an absolute constant. The
bounds come from the reciprocal's terminating rational anchor search. -/
theorem balanced_separation (v : Scalar) (hv : Nonzero v) :
    ∃ H K : QPos, Small v.val H.val ∧
      Small (RepresentedReciprocal.inverse v hv).val K.val ∧ H.val*K.val≤16 := by
  let c := ReciprocalAnchor.center v hv
  let B := coordinateBound c
  let C := coordinateBound (RationalReciprocal.inverse c)
  let R := ReciprocalAnchor.radius (v.val.compute (ReciprocalAnchor.stage v hv))
  have hn : 0<QComplex.normSq c := (ReciprocalAnchor.stage_spec v hv).1
  have hB : 0<B := by
    have hb := coordinateBound_bounds c
    have h0 := coordinateBound_nonneg c
    change 0≤B at h0
    change -B≤c.re ∧ c.re≤B ∧ -B≤c.im ∧ c.im≤B at hb
    by_cases h : 0<B
    · exact h
    exfalso
    have bz : B=0 := by grind only
    have cr : c.re=0 := by grind only
    have ci : c.im=0 := by grind only
    unfold QComplex.normSq at hn
    rw [cr,ci] at hn
    grind only
  have hC : 0<C := by
    have hb := coordinateBound_bounds (RationalReciprocal.inverse c)
    have h0 := coordinateBound_nonneg (RationalReciprocal.inverse c)
    change 0≤C at h0
    by_cases h : 0<C
    · exact h
    exfalso
    have cz : C=0 := by grind only
    have cr : (RationalReciprocal.inverse c).re=0 := by
      change -C≤_ ∧ _≤C ∧ -C≤_ ∧ _≤C at hb; grind only
    have ci : (RationalReciprocal.inverse c).im=0 := by
      change -C≤_ ∧ _≤C ∧ -C≤_ ∧ _≤C at hb; grind only
    have hu := RationalReciprocal.mul_inverse c (Rat.ne_of_gt hn)
    have hre := congrArg QComplex.re hu
    change c.re*(RationalReciprocal.inverse c).re-c.im*(RationalReciprocal.inverse c).im=1 at hre
    rw [cr,ci] at hre
    grind only
  have hBB : B*B≤QComplex.normSq c := by
    dsimp [B,coordinateBound,qabs]
    unfold QComplex.normSq
    have hr := rat_square_nonneg_basic c.re
    have hi := rat_square_nonneg_basic c.im
    simp only [Rat.max_def]
    split <;> split <;> split <;> grind only
  have hInv := RationalReciprocal.coordinateBound_inverse c B (QComplex.normSq c)
    (Rat.le_of_lt hB) hn Rat.le_refl Rat.le_refl
  have hBC : B*C≤1 := by
    have hmul := Rat.mul_le_mul_of_nonneg_left hInv (Rat.le_of_lt hB)
    have hb := Rat.mul_le_mul_of_nonneg_right hBB (Rat.le_of_lt (Rat.inv_pos.mpr hn))
    rw [Rat.mul_inv_cancel _ (Rat.ne_of_gt hn)] at hb
    change B*C≤B*(B/QComplex.normSq c) at hmul
    simp only [Rat.div_def] at hmul
    grind only
  have hR : 0≤R := ReciprocalAnchor.radius_nonneg _ (valid_ordered v.property _)
  have hCR : 2*C*R≤(1:Rat)/8 := (ReciprocalAnchor.stage_spec v hv).2
  let H : QPos := ⟨B+R,by grind only⟩
  let K : QPos := ⟨8*C,Rat.mul_pos (by decide +kernel) hC⟩
  have herr := center_error v (ReciprocalAnchor.stage v hv) R hR
    (by dsimp [R,ReciprocalAnchor.radius]; grind)
    (by dsimp [R,ReciprocalAnchor.radius]; grind)
  have hz : Small v.val H.val := by
    have hs := LocalODE.small_add (rational_small c) herr
    apply Small.congr (add_valid (ofQComplex_valid c) (sub_valid v.property (ofQComplex_valid c))) v.property _ hs
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (ofQComplex_valid c) (sub_valid v.property (ofQComplex_valid c))) (hright := v.property)
    change ComplexRawQuotient.ofRaw (ofQComplex c) (ofQComplex_valid c) +
      (ComplexRawQuotient.ofRaw v.val v.property-ComplexRawQuotient.ofRaw (ofQComplex c) (ofQComplex_valid c))=ComplexRawQuotient.ofRaw v.val v.property
    grind only
  have hi : Small (RepresentedReciprocal.inverse v hv).val K.val := by
    have hs := Small.mul (ReciprocalAnchor.anchor v hv).property
      (ScalarNeumannInverse.value (ReciprocalAnchor.normalized v hv) (ReciprocalAnchor.residual_small v hv)).property
      (Rat.le_of_lt hC) (by decide +kernel) (rational_small (RationalReciprocal.inverse c))
      (ScalarNeumannInverse.value_bound _ _)
    simpa only [RepresentedReciprocal.inverse,K,show (2:Rat)*C*4=8*C by grind only] using hs
  exact ⟨H,K,hz,hi,by dsimp [H,K]; grind only⟩

/-- The actual quotient of two represented function values, evaluated with
the existing terminating reciprocal computation at the nonzero displacement. -/
def complexSecant (f : Map) (z w : Scalar) (hz : f.domain z) (hw : f.domain w)
    (apart : Nonzero (Centered.offset w z)) : Scalar :=
  scalarProduct ⟨sub (f.eval z hz).val (f.eval w hw).val,
    sub_valid (f.eval z hz).property (f.eval w hw).property⟩
    (RepresentedReciprocal.inverse (Centered.offset w z) apart)

/-- Input and output names do not affect the value of a computed secant. -/
theorem complexSecant_congr (f : Map) (z w z' w' : Scalar)
    (hz : f.domain z) (hw : f.domain w) (hz' : f.domain z') (hw' : f.domain w')
    (apart : Nonzero (Centered.offset w z)) (apart' : Nonzero (Centered.offset w' z'))
    (ez : z≈z') (ew : w≈w') :
    complexSecant f z w hz hw apart ≈ complexSecant f z' w' hz' hw' apart' :=
  mul_equiv
    (sub_valid (f.eval z hz).property (f.eval w hw).property)
    (sub_valid (f.eval z' hz').property (f.eval w' hw').property)
    (RepresentedReciprocal.inverse _ apart).property (RepresentedReciprocal.inverse _ apart').property
    (FunctionTheory.sub_congr (f.eval_congr z z' hz hz' ez) (f.eval_congr w w' hw hw' ew))
    (RepresentedReciprocal.inverse_congr _ _ apart apart' (FunctionTheory.sub_congr ez ew))

end ComputableAnalysis.RiemannHilbert.DomainFunctions
