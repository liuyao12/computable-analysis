import ComputableAnalysis.ModularForms.PairedInverseSquareQuadraticExpansion

/-! Cubic center expansion of actual derivative terms and prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem sc2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 2 x
  change ComplexRawQuotient.scaleRat 2 x=(2:ScalarAlgebra.Value)*x at h
  exact h

private theorem sc4 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x := by
  have h := ScalarAlgebra.scale_natural 4 x
  change ComplexRawQuotient.scaleRat 4 x=(4:ScalarAlgebra.Value)*x at h
  exact h

private theorem scm2 (x : ScalarAlgebra.Value) : ComplexRawQuotient.scaleRat (-2) x= -((2:ScalarAlgebra.Value)*x) := by
  have h := ComplexRawQuotient.neg_scaleRat 2 x
  rw [sc2] at h
  exact h.symm

private theorem derivative_algebra (I C Z : ScalarAlgebra.Value) :
    -(ComplexRawQuotient.scaleRat 4 (Z*((I*I-C*C)-ComplexRawQuotient.scaleRat 2 ((C*(C*C))*(Z*Z)))))=
    ((-(I*I)*(Z+Z)+ -(I*I)*(Z+Z))-
      ComplexRawQuotient.scaleRat 2 (Z*ComplexRawQuotient.scaleRat (-2) (C*C)))-
      ComplexRawQuotient.scaleRat 4 (((Z*Z)*Z)*ComplexRawQuotient.scaleRat (-2) (C*(C*C))) := by
  simp only [sc2,sc4,scm2]
  grind only

def pairedDerivativeCubicCenterResidual (z : Scalar) (hz : LocalODE.interior (1/4) z) (n : Nat) : Scalar :=
  let z3 := scalarProduct (scalarProduct z z) z
  let b : Scalar := ⟨pairedCenterQuadraticTerm n,pairedCenterQuadraticTerm_valid n⟩
  let d : Scalar := ⟨pairedCenterQuarticTerm n,pairedCenterQuarticTerm_valid n⟩
  let p := scalarProduct z b
  let q := scalarProduct z3 d
  ⟨sub (sub (pairedRegularDivisionDerivativeTerm z hz n).val (scaleRat 2 p.val)) (scaleRat 4 q.val),
    sub_valid (sub_valid (pairedRegularDivisionDerivativeTerm z hz n).property (scaleRat_valid p.property))
      (scaleRat_valid q.property)⟩

/-- An explicit summable fifth-order bound for each actual derivative term. -/
theorem pairedRegularDivisionDerivativeTerm_cubic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (pairedDerivativeCubicCenterResidual z hz n).val
      (23552*R*R*R*R*R*reciprocalSquare (n+1)) := by
  let e := pairedInverseSquareQuadraticResidual z hz n
  let p := scalarProduct z e
  let rem : Scalar := ⟨neg (scaleRat 4 p.val),neg_valid (scaleRat_valid p.property)⟩
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hc : 0≤reciprocalSquare (n+1) := by
    unfold reciprocalSquare
    exact Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hn hn))
  have hE : 0≤2944*R*R*R*R*reciprocalSquare (n+1) := Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR) hc
  have hp := Small.mul z.property e.property hR hE hs
    (pairedInverseSquare_quadratic_remainder_bound z hz n R hR hs)
  have hb := SeriesLimitLaws.small_neg (LocalODE.small_scale (show (0:Rat)≤4 by decide +kernel) hp)
  have hrate : 4*(2*R*(2944*R*R*R*R*reciprocalSquare (n+1)))=
    23552*R*R*R*R*R*reciprocalSquare (n+1) := by grind only
  rw [hrate] at hb
  have heq : rem.val.Equiv (pairedDerivativeCubicCenterResidual z hz n).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := rem.property)
      (hright := (pairedDerivativeCubicCenterResidual z hz n).property)
    let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
    let c := pairedCenterReciprocal n
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change -(ComplexRawQuotient.scaleRat 4 (Z*((I*I-C*C)-ComplexRawQuotient.scaleRat 2 ((C*(C*C))*(Z*Z)))))=
      ((-(I*I)*(Z+Z)+ -(I*I)*(Z+Z))-
        ComplexRawQuotient.scaleRat 2 (Z*ComplexRawQuotient.scaleRat (-2) (C*C)))-
        ComplexRawQuotient.scaleRat 4 (((Z*Z)*Z)*ComplexRawQuotient.scaleRat (-2) (C*(C*C)))
    exact derivative_algebra I C Z
  exact Small.congr rem.property (pairedDerivativeCubicCenterResidual z hz n).property heq hb

private theorem block_square_majorant (t : Nat → ComplexRaw) (B : Rat) (hB : 0≤B)
    (ht : ∀ n, Small (t n) (B*reciprocalSquare (n+1))) (N : Nat) :
    Small (ScalarSeries.block t 0 N) (2*B) := by
  have h : ∀ N, Small (ScalarSeries.block t 0 N) (B*reciprocalSquareBlock 0 N) := by
    intro N
    induction N with
    | zero => exact Small.zero (by change 0≤B*0; rw [Rat.mul_zero]; decide +kernel)
    | succ N ih =>
      have hb := LocalODE.small_add ih (ht N)
      have he : B*reciprocalSquareBlock 0 N+B*reciprocalSquare (N+1)=B*reciprocalSquareBlock 0 (N+1) := by
        rw [reciprocalSquareBlock]
        simp only [Nat.zero_add]
        grind only
      rw [he] at hb
      simpa only [ScalarSeries.block.eq_2,Nat.zero_add] using hb
  apply (h N).mono
  have hb := Rat.mul_le_mul_of_nonneg_left (inverseSquareBlock_zero_bound N) hB
  grind only

/-- The fifth-order derivative prefix bound is independent of the cutoff. -/
theorem pairedRegularDivisionDerivativePrefix_cubic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (N : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (ScalarSeries.block (fun n => (pairedDerivativeCubicCenterResidual z hz n).val) 0 N)
      (47104*R*R*R*R*R) := by
  have hB : 0≤23552*R*R*R*R*R := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR) hR
  have h := block_square_majorant _ (23552*R*R*R*R*R) hB
    (fun n => pairedRegularDivisionDerivativeTerm_cubic_center_bound z hz n R hR hs) N
  have he : 2*(23552*R*R*R*R*R)=47104*R*R*R*R*R := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
