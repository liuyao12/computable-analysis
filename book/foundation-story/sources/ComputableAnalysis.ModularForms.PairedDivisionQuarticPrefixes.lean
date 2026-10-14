import ComputableAnalysis.ModularForms.PairedDivisionQuarticCoefficient

/-! Actual quartic center polynomials and uniform sextic finite-prefix errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem scale_quartic_algebra (I C Z : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat 2 (((I+C)+(C*C)*(Z*Z))+(C*(C*C))*((Z*Z)*(Z*Z)))=
      ((ComplexRawQuotient.scaleRat 2 I-ComplexRawQuotient.scaleRat (-2) C)-
        (Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C))-
        ((Z*Z)*(Z*Z))*ComplexRawQuotient.scaleRat (-2) (C*(C*C)) := by
  change ComplexRawQuotient.scaleRat 2 (((I+C)+(C*C)*(Z*Z))+(C*(C*C))*((Z*Z)*(Z*Z)))=
    ((ComplexRawQuotient.scaleRat 2 I+ -(ComplexRawQuotient.scaleRat (-2) C))+
      -((Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C)))+
      -(((Z*Z)*(Z*Z))*ComplexRawQuotient.scaleRat (-2) (C*(C*C)))
  rw [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.mul_scaleRat,
    ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat]
  simp only [Rat.neg_neg]
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_add]
  rw [ComplexRawQuotient.mul_comm (C*C) (Z*Z),
    ComplexRawQuotient.mul_comm (C*(C*C)) ((Z*Z)*(Z*Z))]

/-- Each actual division term has a quartic polynomial with a summable sextic error. -/
theorem pairedRegularDivisionTerm_quartic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (sub (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val
      (pairedCenterConstantTerm n)) (mul (mul z.val z.val) (pairedCenterQuadraticTerm n)))
      (mul (mul (mul z.val z.val) (mul z.val z.val)) (pairedCenterQuarticTerm n)))
      (4096*R*R*R*R*R*R*reciprocalSquare (n+1)) := by
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  let residual := pairedInverseQuarticCenterResidual z hz n
  let target : Scalar := ⟨sub (sub (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val
      (pairedCenterConstantTerm n)) (mul (mul z.val z.val) (pairedCenterQuadraticTerm n)))
      (mul (mul (mul z.val z.val) (mul z.val z.val)) (pairedCenterQuarticTerm n)),
    sub_valid (sub_valid (sub_valid (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property
      (pairedCenterConstantTerm_valid n)) (mul_valid (mul_valid z.property z.property) (pairedCenterQuadraticTerm_valid n)))
      (mul_valid (mul_valid (mul_valid z.property z.property) (mul_valid z.property z.property)) (pairedCenterQuarticTerm_valid n))⟩
  have h := LocalODE.small_scale (show (0:Rat)≤2 by decide +kernel)
    (pairedSmallDiskLiteralInverse_quartic_center_remainder_bound z hz n R hR hs)
  have he : (scaleRat 2 residual.val).Equiv target.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid residual.property) (hright := target.property)
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change ComplexRawQuotient.scaleRat 2 (((I+C)+(C*C)*(Z*Z))+(C*(C*C))*((Z*Z)*(Z*Z)))=
      ((ComplexRawQuotient.scaleRat 2 I-ComplexRawQuotient.scaleRat (-2) C)-
        (Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C))-
        ((Z*Z)*(Z*Z))*ComplexRawQuotient.scaleRat (-2) (C*(C*C))
    exact scale_quartic_algebra I C Z
  have hb := Small.congr (scaleRat_valid residual.property) target.property he h
  have hrate : 2*(2048*R*R*R*R*R*R*reciprocalSquare (n+1))=
    4096*R*R*R*R*R*R*reciprocalSquare (n+1) := by grind only
  rw [hrate] at hb
  exact hb

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

/-- The sextic prefix error is independent of the cutoff. -/
theorem pairedRegularDivisionPrefix_quartic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (N : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (ScalarSeries.block (fun n => sub (sub
      (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val (pairedCenterConstantTerm n))
      (mul (mul z.val z.val) (pairedCenterQuadraticTerm n)))
      (mul (mul (mul z.val z.val) (mul z.val z.val)) (pairedCenterQuarticTerm n))) 0 N)
      (8192*R*R*R*R*R*R) := by
  have hB : 0≤4096*R*R*R*R*R*R := Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR) hR) hR
  have h := block_square_majorant _ (4096*R*R*R*R*R*R) hB
    (fun n => pairedRegularDivisionTerm_quartic_center_bound z hz n R hR hs) N
  have he : 2*(4096*R*R*R*R*R*R)=8192*R*R*R*R*R*R := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
