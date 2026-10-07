import ComputableAnalysis.ModularForms.PairedInverseCenterExpansion
import ComputableAnalysis.ModularForms.RepresentedPrefixFactors
import ComputableAnalysis.ModularForms.InverseSquareSeriesBound

/-! Actual quadratic center polynomials and uniform finite-prefix errors. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedCenterConstantTerm (n : Nat) : ComplexRaw := scaleRat (-2) (pairedCenterReciprocal n).val

def pairedCenterQuadraticTerm (n : Nat) : ComplexRaw :=
  scaleRat (-2) (mul (pairedCenterReciprocal n).val (pairedCenterReciprocal n).val)

theorem pairedCenterConstantTerm_valid (n : Nat) : (pairedCenterConstantTerm n).Valid :=
  scaleRat_valid (pairedCenterReciprocal n).property

theorem pairedCenterQuadraticTerm_valid (n : Nat) : (pairedCenterQuadraticTerm n).Valid :=
  scaleRat_valid (mul_valid (pairedCenterReciprocal n).property (pairedCenterReciprocal n).property)

private theorem scale_center_algebra (I C Z : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat 2 (I+C+(C*C)*(Z*Z))=
      (ComplexRawQuotient.scaleRat 2 I-ComplexRawQuotient.scaleRat (-2) C)-
        (Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C) := by
  change ComplexRawQuotient.scaleRat 2 (I+C+(C*C)*(Z*Z))=
    (ComplexRawQuotient.scaleRat 2 I+ -(ComplexRawQuotient.scaleRat (-2) C))+
      -((Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C))
  rw [ComplexRawQuotient.mul_scaleRat,ComplexRawQuotient.neg_scaleRat,ComplexRawQuotient.neg_scaleRat]
  simp only [Rat.neg_neg]
  rw [ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_add]
  rw [ComplexRawQuotient.mul_comm (C*C) (Z*Z)]

/-- Each actual division term admits a quadratic center polynomial with a
summable fourth-order error. -/
theorem pairedRegularDivisionTerm_quadratic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (n : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (sub (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val
      (pairedCenterConstantTerm n)) (mul (mul z.val z.val) (pairedCenterQuadraticTerm n)))
      (512*R*R*R*R*reciprocalSquare (n+1)) := by
  let i := (pairedSmallDiskLiteralInverseMap n).eval z hz
  let c := pairedCenterReciprocal n
  have h := LocalODE.small_scale (show (0:Rat)≤2 by decide +kernel)
    (pairedSmallDiskLiteralInverse_center_remainder_bound z hz n R hR hs)
  have he : (scaleRat 2 (add (add i.val c.val) (mul (mul c.val c.val) (mul z.val z.val)))).Equiv
      (sub (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val
        (pairedCenterConstantTerm n)) (mul (mul z.val z.val) (pairedCenterQuadraticTerm n))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := scaleRat_valid (add_valid (add_valid i.property c.property)
        (mul_valid (mul_valid c.property c.property) (mul_valid z.property z.property))))
      (hright := sub_valid (sub_valid (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property
        (pairedCenterConstantTerm_valid n)) (mul_valid (mul_valid z.property z.property) (pairedCenterQuadraticTerm_valid n)))
    let I := ComplexRawQuotient.ofRaw i.val i.property
    let C := ComplexRawQuotient.ofRaw c.val c.property
    let Z := ComplexRawQuotient.ofRaw z.val z.property
    change ComplexRawQuotient.scaleRat 2 (I+C+(C*C)*(Z*Z))=
      (ComplexRawQuotient.scaleRat 2 I-ComplexRawQuotient.scaleRat (-2) C)-
        (Z*Z)*ComplexRawQuotient.scaleRat (-2) (C*C)
    exact scale_center_algebra I C Z
  have hb := Small.congr
    (scaleRat_valid (add_valid (add_valid i.property c.property)
      (mul_valid (mul_valid c.property c.property) (mul_valid z.property z.property))))
    (sub_valid (sub_valid (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).property
      (pairedCenterConstantTerm_valid n)) (mul_valid (mul_valid z.property z.property) (pairedCenterQuadraticTerm_valid n))) he h
  have hrate : 2*(256*R*R*R*R*reciprocalSquare (n+1))=512*R*R*R*R*reciprocalSquare (n+1) := by grind only
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

/-- Finite prefixes retain a fourth-order bound independent of the cutoff. -/
theorem pairedRegularDivisionPrefix_quadratic_center_bound (z : Scalar)
    (hz : LocalODE.interior (1/4) z) (N : Nat) (R : Rat) (hR : 0≤R) (hs : Small z.val R) :
    Small (ScalarSeries.block (fun n => sub
      (sub (pairedRegularDivisionTerm z (LocalODE.interior_bound _ z hz) n).val (pairedCenterConstantTerm n))
      (mul (mul z.val z.val) (pairedCenterQuadraticTerm n))) 0 N) (1024*R*R*R*R) := by
  have hB : 0≤512*R*R*R*R := Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg
    (Rat.mul_nonneg (by decide +kernel) hR) hR) hR) hR
  have h := block_square_majorant _ (512*R*R*R*R) hB
    (fun n => pairedRegularDivisionTerm_quadratic_center_bound z hz n R hR hs) N
  have he : 2*(512*R*R*R*R)=1024*R*R*R*R := by grind only
  rw [he] at h
  exact h

end ComputableAnalysis.ModularForms
