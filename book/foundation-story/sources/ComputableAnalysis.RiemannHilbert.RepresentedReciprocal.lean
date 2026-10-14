import ComputableAnalysis.RiemannHilbert.ReciprocalAnchor
import ComputableAnalysis.RiemannHilbert.ScalarNeumannInverse

/-! Reciprocal of every nonzero valid represented complex value. The
normalizing box is found by rational search; inversion uses a convergent
Neumann evaluator. Exact laws hide both internal choices. -/
namespace ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
open ComplexRaw FunctionTheory NonzeroBoxSearch

def inverse (z : Scalar) (hz : Nonzero z) : Scalar :=
  let s := ReciprocalAnchor.normalized z hz
  let r := ScalarNeumannInverse.value s (ReciprocalAnchor.residual_small z hz)
  ⟨mul (ReciprocalAnchor.anchor z hz).val r.val,
    mul_valid (ReciprocalAnchor.anchor z hz).property r.property⟩

theorem mul_inverse (z : Scalar) (hz : Nonzero z) :
    (mul z.val (inverse z hz).val).Equiv (ofQComplex QComplex.one) := by
  let a := ReciprocalAnchor.anchor z hz
  let s := ReciprocalAnchor.normalized z hz
  let r := ScalarNeumannInverse.value s (ReciprocalAnchor.residual_small z hz)
  have h := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid s.property r.property) (hright := ofQComplex_valid _)
    (ScalarNeumannInverse.mul_value s (ReciprocalAnchor.residual_small z hz))
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid z.property (inverse z hz).property) (hright := ofQComplex_valid _)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let R := ComplexRawQuotient.ofRaw r.val r.property
  change (A*Z)*R = 1 at h
  change Z*(A*R) = (1 : ScalarAlgebra.Value)
  grind

theorem inverse_mul (z : Scalar) (hz : Nonzero z) :
    (mul (inverse z hz).val z.val).Equiv (ofQComplex QComplex.one) :=
  equiv_trans (mul_valid (inverse z hz).property z.property)
    (mul_valid z.property (inverse z hz).property) (ofQComplex_valid _)
    (mul_comm_equiv _ _ (inverse z hz).property z.property) (mul_inverse z hz)

theorem unique (z r s : Scalar)
    (hr : (mul z.val r.val).Equiv (ofQComplex QComplex.one))
    (hs : (mul z.val s.val).Equiv (ofQComplex QComplex.one)) : r.val.Equiv s.val := by
  have hR := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property r.property) (hright := ofQComplex_valid _) hr
  have hS := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property s.property) (hright := ofQComplex_valid _) hs
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := r.property) (hright := s.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw r.val r.property
  let S := ComplexRawQuotient.ofRaw s.val s.property
  change Z*R = 1 at hR
  change Z*S = 1 at hS
  change R=S
  grind

theorem inverse_unique (z : Scalar) (hz : Nonzero z) (r : Scalar)
    (hr : (mul z.val r.val).Equiv (ofQComplex QComplex.one)) :
    (inverse z hz).val.Equiv r.val := unique z _ r (mul_inverse z hz) hr

theorem inverse_congr (z w : Scalar) (hz : Nonzero z) (hw : Nonzero w)
    (hzw : z.val.Equiv w.val) : (inverse z hz).val.Equiv (inverse w hw).val :=
  inverse_unique z hz (inverse w hw) (equiv_trans
    (mul_valid z.property (inverse w hw).property)
    (mul_valid w.property (inverse w hw).property) (ofQComplex_valid _)
    (mul_equiv z.property w.property (inverse w hw).property (inverse w hw).property
      hzw (equiv_refl _ (inverse w hw).property)) (mul_inverse w hw))

theorem zero_ne_one : ¬ zero.Equiv (ofQComplex QComplex.one) := by
  intro h
  have he := (compareAt_overlap_iff zero (ofQComplex QComplex.one) 0 0).1 (h 0)
  change (0 ≤ (1 : Rat) ∧ 0 ≤ (0 : Rat)) ∧ ((1 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 0) at he
  grind

theorem nonzero_of_inverse (z r : Scalar)
    (hr : (mul z.val r.val).Equiv (ofQComplex QComplex.one)) : Nonzero z := by
  intro hz
  have hZ := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := z.property) (hright := ofQComplex_valid _) hz
  have hR := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property r.property) (hright := ofQComplex_valid _) hr
  have he : (0 : ScalarAlgebra.Value) = 1 := by
    change ComplexRawQuotient.ofRaw z.val z.property *
      ComplexRawQuotient.ofRaw r.val r.property = 1 at hR
    change ComplexRawQuotient.ofRaw z.val z.property = 0 at hZ
    rw [hZ] at hR
    grind
  exact zero_ne_one (ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ofQComplex_valid QComplex.zero) (hright := ofQComplex_valid QComplex.one) he)

theorem inverse_nonzero (z : Scalar) (hz : Nonzero z) : Nonzero (inverse z hz) :=
  nonzero_of_inverse (inverse z hz) z (inverse_mul z hz)

theorem involutive (z : Scalar) (hz : Nonzero z) :
    (inverse (inverse z hz) (inverse_nonzero z hz)).val.Equiv z.val :=
  inverse_unique (inverse z hz) (inverse_nonzero z hz) z (inverse_mul z hz)

theorem mul_cancel (z : Scalar) (hz : Nonzero z) (x y : Scalar)
    (hxy : (mul z.val x.val).Equiv (mul z.val y.val)) : x.val.Equiv y.val := by
  have hunit := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property (inverse z hz).property) (hright := ofQComplex_valid _)
    (mul_inverse z hz)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property x.property) (hright := mul_valid z.property y.property) hxy
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := x.property) (hright := y.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let R := ComplexRawQuotient.ofRaw (inverse z hz).val (inverse z hz).property
  let X := ComplexRawQuotient.ofRaw x.val x.property
  let Y := ComplexRawQuotient.ofRaw y.val y.property
  change Z*R=1 at hunit
  change Z*X=Z*Y at he
  change X=Y
  grind

end ComputableAnalysis.RiemannHilbert.RepresentedReciprocal
