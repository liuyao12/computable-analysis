import ComputableAnalysis.ModularForms.UpperLatticeSampleReciprocal
import ComputableAnalysis.RiemannHilbert.RepresentedReciprocal

/-! Exact reciprocal comparison identities, connecting rational lattice samples
to the represented reciprocal evaluator. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert ComplexRaw FunctionTheory

theorem representedReciprocal_difference (z w : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (hw : NonzeroBoxSearch.Nonzero w) :
    (sub (RepresentedReciprocal.inverse z hz).val
      (RepresentedReciprocal.inverse w hw).val).Equiv
    (mul (mul (RepresentedReciprocal.inverse z hz).val (sub w.val z.val))
      (RepresentedReciprocal.inverse w hw).val) := by
  let r := RepresentedReciprocal.inverse z hz
  let s := RepresentedReciprocal.inverse w hw
  have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid z.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse z hz)
  have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid w.property s.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse w hw)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid r.property s.property)
    (hright := mul_valid (mul_valid r.property (sub_valid w.property z.property)) s.property)
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let W := ComplexRawQuotient.ofRaw w.val w.property
  let R := ComplexRawQuotient.ofRaw r.val r.property
  let S := ComplexRawQuotient.ofRaw s.val s.property
  change Z*R = (1 : ScalarAlgebra.Value) at hr
  change W*S = (1 : ScalarAlgebra.Value) at hs
  change R-S = (R*(W-Z))*S
  grind

theorem representedReciprocal_difference_small (z w : Scalar)
    (hz : NonzeroBoxSearch.Nonzero z) (hw : NonzeroBoxSearch.Nonzero w)
    (B C E : Rat) (hB : 0≤B) (hC : 0≤C) (hE : 0≤E)
    (hr : Small (RepresentedReciprocal.inverse z hz).val B)
    (hs : Small (RepresentedReciprocal.inverse w hw).val C)
    (he : Small (sub w.val z.val) E) :
    Small (sub (RepresentedReciprocal.inverse z hz).val
      (RepresentedReciprocal.inverse w hw).val) (2*(2*B*E)*C) := by
  have hm := Small.mul (RepresentedReciprocal.inverse z hz).property
    (sub_valid w.property z.property) hB hE hr he
  have hp := Small.mul
    (mul_valid (RepresentedReciprocal.inverse z hz).property (sub_valid w.property z.property))
    (RepresentedReciprocal.inverse w hw).property
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hE) hC hm hs
  exact Small.congr
    (mul_valid (mul_valid (RepresentedReciprocal.inverse z hz).property
      (sub_valid w.property z.property)) (RepresentedReciprocal.inverse w hw).property)
    (sub_valid (RepresentedReciprocal.inverse z hz).property
      (RepresentedReciprocal.inverse w hw).property)
    (equiv_symm (representedReciprocal_difference z w hz hw)) hp

/-- Rational sample inversion agrees with the actual represented evaluator;
nonzeroness follows from the checked rational product identity. -/
theorem rationalLatticeInverse_represented (q : QComplex) (x y : Rat)
    (hN : rationalLatticeNorm q x y≠0) :
    let z : Scalar := ⟨ofQComplex ⟨x+y*q.re,y*q.im⟩,ofQComplex_valid _⟩
    let r : Scalar := ⟨ofQComplex (rationalLatticeInverse q x y),ofQComplex_valid _⟩
    ∃ hz : NonzeroBoxSearch.Nonzero z,
      (RepresentedReciprocal.inverse z hz).val.Equiv r.val := by
  let z : Scalar := ⟨ofQComplex ⟨x+y*q.re,y*q.im⟩,ofQComplex_valid _⟩
  let r : Scalar := ⟨ofQComplex (rationalLatticeInverse q x y),ofQComplex_valid _⟩
  have hp : (mul z.val r.val).Equiv (ofQComplex QComplex.one) := by
    have h := RationalReciprocal.raw_mul_constants ⟨x+y*q.re,y*q.im⟩
      (rationalLatticeInverse q x y)
    rw [rationalLatticeInverse_product q x y hN] at h
    exact h
  exact ⟨RepresentedReciprocal.nonzero_of_inverse z r hp,
    RepresentedReciprocal.inverse_unique z _ r hp⟩

end ComputableAnalysis.ModularForms
