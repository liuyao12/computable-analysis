import ComputableAnalysis.RiemannHilbert.ContourBoundaryVanishing

/-! Supplied sequence limits, their proved uniqueness, and the exact zero
candidate for actual holomorphic rectangle boundary computations. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def Converges (p : Nat → Scalar) (a : Scalar) : Prop :=
  ∀ eps : QPos, ∃ N, ∀ n, N≤n → Small (sub (p n).val a.val) eps.val

theorem small_zero_of_all_errors (z : ComplexRaw) (h : ∀ eps : QPos, Small z eps.val) :
    Small z 0 := by
  apply SeriesLimitLaws.small_closed z 0 (fun n => (RepresentedCauchySum.error n).val)
    RepresentedCauchySum.error_shrinks
  intro n
  simpa only [Rat.zero_add] using h (RepresentedCauchySum.error n)

theorem converge_unique (p : Nat → Scalar) (a b : Scalar)
    (ha : Converges p a) (hb : Converges p b) : a ≈ b := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply small_zero_of_all_errors
  intro eps
  let eta : QPos := ⟨eps.val/2,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩
  obtain ⟨A,hA⟩ := ha eta
  obtain ⟨B,hB⟩ := hb eta
  let n := max A B
  have hs := LocalODE.small_add
    (RepresentedCauchySum.small_sub_symm _ _ _ (hA n (Nat.le_max_left _ _)))
    (hB n (Nat.le_max_right _ _))
  have he : eta.val+eta.val=eps.val := by dsimp [eta]; grind only
  rw [he] at hs
  exact Small.congr (add_valid (sub_valid a.property (p n).property)
    (sub_valid (p n).property b.property)) (sub_valid a.property b.property)
    (representedDifference_split a (p n) b) hs

theorem converge_congr (p q : Nat → Scalar) (a : Scalar)
    (hp : Converges p a) (he : ∀ n, p n ≈ q n) : Converges q a := by
  intro eps
  obtain ⟨N,hN⟩ := hp eps
  exact ⟨N,fun n hn => Small.congr (sub_valid (p n).property a.property)
    (sub_valid (q n).property a.property)
    (FunctionTheory.sub_congr (he n) (equiv_refl _ a.property)) (hN n hn)⟩

theorem converge_zero (p : Nat → Scalar)
    (hp : ∀ eps : QPos, ∃ N, ∀ n, N≤n → Small (p n).val eps.val) :
    Converges p ⟨zero,ofQComplex_valid _⟩ := by
  intro eps
  obtain ⟨N,hN⟩ := hp eps
  refine ⟨N,fun n hn => ?_⟩
  have he : (sub (p n).val zero).Equiv (p n).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (p n).property (ofQComplex_valid _)) (hright := (p n).property)
    change ComplexRawQuotient.ofRaw (p n).val (p n).property-0=
      ComplexRawQuotient.ofRaw (p n).val (p n).property
    grind only
  exact Small.congr (p n).property (sub_valid (p n).property (ofQComplex_valid _))
    (equiv_symm he) (hN n hn)

theorem holomorphic_rectangle_zero (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) :
    Converges (holomorphicRectangleGridBoundary f hf J hdom) ⟨zero,ofQComplex_valid _⟩ :=
  converge_zero _ (holomorphicRectangleGridBoundary_converges_zero f hf J hdom hX hY)

theorem holomorphic_rectangle_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval)
    (hdom : ∀ z : Scalar, representedRectangleContains J z → f.domain z)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi) (a : Scalar)
    (ha : Converges (holomorphicRectangleGridBoundary f hf J hdom) a) :
    a.val.Equiv zero :=
  converge_unique _ a _ ha (holomorphic_rectangle_zero f hf J hdom hX hY)

end ComputableAnalysis.RiemannHilbert.RectangularContour
