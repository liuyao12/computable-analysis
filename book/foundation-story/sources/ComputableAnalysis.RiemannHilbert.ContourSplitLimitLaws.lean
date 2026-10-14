import ComputableAnalysis.RiemannHilbert.ContourContinuousSplit

/-! Actual split errors converge to zero. Independently justified edge
limits satisfy exact addition; no existence or uniqueness field is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem representedSum_difference (p q a b : Scalar) :
    (sub (scalarSum p q).val (scalarSum a b).val).Equiv (add (sub p.val a.val) (sub q.val b.val)) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scalarSum p q).property (scalarSum a b).property)
    (hright := add_valid (sub_valid p.property a.property) (sub_valid q.property b.property))
  let P := gridScalarValue p
  let Q := gridScalarValue q
  let A := gridScalarValue a
  let B := gridScalarValue b
  change (P+Q)-(A+B)=(P-A)+(Q-B)
  grind only

theorem converge_sum (p q : Nat → Scalar) (a b : Scalar) (hp : Converges p a) (hq : Converges q b) :
    Converges (fun n => scalarSum (p n) (q n)) (scalarSum a b) := by
  intro eps
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := hp eta
  obtain ⟨B,hB⟩ := hq eta
  refine ⟨max A B, ?_⟩
  intro n hn
  have hs := LocalODE.small_add (hA n (by omega)) (hB n (by omega))
  have he : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [he] at hs
  exact Small.congr (add_valid (sub_valid (p n).property a.property) (sub_valid (q n).property b.property))
    (sub_valid (scalarSum (p n) (q n)).property (scalarSum a b).property)
    (equiv_symm (representedSum_difference (p n) (q n) a b)) hs

theorem horizontalSplitError_converges_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) :
    Converges (horizontalSplitError f I y hf c hl hr) (rationalRectangleScalar QComplex.zero) :=
  converge_zero _ (horizontalSplitError_eventual_zero f hc I y hf c hl hr)

theorem verticalSplitError_converges_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) :
    Converges (verticalSplitError f I x hf c hl hr) (rationalRectangleScalar QComplex.zero) :=
  converge_zero _ (verticalSplitError_eventual_zero f hc I x hf c hl hr)

theorem horizontalContinuousSplit_limit_identity (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (u v w : Scalar)
    (hu : Converges (horizontalContinuousPrefix f I y hf) u)
    (hv : Converges (horizontalContinuousPrefix f (splitIntervalLeft I c) y
      (horizontalInterval_subdomain f I _ y hf Rat.le_refl hr)) v)
    (hw : Converges (horizontalContinuousPrefix f (splitIntervalRight I c) y
      (horizontalInterval_subdomain f I _ y hf hl Rat.le_refl)) w) : u≈scalarSum v w := by
  apply converge_unique _ _ _ hu
  exact converge_perturbation _ _ _ (converge_sum _ _ v w hv hw)
    (horizontalSplitError_eventual_zero f hc I y hf c hl hr)

theorem verticalContinuousSplit_limit_identity (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (u v w : Scalar)
    (hu : Converges (verticalContinuousPrefix f I x hf) u)
    (hv : Converges (verticalContinuousPrefix f (splitIntervalLeft I c) x
      (verticalInterval_subdomain f I _ x hf Rat.le_refl hr)) v)
    (hw : Converges (verticalContinuousPrefix f (splitIntervalRight I c) x
      (verticalInterval_subdomain f I _ x hf hl Rat.le_refl)) w) : u≈scalarSum v w := by
  apply converge_unique _ _ _ hu
  exact converge_perturbation _ _ _ (converge_sum _ _ v w hv hw)
    (verticalSplitError_eventual_zero f hc I x hf c hl hr)

end ComputableAnalysis.RiemannHilbert.RectangularContour
