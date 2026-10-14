import ComputableAnalysis.RiemannHilbert.ContourSplitLimitLaws

/-! Two rational cuts give the three boundary pieces needed for rectangular
ribbon assembly. Degenerate pieces and endpoint cuts remain in the domain. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem representedNestedSplit_difference (a l t m r : Scalar) :
    (add (sub a.val (scalarSum l t).val) (sub t.val (scalarSum m r).val)).Equiv
      (sub a.val (scalarSum l (scalarSum m r)).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid a.property (scalarSum l t).property) (sub_valid t.property (scalarSum m r).property))
    (hright := sub_valid a.property (scalarSum l (scalarSum m r)).property)
  let A := gridScalarValue a
  let L := gridScalarValue l
  let T := gridScalarValue t
  let M := gridScalarValue m
  let R := gridScalarValue r
  change (A-(L+T))+(T-(M+R))=A-(L+(M+R))
  grind only

def horizontalTripleSplitError (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) (n : Nat) : Scalar :=
  gridScalarSub (horizontalContinuousPrefix f I y hf n) (scalarSum
    (horizontalContinuousPrefix f (splitIntervalLeft I c) y
      (horizontalInterval_subdomain f I _ y hf Rat.le_refl (Rat.le_trans hcd hd)) n)
    (scalarSum (horizontalContinuousPrefix f ⟨c,d⟩ y
      (horizontalInterval_subdomain f I _ y hf hc hd) n)
      (horizontalContinuousPrefix f (splitIntervalRight I d) y
        (horizontalInterval_subdomain f I _ y hf (Rat.le_trans hc hcd) Rat.le_refl) n)))

def verticalTripleSplitError (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) (n : Nat) : Scalar :=
  gridScalarSub (verticalContinuousPrefix f I x hf n) (scalarSum
    (verticalContinuousPrefix f (splitIntervalLeft I c) x
      (verticalInterval_subdomain f I _ x hf Rat.le_refl (Rat.le_trans hcd hd)) n)
    (scalarSum (verticalContinuousPrefix f ⟨c,d⟩ x
      (verticalInterval_subdomain f I _ x hf hc hd) n)
      (verticalContinuousPrefix f (splitIntervalRight I d) x
        (verticalInterval_subdomain f I _ x hf (Rat.le_trans hc hcd) Rat.le_refl) n)))

theorem horizontalTripleSplitError_eventual_zero (f : DomainFunctions.Map) (hcont : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (horizontalTripleSplitError f I y hf c d hc hcd hd n).val eps.val := by
  let K := splitIntervalRight I c
  let hK := horizontalInterval_subdomain f I K y hf hc Rat.le_refl
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := horizontalSplitError_eventual_zero f hcont I y hf c hc (Rat.le_trans hcd hd) eta
  obtain ⟨B,hB⟩ := horizontalSplitError_eventual_zero f hcont K y hK d hcd hd eta
  refine ⟨max A B, ?_⟩
  intro n hn
  have hs := LocalODE.small_add (hA n (by omega)) (hB n (by omega))
  have he : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [he] at hs
  let a := horizontalContinuousPrefix f I y hf n
  let l := horizontalContinuousPrefix f (splitIntervalLeft I c) y
    (horizontalInterval_subdomain f I _ y hf Rat.le_refl (Rat.le_trans hcd hd)) n
  let t := horizontalContinuousPrefix f K y hK n
  let m := horizontalContinuousPrefix f ⟨c,d⟩ y (horizontalInterval_subdomain f I _ y hf hc hd) n
  let r := horizontalContinuousPrefix f (splitIntervalRight I d) y
    (horizontalInterval_subdomain f I _ y hf (Rat.le_trans hc hcd) Rat.le_refl) n
  exact Small.congr
    (add_valid (horizontalSplitError f I y hf c hc (Rat.le_trans hcd hd) n).property
      (horizontalSplitError f K y hK d hcd hd n).property)
    (horizontalTripleSplitError f I y hf c d hc hcd hd n).property
    (representedNestedSplit_difference a l t m r) hs

theorem verticalTripleSplitError_eventual_zero (f : DomainFunctions.Map) (hcont : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (verticalTripleSplitError f I x hf c d hc hcd hd n).val eps.val := by
  let K := splitIntervalRight I c
  let hK := verticalInterval_subdomain f I K x hf hc Rat.le_refl
  let eta := divideRadius eps (⟨2,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := verticalSplitError_eventual_zero f hcont I x hf c hc (Rat.le_trans hcd hd) eta
  obtain ⟨B,hB⟩ := verticalSplitError_eventual_zero f hcont K x hK d hcd hd eta
  refine ⟨max A B, ?_⟩
  intro n hn
  have hs := LocalODE.small_add (hA n (by omega)) (hB n (by omega))
  have he : eta.val+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨2,by decide +kernel⟩ : QPos)
    change 2*eta.val=eps.val at h
    grind only
  rw [he] at hs
  let a := verticalContinuousPrefix f I x hf n
  let l := verticalContinuousPrefix f (splitIntervalLeft I c) x
    (verticalInterval_subdomain f I _ x hf Rat.le_refl (Rat.le_trans hcd hd)) n
  let t := verticalContinuousPrefix f K x hK n
  let m := verticalContinuousPrefix f ⟨c,d⟩ x (verticalInterval_subdomain f I _ x hf hc hd) n
  let r := verticalContinuousPrefix f (splitIntervalRight I d) x
    (verticalInterval_subdomain f I _ x hf (Rat.le_trans hc hcd) Rat.le_refl) n
  exact Small.congr
    (add_valid (verticalSplitError f I x hf c hc (Rat.le_trans hcd hd) n).property
      (verticalSplitError f K x hK d hcd hd n).property)
    (verticalTripleSplitError f I x hf c d hc hcd hd n).property
    (representedNestedSplit_difference a l t m r) hs

theorem horizontalTripleSplitError_converges_zero (f : DomainFunctions.Map) (hcont : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) :
    Converges (horizontalTripleSplitError f I y hf c d hc hcd hd) (rationalRectangleScalar QComplex.zero) :=
  converge_zero _ (horizontalTripleSplitError_eventual_zero f hcont I y hf c d hc hcd hd)

theorem verticalTripleSplitError_converges_zero (f : DomainFunctions.Map) (hcont : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c d : Rat) (hc : I.lo≤c) (hcd : c≤d) (hd : d≤I.hi) :
    Converges (verticalTripleSplitError f I x hf c d hc hcd hd) (rationalRectangleScalar QComplex.zero) :=
  converge_zero _ (verticalTripleSplitError_eventual_zero f hcont I x hf c d hc hcd hd)

end ComputableAnalysis.RiemannHilbert.RectangularContour
