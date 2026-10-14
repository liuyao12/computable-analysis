import ComputableAnalysis.RiemannHilbert.ContourSplitDomains

/-! Actual continuous edge sums respect every rational cut, including the
endpoints. The subedge domain certificates and common meshes are internal. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem horizontalIntervalPrefix_subinterval (f : DomainFunctions.Map) (I K : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (hk : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle K y) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) (hK : K.lo≤K.hi) (M : Nat) (hM : 0<M) :
    intervalGridPrefix (horizontalIntervalSample f I y hf) K M ≈
      intervalGridPrefix (horizontalIntervalSample f K y hk) K M := by
  apply intervalGridPrefix_congr _ _ K M
  intro j hj
  exact Setoid.symm (horizontalIntervalSample_subinterval f I K y hf hk hlo hhi _
    (intervalGridTag_mem_interval K M j hK hM hj))

theorem verticalIntervalPrefix_subinterval (f : DomainFunctions.Map) (I K : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (hk : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle K x) z → f.domain z)
    (hlo : I.lo≤K.lo) (hhi : K.hi≤I.hi) (hK : K.lo≤K.hi) (M : Nat) (hM : 0<M) :
    intervalGridPrefix (verticalIntervalSample f I x hf) K M ≈
      intervalGridPrefix (verticalIntervalSample f K x hk) K M := by
  apply intervalGridPrefix_congr _ _ K M
  intro j hj
  exact Setoid.symm (verticalIntervalSample_subinterval f I K x hf hk hlo hhi _
    (intervalGridTag_mem_interval K M j hK hM hj))

def horizontalSplitError (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (n : Nat) : Scalar :=
  gridScalarSub (horizontalContinuousPrefix f I y hf n) (scalarSum
    (horizontalContinuousPrefix f (splitIntervalLeft I c) y
      (horizontalInterval_subdomain f I _ y hf Rat.le_refl hr) n)
    (horizontalContinuousPrefix f (splitIntervalRight I c) y
      (horizontalInterval_subdomain f I _ y hf hl Rat.le_refl) n))

def verticalSplitError (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (n : Nat) : Scalar :=
  gridScalarSub (verticalContinuousPrefix f I x hf n) (scalarSum
    (verticalContinuousPrefix f (splitIntervalLeft I c) x
      (verticalInterval_subdomain f I _ x hf Rat.le_refl hr) n)
    (verticalContinuousPrefix f (splitIntervalRight I c) x
      (verticalInterval_subdomain f I _ x hf hl Rat.le_refl) n))

theorem horizontalSplitError_shared (f : DomainFunctions.Map) (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (n : Nat) :
    intervalSplitError (horizontalIntervalSample f I y hf) I c n ≈ horizontalSplitError f I y hf c hl hr n := by
  have hL := horizontalIntervalPrefix_subinterval f I (splitIntervalLeft I c) y hf
    (horizontalInterval_subdomain f I _ y hf Rat.le_refl hr) Rat.le_refl hr hl (2^n) (Nat.two_pow_pos n)
  have hR := horizontalIntervalPrefix_subinterval f I (splitIntervalRight I c) y hf
    (horizontalInterval_subdomain f I _ y hf hl Rat.le_refl) hl Rat.le_refl hr (2^n) (Nat.two_pow_pos n)
  exact FunctionTheory.sub_congr (equiv_refl _ (horizontalContinuousPrefix f I y hf n).property) (add_equiv hL hR)

theorem verticalSplitError_shared (f : DomainFunctions.Map) (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (n : Nat) :
    verticalSplitError f I x hf c hl hr n ≈ scalarProduct (rationalRectangleScalar ⟨0,1⟩)
      (intervalSplitError (verticalIntervalSample f I x hf) I c n) := by
  let g := verticalIntervalSample f I x hf
  let leftDom := verticalInterval_subdomain f I (splitIntervalLeft I c) x hf Rat.le_refl hr
  let rightDom := verticalInterval_subdomain f I (splitIntervalRight I c) x hf hl Rat.le_refl
  have hL := verticalIntervalPrefix_subinterval f I (splitIntervalLeft I c) x hf leftDom
    Rat.le_refl hr hl (2^n) (Nat.two_pow_pos n)
  have hR := verticalIntervalPrefix_subinterval f I (splitIntervalRight I c) x hf rightDom
    hl Rat.le_refl hr (2^n) (Nat.two_pow_pos n)
  have heL := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (intervalGridPrefix g (splitIntervalLeft I c) (2^n)).property)
    (hright := (intervalGridPrefix (verticalIntervalSample f (splitIntervalLeft I c) x leftDom) (splitIntervalLeft I c) (2^n)).property) hL
  have heR := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (intervalGridPrefix g (splitIntervalRight I c) (2^n)).property)
    (hright := (intervalGridPrefix (verticalIntervalSample f (splitIntervalRight I c) x rightDom) (splitIntervalRight I c) (2^n)).property) hR
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := (verticalSplitError f I x hf c hl hr n).property)
    (hright := (scalarProduct (rationalRectangleScalar ⟨0,1⟩) (intervalSplitError g I c n)).property)
  let V := gridScalarValue (rationalRectangleScalar ⟨0,1⟩)
  let W := gridScalarValue (intervalGridPrefix g I (2^n))
  let L := gridScalarValue (intervalGridPrefix g (splitIntervalLeft I c) (2^n))
  let R := gridScalarValue (intervalGridPrefix g (splitIntervalRight I c) (2^n))
  let LL := gridScalarValue (intervalGridPrefix (verticalIntervalSample f (splitIntervalLeft I c) x leftDom) (splitIntervalLeft I c) (2^n))
  let RR := gridScalarValue (intervalGridPrefix (verticalIntervalSample f (splitIntervalRight I c) x rightDom) (splitIntervalRight I c) (2^n))
  change L=LL at heL
  change R=RR at heR
  change V*W-(V*LL+V*RR)=V*(W-(L+R))
  grind only

theorem horizontalSplitError_eventual_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (y : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (horizontalSplitError f I y hf c hl hr n).val eps.val := by
  let g := horizontalIntervalSample f I y hf
  obtain ⟨N,hN⟩ := intervalSplitError_eventual_zero g I c hl hr
    (horizontalIntervalSample_oscillation f hc I y (Rat.le_trans hl hr) hf)
    (horizontalIntervalSample_subinterval_oscillation f hc I (splitIntervalLeft I c) y hl hf Rat.le_refl hr)
    (horizontalIntervalSample_subinterval_oscillation f hc I (splitIntervalRight I c) y hr hf hl Rat.le_refl) eps
  exact ⟨N,fun n hn => Small.congr (intervalSplitError g I c n).property
    (horizontalSplitError f I y hf c hl hr n).property (horizontalSplitError_shared f I y hf c hl hr n) (hN n hn)⟩

theorem verticalSplitError_eventual_zero (f : DomainFunctions.Map) (hc : ContinuousOn f.domain f.eval)
    (I : QInterval) (x : Rat)
    (hf : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (c : Rat) (hl : I.lo≤c) (hr : c≤I.hi) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (verticalSplitError f I x hf c hl hr n).val eps.val := by
  let g := verticalIntervalSample f I x hf
  let v := rationalRectangleScalar (⟨0,1⟩ : QComplex)
  let D : QPos := ⟨2*scalarBound v,Rat.mul_pos (by decide +kernel) (scalarBound_pos v)⟩
  let eta := divideRadius eps D
  obtain ⟨N,hN⟩ := intervalSplitError_eventual_zero g I c hl hr
    (verticalIntervalSample_oscillation f hc I x (Rat.le_trans hl hr) hf)
    (verticalIntervalSample_subinterval_oscillation f hc I (splitIntervalLeft I c) x hl hf Rat.le_refl hr)
    (verticalIntervalSample_subinterval_oscillation f hc I (splitIntervalRight I c) x hr hf hl Rat.le_refl) eta
  refine ⟨N, ?_⟩
  intro n hn
  have hb := Small.mul v.property (intervalSplitError g I c n).property (Rat.le_of_lt (scalarBound_pos v))
    (Rat.le_of_lt eta.property) (scalar_small v) (hN n hn)
  have he := divideRadius_identity eps D
  change 2*scalarBound v*eta.val=eps.val at he
  rw [he] at hb
  exact Small.congr (scalarProduct v (intervalSplitError g I c n)).property
    (verticalSplitError f I x hf c hl hr n).property (equiv_symm (verticalSplitError_shared f I x hf c hl hr n)) hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
