import ComputableAnalysis.RiemannHilbert.ContourRationalSplitAlignment
import ComputableAnalysis.RiemannHilbert.ContourIntegerRefinement

/-! A rational cut preserves the actual interval quadrature limit. Common
meshes are constructed internally, including endpoint and zero-width cuts. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

def intervalSplitError (sample : Rat → Scalar) (I : QInterval) (c : Rat) (n : Nat) : Scalar :=
  gridScalarSub (intervalGridPrefix sample I (2^n))
    (scalarSum (intervalGridPrefix sample (splitIntervalLeft I c) (2^n))
      (intervalGridPrefix sample (splitIntervalRight I c) (2^n)))

theorem representedSplit_difference (x w a b l r : Scalar) (he : w ≈ scalarSum a b) :
    (add (add (sub x.val w.val) (sub a.val l.val)) (sub b.val r.val)).Equiv
      (sub x.val (scalarSum l r).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (add_valid (sub_valid x.property w.property) (sub_valid a.property l.property))
      (sub_valid b.property r.property))
    (hright := sub_valid x.property (scalarSum l r).property)
  have hw := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := w.property) (hright := (scalarSum a b).property) he
  let X := gridScalarValue x
  let W := gridScalarValue w
  let A := gridScalarValue a
  let B := gridScalarValue b
  let L := gridScalarValue l
  let R := gridScalarValue r
  change W=A+B at hw
  change ((X-W)+(A-L))+(B-R)=X-(L+R)
  grind only

theorem intervalSplitError_strict_eventual (sample : Rat → Scalar) (I : QInterval) (c : Rat)
    (hl : I.lo<c) (hr : c<I.hi) (hwhole : intervalCellOscillation sample I)
    (hleft : intervalCellOscillation sample (splitIntervalLeft I c))
    (hright : intervalCellOscillation sample (splitIntervalRight I c)) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (intervalSplitError sample I c n).val eps.val := by
  let eta := divideRadius eps (⟨3,by decide +kernel⟩ : QPos)
  obtain ⟨A,hA⟩ := intervalGridPrefix_eventual_integer_refinement sample I (by grind only) hwhole eta
  obtain ⟨B,hB⟩ := intervalGridPrefix_eventual_integer_refinement sample (splitIntervalLeft I c)
    (Rat.le_of_lt hl) hleft eta
  obtain ⟨C,hC⟩ := intervalGridPrefix_eventual_integer_refinement sample (splitIntervalRight I c)
    (Rat.le_of_lt hr) hright eta
  let L := rationalSplitLeftCount I c
  let R := rationalSplitRightCount I c
  have hL : 0<L := rationalSplitLeftCount_pos I c hl
  have hR : 0<R := rationalSplitRightCount_pos I c hr
  refine ⟨max A (max B C), ?_⟩
  intro n hn
  have hw := hA n (by omega) (L+R) (by omega)
  have hleft := hB n (by omega) L hL
  have hright := hC n (by omega) R hR
  rw [Nat.mul_comm (2^n) (L+R)] at hw
  rw [Nat.mul_comm (2^n) L] at hleft
  rw [Nat.mul_comm (2^n) R] at hright
  have hs := LocalODE.small_add
    (LocalODE.small_add (RepresentedCauchySum.small_sub_symm _ _ _ hw) hleft) hright
  have heps : (eta.val+eta.val)+eta.val=eps.val := by
    have h := divideRadius_identity eps (⟨3,by decide +kernel⟩ : QPos)
    change 3*eta.val=eps.val at h
    grind only
  rw [heps] at hs
  let x := intervalGridPrefix sample I (2^n)
  let w := intervalGridPrefix sample I ((L+R)*2^n)
  let a := intervalGridPrefix sample (splitIntervalLeft I c) (L*2^n)
  let b := intervalGridPrefix sample (splitIntervalRight I c) (R*2^n)
  let l := intervalGridPrefix sample (splitIntervalLeft I c) (2^n)
  let r := intervalGridPrefix sample (splitIntervalRight I c) (2^n)
  exact Small.congr
    (add_valid (add_valid (sub_valid x.property w.property) (sub_valid a.property l.property))
      (sub_valid b.property r.property)) (intervalSplitError sample I c n).property
    (representedSplit_difference x w a b l r (rationalSplit_prefix_aligned sample I c hl hr (2^n) (Nat.two_pow_pos n))) hs

theorem intervalGridPrefix_zero_width (sample : Rat → Scalar) (I : QInterval) (he : I.lo=I.hi) (M : Nat) :
    intervalGridPrefix sample I M ≈ rationalRectangleScalar QComplex.zero := by
  have hs : intervalGridStep I M=0 := by
    unfold intervalGridStep QInterval.width
    rw [he]
    have hz : I.hi-I.hi=0 := by grind only
    rw [hz,Rat.div_def,Rat.zero_mul]
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (intervalGridPrefix sample I M).property) (hright := (ofQComplex_valid _))
  change gridScalarValue (gridScalarSum M (fun j => scale (intervalGridStep I M) (sample (intervalGridTag I M j))))=0
  rw [gridScalarSum_value,hs]
  change gridValueSum M (fun j => ComplexRawQuotient.scaleRat 0 (gridScalarValue (sample (intervalGridTag I M j))))=0
  simp only [ComplexRawQuotient.scaleRat_zeroScalar]
  exact gridValueSum_zero M

theorem intervalSplitError_at_lo (sample : Rat → Scalar) (I : QInterval) (n : Nat) :
    intervalSplitError sample I I.lo n ≈ rationalRectangleScalar QComplex.zero := by
  have hzero := intervalGridPrefix_zero_width sample (splitIntervalLeft I I.lo) rfl (2^n)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (intervalGridPrefix sample (splitIntervalLeft I I.lo) (2^n)).property)
    (hright := (ofQComplex_valid _)) hzero
  change gridScalarValue (intervalGridPrefix sample (splitIntervalLeft I I.lo) (2^n))=0 at he
  have hr : splitIntervalRight I I.lo=I := by cases I; rfl
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (intervalSplitError sample I I.lo n).property) (hright := (ofQComplex_valid _))
  change gridScalarValue (intervalGridPrefix sample I (2^n))-
    (gridScalarValue (intervalGridPrefix sample (splitIntervalLeft I I.lo) (2^n))+
      gridScalarValue (intervalGridPrefix sample (splitIntervalRight I I.lo) (2^n)))=0
  rw [hr,he]
  grind only

theorem intervalSplitError_at_hi (sample : Rat → Scalar) (I : QInterval) (n : Nat) :
    intervalSplitError sample I I.hi n ≈ rationalRectangleScalar QComplex.zero := by
  have hzero := intervalGridPrefix_zero_width sample (splitIntervalRight I I.hi) rfl (2^n)
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := (intervalGridPrefix sample (splitIntervalRight I I.hi) (2^n)).property)
    (hright := (ofQComplex_valid _)) hzero
  change gridScalarValue (intervalGridPrefix sample (splitIntervalRight I I.hi) (2^n))=0 at he
  have hl : splitIntervalLeft I I.hi=I := by cases I; rfl
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (intervalSplitError sample I I.hi n).property) (hright := (ofQComplex_valid _))
  change gridScalarValue (intervalGridPrefix sample I (2^n))-
    (gridScalarValue (intervalGridPrefix sample (splitIntervalLeft I I.hi) (2^n))+
      gridScalarValue (intervalGridPrefix sample (splitIntervalRight I I.hi) (2^n)))=0
  rw [hl,he]
  grind only

theorem intervalSplitError_eventual_zero (sample : Rat → Scalar) (I : QInterval) (c : Rat)
    (hl : I.lo≤c) (hr : c≤I.hi) (hwhole : intervalCellOscillation sample I)
    (hleft : intervalCellOscillation sample (splitIntervalLeft I c))
    (hright : intervalCellOscillation sample (splitIntervalRight I c)) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (intervalSplitError sample I c n).val eps.val := by
  by_cases hL : I.lo<c
  · by_cases hR : c<I.hi
    · exact intervalSplitError_strict_eventual sample I c hL hR hwhole hleft hright eps
    · have he : c=I.hi := by grind only
      subst c
      exact ⟨0,fun n _ => Small.congr (ofQComplex_valid _) (intervalSplitError sample I I.hi n).property
        (equiv_symm (intervalSplitError_at_hi sample I n)) (Small.zero (Rat.le_of_lt eps.property))⟩
  · have he : c=I.lo := by grind only
    subst c
    exact ⟨0,fun n _ => Small.congr (ofQComplex_valid _) (intervalSplitError sample I I.lo n).property
      (equiv_symm (intervalSplitError_at_lo sample I n)) (Small.zero (Rat.le_of_lt eps.property))⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
