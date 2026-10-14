import ComputableAnalysis.RiemannHilbert.ContourGridRefinementAlgebra
import ComputableAnalysis.RiemannHilbert.ContourIntervalGrid

/-! Actual weighted rational interval quadratures. Refinement errors depend
on coarse-cell value oscillation, independently of the number of refinements. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions RadialLogarithmChains
set_option autoImplicit false

def intervalGridTaggedPrefix (sample : Rat → Scalar) (I : QInterval) (M : Nat)
    (tag : Nat → Rat) : Scalar :=
  gridScalarSum M (fun j => scale (intervalGridStep I M) (sample (tag j)))

def intervalGridPrefix (sample : Rat → Scalar) (I : QInterval) (M : Nat) : Scalar :=
  intervalGridTaggedPrefix sample I M (intervalGridTag I M)

theorem intervalGrid_coarse_repeat (sample : Rat → Scalar) (I : QInterval) (M F : Nat) (hF : 0<F) :
    gridScalarSum M (fun j => gridScalarSum F (fun _ =>
      scale (intervalGridStep I (M*F)) (sample (intervalGridTag I M j)))) ≈
      intervalGridPrefix sample I M := by
  apply gridScalarSum_congr M
  intro j
  have he := gridScalarSum_scaled_constant F (intervalGridStep I (M*F)) (sample (intervalGridTag I M j))
  rw [intervalGridStep_refinement I M F hF] at he
  exact he

theorem intervalGridPrefix_refinement_bound (sample : Rat → Scalar) (I : QInterval) (M F : Nat)
    (hI : I.lo≤I.hi) (hM : 0<M) (hF : 0<F) (E : Rat) (hE : 0≤E)
    (hosc : ∀ j t, j<M → t<F → Small (sub
      (sample (intervalGridTag I (M*F) (j*F+t))).val
      (sample (intervalGridTag I M j)).val) E) :
    Small (sub (intervalGridPrefix sample I (M*F)).val (intervalGridPrefix sample I M).val) (I.width*E) := by
  let r := intervalGridStep I (M*F)
  have hr : 0≤r := intervalGridStep_nonneg I (M*F) hI (Nat.mul_pos hM hF)
  let fine := fun j t => scale r (sample (intervalGridTag I (M*F) (j*F+t)))
  let coarse := fun j (_ : Nat) => scale r (sample (intervalGridTag I M j))
  let error := gridScalarSum M (fun j => gridScalarSum F (fun t => gridScalarSub (fine j t) (coarse j t)))
  have hb := gridScalarDoubleSum_bound M F (fun j t => gridScalarSub (fine j t) (coarse j t))
    (r*E) (Rat.mul_nonneg hr hE)
    (fun j t hj ht => RationalDilation.displacement_bound r hr _ _ E (hosc j t hj ht))
  have ht := intervalGridStep_total I (M*F) (Nat.mul_pos hM hF)
  rw [Rat.natCast_mul] at ht
  have hsize : (M:Rat)*((F:Rat)*(r*E))=I.width*E := by
    change (M:Rat)*((F:Rat)*(intervalGridStep I (M*F)*E))=I.width*E
    grind only
  rw [hsize] at hb
  have he1 := gridScalarDoubleSum_sub_agreement M F fine coarse
  have he2 : gridScalarSum M (fun j => gridScalarSum F (fine j)) ≈ intervalGridPrefix sample I (M*F) :=
    Setoid.symm (gridScalarSum_blocks M F (fun j => scale r (sample (intervalGridTag I (M*F) j))))
  have he3 := intervalGrid_coarse_repeat sample I M F hF
  have he : error ≈ gridScalarSub (intervalGridPrefix sample I (M*F)) (intervalGridPrefix sample I M) :=
    Setoid.trans he1 (FunctionTheory.sub_congr he2 he3)
  exact Small.congr error.property
    (sub_valid (intervalGridPrefix sample I (M*F)).property (intervalGridPrefix sample I M).property) he hb

theorem intervalGridTaggedPrefix_difference_bound (sample : Rat → Scalar) (I : QInterval) (M : Nat)
    (hI : I.lo≤I.hi) (hM : 0<M) (tag other : Nat → Rat) (E : Rat) (hE : 0≤E)
    (hosc : ∀ j, j<M → Small (sub (sample (tag j)).val (sample (other j)).val) E) :
    Small (sub (intervalGridTaggedPrefix sample I M tag).val
      (intervalGridTaggedPrefix sample I M other).val) (I.width*E) := by
  let r := intervalGridStep I M
  have hr : 0≤r := intervalGridStep_nonneg I M hI hM
  let f := fun j => scale r (sample (tag j))
  let g := fun j => scale r (sample (other j))
  let error := gridScalarSum M (fun j => gridScalarSub (f j) (g j))
  have hb := gridScalarSum_bound M (fun j => gridScalarSub (f j) (g j)) (r*E) (Rat.mul_nonneg hr hE)
    (fun j hj => RationalDilation.displacement_bound r hr _ _ E (hosc j hj))
  have ht := intervalGridStep_total I M hM
  have hsize : (M:Rat)*(r*E)=I.width*E := by
    change (M:Rat)*(intervalGridStep I M*E)=I.width*E
    grind only
  rw [hsize] at hb
  exact Small.congr error.property
    (sub_valid (intervalGridTaggedPrefix sample I M tag).property
      (intervalGridTaggedPrefix sample I M other).property)
    (gridScalarSum_sub_agreement M f g) hb

end ComputableAnalysis.RiemannHilbert.RectangularContour
