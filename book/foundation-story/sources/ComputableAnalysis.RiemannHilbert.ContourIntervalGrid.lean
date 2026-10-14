import ComputableAnalysis.RiemannHilbert.ContourContinuousCells

/-! Literal rational interval cells and midpoint tags, with arbitrary finite
refinements certified to stay in their original coarse cell. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def intervalGridStep (I : QInterval) (M : Nat) : Rat := I.width/(M:Rat)
def intervalGridCell (I : QInterval) (M j : Nat) : QInterval :=
  ⟨I.lo+(j:Rat)*intervalGridStep I M,I.lo+((j+1:Nat):Rat)*intervalGridStep I M⟩
def intervalGridTag (I : QInterval) (M j : Nat) : Rat :=
  I.lo+((j:Rat)+1/2)*intervalGridStep I M

theorem intervalGridStep_nonneg (I : QInterval) (M : Nat) (hI : I.lo≤I.hi) (hM : 0<M) :
    0≤intervalGridStep I M := by
  have hw : 0≤I.width := by unfold QInterval.width; grind only
  unfold intervalGridStep
  rw [Rat.div_def]
  exact Rat.mul_nonneg hw (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM)))

theorem intervalGridStep_refinement (I : QInterval) (M F : Nat) (hF : 0<F) :
    (F:Rat)*intervalGridStep I (M*F)=intervalGridStep I M := by
  have he := Rat.mul_inv_cancel (F:Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr hF))
  simp only [intervalGridStep,Rat.natCast_mul,Rat.div_def,Rat.inv_mul_rev]
  grind only

theorem intervalGridStep_total (I : QInterval) (M : Nat) (hM : 0<M) :
    (M:Rat)*intervalGridStep I M=I.width := by
  unfold intervalGridStep
  rw [Rat.mul_comm]
  exact Rat.div_mul_cancel (Rat.ne_of_gt (Rat.natCast_pos.mpr hM))

theorem intervalGridTag_mem_cell (I : QInterval) (M j : Nat) (hI : I.lo≤I.hi) (hM : 0<M) :
    (intervalGridCell I M j).lo≤intervalGridTag I M j ∧
    intervalGridTag I M j≤(intervalGridCell I M j).hi := by
  have hs := intervalGridStep_nonneg I M hI hM
  have h0 := Rat.mul_nonneg (show (0:Rat)≤1/2 by decide +kernel) hs
  unfold intervalGridCell intervalGridTag
  simp only [Rat.natCast_add]
  change I.lo+(j:Rat)*intervalGridStep I M≤I.lo+((j:Rat)+1/2)*intervalGridStep I M ∧
    I.lo+((j:Rat)+1/2)*intervalGridStep I M≤I.lo+((j:Rat)+1)*intervalGridStep I M
  constructor <;> grind only

theorem intervalGridRefinedTag_mem_cell (I : QInterval) (M F j t : Nat)
    (hI : I.lo≤I.hi) (hM : 0<M) (hF : 0<F) (ht : t<F) :
    (intervalGridCell I M j).lo≤intervalGridTag I (M*F) (j*F+t) ∧
    intervalGridTag I (M*F) (j*F+t)≤(intervalGridCell I M j).hi := by
  have hs := intervalGridStep_nonneg I (M*F) hI (Nat.mul_pos hM hF)
  have ht0 : 0≤(t:Rat) := Rat.natCast_nonneg
  have ht1 : (t:Rat)+1≤(F:Rat) := by
    have hh : ((t+1:Nat):Rat)≤(F:Rat) := by exact_mod_cast (show t+1≤F by omega)
    simpa only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel] using hh
  have hl := Rat.mul_nonneg (show 0≤(t:Rat)+1/2 by grind only) hs
  have hu := Rat.mul_le_mul_of_nonneg_right (show (t:Rat)+1/2≤(F:Rat) by grind only) hs
  have he := intervalGridStep_refinement I M F hF
  rw [he] at hu
  unfold intervalGridCell intervalGridTag
  simp only [Rat.natCast_mul,Rat.natCast_add]
  change I.lo+(j:Rat)*intervalGridStep I M≤
    I.lo+((j:Rat)*(F:Rat)+(t:Rat)+1/2)*intervalGridStep I (M*F) ∧
    I.lo+((j:Rat)*(F:Rat)+(t:Rat)+1/2)*intervalGridStep I (M*F)≤
      I.lo+((j:Rat)+1)*intervalGridStep I M
  have hrewrite : ((j:Rat)*(F:Rat)+(t:Rat)+1/2)*intervalGridStep I (M*F)=
      (j:Rat)*intervalGridStep I M+((t:Rat)+1/2)*intervalGridStep I (M*F) := by
    calc
      _ = (j:Rat)*((F:Rat)*intervalGridStep I (M*F))+((t:Rat)+1/2)*intervalGridStep I (M*F) := by grind only
      _ = _ := by rw [he]
  rw [hrewrite]
  constructor <;> grind only

def horizontalIntervalRectangle (I : QInterval) (y : Rat) : QInterval × QInterval := (I,⟨y,y⟩)
def verticalIntervalRectangle (I : QInterval) (x : Rat) : QInterval × QInterval := (⟨x,x⟩,I)

theorem horizontalIntervalRectangle_cell (I : QInterval) (y : Rat) (M j : Nat) :
    rectangleGridCell (horizontalIntervalRectangle I y) M j 0=(intervalGridCell I M j,⟨y,y⟩) := by
  simp [rectangleGridCell,horizontalIntervalRectangle,intervalGridCell,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY,QInterval.width,Rat.div_def]
  constructor <;> grind only

theorem verticalIntervalRectangle_cell (I : QInterval) (x : Rat) (M j : Nat) :
    rectangleGridCell (verticalIntervalRectangle I x) M 0 j=(⟨x,x⟩,intervalGridCell I M j) := by
  simp [rectangleGridCell,verticalIntervalRectangle,intervalGridCell,intervalGridStep,
    rectangleGridStepX,rectangleGridStepY,QInterval.width,Rat.div_def]
  constructor <;> grind only

end ComputableAnalysis.RiemannHilbert.RectangularContour
