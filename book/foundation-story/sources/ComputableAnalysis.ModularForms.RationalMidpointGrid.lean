import ComputableAnalysis.ModularForms.RepresentedGridCancellation

/-! Literal Cartesian midpoint grids for the actual finite Stokes assembly. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def rectangleGridStepX (J : QInterval × QInterval) (M : Nat) : Rat := J.1.width/(M:Rat)
def rectangleGridStepY (J : QInterval × QInterval) (M : Nat) : Rat := J.2.width/(M:Rat)
def rectangleGridCell (J : QInterval × QInterval) (M j k : Nat) : QInterval × QInterval :=
  (⟨J.1.lo+(j:Rat)*rectangleGridStepX J M,J.1.lo+((j+1:Nat):Rat)*rectangleGridStepX J M⟩,
   ⟨J.2.lo+(k:Rat)*rectangleGridStepY J M,J.2.lo+((k+1:Nat):Rat)*rectangleGridStepY J M⟩)
def rectangleGridHorizontalPoint (J : QInterval × QInterval) (M j k : Nat) : QComplex :=
  ⟨J.1.lo+((j:Rat)+1/2)*rectangleGridStepX J M,J.2.lo+(k:Rat)*rectangleGridStepY J M⟩
def rectangleGridVerticalPoint (J : QInterval × QInterval) (M j k : Nat) : QComplex :=
  ⟨J.1.lo+(j:Rat)*rectangleGridStepX J M,J.2.lo+((k:Rat)+1/2)*rectangleGridStepY J M⟩

theorem rectangleGridCell_widths (J : QInterval × QInterval) (M j k : Nat) :
    (rectangleGridCell J M j k).1.width=rectangleGridStepX J M ∧
    (rectangleGridCell J M j k).2.width=rectangleGridStepY J M := by
  simp only [rectangleGridCell,QInterval.width,Rat.natCast_add]
  change (J.1.lo+(j+1)*rectangleGridStepX J M)-(J.1.lo+j*rectangleGridStepX J M)=rectangleGridStepX J M ∧
    (J.2.lo+(k+1)*rectangleGridStepY J M)-(J.2.lo+k*rectangleGridStepY J M)=rectangleGridStepY J M
  grind only

theorem rectangleGridCell_midpoints (J : QInterval × QInterval) (M j k : Nat) :
    rectangleRight (rectangleGridCell J M j k)=rectangleGridVerticalPoint J M (j+1) k ∧
    rectangleLeft (rectangleGridCell J M j k)=rectangleGridVerticalPoint J M j k ∧
    rectangleTop (rectangleGridCell J M j k)=rectangleGridHorizontalPoint J M j (k+1) ∧
    rectangleBottom (rectangleGridCell J M j k)=rectangleGridHorizontalPoint J M j k := by
  simp only [rectangleRight,rectangleLeft,rectangleTop,rectangleBottom,rectangleGridCell,
    rectangleGridHorizontalPoint,rectangleGridVerticalPoint,QInterval.midpoint,QComplex.mk.injEq,Rat.natCast_add]
  grind only

def rectangleGridHorizontal (f : QComplex → Scalar) (J : QInterval × QInterval)
    (M j k : Nat) : Scalar :=
  scalarProduct (f (rectangleGridHorizontalPoint J M j k))
    (rationalRectangleScalar ⟨rectangleGridStepX J M,0⟩)
def rectangleGridVertical (f : QComplex → Scalar) (J : QInterval × QInterval)
    (M j k : Nat) : Scalar :=
  scalarProduct (f (rectangleGridVerticalPoint J M j k))
    (rationalRectangleScalar ⟨0,rectangleGridStepY J M⟩)

theorem rectangleGridCell_contains_initial (J : QInterval × QInterval)
    (M j k : Nat) (hM : 0<M) (hj : j<M) (hk : k<M)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (q : QComplex) (hq : rationalRectangleContains (rectangleGridCell J M j k) q) :
    rationalRectangleContains J q := by
  have hm : 0<(M:Rat) := Rat.natCast_pos.mpr hM
  have hx0 : 0≤J.1.width := by unfold QInterval.width; grind only
  have hy0 : 0≤J.2.width := by unfold QInterval.width; grind only
  have hsx : 0≤rectangleGridStepX J M := by
    unfold rectangleGridStepX
    rw [Rat.div_def]
    exact Rat.mul_nonneg hx0 (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have hsy : 0≤rectangleGridStepY J M := by
    unfold rectangleGridStepY
    rw [Rat.div_def]
    exact Rat.mul_nonneg hy0 (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have hmx : (M:Rat)*rectangleGridStepX J M=J.1.width := by
    unfold rectangleGridStepX
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel (Rat.ne_of_gt hm)
  have hmy : (M:Rat)*rectangleGridStepY J M=J.2.width := by
    unfold rectangleGridStepY
    rw [Rat.mul_comm]
    exact Rat.div_mul_cancel (Rat.ne_of_gt hm)
  have hjr : ((j+1:Nat):Rat)≤(M:Rat) := by exact_mod_cast (show j+1≤M by omega)
  have hkr : ((k+1:Nat):Rat)≤(M:Rat) := by exact_mod_cast (show k+1≤M by omega)
  have hj0 : 0≤(j:Rat) := Rat.natCast_nonneg
  have hk0 : 0≤(k:Rat) := Rat.natCast_nonneg
  have hjlo := Rat.mul_nonneg hj0 hsx
  have hklo := Rat.mul_nonneg hk0 hsy
  have hjhi := Rat.mul_le_mul_of_nonneg_right hjr hsx
  have hkhi := Rat.mul_le_mul_of_nonneg_right hkr hsy
  rw [hmx] at hjhi
  rw [hmy] at hkhi
  change J.1.lo+(j:Rat)*rectangleGridStepX J M≤q.re ∧
    q.re≤J.1.lo+((j+1:Nat):Rat)*rectangleGridStepX J M ∧
    J.2.lo+(k:Rat)*rectangleGridStepY J M≤q.im ∧
    q.im≤J.2.lo+((k+1:Nat):Rat)*rectangleGridStepY J M at hq
  unfold rationalRectangleContains
  unfold QInterval.width at hjhi hkhi
  grind only

end ComputableAnalysis.ModularForms
