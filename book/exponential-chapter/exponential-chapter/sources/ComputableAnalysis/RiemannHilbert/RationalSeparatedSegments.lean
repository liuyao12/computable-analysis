import ComputableAnalysis.RiemannHilbert.RationalLogarithmAnchor

/-! Quantitative geometry of rational affine segments. A directed coordinate
separates the entire segment from zero and supplies a uniform rational
reciprocal bound for the logarithm mesh construction. -/
namespace ComputableAnalysis.RiemannHilbert.RationalSeparatedSegments
open ComplexRaw FunctionTheory LocalODE BoxApproximation

inductive Axis where | real | imag
def coordinate : Axis → QComplex → Rat
  | .real, z => z.re
  | .imag, z => z.im
def directed (axis : Axis) (positive : Bool) (z : QComplex) : Rat :=
  if positive then coordinate axis z else -coordinate axis z

def point (p q : QComplex) (t : Rat) : QComplex :=
  ⟨(1-t)*p.re+t*q.re,(1-t)*p.im+t*q.im⟩

theorem point_zero (p q : QComplex) : point p q 0=p := by
  cases p; cases q; simp [point]; constructor <;> grind only
theorem point_one (p q : QComplex) : point p q 1=q := by
  cases p; cases q; simp [point]; constructor <;> grind only

theorem directed_point (axis : Axis) (positive : Bool) (p q : QComplex) (t : Rat) :
    directed axis positive (point p q t)=(1-t)*directed axis positive p+t*directed axis positive q := by
  cases axis <;> cases positive <;> dsimp [directed,coordinate,point] <;> grind only

structure Separation (p q : QComplex) where
  axis : Axis
  positive : Bool
  gap : QPos
  lower_left : gap.val ≤ directed axis positive p
  lower_right : gap.val ≤ directed axis positive q

theorem directed_lower (p q : QComplex) (h : Separation p q) (t : Rat) (ht : UniformPath.unitInterval t) :
    h.gap.val ≤ directed h.axis h.positive (point p q t) := by
  have hl := Rat.mul_le_mul_of_nonneg_left h.lower_left (show 0 ≤ 1-t by grind only)
  have hr := Rat.mul_le_mul_of_nonneg_left h.lower_right ht.1
  rw [directed_point]
  grind only

private theorem square_mono (a b : Rat) (ha : 0 ≤ a) (hab : a ≤ b) : a*a ≤ b*b := by
  have hb : 0 ≤ b := Rat.le_trans ha hab
  have h1 := Rat.mul_le_mul_of_nonneg_left hab ha
  have h2 := Rat.mul_le_mul_of_nonneg_right hab hb
  grind only

theorem normSq_lower (p q : QComplex) (h : Separation p q) (t : Rat) (ht : UniformPath.unitInterval t) :
    h.gap.val*h.gap.val ≤ QComplex.normSq (point p q t) := by
  have hl := directed_lower p q h t ht
  have hs := square_mono _ _ (Rat.le_of_lt h.gap.property) hl
  have hr := rat_square_nonneg_basic (point p q t).re
  have hi := rat_square_nonneg_basic (point p q t).im
  cases ha : h.axis <;> cases hp : h.positive <;>
    simp only [directed,coordinate,ha,hp,Bool.false_eq_true,if_false,if_true] at hs <;>
    unfold QComplex.normSq <;> grind only

theorem normSq_ne_zero (p q : QComplex) (h : Separation p q) (t : Rat) (ht : UniformPath.unitInterval t) :
    QComplex.normSq (point p q t) ≠ 0 := by
  have hl := normSq_lower p q h t ht
  have hp := Rat.mul_pos h.gap.property h.gap.property
  exact Rat.ne_of_gt (by grind only)

def bound (p q : QComplex) : Rat := max (coordinateBound p) (coordinateBound q)
theorem bound_nonneg (p q : QComplex) : 0 ≤ bound p q := by
  have hp := coordinateBound_nonneg p
  unfold bound
  grind

private theorem convex_bound (u v C t : Rat) (hu : -C ≤ u ∧ u ≤ C) (hv : -C ≤ v ∧ v ≤ C)
    (ht : UniformPath.unitInterval t) : -C ≤ (1-t)*u+t*v ∧ (1-t)*u+t*v ≤ C := by
  have htc : 0 ≤ 1-t := by grind only
  have h1 := Rat.mul_le_mul_of_nonneg_left hu.1 htc
  have h2 := Rat.mul_le_mul_of_nonneg_left hv.1 ht.1
  have h3 := Rat.mul_le_mul_of_nonneg_left hu.2 htc
  have h4 := Rat.mul_le_mul_of_nonneg_left hv.2 ht.1
  constructor <;> grind only

theorem point_bound (p q : QComplex) (t : Rat) (ht : UniformPath.unitInterval t) :
    coordinateBound (point p q t) ≤ bound p q := by
  have hp := coordinateBound_bounds p
  have hq := coordinateBound_bounds q
  have hpb : coordinateBound p ≤ bound p q := by unfold bound; grind
  have hqb : coordinateBound q ≤ bound p q := by unfold bound; grind
  have hr := convex_bound p.re q.re (bound p q) t (by constructor <;> grind only) (by constructor <;> grind only) ht
  have hi := convex_bound p.im q.im (bound p q) t (by constructor <;> grind only) (by constructor <;> grind only) ht
  dsimp [coordinateBound,point,qabs]
  split <;> split <;> grind

def inverseBound (p q : QComplex) (h : Separation p q) : Rat := bound p q/(h.gap.val*h.gap.val)
theorem inverseBound_nonneg (p q : QComplex) (h : Separation p q) : 0 ≤ inverseBound p q h :=
  Rat.mul_nonneg (bound_nonneg p q) (Rat.le_of_lt ((Rat.inv_pos).2 (Rat.mul_pos h.gap.property h.gap.property)))

theorem inverse_bound (p q : QComplex) (h : Separation p q) (t : Rat) (ht : UniformPath.unitInterval t) :
    coordinateBound (RationalReciprocal.inverse (point p q t)) ≤ inverseBound p q h :=
  RationalReciprocal.coordinateBound_inverse _ _ _ (bound_nonneg p q) (Rat.mul_pos h.gap.property h.gap.property)
    (normSq_lower p q h t ht) (point_bound p q t ht)

end ComputableAnalysis.RiemannHilbert.RationalSeparatedSegments
