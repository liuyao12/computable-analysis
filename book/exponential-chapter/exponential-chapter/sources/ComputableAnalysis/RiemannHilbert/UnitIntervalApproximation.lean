import ComputableAnalysis.RiemannHilbert.UnitIntervalTopology
import ComputableAnalysis.RiemannHilbert.BoxApproximation

/-! Executable rational approximations which stay in the closed unit
interval. Clamping the midpoint is justified even when the input's early
box extends past an endpoint. No represented-real comparison is decided. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
open ComplexRaw FunctionTheory

def clamp (q : Rat) : Rat := max 0 (min 1 q)

theorem clamp_bounds (q : Rat) : 0 ≤ clamp q ∧ clamp q ≤ 1 := by
  unfold clamp
  grind

def approximation (t : Point) (eps : QPos) : Rat :=
  let k := PrecisionSearch.stage (scalar t).val (scalar t).property eps
  let I := t.value.compute k
  clamp ((I.lo+I.hi)/2)

theorem approximation_bounds (t : Point) (eps : QPos) :
    0 ≤ approximation t eps ∧ approximation t eps ≤ 1 := clamp_bounds _

theorem clamped_midpoint_mem (t : Point) (k : Nat) :
    (t.value.compute k).lo ≤ clamp (((t.value.compute k).lo+(t.value.compute k).hi)/2) ∧
    clamp (((t.value.compute k).lo+(t.value.compute k).hi)/2) ≤ (t.value.compute k).hi := by
  have hl := t.lower 0 k
  have hu := t.upper k 0
  have ho := RealRaw.interval_order_of_valid t.value t.valid k
  change 0 ≤ (t.value.compute k).hi at hl
  change (t.value.compute k).lo ≤ 1 at hu
  unfold clamp
  grind

def approximatePoint (t : Point) (eps : QPos) : Point :=
  rational (approximation t eps) (approximation_bounds t eps).1 (approximation_bounds t eps).2

theorem approximation_error (t : Point) (eps : QPos) :
    Small (sub (scalar t).val (ofQComplex (QComplex.ofRat (approximation t eps)))) eps.val := by
  let k := PrecisionSearch.stage (scalar t).val (scalar t).property eps
  apply BoxApproximation.point_error (scalar t) k _ eps.val (Rat.le_of_lt eps.property)
  · have h := clamped_midpoint_mem t k
    change ((t.value.compute k).lo ≤ approximation t eps ∧ (0 : Rat) ≤ 0) ∧
      (approximation t eps ≤ (t.value.compute k).hi ∧ (0 : Rat) ≤ 0)
    exact ⟨⟨h.1,Rat.le_refl⟩,⟨h.2,Rat.le_refl⟩⟩
  · exact (PrecisionSearch.stage_spec (scalar t).val (scalar t).property eps).1
  · exact (PrecisionSearch.stage_spec (scalar t).val (scalar t).property eps).2

theorem approximatePoint_error (t : Point) (eps : QPos) :
    Small (sub (scalar t).val (scalar (approximatePoint t eps)).val) eps.val :=
  Small.congr (sub_valid (scalar t).property (ofQComplex_valid _))
    (sub_valid (scalar t).property (scalar (approximatePoint t eps)).property)
    (add_equiv (equiv_refl _ (scalar t).property) (neg_equiv (equiv_symm (scalar_rational _ _ _))))
    (approximation_error t eps)

end ComputableAnalysis.RiemannHilbert.UnitInterval
