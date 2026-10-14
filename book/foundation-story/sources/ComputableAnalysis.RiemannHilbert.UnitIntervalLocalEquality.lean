import ComputableAnalysis.RiemannHilbert.UnitIntervalOpenCover
import ComputableAnalysis.RiemannHilbert.RationalParameterCuts

/-! Local value equality propagates along the represented unit interval.
The finite bisection cover is proved from pointwise open coverage, and its
neighboring rational cells meet at an actual common rational parameter. -/
namespace ComputableAnalysis.RiemannHilbert.UnitInterval
universe u v
open ComplexRaw FunctionTheory RectangularContour
set_option autoImplicit false
variable {I : Type u} {X : Type v} [Setoid X]

theorem rational_endpoint_contains (J : QInterval) (h0 : 0≤J.lo) (hJ : J.lo≤J.hi) (h1 : J.hi≤1) :
    intervalContains J (⟨J.lo,h0,Rat.le_trans hJ h1⟩ : RationalParameter).point ∧
      intervalContains J (⟨J.hi,Rat.le_trans h0 hJ,h1⟩ : RationalParameter).point := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> intro k l
  · exact Rat.le_refl
  · exact hJ
  · exact hJ
  · exact Rat.le_refl

namespace RationalOpenCover

theorem endpoint_values_equal (U : I → Point → Prop) (value : Point → X)
    (localEqual : ∀ i s t, U i s → U i t → value s≈value t)
    (J : QInterval) (hc : RationalOpenCover U J) :
    ∀ h0 : 0≤J.lo, ∀ hJ : J.lo≤J.hi, ∀ h1 : J.hi≤1,
      value (⟨J.lo,h0,Rat.le_trans hJ h1⟩ : RationalParameter).point≈
        value (⟨J.hi,Rat.le_trans h0 hJ,h1⟩ : RationalParameter).point := by
  induction hc with
  | cell J i inside =>
    intro h0 hJ h1
    have hp := rational_endpoint_contains J h0 hJ h1
    exact localEqual i _ _ (inside _ hp.1) (inside _ hp.2)
  | split J hl hr il ir =>
    intro h0 hJ h1
    have bl := bisectInterval_bounds J hJ false
    have br := bisectInterval_bounds J hJ true
    exact Setoid.trans
      (il (Rat.le_trans h0 bl.1) bl.2.1 (Rat.le_trans bl.2.2 h1))
      (ir (Rat.le_trans h0 br.1) br.2.1 (Rat.le_trans br.2.2 h1))

end RationalOpenCover

/-- Equality on each member of a pointwise relative-open cover proves
endpoint equality. No uniform radius or finite cover is a caller input. -/
theorem values_equal_of_local (U : I → Point → Prop) (hU : ∀ i, IsOpen (U i))
    (cover : ∀ s, ∃ i, U i s) (value : Point → X)
    (localEqual : ∀ i s t, U i s → U i t → value s≈value t) :
    value UnitInterval.zero≈value UnitInterval.one :=
  RationalOpenCover.endpoint_values_equal U value localEqual ⟨0,1⟩ (rational_open_cover U hU cover)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end ComputableAnalysis.RiemannHilbert.UnitInterval
