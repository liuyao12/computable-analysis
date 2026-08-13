import ComputableAnalysis.FiniteChordPowerExample
import ComputableAnalysis.FiniteHeronExample

/-!
# Reusable finite interfaces for classical geometry formulas

The formulas are exposed as rational certificates.  A square-root output is
transported to `RealRaw` only when its rational witness has been checked.
-/

namespace ComputableAnalysis
namespace RationalCircle

theorem horizontalChordPower_certificate {r h t : Rat}
    (hcircle : r * r + h * h = 1)
    (hr : 0 <= r)
    (hout : r <= t ∨ t <= -r) :
    0 <= (t + r) * (t - r) ∧
      (t + r) * (t - r) = t * t + h * h - 1 := by
  exact ⟨horizontalChord_power_nonneg_of_outside hr hout,
    horizontalChord_power_identity hcircle⟩

theorem heronAreaRaw_equiv_of_coordinate_certificate
    (p q r : PiCirclePoint) (a b c : Rat)
    (hprod : 0 <= heronProduct a b c)
    (hsquare : heronProduct a b c =
      (triangleTwiceArea p q r / 2) ^ 2) :
    (heronAreaRaw a b c hprod).Equiv
      (RealRaw.ofRat (qabs (triangleTwiceArea p q r / 2))) := by
  have h := heronAreaRaw_equiv_of_square a b c
    (triangleTwiceArea p q r / 2) hprod (by
      simpa [sq, Rat.pow_succ] using hsquare.symm)
  simpa [qabs_eq_self_of_nonneg (qabs_nonneg _)] using h

end RationalCircle
end ComputableAnalysis
