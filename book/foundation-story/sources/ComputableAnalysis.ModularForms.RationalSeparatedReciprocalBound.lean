import ComputableAnalysis.ModularForms.RepresentedNegativeHorizontalReciprocalBound

/-! Rational reciprocal bounds for separation in any coordinate direction. -/
namespace ComputableAnalysis.ModularForms

theorem rationalNegativeVertical_reciprocal_bounds (a b eta : Rat)
    (heta : 0<eta) (hb : b≤ -eta) :
    (-(1/eta)≤a/(a*a+b*b) ∧ a/(a*a+b*b)≤1/eta) ∧
    (-(1/eta)≤ -b/(a*a+b*b) ∧ -b/(a*a+b*b)≤1/eta) := by
  have h := rationalVertical_reciprocal_bounds (-a) (-b) eta heta (by grind only)
  constructor <;> constructor <;> grind [Rat.div_def]

theorem rationalSeparated_reciprocal_bounds (a b eta : Rat) (heta : 0<eta)
    (hsep : eta≤a ∨ a≤ -eta ∨ eta≤b ∨ b≤ -eta) :
    (-(1/eta)≤a/(a*a+b*b) ∧ a/(a*a+b*b)≤1/eta) ∧
    (-(1/eta)≤ -b/(a*a+b*b) ∧ -b/(a*a+b*b)≤1/eta) := by
  rcases hsep with h | h | h | h
  · exact rationalHorizontal_reciprocal_bounds a b eta heta h
  · exact rationalNegativeHorizontal_reciprocal_bounds a b eta heta h
  · exact rationalVertical_reciprocal_bounds a b eta heta h
  · exact rationalNegativeVertical_reciprocal_bounds a b eta heta h

theorem rationalSeparated_inverse_coordinate_bound (q : QComplex) (eta : Rat) (heta : 0<eta)
    (hsep : eta≤q.re ∨ q.re≤ -eta ∨ eta≤q.im ∨ q.im≤ -eta) :
    RiemannHilbert.BoxApproximation.coordinateBound (RiemannHilbert.RationalReciprocal.inverse q)≤1/eta := by
  have h := rationalSeparated_reciprocal_bounds q.re q.im eta heta hsep
  unfold RiemannHilbert.BoxApproximation.coordinateBound RiemannHilbert.RationalReciprocal.inverse
    QComplex.normSq qabs
  grind

end ComputableAnalysis.ModularForms
