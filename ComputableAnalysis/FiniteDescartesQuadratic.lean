import ComputableAnalysis.PolynomialDescartes

/-!
# A parametric two-variation Descartes certificate

For a rational quadratic with positive leading and constant coefficients and
negative middle coefficient, the supplied coefficient list has two sign
variations.  The accompanying root statement is the finite rational
two-root bound, proved by the quadratic factor identity.  This is a
certificate-level boundary for item 100; it is not the general real-root
counting theorem.
-/

namespace ComputableAnalysis

namespace Polynomial

theorem quadratic_two_variation_certificate
    {a b c : Rat} (ha : 0 < a) (hb : b < 0) (hc : 0 < c) :
    signChangeCountIgnoringZeros [a, b, c] = 2 /\
      (forall x y z : Rat,
        0 < x -> 0 < y -> 0 < z ->
        eval [c, b, a] x = 0 ->
        eval [c, b, a] y = 0 ->
        eval [c, b, a] z = 0 ->
        x = y \/ x = z \/ y = z) := by
  constructor
  · exact signChangeCountIgnoringZeros_quadratic ha hb hc
  · intro x y z hx hy hz hxr hyr hzr
    by_cases hxy : x = y
    · exact Or.inl hxy
    by_cases hxz : x = z
    · exact Or.inr (Or.inl hxz)
    by_cases hyz : y = z
    · exact Or.inr (Or.inr hyz)
    exact False.elim (quadratic_three_distinct_roots_impossible
      (Rat.ne_of_gt ha) hxy hxz hyz hxr hyr hzr)

end Polynomial

end ComputableAnalysis
