import ComputableAnalysis.ComplexAnalysis.Residue
import ComputableAnalysis.ComplexAnalysis.Examples

namespace ComputableAnalysis.ComplexAnalysis
open QComplex

/-- The regular part is an actual nonconstant polynomial, for every square. -/
def Square.quadraticRegular (s : Square) : s.Regular squareRaw where
  lower := s.lower.squareCertificate.toCauchyData
  upper := s.upper.squareCertificate.toCauchyData

/-- The integral of rho/(z-a) + z² around any positive rational square
centered at a. The residue rho can be an irrational represented complex value. -/
theorem quadratic_simple_pole_residue (s : Square) (rho : ComplexRaw) (hrho : rho.Valid) :
    (s.residueContour rho s.quadraticRegular SquarePole.midpoints).Equiv
      (ComplexRaw.mul rho PDE.CauchyContour.twoPiI) :=
  s.residue rho hrho s.quadraticRegular SquarePole.midpoints

/-- Two genuinely different quadrature algorithms agree. -/
theorem quadratic_tags_agree (s : Square) (rho : ComplexRaw) (hrho : rho.Valid) :
    (s.residueContour rho s.quadraticRegular SquarePole.midpoints).Equiv
      (s.residueContour rho s.quadraticRegular SquarePole.leftEndpoints) :=
  s.residue_independent rho rho hrho hrho (ComplexRaw.equiv_refl rho hrho)
    s.quadraticRegular s.quadraticRegular SquarePole.midpoints SquarePole.leftEndpoints

end ComputableAnalysis.ComplexAnalysis
