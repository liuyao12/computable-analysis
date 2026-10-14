import ComputableAnalysis.ModularForms.UpperLatticeAction

/-! Quantitative rational lattice geometry for upper-half-plane regions. -/
namespace ComputableAnalysis.ModularForms

private theorem square_nonnegative (x : Rat) : 0≤x*x := by
  by_cases h : 0≤x
  · exact Rat.mul_nonneg h h
  · have hn : 0≤ -x := by grind
    have hm := Rat.mul_nonneg hn hn
    grind


/-- Squared coordinate norm of the lattice vector x+y*z, computed rationally. -/
def rationalLatticeNorm (z : QComplex) (x y : Rat) : Rat :=
  (x+y*z.re)*(x+y*z.re)+(y*z.im)*(y*z.im)

/-- On a region with bounded real coordinate and imaginary coordinate bounded
away from zero, the lattice-vector norm controls its two index coordinates.
This explicit polynomial estimate is uniform over that region. -/
theorem rationalLattice_coercive (z : QComplex) (x y R eta : Rat)
    (_hR : 0≤R) (heta : 0<eta) (hre : -R≤z.re ∧ z.re≤R) (him : eta≤z.im) :
    eta*eta*(x*x+y*y)≤(2*eta*eta+2*R*R+1)*rationalLatticeNorm z x y := by
  have he0 : 0≤eta := Rat.le_of_lt heta
  have hi0 : 0≤z.im := Rat.le_trans he0 him
  have hxx := square_nonnegative x
  have hyy := square_nonnegative y
  have haa := square_nonnegative (x+y*z.re)
  have hbb := square_nonnegative (y*z.im)
  have hrr := square_nonnegative R
  have hee := square_nonnegative eta
  have hreal := Rat.mul_nonneg (show 0≤R-z.re by grind) (show 0≤R+z.re by grind)
  have himag := Rat.mul_nonneg (show 0≤z.im-eta by grind) (show 0≤z.im+eta by grind)
  have hr2 : z.re*z.re≤R*R := by grind
  have hi2 : eta*eta≤z.im*z.im := by grind
  have hyeta := Rat.mul_le_mul_of_nonneg_left hi2 hyy
  have hyr := Rat.mul_le_mul_of_nonneg_left hr2 hyy
  have hs := square_nonnegative (x+2*y*z.re)
  have hn : 0≤rationalLatticeNorm z x y := Rat.add_nonneg haa hbb
  have hye : eta*eta*y*y≤rationalLatticeNorm z x y := by
    unfold rationalLatticeNorm
    grind
  have hx : x*x≤2*rationalLatticeNorm z x y+2*R*R*y*y := by
    unfold rationalLatticeNorm
    grind
  have hxm := Rat.mul_le_mul_of_nonneg_left hx hee
  have hym := Rat.mul_le_mul_of_nonneg_left hye (show 0≤2*R*R by grind)
  grind

theorem rationalLattice_outside_square (z : QComplex) (x y r R eta : Rat)
    (hr : 0≤r) (hR : 0≤R) (heta : 0<eta)
    (hre : -R≤z.re ∧ z.re≤R) (him : eta≤z.im)
    (hout : r≤x ∨ x≤ -r ∨ r≤y ∨ y≤ -r) :
    eta*eta*r*r≤(2*eta*eta+2*R*R+1)*rationalLatticeNorm z x y := by
  have hcoord : r*r≤x*x+y*y := by
    have hx := square_nonnegative x
    have hy := square_nonnegative y
    rcases hout with h|h|h|h
    · have hm := Rat.mul_nonneg (show 0≤x-r by grind) (show 0≤x+r by grind)
      grind
    · have hm := Rat.mul_nonneg (show 0≤ -x-r by grind) (show 0≤ -x+r by grind)
      grind
    · have hm := Rat.mul_nonneg (show 0≤y-r by grind) (show 0≤y+r by grind)
      grind
    · have hm := Rat.mul_nonneg (show 0≤ -y-r by grind) (show 0≤ -y+r by grind)
      grind
  have hm := Rat.mul_le_mul_of_nonneg_left hcoord (square_nonnegative eta)
  have hb := rationalLattice_coercive z x y R eta hR heta hre him
  grind

end ComputableAnalysis.ModularForms
