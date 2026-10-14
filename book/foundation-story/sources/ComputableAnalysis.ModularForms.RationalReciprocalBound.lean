import ComputableAnalysis.ModularForms.UpperLatticeRegionSearch

/-! Rational reciprocal bounds from quantitative lattice norm lower estimates. -/
namespace ComputableAnalysis.ModularForms

/-- Division by the squared norm converts a linear numerator bound into a
reciprocal-radius bound when the norm has a quadratic lower estimate. -/
theorem rationalReciprocal_coordinate_upper (a A r s C N : Rat)
    (hA : 0≤A) (hr : 0<r) (hs : 0<s) (_hC : 0≤C) (hN : 0<N)
    (ha : a≤A*r) (hlower : s*r*r≤C*N) : a/N≤(C*A/s)/r := by
  have h1 := Rat.mul_le_mul_of_nonneg_right ha
    (Rat.mul_nonneg (Rat.le_of_lt hs) (Rat.le_of_lt hr))
  have h2 := Rat.mul_le_mul_of_nonneg_left hlower hA
  have hb : a*s*r≤C*A*N := by grind
  have hcn := Rat.mul_inv_cancel N (Rat.ne_of_gt hN)
  have hcs := Rat.mul_inv_cancel s (Rat.ne_of_gt hs)
  have hcr := Rat.mul_inv_cancel r (Rat.ne_of_gt hr)
  apply Rat.le_of_mul_le_mul_right (c := N*s*r)
  · calc
      _ = a*s*r := by grind [Rat.div_def]
      _ ≤ C*A*N := hb
      _ = _ := by grind [Rat.div_def]
  · exact Rat.mul_pos (Rat.mul_pos hN hs) hr

/-- Both signs of a reciprocal coordinate are controlled by the same explicit rate. -/
theorem rationalReciprocal_coordinate_bounds (a A r s C N : Rat)
    (hA : 0≤A) (hr : 0<r) (hs : 0<s) (hC : 0≤C) (hN : 0<N)
    (ha : -A*r≤a ∧ a≤A*r) (hlower : s*r*r≤C*N) :
    -((C*A/s)/r)≤a/N ∧ a/N≤(C*A/s)/r := by
  have hu := rationalReciprocal_coordinate_upper a A r s C N hA hr hs hC hN ha.2 hlower
  have hn := rationalReciprocal_coordinate_upper (-a) A r s C N hA hr hs hC hN
    (show -a≤A*r by grind) hlower
  constructor
  · grind [Rat.div_def]
  · exact hu

/-- Rational reciprocal coordinates have an explicit reciprocal-radius bound.
The numerator bounds are supplied quantitative estimates, not conclusions
about reciprocals. The squared norm is proved positive from lattice geometry. -/
theorem rationalLattice_reciprocal_bounds (z : QComplex) (x y r R eta A : Rat)
    (hr : 0<r) (hR : 0≤R) (heta : 0<eta) (hA : 0≤A)
    (hre : -R≤z.re ∧ z.re≤R) (him : eta≤z.im)
    (hout : r≤x ∨ x≤ -r ∨ r≤y ∨ y≤ -r)
    (ha : -A*r≤x+y*z.re ∧ x+y*z.re≤A*r)
    (hb : -A*r≤ -(y*z.im) ∧ -(y*z.im)≤A*r) :
    let N := rationalLatticeNorm z x y
    let C := 2*eta*eta+2*R*R+1
    (-((C*A/(eta*eta))/r)≤(x+y*z.re)/N ∧ (x+y*z.re)/N≤(C*A/(eta*eta))/r) ∧
    (-((C*A/(eta*eta))/r)≤ -(y*z.im)/N ∧ -(y*z.im)/N≤(C*A/(eta*eta))/r) := by
  have hl := rationalLattice_outside_square z x y r R eta (Rat.le_of_lt hr) hR heta hre him hout
  have he := Rat.mul_pos heta heta
  have hc : 0≤2*eta*eta+2*R*R+1 := by
    have hh := Rat.mul_nonneg hR hR
    grind
  have hn : 0<rationalLatticeNorm z x y := by
    have hpos := Rat.mul_pos (Rat.mul_pos he hr) hr
    by_cases hp : 0<rationalLatticeNorm z x y
    · exact hp
    · have hneg : rationalLatticeNorm z x y≤0 := by grind
      have hm := Rat.mul_le_mul_of_nonneg_left hneg hc
      grind
  exact ⟨rationalReciprocal_coordinate_bounds _ A r (eta*eta) _ _ hA hr he hc hn ha hl,
    rationalReciprocal_coordinate_bounds _ A r (eta*eta) _ _ hA hr he hc hn hb hl⟩

end ComputableAnalysis.ModularForms
