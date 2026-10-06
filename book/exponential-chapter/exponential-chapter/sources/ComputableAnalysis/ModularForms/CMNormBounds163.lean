import ComputableAnalysis.ModularForms.CMIdealHomothety163

/-! Quantitative coordinate coercivity of the CM lattice norm. -/
namespace ComputableAnalysis.ModularForms.QuadraticOrder163

private theorem square_nonnegative (x : Int) : 0≤x*x := by
  by_cases hx : 0≤x
  · exact Int.mul_nonneg hx hx
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem norm_coordinate_bound (u : QuadraticOrder163) :
    u.x*u.x+u.y*u.y≤2*norm u := by
  have hs := square_nonnegative (u.x+u.y)
  have hy := square_nonnegative u.y
  unfold norm
  grind

theorem norm_x_bound (u : QuadraticOrder163) : u.x*u.x≤2*norm u := by
  have h := norm_coordinate_bound u
  have hy := square_nonnegative u.y
  omega

theorem norm_y_bound (u : QuadraticOrder163) : u.y*u.y≤2*norm u := by
  have h := norm_coordinate_bound u
  have hx := square_nonnegative u.x
  omega

theorem norm_lower_of_x (u : QuadraticOrder163) (r : Int) (hr : 0≤r)
    (hx : r≤u.x ∨ u.x≤ -r) : r*r≤2*norm u := by
  have h := norm_x_bound u
  have hs : r*r≤u.x*u.x := by
    rcases hx with hx | hx
    · have hp := Int.mul_nonneg (show 0≤u.x-r by omega) (show 0≤u.x+r by omega)
      grind
    · have hp := Int.mul_nonneg_of_nonpos_of_nonpos
        (show u.x-r≤0 by omega) (show u.x+r≤0 by omega)
      grind
  omega

theorem norm_lower_of_y (u : QuadraticOrder163) (r : Int) (hr : 0≤r)
    (hy : r≤u.y ∨ u.y≤ -r) : r*r≤2*norm u := by
  have h := norm_y_bound u
  have hs : r*r≤u.y*u.y := by
    rcases hy with hy | hy
    · have hp := Int.mul_nonneg (show 0≤u.y-r by omega) (show 0≤u.y+r by omega)
      grind
    · have hp := Int.mul_nonneg_of_nonpos_of_nonpos
        (show u.y-r≤0 by omega) (show u.y+r≤0 by omega)
      grind
  omega

theorem norm_lower_outside_box (u : QuadraticOrder163) (r : Int) (hr : 0≤r)
    (houtside : r≤u.x ∨ u.x≤ -r ∨ r≤u.y ∨ u.y≤ -r) : r*r≤2*norm u := by
  rcases houtside with hx | hx | hy | hy
  · exact norm_lower_of_x u r hr (Or.inl hx)
  · exact norm_lower_of_x u r hr (Or.inr hx)
  · exact norm_lower_of_y u r hr (Or.inl hy)
  · exact norm_lower_of_y u r hr (Or.inr hy)

end ComputableAnalysis.ModularForms.QuadraticOrder163
