import ComputableAnalysis.RationalAreaFoundation
open ComputableAnalysis.RationalAreaFoundation

#check area_pythagoras_of_bilinear
#check square_content_coordinates
#check uniform_fan_gap_bound

#print axioms area_pythagoras_of_bilinear
#print axioms pythagoras_square_areas
#print axioms four_triangle_dissection_content
#print axioms similarity_square_content
#print axioms circle_point_square_content
#print axioms tangent_intersection_supporting_lines
#print axioms outer_wedge_quadrilateral_content
#print axioms unit_disk_support
#print axioms wedge_gap_bounds
#print axioms uniform_fan_gap_bound
#print axioms unit_chart_increment_bounds

example : squareContent ⟨1,1⟩=2 := by decide +kernel
example : circlePoint (1/2)=⟨3/5,4/5⟩ := by decide +kernel
example : lowerFan (1/2) 2=7/10 := by decide +kernel
example : upperFan (1/2) 2=5/6 := by decide +kernel
