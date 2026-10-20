import ComputableAnalysis.ArctanInverseCircleAudit

open ComputableAnalysis ComputableAnalysis.ArctanInverseCircleAudit

#check value_order_reflects
#check inverse_at_geometric_source
#check geometric_chart_check
#check quarter_chart_check
#check coordinate_ranges
#check quarter_unit_circle
#check quarter_endpoints
#check geometric_pi_clock
#check quarter_angle_normalization

#print axioms inverse_at_geometric_source
#print axioms geometric_chart_check
#print axioms quarter_chart_check
#print axioms quarter_unit_circle
#print axioms quarter_endpoints
#print axioms geometric_pi_clock
#print axioms quarter_angle_normalization

-- Exact, non-decimal chart regressions: angle 2*atan(1/2) has (sin,cos)=(4/5,3/5).
example : SinPiIntegral.rationalCircleSin (1/2) = 4/5 := by decide +kernel
example : SinPiIntegral.rationalCircleCos (1/2) = 3/5 := by decide +kernel
example : SinPiIntegral.rationalCircleSin 0 = 0 := by decide +kernel
example : SinPiIntegral.rationalCircleCos 0 = 1 := by decide +kernel
example : SinPiIntegral.rationalCircleSin 1 = 1 := by decide +kernel
example : SinPiIntegral.rationalCircleCos 1 = 0 := by decide +kernel
