import ComputableAnalysis.IntegralEnclosureExamples
import ComputableAnalysis.ComplexIntegralEnclosure

open ComputableAnalysis
open ComputableAnalysis.ComplexPathIntegral

-- An arbitrary valid number no longer has an API named as an integral.
#check_failure Integral.ConstructionFor
#check_failure Integral.integralFor
#check_failure Integral.integral
#check_failure ComplexPathIntegral.polygonalPolynomialIntegralRaw

example : (Integral.EnclosureConstructionFor.constant 1 0 (1/2)
    (by native_decide)).value.Valid :=
  Integral.EnclosureConstructionFor.valid _
example : (Integral.EnclosureConstructionFor.constant 1 0 (1/2)
    (by native_decide)).value.Equiv (RealRaw.ofRat (1/2)) :=
  Integral.constant_half_interval

-- The complex first stage must enclose a nonzero open-path displacement.
example : (polygonalIntegralRawEntire (constantBoxFunction ⟨1,0⟩)
    [⟨1,0⟩,⟨1,1⟩]).compute 0 = QBox.point ⟨0,1⟩ := by native_decide
example : (polygonalIntegralRawEntire (constantBoxFunction ⟨1,0⟩)
    [⟨1,0⟩,⟨1,1⟩]).Valid :=
  polygonalIntegralRawEntire_valid
    (constantPolygonalIntegralCertificate ⟨1,0⟩ ⟨1,0⟩ [⟨1,1⟩])
example : (polygonalIntegralRawEntire (constantBoxFunction ⟨1,0⟩)
    [⟨1,1⟩,⟨1,0⟩]).compute 0 = QBox.point ⟨0,-1⟩ := by native_decide
example : (polygonalIntegralRawEntire (constantBoxFunction ⟨1,0⟩)
    [⟨1,1⟩,⟨1,1⟩]).compute 0 = QBox.point ⟨0,0⟩ := by native_decide

-- Rotation exchanges which corners provide the lower and upper bounds.
example : rotateRange ⟨⟨1,-3⟩,⟨2,-1⟩⟩ = ⟨⟨1,1⟩,⟨3,2⟩⟩ := by native_decide

#print axioms Integral.EnclosurePlanFor.contains_later
#print axioms Integral.EnclosureConstructionFor.constant_value
#print axioms Integral.arctanEnclosureRealization_equiv_geometric
#print axioms ComplexPathIntegral.subsegmentIntegralBox_contains_point_box
#print axioms ComplexPathIntegral.zSquared_sound
#print axioms ComplexPathIntegral.constant_vertical_value
#print axioms ComplexPathIntegral.constantPolygonalIntegralCertificate
