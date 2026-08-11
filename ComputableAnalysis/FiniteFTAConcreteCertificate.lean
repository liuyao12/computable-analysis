import ComputableAnalysis.FTA
import ComputableAnalysis.FiniteFTARootExclusion

namespace ComputableAnalysis

/-! A concrete finite complex-root certificate for the quadratic `X^2 + 1`.

This is deliberately a supplied-root example: it checks exact rational
coordinates and the finite Horner evaluator, without asserting global root
existence or invoking completed complex numbers.
-/

def finiteFTAQuadratic : CPoly.Coeffs :=
  [QComplex.one, QComplex.zero, QComplex.one]

def finiteFTAUpperRoot : QComplex := { re := 0, im := 1 }

def finiteFTALowerRoot : QComplex := { re := 0, im := -1 }

theorem finiteFTAQuadratic_upper_root :
    CPoly.eval finiteFTAQuadratic finiteFTAUpperRoot = QComplex.zero := by
  native_decide

theorem finiteFTAQuadratic_lower_root :
    CPoly.eval finiteFTAQuadratic finiteFTALowerRoot = QComplex.zero := by
  native_decide

theorem finiteFTAQuadratic_roots_are_distinct :
    finiteFTAUpperRoot ≠ finiteFTALowerRoot := by
  native_decide

theorem finiteFTAQuadratic_point_eval_upper :
    QBox.evalPoly finiteFTAQuadratic (QBox.point finiteFTAUpperRoot) = QBox.zero := by
  rw [QBox.evalPoly_point, finiteFTAQuadratic_upper_root]
  rfl

theorem finiteFTAQuadratic_point_eval_lower :
    QBox.evalPoly finiteFTAQuadratic (QBox.point finiteFTALowerRoot) = QBox.zero := by
  rw [QBox.evalPoly_point, finiteFTAQuadratic_lower_root]
  rfl

theorem finiteFTAQuadratic_root_search_upper :
    exactRootSearch finiteFTAQuadratic
        [finiteFTAUpperRoot, finiteFTALowerRoot] = some finiteFTAUpperRoot := by
  native_decide

theorem finiteFTAQuadratic_root_search_sound :
    CPoly.hasExactRoot finiteFTAQuadratic finiteFTAUpperRoot := by
  apply exactRootSearch_sound finiteFTAQuadratic_root_search_upper

theorem finiteFTAQuadratic_root_search_skips_nonroot :
    exactRootSearch finiteFTAQuadratic
        [QComplex.zero, finiteFTAUpperRoot, finiteFTALowerRoot] =
      some finiteFTAUpperRoot := by
  native_decide

def finiteFTAQuadratic_zero_exclusion :
    QBox.FiniteRootExclusionCertificate finiteFTAQuadratic where
  domain := QBox.zero
  boxes := [QBox.zero]
  cover := by
    intro z hzlo hzhi
    change QComplex.zero <= z at hzlo
    change z <= QComplex.zero at hzhi
    have hz : z = QComplex.zero := QComplex.le_antisymm hzhi hzlo
    subst z
    refine ⟨QBox.zero, by simp, ?_, ?_⟩
    · change QComplex.zero <= QComplex.zero
      exact QComplex.le_refl _
    · change QComplex.zero <= QComplex.zero
      exact QComplex.le_refl _
  misses_zero := by
    intro Z hZ
    have hZeq : Z = QBox.zero := by simpa using hZ
    subst Z
    change ¬ QBox.Overlaps
      (QBox.evalPoly finiteFTAQuadratic (QBox.point QComplex.zero)) QBox.zero
    rw [QBox.evalPoly_point]
    native_decide

theorem finiteFTAQuadratic_zero_is_excluded :
    CPoly.eval finiteFTAQuadratic QComplex.zero ≠ QComplex.zero := by
  apply finiteFTAQuadratic_zero_exclusion.no_root_in_domain
  · native_decide
  · native_decide

end ComputableAnalysis
