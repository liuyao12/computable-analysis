import ComputableAnalysis.ModularForms.Hecke41Matrices
import ComputableAnalysis.ModularForms.CMHeckeOrbit41

/-! Literal degree-41 Hecke points on arbitrary represented upper-half-plane inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- The affine and dilation points of the degree-41 correspondence. -/
def hecke41Point (i : Fin 42) (z : Scalar) : Scalar :=
  if i.val=41 then ⟨scaleRat 41 z.val,scaleRat_valid z.property⟩ else
    ⟨scaleRat (1/41) (translate (i.val:Rat) z.val),scaleRat_valid (translate_valid _ z.property)⟩

/-- Every actual degree-41 point preserves upper-half-plane membership. -/
theorem hecke41Point_upper (i : Fin 42) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    InUpperHalfPlane (hecke41Point i z).val := by
  obtain ⟨N,hN⟩ := hz
  refine ⟨N,?_⟩
  by_cases hi : i.val=41
  · simp only [hecke41Point,if_pos hi]
    change 0<(41:Rat)*(z.val.compute N).lo.im
    exact Rat.mul_pos (by decide +kernel) hN
  · simp only [hecke41Point,if_neg hi,imagPart,scaleRat,QBox.scaleRat,
      if_pos (show (0:Rat)≤1/41 by decide +kernel),translate,add,ofQComplex,QBox.add,QComplex.add]
    change 0<(1/41:Rat)*((z.val.compute N).lo.im+0)
    rw [Rat.add_zero]
    exact Rat.mul_pos (by decide +kernel) hN

/-- Each actual degree-41 point respects equality of represented inputs. -/
theorem hecke41Point_congr (i : Fin 42) (z w : Scalar) (he : z.val.Equiv w.val) :
    (hecke41Point i z).val.Equiv (hecke41Point i w).val := by
  by_cases hi : i.val=41
  · simp only [hecke41Point,if_pos hi]
    exact scaleRat_equiv (r := 41) he
  · simp only [hecke41Point,if_neg hi]
    exact scaleRat_equiv (r := (1/41:Rat)) (translate_equiv (i.val:Rat) he)

/-- The fortieth actual Hecke representative at the CM point is the proved modular orbit point. -/
theorem hecke41Point_cm_forty : (hecke41Point ⟨40,by decide +kernel⟩ cmScalar163).val.Equiv
    cmHeckePointForty163.val := by
  exact equiv_refl cmHeckePointForty163.val cmHeckePointForty163.property

/-- The lattice j evaluator is justified at the concrete CM fortieth Hecke representative. -/
theorem hecke41Point_cm_forty_j_domain :
    latticeJMap.domain (hecke41Point ⟨40,by decide +kernel⟩ cmScalar163) :=
  cmHeckePointForty163_j_domain

/-- The actual CM j value is repeated at the fortieth Hecke representative. -/
theorem hecke41Point_cm_forty_j :
    (latticeJMap.eval (hecke41Point ⟨40,by decide +kernel⟩ cmScalar163)
      hecke41Point_cm_forty_j_domain).val.Equiv cmJValue163.val :=
  cmHeckePointForty163_j_agreement

end ComputableAnalysis.ModularForms
