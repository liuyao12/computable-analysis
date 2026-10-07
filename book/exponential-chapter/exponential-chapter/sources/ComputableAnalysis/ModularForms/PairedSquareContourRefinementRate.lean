import ComputableAnalysis.ModularForms.PairedSquareDensityLipschitz
import ComputableAnalysis.ModularForms.PairedSquareContourDyadicCauchy

/-! A rational geometric refinement bound for the actual square samples. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem pairedSquareDyadicAverage_refinement_rate (a : Scalar) (edge : HalfEdge)
    (R : Rat) (hR : 0<R) (n k : Nat) :
    Small (sub (pairedSquareDyadicAverage a edge R (n+k)).val
      (pairedSquareDyadicAverage a edge R n).val)
      (squareDensityLipschitzConstant R*((1:Rat)/2)^n) := by
  apply dyadicSampleAverage_refinement_error
  intro choice
  let J := bisectionInterval (⟨0,1⟩ : QInterval) choice n
  have hj := bisectionInterval_nested (⟨0,1⟩ : QInterval)
    (by decide +kernel) choice 0 n (Nat.zero_le n)
  have hm := midpoint_mem J hj.2.1
  apply dyadicSampleAverage_error _ _ J hj.2.1
  intro u hu0 hu1
  have hb := pairedSquareDensity_parameter_lipschitz a edge R u J.midpoint hR
    (Rat.le_trans hj.1 hu0) (Rat.le_trans hu1 hj.2.2)
    (Rat.le_trans hj.1 hm.1) (Rat.le_trans hm.2 hj.2.2)
  exact hb.mono (Rat.mul_le_mul_of_nonneg_left
    (dyadicCell_distance_bound choice n u J.midpoint ⟨hu0,hu1⟩ hm)
    (squareDensityLipschitzConstant_nonneg R hR))

theorem pairedSquareDyadicEdgeList_refinement_rate (a : Scalar) (R : Rat)
    (hR : 0<R) (n k : Nat) (edges : List HalfEdge) :
    Small (sub (pairedSquareDyadicEdgeList a R (n+k) edges).val
      (pairedSquareDyadicEdgeList a R n edges).val)
      ((edges.length:Rat)*(squareDensityLipschitzConstant R*((1:Rat)/2)^n)) := by
  induction edges with
  | nil =>
    have he : zero.Equiv (sub zero zero) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := ofQComplex_valid _)
        (hright := sub_valid (ofQComplex_valid _) (ofQComplex_valid _))
      change (0:ScalarAlgebra.Value)=0-0
      grind only
    have hb := Small.congr (ofQComplex_valid _)
      (sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) he
      (Small.zero (Rat.le_refl (a:=0)))
    change Small (sub zero zero) (0*_)
    rw [Rat.zero_mul]
    exact hb
  | cons edge edges ih =>
    have hb := LocalODE.small_add
      (pairedSquareDyadicAverage_refinement_rate a edge R hR n k) ih
    have hd := Small.congr
      (add_valid
        (sub_valid (pairedSquareDyadicAverage a edge R (n+k)).property
          (pairedSquareDyadicAverage a edge R n).property)
        (sub_valid (pairedSquareDyadicEdgeList a R (n+k) edges).property
          (pairedSquareDyadicEdgeList a R n edges).property))
      (sub_valid (pairedSquareDyadicEdgeList a R (n+k) (edge::edges)).property
        (pairedSquareDyadicEdgeList a R n (edge::edges)).property)
      (sumPair_difference (pairedSquareDyadicAverage a edge R (n+k))
        (pairedSquareDyadicEdgeList a R (n+k) edges)
        (pairedSquareDyadicAverage a edge R n)
        (pairedSquareDyadicEdgeList a R n edges)) hb
    have he : squareDensityLipschitzConstant R*((1:Rat)/2)^n+
        (edges.length:Rat)*(squareDensityLipschitzConstant R*((1:Rat)/2)^n)=
        ((edge::edges).length:Rat)*(squareDensityLipschitzConstant R*((1:Rat)/2)^n) := by
      rw [List.length_cons,Rat.natCast_add]
      change _=((edges.length:Rat)+1)*_
      grind only
    rw [he] at hd
    exact hd

def squareContourTail (R : Rat) (n : Nat) : Rat :=
  8*(squareDensityLipschitzConstant R*((1:Rat)/2)^n)

theorem pairedSquareDyadicContour_refinement_rate (a : Scalar) (R : Rat)
    (hR : 0<R) (n k : Nat) :
    Small (sub (pairedSquareDyadicContour a R (n+k)).val
      (pairedSquareDyadicContour a R n).val) (squareContourTail R n) :=
  pairedSquareDyadicEdgeList_refinement_rate a R hR n k square

end ComputableAnalysis.ModularForms
