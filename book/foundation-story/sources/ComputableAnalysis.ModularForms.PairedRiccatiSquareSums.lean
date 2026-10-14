import ComputableAnalysis.ModularForms.PairedRiccatiSquareDensityBound

/-! Finite midpoint sums of the actual represented squared-kernel density. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions PDE.CauchyContour

def pairedSquareDensity (a : Scalar) (edge : HalfEdge) (u R : Rat) : ComplexRaw :=
  let q := QComplex.scaleRat R (point edge u)
  let z : Scalar := ⟨add a.val (ofQComplex q),add_valid a.property (ofQComplex_valid _)⟩
  let d := mul (mul (pairedEntireRiccatiMap.eval z trivial).val
    (mul (ofQComplex (RationalReciprocal.inverse q))
      (ofQComplex (RationalReciprocal.inverse q))))
    (ofQComplex (QComplex.scaleRat R (velocity edge)))
  if edge.upper then d else neg d

theorem pairedSquareDensity_bound (a : Scalar) (edge : HalfEdge) (u R : Rat) (hR : 0<R) :
    Small (pairedSquareDensity a edge u R) (42958720*(1/R)) := by
  have h := pairedEntireRiccatiMap_square_density_bound
    (⟨add a.val (ofQComplex (QComplex.scaleRat R (point edge u))),
      add_valid a.property (ofQComplex_valid _)⟩ : Scalar) edge u R hR
  dsimp only [pairedSquareDensity]
  split
  · exact h
  · exact SeriesLimitLaws.small_neg h

def pairedSquareHalfEdgeSum (a : Scalar) (edge : HalfEdge) (R : Rat) (N : Nat) : ComplexRaw :=
  scaleRat ((N:Rat)⁻¹) (ScalarSeries.block (fun j =>
    pairedSquareDensity a edge
      (if edge.upper then ((j:Rat)+1/2)/(N:Rat) else 1-((j:Rat)+1/2)/(N:Rat)) R) 0 N)

theorem pairedSquareHalfEdgeSum_bound (a : Scalar) (edge : HalfEdge) (R : Rat)
    (hR : 0<R) (N : Nat) (hN : 0<N) :
    Small (pairedSquareHalfEdgeSum a edge R N) (42958720*(1/R)) := by
  have hb (K : Nat) : Small (ScalarSeries.block (fun j => pairedSquareDensity a edge
      (if edge.upper then ((j:Rat)+1/2)/(N:Rat) else 1-((j:Rat)+1/2)/(N:Rat)) R) 0 K)
      ((K:Rat)*(42958720*(1/R))) := by
    induction K with
    | zero => exact Small.zero (by change (0:Rat)≤0*(42958720*(1/R)); rw [Rat.zero_mul]; decide +kernel)
    | succ K ih =>
      have hs := LocalODE.small_add ih (pairedSquareDensity_bound a edge (if edge.upper then ((K:Rat)+1/2)/(N:Rat) else 1-((K:Rat)+1/2)/(N:Rat)) R hR)
      have he : (K:Rat)*(42958720*(1/R))+42958720*(1/R)=
          ((K+1:Nat):Rat)*(42958720*(1/R)) := by
        rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
        grind only
      rw [he] at hs
      simpa only [ScalarSeries.block,Nat.zero_add] using hs
  have hn : 0<(N:Rat) := Rat.natCast_pos.mpr hN
  have hs := LocalODE.small_scale (Rat.le_of_lt (Rat.inv_pos.mpr hn)) (hb N)
  have hc := Rat.inv_mul_cancel (N:Rat) (Rat.ne_of_gt hn)
  have he : (N:Rat)⁻¹*((N:Rat)*(42958720*(1/R)))=42958720*(1/R) := by
    calc
      _ = ((N:Rat)⁻¹*(N:Rat))*(42958720*(1/R)) := by grind only
      _ = _ := by rw [hc]; exact Rat.one_mul _
  rw [he] at hs
  exact hs

end ComputableAnalysis.ModularForms
