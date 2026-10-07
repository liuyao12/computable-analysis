import ComputableAnalysis.ModularForms.PairedSquareContourDyadicCauchy
import ComputableAnalysis.ModularForms.PairedRiccatiLargeSquareDecay

/-! The Cauchy dyadic contour averages obey the actual large-radius bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem pairedSquareDyadicAverage_bound (a : Scalar) (edge : HalfEdge)
    (R : Rat) (hR : 0<R) (n : Nat) :
    Small (pairedSquareDyadicAverage a edge R n).val (42958720*(1/R)) :=
  dyadicSampleAverage_bound (pairedSquareDensitySample a edge R) ⟨0,1⟩ _
    (fun u => pairedSquareDensity_bound a edge u R hR) n

theorem pairedSquareDyadicEdgeList_bound (a : Scalar) (R : Rat) (hR : 0<R)
    (n : Nat) (edges : List HalfEdge) :
    Small (pairedSquareDyadicEdgeList a R n edges).val
      ((edges.length:Rat)*(42958720*(1/R))) := by
  induction edges with
  | nil =>
    apply Small.zero
    change (0:Rat)≤0*(42958720*(1/R))
    rw [Rat.zero_mul]
    exact Rat.le_refl
  | cons edge edges ih =>
    have hb := LocalODE.small_add (pairedSquareDyadicAverage_bound a edge R hR n) ih
    have he : 42958720*(1/R)+(edges.length:Rat)*(42958720*(1/R))=
        ((edge::edges).length:Rat)*(42958720*(1/R)) := by
      rw [List.length_cons,Rat.natCast_add]
      change _=((edges.length:Rat)+1)*(42958720*(1/R))
      grind only
    rw [he] at hb
    exact hb

theorem pairedSquareDyadicContour_bound (a : Scalar) (R : Rat) (hR : 0<R)
    (n : Nat) : Small (pairedSquareDyadicContour a R n).val (343669760*(1/R)) := by
  have hb := pairedSquareDyadicEdgeList_bound a R hR n square
  have he : (square.length:Rat)*(42958720*(1/R))=343669760*(1/R) := by
    change 8*(42958720*(1/R))=343669760*(1/R)
    grind only
  rw [he] at hb
  exact hb

theorem pairedSquareDyadicContour_large_radius_small (a : Scalar) (eps : QPos) :
    ∃ K, ∀ n, K≤n → ∀ depth,
      Small (pairedSquareDyadicContour a ((n+1:Nat):Rat) depth).val eps.val := by
  obtain ⟨K,hK⟩ := pairedReciprocalTail_shrinks 343669760 eps
  refine ⟨K, ?_⟩
  intro n hn depth
  have hb := pairedSquareDyadicContour_bound a ((n+1:Nat):Rat)
    (Rat.natCast_pos.mpr (Nat.succ_pos n)) depth
  apply hb.mono
  have hk := hK n hn
  have hc : ((343669760:Nat):Rat)=343669760 := by decide +kernel
  rw [hc] at hk
  simpa only [Rat.div_def,Rat.one_mul] using hk

end ComputableAnalysis.ModularForms
