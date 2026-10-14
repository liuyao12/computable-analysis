import ComputableAnalysis.ModularForms.PairedRiccatiUniformDyadicCover
import ComputableAnalysis.ModularForms.PairedRiccatiKernelProductContinuity

/-! Uniform dyadic variation of actual Riccati values times the square
squared reciprocal kernel. The kernel error has an explicit geometric rate. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem dyadicCell_distance_bound (choice : Nat → Bool) (n : Nat) (u v : Rat)
    (hu : (bisectionInterval ⟨0,1⟩ choice n).lo≤u ∧
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi)
    (hv : (bisectionInterval ⟨0,1⟩ choice n).lo≤v ∧
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi) :
    qabs (u-v)≤((1:Rat)/2)^n := by
  have hw := bisectionInterval_width (⟨0,1⟩ : QInterval) choice n
  have hwidth : (bisectionInterval ⟨0,1⟩ choice n).hi-
      (bisectionInterval ⟨0,1⟩ choice n).lo=((1:Rat)/2)^n := by
    simpa only [QInterval.width, show (1:Rat)-0=1 by decide +kernel, Rat.one_mul] using hw
  apply qabs_le_of_neg_le_le <;> grind only

theorem pairedRiccati_dyadic_kernel_variation (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (edge : HalfEdge) (R : Rat) (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub
        (mul (pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial).val
          (rationalSquaredKernel (QComplex.scaleRat R (point edge u))).val)
        (mul (pairedEntireRiccatiMap.eval (AffineSegment.point p q v) trivial).val
          (rationalSquaredKernel (QComplex.scaleRat R (point edge v))).val))
        (4*eps.val*(2*(1/R)*(1/R))+
          2*5369840*((2*((2*R)*(R*R)⁻¹)^3*R)*((1:Rat)/2)^n)) := by
  obtain ⟨N,hN⟩ := pairedRiccati_uniform_dyadic_variation p q W hd eps
  refine ⟨N, ?_⟩
  intro choice n hn u v hulo huhi hvlo hvhi
  have he := bisectionInterval_nested (⟨0,1⟩ : QInterval)
    (by decide +kernel) choice 0 n (Nat.zero_le n)
  have hb := pairedRiccati_square_kernel_product_difference_bound
    (AffineSegment.point p q u) (AffineSegment.point p q v) edge u v R (2*eps.val)
    hR (Rat.le_trans he.1 hulo) (Rat.le_trans huhi he.2.2)
    (Rat.le_trans he.1 hvlo) (Rat.le_trans hvhi he.2.2)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt eps.property))
    (hN choice n hn u v hulo huhi hvlo hvhi)
  apply hb.mono
  have hdist := dyadicCell_distance_bound choice n u v ⟨hulo,huhi⟩ ⟨hvlo,hvhi⟩
  have hcoef : 0≤2*((2*R)*(R*R)⁻¹)^3*R := by
    apply Rat.mul_nonneg _ (Rat.le_of_lt hR)
    apply Rat.mul_nonneg (by decide +kernel)
    apply Rat.pow_nonneg
    exact Rat.mul_nonneg
      (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hR hR)))
  have hm := Rat.mul_le_mul_of_nonneg_left hdist hcoef
  have hm' := Rat.mul_le_mul_of_nonneg_left hm
    (by decide +kernel : (0:Rat)≤2*5369840)
  grind only

end ComputableAnalysis.ModularForms
