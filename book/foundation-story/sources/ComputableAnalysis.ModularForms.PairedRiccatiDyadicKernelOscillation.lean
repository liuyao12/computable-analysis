import ComputableAnalysis.ModularForms.PairedRiccatiDyadicKernelVariation

/-! Arbitrarily small dyadic cell oscillation for the kernel product. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert PDE.CauchyContour

theorem scaledTolerance_exists (A : Rat) (hA : 0≤A) (eps : QPos) :
    ∃ e : QPos, A*e.val≤eps.val/2 := by
  have hd : 0<A+1 := by grind only
  have ht : 0<eps.val/(A+1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr hd)
  let e : QPos := ⟨(eps.val/(A+1))/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos ht (by decide +kernel)⟩
  have hc : (A+1)*(eps.val/(A+1))=eps.val := by
    rw [Rat.div_def, Rat.mul_comm eps.val, ← Rat.mul_assoc,
      Rat.mul_inv_cancel (A+1) (Rat.ne_of_gt hd), Rat.one_mul]
  have hm := Rat.mul_le_mul_of_nonneg_right
    (show A≤A+1 by grind only) (Rat.le_of_lt e.property)
  refine ⟨e, ?_⟩
  dsimp [e] at hm ⊢
  grind only

def riccatiSquareKernelSample (p q : Scalar) (edge : HalfEdge) (R u : Rat) : Scalar :=
  let f := pairedEntireRiccatiMap.eval (AffineSegment.point p q u) trivial
  let k := rationalSquaredKernel (QComplex.scaleRat R (point edge u))
  ⟨mul f.val k.val, mul_valid f.property k.property⟩

theorem pairedRiccati_dyadic_kernel_oscillation (p q : Scalar) (W : QPos)
    (hd : Small (AffineSegment.displacement p q).val W.val)
    (edge : HalfEdge) (R : Rat) (hR : 0<R) (eps : QPos) :
    ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub (riccatiSquareKernelSample p q edge R u).val
        (riccatiSquareKernelSample p q edge R v).val) eps.val := by
  let A : Rat := 4*(2*(1/R)*(1/R))
  let B : Rat := 2*5369840*(2*((2*R)*(R*R)⁻¹)^3*R)
  have hi : 0≤(1:Rat)/R := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hR))
  have hA : 0≤A := Rat.mul_nonneg (by decide +kernel)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hi) hi)
  have hB : 0≤B := by
    apply Rat.mul_nonneg (by decide +kernel)
    apply Rat.mul_nonneg _ (Rat.le_of_lt hR)
    apply Rat.mul_nonneg (by decide +kernel)
    apply Rat.pow_nonneg
    exact Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hR))
      (Rat.le_of_lt (Rat.inv_pos.mpr (Rat.mul_pos hR hR)))
  obtain ⟨e,he⟩ := scaledTolerance_exists A hA eps
  obtain ⟨N,hN⟩ := pairedRiccati_dyadic_kernel_variation p q W hd edge R hR e
  let half : QPos := ⟨eps.val/2, by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (by decide +kernel)⟩
  let K := RationalMajorant.natRateStage B half
  refine ⟨max N K, ?_⟩
  intro choice n hn u v hulo huhi hvlo hvhi
  have hb := hN choice n (by omega) u v hulo huhi hvlo hvhi
  have hpow := Rat.mul_le_mul_of_nonneg_left
    (RationalMajorant.half_pow_le_one_div_succ n) hB
  have hr := RationalMajorant.natRateStage_spec_of_le hB half (by omega : K≤n)
  have htail : B*((1:Rat)/2)^n≤eps.val/2 := by
    have hh : B*(1/((n+1:Nat):Rat))=B/((n+1:Nat):Rat) := by
      rw [Rat.div_def, Rat.div_def, Rat.one_mul]
    rw [hh] at hpow
    exact Rat.le_trans hpow hr
  apply hb.mono
  change _≤eps.val
  dsimp [A] at he
  dsimp [B] at htail
  grind only

end ComputableAnalysis.ModularForms
