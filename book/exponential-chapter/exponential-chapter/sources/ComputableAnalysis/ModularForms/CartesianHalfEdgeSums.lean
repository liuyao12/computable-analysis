import ComputableAnalysis.ModularForms.SquareHalfEdgeReflection

/-! Normalized Cartesian half-edge sums agree with the original finite sums. -/

namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem gridScalarSum_block_agreement (f : Nat → Scalar) (N K : Nat) :
    (gridScalarSum K (fun j => f (N+j))).val.Equiv
      (ScalarSeries.block (fun j => (f j).val) N K) := by
  induction K with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ K ih => exact add_equiv ih (equiv_refl _ (f (N+K)).property)

def cartesianHalfEdgeSum (c : Scalar) (quarter : Quarter) (S : Rat) (M : Nat) (upper : Bool) : Scalar :=
  let terms := gridScalarSum M (fun j => pairedSquareDensitySample c ⟨quarter,true⟩ S
    (if upper then squareMidpointParameter M j else squareMidpointParameter M j-1))
  ⟨scaleRat ((M:Rat)⁻¹) terms.val,scaleRat_valid terms.property⟩

theorem cartesianHalfEdgeSum_agreement (c : Scalar) (quarter : Quarter) (S : Rat)
    (M : Nat) (hM : 0<M) (upper : Bool) :
    (cartesianHalfEdgeSum c quarter S M upper).val.Equiv
      (pairedSquareHalfEdgeSum c ⟨quarter,upper⟩ S M) := by
  have hr : 0≤(M:Rat)⁻¹ := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr hM))
  cases upper with
  | true =>
    have hb := gridScalarSum_block_agreement
      (fun j => pairedSquareDensitySample c ⟨quarter,true⟩ S (squareMidpointParameter M j)) 0 M
    have hs := ComplexRaw.scaleRat_equiv_of_nonneg hr hb
    simpa only [cartesianHalfEdgeSum,pairedSquareHalfEdgeSum,↓reduceIte,Nat.zero_add,
      pairedSquareDensitySample,squareMidpointParameter] using hs
  | false =>
    let f := fun j => pairedSquareDensitySample c ⟨quarter,true⟩ S (squareMidpointParameter M j-1)
    let g := fun j => pairedSquareDensitySample c ⟨quarter,false⟩ S (1-squareMidpointParameter M j)
    have he : ∀ j, (f j).val.Equiv (g j).val := by
      intro j
      have h := pairedSquareDensitySample_lower_reflection c quarter S (1-squareMidpointParameter M j)
      have hp : -(1-squareMidpointParameter M j)=squareMidpointParameter M j-1 := by grind only
      rw [hp] at h
      exact equiv_symm h
    have hb := gridScalarSum_block_agreement g 0 M
    simp only [Nat.zero_add] at hb
    have ha := gridScalarSum_congr M f g he
    have ht := equiv_trans (gridScalarSum M f).property (gridScalarSum M g).property
      (ScalarSeries.block_valid (fun j => (g j).val) (fun j => (g j).property) 0 M) ha hb
    have hs := ComplexRaw.scaleRat_equiv_of_nonneg hr ht
    simpa only [cartesianHalfEdgeSum,pairedSquareHalfEdgeSum,Bool.false_eq_true,↓reduceIte,
      f,g,Nat.zero_add,pairedSquareDensitySample,squareMidpointParameter] using hs

end ComputableAnalysis.ModularForms
