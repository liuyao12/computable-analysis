import ComputableAnalysis.ModularForms.PairedEntireContourDerivativeZero
import ComputableAnalysis.ModularForms.PairedEntireIntegerNormalization

/-! Exact constancy of the actual entire Riccati map at represented inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem pairedEntireRiccatiMap_derivative_zero_bound (c : Scalar) :
    Small (pairedEntireRiccatiMap_holomorphic.derivative c trivial).val 0 :=
  Small.congr (ofQComplex_valid _)
    (pairedEntireRiccatiMap_holomorphic.derivative c trivial).property
    (equiv_symm (pairedEntireRiccatiMap_derivative_equiv_zero c))
    (Small.zero (by decide +kernel))

theorem pairedEntireRiccatiMap_difference_zero_bound (p q : Scalar) :
    Small (sub (pairedEntireRiccatiMap.eval q trivial).val
      (pairedEntireRiccatiMap.eval p trivial).val) 0 := by
  let v := AffineSegment.displacement p q
  let B := LocalODE.boxCoordinateBound (v.val.compute 0)
  have hB : 0≤B := LocalODE.boxCoordinateBound_nonneg _
  let W : QPos := ⟨B+1,by dsimp [B]; have := LocalODE.boxCoordinateBound_nonneg (v.val.compute 0); grind only⟩
  have hv : Small v.val W.val := (LocalODE.small_from_box v.val v.property 0).mono (by dsimp [W]; grind only)
  let z : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hr (eps : QPos) : Small (sub (pairedEntireRiccatiMap.eval q trivial).val
      (pairedEntireRiccatiMap.eval p trivial).val) (4*eps.val*W.val) := by
    have hs := pairedRiccati_segment_linearization_error p q z W eps hv (by
      intro t
      have hb := SeriesLimitLaws.small_sub
        (pairedEntireRiccatiMap_derivative_zero_bound (RepresentedAffineSegment.point p q t))
        (Small.zero (by decide +kernel : (0:Rat)≤0))
      exact hb.mono (by simpa only [Rat.zero_add] using Rat.le_of_lt eps.property))
    have he : (remainder pairedEntireRiccatiMap p trivial z q trivial).Equiv
        (sub (pairedEntireRiccatiMap.eval q trivial).val (pairedEntireRiccatiMap.eval p trivial).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := remainder_valid pairedEntireRiccatiMap p trivial z q trivial)
        (hright := sub_valid (pairedEntireRiccatiMap.eval q trivial).property
          (pairedEntireRiccatiMap.eval p trivial).property)
      let F := gridScalarValue (pairedEntireRiccatiMap.eval q trivial)
      let G := gridScalarValue (pairedEntireRiccatiMap.eval p trivial)
      let P := gridScalarValue p
      let Q := gridScalarValue q
      change (F-G)-0*(Q-P)=F-G
      grind only
    exact Small.congr (remainder_valid pairedEntireRiccatiMap p trivial z q trivial)
      (sub_valid (pairedEntireRiccatiMap.eval q trivial).property (pairedEntireRiccatiMap.eval p trivial).property) he hs
  apply SeriesLimitLaws.small_closed _ 0 (fun n => (4*W.val)*((1:Rat)/2)^n)
    (rational_half_geometric_shrinks _ (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt W.property)))
  intro n
  let eps : QPos := ⟨((1:Rat)/2)^n,Rat.pow_pos (by decide +kernel)⟩
  have hs := hr eps
  have he : 4*eps.val*W.val=0+(4*W.val)*((1:Rat)/2)^n := by dsimp [eps]; grind only
  rw [he] at hs
  exact hs

theorem pairedEntireRiccatiMap_constant (p q : Scalar) :
    (pairedEntireRiccatiMap.eval q trivial).val.Equiv (pairedEntireRiccatiMap.eval p trivial).val :=
  SeriesLimitLaws.equiv_of_small_sub_zero _ _ (pairedEntireRiccatiMap_difference_zero_bound p q)

theorem pairedEntireRiccatiMap_center_identity (z : Scalar) :
    (pairedEntireRiccatiMap.eval z trivial).val.Equiv pairedRiccatiCenterConstant.val := by
  have he : pairedZeroScalar.val.Equiv (rationalInteger 0).val := by
    change zero.Equiv zero
    exact equiv_refl _ (ofQComplex_valid _)
  exact equiv_trans (pairedEntireRiccatiMap.eval z trivial).property
    (pairedEntireRiccatiMap.eval pairedZeroScalar trivial).property pairedRiccatiCenterConstant.property
    (pairedEntireRiccatiMap_constant pairedZeroScalar z)
    (pairedEntireRiccatiMap_value_at_integer 0 pairedZeroScalar he)

theorem pairedGlobalOffPoleRiccatiMap_center_identity (z : Scalar) (hz : pairedOffPoleDomain z) :
    (pairedGlobalOffPoleRiccatiMap.eval z hz).val.Equiv pairedRiccatiCenterConstant.val :=
  equiv_trans (pairedGlobalOffPoleRiccatiMap.eval z hz).property
    (pairedEntireRiccatiMap.eval z trivial).property pairedRiccatiCenterConstant.property
    (pairedEntireRiccatiMap_chart_agreement .offPole z hz)
    (pairedEntireRiccatiMap_center_identity z)

theorem pairedGlobalOffPoleAssemblyMap_riccati_identity (z : Scalar) (hz : pairedOffPoleDomain z) :
    (add (pairedGlobalOffPoleAssemblyMap_holomorphic.derivative z hz).val
      (mul (pairedGlobalOffPoleAssemblyMap.eval z hz).val
        (pairedGlobalOffPoleAssemblyMap.eval z hz).val)).Equiv pairedRiccatiCenterConstant.val :=
  pairedGlobalOffPoleRiccatiMap_center_identity z hz

end ComputableAnalysis.ModularForms
