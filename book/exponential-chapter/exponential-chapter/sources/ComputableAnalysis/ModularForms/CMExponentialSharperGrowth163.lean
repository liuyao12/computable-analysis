import ComputableAnalysis.ModularForms.RealExponentialReality
import ComputableAnalysis.ModularForms.CMGrowthSharperBounds163
import ComputableAnalysis.ModularForms.RealPowerLowerBound
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! A power-amplified lower bound for the actual CM growth exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def cmGrowthUnitThirtySix163 : RealRaw := RealRaw.scaleRat (1/36) cmGrowthReal163

theorem cmGrowthUnitThirtySix163_valid : cmGrowthUnitThirtySix163.Valid := RealRaw.scaleRat_valid cmGrowthReal163_valid

theorem cmGrowthUnitThirtySix163_lower_one : (RealRaw.ofRat 1).Le cmGrowthUnitThirtySix163 := by
  intro n m
  have h := cmGrowthReal163_lower_thirtySix 0 m
  change (36:Rat) ≤ (cmGrowthReal163.compute m).hi at h
  have hb := Rat.mul_le_mul_of_nonneg_left h (show (0:Rat)≤1/36 by decide +kernel)
  simp only [cmGrowthUnitThirtySix163,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤1/36 by decide +kernel),RealRaw.ofRat]
  have hc : (1/36:Rat)*36=1 := by decide +kernel
  rw [hc] at hb
  exact hb

theorem cmGrowthUnitThirtySix163_positive : cmGrowthUnitThirtySix163.Pos := by
  obtain ⟨N,hN⟩ := cmGrowthUnitThirtySix163_valid.2.2 (⟨1/2,by decide +kernel⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hl := cmGrowthUnitThirtySix163_lower_one 0 N
  change (1:Rat) ≤ (cmGrowthUnitThirtySix163.compute N).hi at hl
  unfold QInterval.width at hw
  refine ⟨N,?_⟩
  change 0 < (cmGrowthUnitThirtySix163.compute N).lo
  grind only

def cmGrowthUnitThirtySixScalar163 : Scalar := ⟨ofRealRaw cmGrowthUnitThirtySix163,ofRealRaw_valid _ cmGrowthUnitThirtySix163_valid⟩

def cmGrowthUnitThirtySixExponential163 : RealRaw := (entireExponentialValue cmGrowthUnitThirtySixScalar163).val.realPart

theorem cmGrowthUnitThirtySixExponential163_valid : cmGrowthUnitThirtySixExponential163.Valid :=
  realPart_valid (entireExponentialValue _).property

theorem cmGrowthUnitThirtySixExponential163_lower_two : (RealRaw.ofRat 2).Le cmGrowthUnitThirtySixExponential163 := by
  have h := entireExponential_real_rational_lower cmGrowthUnitThirtySix163 cmGrowthUnitThirtySix163_valid
    cmGrowthUnitThirtySix163_positive 1 cmGrowthUnitThirtySix163_lower_one
  have hc : (1:Rat)+1=2 := by decide +kernel
  rw [hc] at h
  exact h

private theorem cmGrowthUnitThirtySix163_rescale :
    (scaleRat ((36:Nat):Rat) cmGrowthUnitThirtySixScalar163.val).Equiv (ofRealRaw cmGrowthReal163) := by
  have hc : ((36:Nat):Rat)=(36:Rat) := by decide +kernel
  rw [hc]
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ cmGrowthReal163_valid n
  simp only [cmGrowthUnitThirtySixScalar163,cmGrowthUnitThirtySix163,scaleRat,ofRealRaw,QBox.scaleRat,
    RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤36 by decide),
    if_pos (show (0:Rat)≤1/36 by decide +kernel),QBox.Overlaps,QComplex.le_def]
  have he (r : Rat) : (36:Rat)*((1/36)*r)=r := by
    have h : (36:Rat)*(1/36)=1 := by decide +kernel
    grind only
  constructor <;> constructor <;> simp only [he,Rat.mul_zero] <;> first | exact ho | exact Rat.le_refl

theorem cmGrowthExponential163_thirtySix_power_agreement :
    (entireExponentialValue cmGrowthExponent163).val.Equiv
      (ofRealRaw (realFinitePower cmGrowthUnitThirtySixExponential163 36)) := by
  let s : Scalar := ⟨scaleRat ((36:Nat):Rat) cmGrowthUnitThirtySixScalar163.val,scaleRat_valid cmGrowthUnitThirtySixScalar163.property⟩
  have hi := entireExponential_real_embedding cmGrowthUnitThirtySix163 cmGrowthUnitThirtySix163_valid
  have hp := LocalODE.power_congr _ _ (entireExponentialValue cmGrowthUnitThirtySixScalar163).property
    (ofRealRaw_valid _ cmGrowthUnitThirtySixExponential163_valid) hi 36
  have he := equiv_trans s.property (ofRealRaw_valid _ cmGrowthReal163_valid) cmGrowthExponent163.property
    cmGrowthUnitThirtySix163_rescale (equiv_symm cmGrowthExponent163_real)
  exact equiv_trans (entireExponentialValue cmGrowthExponent163).property
    (entireExponentialValue s).property (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36))
    (entireExponentialValue_congr _ s (equiv_symm he))
    (equiv_trans (entireExponentialValue s).property
      (LocalODE.power_valid _ (entireExponentialValue cmGrowthUnitThirtySixScalar163).property 36)
      (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36))
      (entireExponential_nat_multiple cmGrowthUnitThirtySixScalar163 36)
      (equiv_trans (LocalODE.power_valid _ (entireExponentialValue cmGrowthUnitThirtySixScalar163).property 36)
        (LocalODE.power_valid _ (ofRealRaw_valid _ cmGrowthUnitThirtySixExponential163_valid) 36)
        (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36)) hp
        (realFinitePower_complex _ cmGrowthUnitThirtySixExponential163_valid 36)))

theorem cmGrowthExponential163_lower_thirtySix_power :
    (RealRaw.ofRat 68719476736).Le (entireExponentialValue cmGrowthExponent163).val.realPart := by
  have hb := realFinitePower_lower cmGrowthUnitThirtySixExponential163 cmGrowthUnitThirtySixExponential163_valid 2
    (by decide) cmGrowthUnitThirtySixExponential163_lower_two 36
  have hc : (2:Rat)^36=68719476736 := by decide +kernel
  rw [hc] at hb
  have hr := ComplexRaw.realPart_equiv (equiv_symm cmGrowthExponential163_thirtySix_power_agreement)
  exact RealRaw.le_trans (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36) hb
    (RealRaw.le_of_equiv (realFinitePower_valid _ cmGrowthUnitThirtySixExponential163_valid 36)
      (realPart_valid (entireExponentialValue cmGrowthExponent163).property) hr)

end ComputableAnalysis.ModularForms
