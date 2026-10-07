import ComputableAnalysis.ModularForms.RealExponentialReality
import ComputableAnalysis.ModularForms.RealPowerLowerBound
import ComputableAnalysis.ModularForms.ExponentialPowers

/-! A power-amplified lower bound for the actual CM growth exponential. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def cmGrowthUnit163 : RealRaw := RealRaw.scaleRat (1/24) cmGrowthReal163

theorem cmGrowthUnit163_valid : cmGrowthUnit163.Valid := RealRaw.scaleRat_valid cmGrowthReal163_valid

theorem cmGrowthUnit163_lower_one : (RealRaw.ofRat 1).Le cmGrowthUnit163 := by
  intro n m
  have h := cmGrowthReal163_lower_twentyFour 0 m
  change (24:Rat) ≤ (cmGrowthReal163.compute m).hi at h
  have hb := Rat.mul_le_mul_of_nonneg_left h (show (0:Rat)≤1/24 by decide +kernel)
  simp only [cmGrowthUnit163,RealRaw.scaleRat,RealRaw.scaleRatCompute,
    if_pos (show (0:Rat)≤1/24 by decide +kernel),RealRaw.ofRat]
  have hc : (1/24:Rat)*24=1 := by decide +kernel
  rw [hc] at hb
  exact hb

theorem cmGrowthUnit163_positive : cmGrowthUnit163.Pos := by
  obtain ⟨N,hN⟩ := cmGrowthUnit163_valid.2.2 (⟨1/2,by decide +kernel⟩ : QPos)
  have hw := hN N (Nat.le_refl N)
  have hl := cmGrowthUnit163_lower_one 0 N
  change (1:Rat) ≤ (cmGrowthUnit163.compute N).hi at hl
  unfold QInterval.width at hw
  refine ⟨N,?_⟩
  change 0 < (cmGrowthUnit163.compute N).lo
  grind only

def cmGrowthUnitScalar163 : Scalar := ⟨ofRealRaw cmGrowthUnit163,ofRealRaw_valid _ cmGrowthUnit163_valid⟩

def cmGrowthUnitExponential163 : RealRaw := (entireExponentialValue cmGrowthUnitScalar163).val.realPart

theorem cmGrowthUnitExponential163_valid : cmGrowthUnitExponential163.Valid :=
  realPart_valid (entireExponentialValue _).property

theorem cmGrowthUnitExponential163_lower_two : (RealRaw.ofRat 2).Le cmGrowthUnitExponential163 := by
  have h := entireExponential_real_rational_lower cmGrowthUnit163 cmGrowthUnit163_valid
    cmGrowthUnit163_positive 1 cmGrowthUnit163_lower_one
  have hc : (1:Rat)+1=2 := by decide +kernel
  rw [hc] at h
  exact h

private theorem cmGrowthUnit163_rescale :
    (scaleRat ((24:Nat):Rat) cmGrowthUnitScalar163.val).Equiv (ofRealRaw cmGrowthReal163) := by
  have hc : ((24:Nat):Rat)=(24:Rat) := by decide +kernel
  rw [hc]
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ cmGrowthReal163_valid n
  simp only [cmGrowthUnitScalar163,cmGrowthUnit163,scaleRat,ofRealRaw,QBox.scaleRat,
    RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤24 by decide),
    if_pos (show (0:Rat)≤1/24 by decide +kernel),QBox.Overlaps,QComplex.le_def]
  have he (r : Rat) : (24:Rat)*((1/24)*r)=r := by
    have h : (24:Rat)*(1/24)=1 := by decide +kernel
    grind only
  constructor <;> constructor <;> simp only [he,Rat.mul_zero] <;> first | exact ho | exact Rat.le_refl

theorem cmGrowthExponential163_power_agreement :
    (entireExponentialValue cmGrowthExponent163).val.Equiv
      (ofRealRaw (realFinitePower cmGrowthUnitExponential163 24)) := by
  let s : Scalar := ⟨scaleRat ((24:Nat):Rat) cmGrowthUnitScalar163.val,scaleRat_valid cmGrowthUnitScalar163.property⟩
  have hi := entireExponential_real_embedding cmGrowthUnit163 cmGrowthUnit163_valid
  have hp := LocalODE.power_congr _ _ (entireExponentialValue cmGrowthUnitScalar163).property
    (ofRealRaw_valid _ cmGrowthUnitExponential163_valid) hi 24
  have he := equiv_trans s.property (ofRealRaw_valid _ cmGrowthReal163_valid) cmGrowthExponent163.property
    cmGrowthUnit163_rescale (equiv_symm cmGrowthExponent163_real)
  exact equiv_trans (entireExponentialValue cmGrowthExponent163).property
    (entireExponentialValue s).property (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitExponential163_valid 24))
    (entireExponentialValue_congr _ s (equiv_symm he))
    (equiv_trans (entireExponentialValue s).property
      (LocalODE.power_valid _ (entireExponentialValue cmGrowthUnitScalar163).property 24)
      (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitExponential163_valid 24))
      (entireExponential_nat_multiple cmGrowthUnitScalar163 24)
      (equiv_trans (LocalODE.power_valid _ (entireExponentialValue cmGrowthUnitScalar163).property 24)
        (LocalODE.power_valid _ (ofRealRaw_valid _ cmGrowthUnitExponential163_valid) 24)
        (ofRealRaw_valid _ (realFinitePower_valid _ cmGrowthUnitExponential163_valid 24)) hp
        (realFinitePower_complex _ cmGrowthUnitExponential163_valid 24)))

theorem cmGrowthExponential163_lower_power :
    (RealRaw.ofRat 16777216).Le (entireExponentialValue cmGrowthExponent163).val.realPart := by
  have hb := realFinitePower_lower cmGrowthUnitExponential163 cmGrowthUnitExponential163_valid 2
    (by decide) cmGrowthUnitExponential163_lower_two 24
  have hc : (2:Rat)^24=16777216 := by decide +kernel
  rw [hc] at hb
  have hr := ComplexRaw.realPart_equiv (equiv_symm cmGrowthExponential163_power_agreement)
  exact RealRaw.le_trans (realFinitePower_valid _ cmGrowthUnitExponential163_valid 24) hb
    (RealRaw.le_of_equiv (realFinitePower_valid _ cmGrowthUnitExponential163_valid 24)
      (realPart_valid (entireExponentialValue cmGrowthExponent163).property) hr)

end ComputableAnalysis.ModularForms
