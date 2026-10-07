import ComputableAnalysis.ModularForms.PairedEntireFixedBoxDerivativeBound

/-! Quantitative interior margin for the executable height-balanced cutoff. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedHeightBalancedSecondDerivativeCutoff (z : Scalar) (N : Nat) : Nat :=
  pairedHeightBalancedCutoff z N+1

theorem pairedHeightBalancedCutoff_second_derivative_room (z : Scalar) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3) :
    Small z.val ((pairedHeightBalancedSecondDerivativeCutoff z N:Rat)-2) := by
  let a := (z.val.compute N).hi.im+3
  have hl : a≤(a.ceil:Rat) := Rat.le_ceil
  have ho := valid_ordered z.property N
  have hip := ho.2
  have hrp := ho.1
  have hapos : (0:Rat)<(a.ceil:Rat) := by dsimp [a] at *; grind only
  have hint : (0:Int)<a.ceil := by exact_mod_cast hapos
  have hcast : (pairedHeightBalancedCutoff z N:Rat)=(a.ceil:Rat) := by
    have hc := Int.toNat_of_nonneg (show 0≤a.ceil by omega)
    have hcq := congrArg (fun k : Int => (k:Rat)) hc
    simpa only [Rat.intCast_natCast,pairedHeightBalancedCutoff,a] using hcq
  apply (LocalODE.small_from_box z.val z.property N).mono
  simp only [pairedHeightBalancedSecondDerivativeCutoff,Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
  rw [hcast]
  unfold LocalODE.boxCoordinateBound
  dsimp [a] at hl
  grind

theorem pairedHeightBalancedSecondDerivativeCutoff_bounds (z : Scalar) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3)
    (hh : (z.val.compute N).height≤1) :
    0<pairedHeightBalancedSecondDerivativeCutoff z N ∧
      (pairedHeightBalancedSecondDerivativeCutoff z N:Rat)≤7*(z.val.compute N).lo.im := by
  have h := pairedHeightBalancedCutoff_bounds z N him hre hhi hh
  constructor
  · unfold pairedHeightBalancedSecondDerivativeCutoff
    omega
  · simp only [pairedHeightBalancedSecondDerivativeCutoff,Rat.natCast_add,
      show ((1:Nat):Rat)=1 by decide +kernel]
    have hb := h.2.2
    grind only

end ComputableAnalysis.ModularForms
