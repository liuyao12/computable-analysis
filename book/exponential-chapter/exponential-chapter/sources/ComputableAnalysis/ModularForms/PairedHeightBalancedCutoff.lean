import ComputableAnalysis.ModularForms.PairedVerticalValuePrefixes

/-! A rational-box cutoff proportional to the certified imaginary height. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedHeightBalancedCutoff (z : Scalar) (N : Nat) : Nat :=
  ((z.val.compute N).hi.im+3).ceil.toNat

theorem pairedHeightBalancedCutoff_bounds (z : Scalar) (N : Nat)
    (him : 1≤(z.val.compute N).lo.im)
    (hre : -3≤(z.val.compute N).lo.re) (hhi : (z.val.compute N).hi.re≤3)
    (hh : (z.val.compute N).height≤1) :
    0<pairedHeightBalancedCutoff z N ∧
    Small z.val (pairedHeightBalancedCutoff z N:Rat) ∧
    (pairedHeightBalancedCutoff z N:Rat)≤6*(z.val.compute N).lo.im := by
  let a := (z.val.compute N).hi.im+3
  have hl : a≤(a.ceil:Rat) := Rat.le_ceil
  have hu : (a.ceil:Rat)<a+1 := Rat.ceil_lt
  have ho := valid_ordered z.property N
  have hip := ho.2
  have hapos : (0:Rat)<(a.ceil:Rat) := by dsimp [a] at *; grind only
  have hint : (0:Int)<a.ceil := by exact_mod_cast hapos
  have hcast : (pairedHeightBalancedCutoff z N:Rat)=(a.ceil:Rat) := by
    have hc := Int.toNat_of_nonneg (show 0≤a.ceil by omega)
    have hcq := congrArg (fun k : Int => (k:Rat)) hc
    simpa only [Rat.intCast_natCast,pairedHeightBalancedCutoff,a] using hcq
  refine ⟨?_,?_,?_⟩
  · have hn : 0<a.ceil.toNat := by omega
    exact hn
  · apply (LocalODE.small_from_box z.val z.property N).mono
    rw [hcast]
    unfold LocalODE.boxCoordinateBound
    dsimp [a] at hl
    grind
  · rw [hcast]
    change (z.val.compute N).hi.im-(z.val.compute N).lo.im≤1 at hh
    dsimp [a] at hu
    grind only

end ComputableAnalysis.ModularForms
