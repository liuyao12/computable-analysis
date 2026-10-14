import ComputableAnalysis.ModularForms.PairedHorizontalDerivativeDecay
import ComputableAnalysis.ModularForms.InverseSquareSeries

/-! Height-independent tail block bounds for the actual derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem inverseSquare_block_bound_from (t : Nat → ComplexRaw) (C : Nat) (N : Nat)
    (hB : ∀ n, N≤n → Small (t n) ((C:Rat)*reciprocalSquare (n+1))) (k : Nat) :
    Small (ScalarSeries.block t N k) ((C:Rat)*reciprocalSquareBlock N k) := by
  induction k with
  | zero => exact Small.zero (by change (0:Rat)≤(C:Rat)*0; simp [Rat.mul_zero])
  | succ k ih =>
    have hs := LocalODE.small_add ih (hB (N+k) (by omega))
    have he : (C:Rat)*reciprocalSquareBlock N k+(C:Rat)*reciprocalSquare (N+k+1)=
        (C:Rat)*reciprocalSquareBlock N (k+1) := by
      rw [reciprocalSquareBlock]; grind only
    rw [he] at hs
    exact hs

theorem pairedGlobalDerivative_horizontal_block_bound (z : Scalar) (hz : InUpperHalfPlane z.val)
    (boxStage : Nat) (R : Rat) (hre : -R≤(z.val.compute boxStage).lo.re)
    (hhi : (z.val.compute boxStage).hi.re≤R) (N k : Nat)
    (hlarge : 2*R≤((N+1:Nat):Rat)) :
    Small (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) N k)
      (1024*reciprocalSquareBlock N k) := by
  apply inverseSquare_block_bound_from _ 1024 N _ k
  intro n hn
  have hcast : ((N+1:Nat):Rat)≤((n+1:Nat):Rat) := by exact_mod_cast (show N+1≤n+1 by omega)
  have hs := pairedGlobalDerivativeTerm_horizontal_decay z hz boxStage R hre hhi n
    (Rat.le_trans hlarge hcast)
  apply hs.mono
  simp only [reciprocalSquare,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
  change 1024*((n+1:Nat):Rat)⁻¹*((n+1:Nat):Rat)⁻¹ ≤
    1024*(((n+1:Nat):Rat)⁻¹*((n+1:Nat):Rat)⁻¹)
  grind only

theorem pairedGlobalDerivative_horizontal_block_tail (z : Scalar) (hz : InUpperHalfPlane z.val)
    (boxStage : Nat) (R : Rat) (hre : -R≤(z.val.compute boxStage).lo.re)
    (hhi : (z.val.compute boxStage).hi.re≤R) (N k : Nat)
    (hN : 0<N) (hlarge : 2*R≤((N+1:Nat):Rat)) :
    Small (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) N k)
      (1024*(N:Rat)⁻¹) :=
  (pairedGlobalDerivative_horizontal_block_bound z hz boxStage R hre hhi N k hlarge).mono
    (Rat.mul_le_mul_of_nonneg_left (reciprocalSquareBlock_tail N k hN) (by decide +kernel))

end ComputableAnalysis.ModularForms
