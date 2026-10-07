import ComputableAnalysis.ModularForms.RepresentedNegativeHorizontalReciprocalBound
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeTerms
import ComputableAnalysis.ModularForms.PairedGlobalOffPoleUpperAgreement

/-! Height-independent summable estimates for actual paired derivative terms. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedHorizontal_reciprocal_bounds (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (R : Rat) (hre : -R≤(z.val.compute N).lo.re)
    (hhi : (z.val.compute N).hi.re≤R) (n : Nat) (hlarge : 2*R≤((n+1:Nat):Rat)) :
    Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val (16/((n+1:Nat):Rat)) ∧
    Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val (16/((n+1:Nat):Rat)) :=
  ⟨globalIntegerReciprocal_negative_index_decay z (pairedGlobalOffPole_upper_mem z hz)
      N R hhi (n+1) (by omega) hlarge,
    globalIntegerReciprocal_positive_index_decay z (pairedGlobalOffPole_upper_mem z hz)
      N R hre (n+1) (by omega) hlarge⟩

theorem integerReciprocalDerivativeMap_bound (k : Int) (z : Scalar)
    (hz : InUpperHalfPlane z.val) (M : Rat) (hM : 0≤M)
    (hs : Small ((integerReciprocalMap k).eval z hz).val M) :
    Small ((integerReciprocalDerivativeMap k).eval z hz).val (2*M*M) :=
  SeriesLimitLaws.small_neg (Small.mul ((integerReciprocalMap k).eval z hz).property
    ((integerReciprocalMap k).eval z hz).property hM hM hs hs)

theorem pairedGlobalDerivativeTerm_horizontal_decay (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (R : Rat) (hre : -R≤(z.val.compute N).lo.re)
    (hhi : (z.val.compute N).hi.re≤R) (n : Nat) (hlarge : 2*R≤((n+1:Nat):Rat)) :
    Small ((pairedGlobalDerivativeTermMap n).eval z hz).val
      (1024*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))) := by
  have hb := pairedHorizontal_reciprocal_bounds z hz N R hre hhi n hlarge
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hM : 0≤16/((n+1:Nat):Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  have hs := LocalODE.small_add
    (integerReciprocalDerivativeMap_bound _ z hz _ hM hb.1)
    (integerReciprocalDerivativeMap_bound _ z hz _ hM hb.2)
  exact hs.mono (by simp only [Rat.div_def,Rat.one_mul]; grind only)

theorem pairedGlobalSecondDerivativeTerm_horizontal_decay (z : Scalar) (hz : InUpperHalfPlane z.val)
    (N : Nat) (R : Rat) (hre : -R≤(z.val.compute N).lo.re)
    (hhi : (z.val.compute N).hi.re≤R) (n : Nat) (hlarge : 2*R≤((n+1:Nat):Rat)) :
    Small (pairedGlobalSecondDerivativeTerm n z hz).val
      (65536*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))*(1/((n+1:Nat):Rat))) := by
  have hb := pairedHorizontal_reciprocal_bounds z hz N R hre hhi n hlarge
  have hn : (0:Rat)<((n+1:Nat):Rat) := by exact_mod_cast (show 0<n+1 by omega)
  have hM : 0≤16/((n+1:Nat):Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  exact (pairedGlobalSecondDerivativeTerm_bound n z hz _ hM hb.1 hb.2).mono
    (by simp only [Rat.div_def,Rat.one_mul]; grind only)

end ComputableAnalysis.ModularForms
