import ComputableAnalysis.ModularForms.InverseSquareSeriesBound
import ComputableAnalysis.ModularForms.PairedGlobalSecondDerivativeInvariance

/-! Bounds for the complete actual second derivative from finite reciprocal bounds. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalSecondDerivativePrefix_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) (M : Rat) (hM : 0≤M)
    (hm : ∀ n, n<N → Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hp : ∀ n, n<N → Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M) :
    Small (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n z hz).val) 0 N)
      ((N:Rat)*(16*M*M*M)) := by
  induction N with
  | zero => exact Small.zero (by simp [Rat.zero_mul])
  | succ N ih =>
    have hi := ih (fun n hn => hm n (by omega)) (fun n hn => hp n (by omega))
    have ht := pairedGlobalSecondDerivativeTerm_bound N z hz M hM
      (hm N (by omega)) (hp N (by omega))
    have hs := LocalODE.small_add hi ht
    have he : (N:Rat)*(16*M*M*M)+(16*M*M*M)=((N+1:Nat):Rat)*(16*M*M*M) := by
      rw [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
      grind only
    rw [he] at hs
    simpa only [ScalarSeries.block,Nat.zero_add] using hs

theorem pairedGlobalSecondDerivativeAssembly_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hB : Small z.val (B:Rat))
    (M : Rat) (hM : 0≤M)
    (hzero : Small ((integerReciprocalMap 0).eval z hz).val M)
    (hm : ∀ n, n<4*B → Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hp : ∀ n, n<4*B → Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M) :
    Small (pairedGlobalSecondDerivativeAssembly z hz B hB).val
      (8*M*M*M+((4*B:Nat):Rat)*(16*M*M*M)+131072) := by
  have hc := integerReciprocalSecondDerivative_bound 0 z hz M hM hzero
  have hf := pairedGlobalSecondDerivativePrefix_bound z hz (4*B) M hM hm hp
  have ht := pairedGlobalSecondDerivativeTailValue_bound z hz B hB
  exact (LocalODE.small_add hc (LocalODE.small_add hf ht)).mono (by grind only)

theorem pairedCanonicalSecondDerivative_regional_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (B : Nat) (hroom : Small z.val ((B:Rat)-2))
    (M : Rat) (hM : 0≤M)
    (hzero : Small ((integerReciprocalMap 0).eval z hz).val M)
    (hm : ∀ n, n<4*B → Small ((integerReciprocalMap (-((n+1:Nat):Int))).eval z hz).val M)
    (hp : ∀ n, n<4*B → Small ((integerReciprocalMap ((n+1:Nat):Int)).eval z hz).val M) :
    Small (pairedCanonicalSecondDerivative z hz).val
      (8*M*M*M+((4*B:Nat):Rat)*(16*M*M*M)+131072) :=
  Small.congr (pairedGlobalSecondDerivativeAssembly z hz B (hroom.mono (by grind only))).property
    (pairedCanonicalSecondDerivative z hz).property
    (pairedCanonicalSecondDerivative_cutoff B z hz hroom)
    (pairedGlobalSecondDerivativeAssembly_bound z hz B (hroom.mono (by grind only)) M hM hzero hm hp)

end ComputableAnalysis.ModularForms
