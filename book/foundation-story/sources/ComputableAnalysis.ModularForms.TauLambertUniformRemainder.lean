import ComputableAnalysis.ModularForms.TauLambertPrefixRemainder

/-! Uniform quadratic remainder bounds for actual Lambert prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem block_first (t : Nat → Scalar) (N : Nat) :
    (ScalarSeries.block (fun n => (t n).val) 0 (N+1)).Equiv
      (add (t 0).val (ScalarSeries.block (fun n => (t (n+1)).val) 0 N)) := by
  induction N with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid _ (fun n => (t n).property) 0 1)
      (hright := add_valid (t 0).property (ofQComplex_valid _))
    let T := ComplexRawQuotient.ofRaw (t 0).val (t 0).property
    change 0+T=T+0
    grind only
  | succ N ih =>
    have he := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid _ (fun n => (t n).property) 0 (N+1))
      (hright := add_valid (t 0).property (ScalarSeries.block_valid _ (fun n => (t (n+1)).property) 0 N)) ih
    have hb : ScalarSeries.block (fun n => (t n).val) 0 (N+1+1) =
        add (ScalarSeries.block (fun n => (t n).val) 0 (N+1)) (t (N+1)).val := by
      simp only [ScalarSeries.block,Nat.zero_add]
    have hs : ScalarSeries.block (fun n => (t (n+1)).val) 0 (N+1) =
        add (ScalarSeries.block (fun n => (t (n+1)).val) 0 N) (t (N+1)).val := by
      simp only [ScalarSeries.block,Nat.zero_add]
    rw [hb,hs]
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (ScalarSeries.block_valid _ (fun n => (t n).property) 0 (N+1)) (t (N+1)).property)
      (hright := add_valid (t 0).property (add_valid (ScalarSeries.block_valid _ (fun n => (t (n+1)).property) 0 N) (t (N+1)).property))
    let T := ComplexRawQuotient.ofRaw (t 0).val (t 0).property
    let B := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (t (n+1)).val) 0 N)
      (ScalarSeries.block_valid _ (fun n => (t (n+1)).property) 0 N)
    let U := ComplexRawQuotient.ofRaw (t (N+1)).val (t (N+1)).property
    let Q := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (t n).val) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (t n).property) 0 (N+1))
    change Q=T+B at he
    change Q+U=T+(B+U)
    rw [he]
    grind only

/-- All actual finite prefixes obey the same quadratic remainder bound. -/
theorem tauLambertPrefix_uniform_remainder_bound (a z : Scalar)
    (ha : tauEulerNomeDomain a) (hz : tauEulerNomeDomain z)
    (H : Rat) (hH : 0≤H) (hd : Small (sub z.val a.val) H) (N : Nat) :
    Small (SeriesLimitLaws.remainder ((tauLambertPrefixMap 1 N).eval z hz).val
      ((tauLambertPrefixMap 1 N).eval a ha).val
      ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).val (sub z.val a.val))
      (71680*H^2) := by
  have hblock : Small (ScalarSeries.block (fun n => (tauLambertTermRemainder a z ha hz n).val) 0 N)
      (71680*H^2) := by
    cases N with
    | zero => exact Small.zero (Rat.mul_nonneg (by decide +kernel) (Rat.pow_nonneg hH))
    | succ K =>
      exact Small.congr
        (add_valid (tauLambertTermRemainder a z ha hz 0).property
          (ScalarSeries.block_valid _ (fun n => (tauLambertTermRemainder a z ha hz (n+1)).property) 0 K))
        (ScalarSeries.block_valid _ (fun n => (tauLambertTermRemainder a z ha hz n).property) 0 (K+1))
        (equiv_symm (block_first (tauLambertTermRemainder a z ha hz) K))
        (tauLambertRemainder_sum_bound a z ha hz H hH hd K)
  exact Small.congr
    (ScalarSeries.block_valid _ (fun n => (tauLambertTermRemainder a z ha hz n).property) 0 N)
    (SeriesLimitLaws.remainder_valid _ _ _ _ ((tauLambertPrefixMap 1 N).eval z hz).property
      ((tauLambertPrefixMap 1 N).eval a ha).property
      ((tauLambertPrefixMap_holomorphic 1 N).derivative a ha).property (sub_valid z.property a.property))
    (equiv_symm (tauLambertPrefix_remainder_block a z ha hz N)) hblock

end ComputableAnalysis.ModularForms
