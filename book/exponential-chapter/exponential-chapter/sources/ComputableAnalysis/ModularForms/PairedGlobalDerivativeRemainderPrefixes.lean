import ComputableAnalysis.ModularForms.PairedGlobalDerivativeRemainderAgreement
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Exact finite remainder comparison for global derivative blocks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalDerivativeRemainderPrefix_identity (N k : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (ScalarSeries.block (fun n => (pairedGlobalDerivativeRemainder n a z ha hz).val) N k).Equiv
      (SeriesLimitLaws.remainder
        (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).val) N k)
        (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap n).eval a ha).val) N k)
        (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm n a ha).val) N k)
        (sub z.val a.val)) := by
  have he := ScalarSeries.block_congr _ _
    (fun n => equiv_symm (pairedGlobalDerivativeTermMap_remainder n a z ha hz)) N k
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (pairedGlobalDerivativeRemainder n a z ha hz).property) N k)
    (ScalarSeries.block_valid _ (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) N k)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property) N k)
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap n).eval a ha).property) N k)
      (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTerm n a ha).property) N k)
      (sub_valid z.property a.property)) he
    (finiteRemainderSum _ _ _
      (fun n => ((pairedGlobalDerivativeTermMap n).eval z hz).property)
      (fun n => ((pairedGlobalDerivativeTermMap n).eval a ha).property)
      (fun n => (pairedGlobalSecondDerivativeTerm n a ha).property)
      _ (sub_valid z.property a.property) N k)

end ComputableAnalysis.ModularForms
