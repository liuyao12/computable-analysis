import ComputableAnalysis.ModularForms.PairedGlobalDerivativeRemainderTailLimit
import ComputableAnalysis.ModularForms.FiniteRemainderSum

/-! Exact finite remainder comparison for global derivative blocks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedGlobalDerivativeRemainderTailPrefix_identity (B N k : Nat) (a z : Scalar)
    (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val) :
    (ScalarSeries.block (fun n => (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).val) N k).Equiv
      (SeriesLimitLaws.remainder
        (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval z hz).val) N k)
        (ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval a ha).val) N k)
        (ScalarSeries.block (fun n => (pairedGlobalSecondDerivativeTerm (4*B+n) a ha).val) N k)
        (sub z.val a.val)) := by
  have he := ScalarSeries.block_congr _ _
    (fun n => equiv_symm (pairedGlobalDerivativeTermMap_remainder (4*B+n) a z ha hz)) N k
  exact equiv_trans
    (ScalarSeries.block_valid _ (fun n => (pairedGlobalDerivativeRemainderTailTerm a z ha hz B n).property) N k)
    (ScalarSeries.block_valid _ (fun n => DomainFunctions.remainder_valid _ _ _ _ _ _) N k)
    (SeriesLimitLaws.remainder_valid _ _ _ _
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval z hz).property) N k)
      (ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval a ha).property) N k)
      (ScalarSeries.block_valid _ (fun n => (pairedGlobalSecondDerivativeTerm (4*B+n) a ha).property) N k)
      (sub_valid z.property a.property)) he
    (finiteRemainderSum _ _ _
      (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval z hz).property)
      (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval a ha).property)
      (fun n => (pairedGlobalSecondDerivativeTerm (4*B+n) a ha).property)
      _ (sub_valid z.property a.property) N k)

def pairedGlobalDerivativeTailMapPrefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B N : Nat) : ComplexRaw :=
  ScalarSeries.block (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval z hz).val) 0 (N+1)

theorem pairedGlobalDerivativeTailMapPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B N : Nat) : (pairedGlobalDerivativeTailMapPrefix z hz B N).Valid :=
  ScalarSeries.block_valid _ (fun n => ((pairedGlobalDerivativeTermMap (4*B+n)).eval z hz).property) 0 (N+1)

theorem pairedGlobalDerivativeTailMapPrefix_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (B : Nat) (hB : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedDerivativeTailValue z hz B) (pairedGlobalDerivativeTailMapPrefix z hz B N))
      (1024*((N+1:Nat):Rat)⁻¹) := by
  have he := ScalarSeries.block_congr _ _
    (fun n => pairedGlobalDerivativeTermMap_eval (4*B+n) z hz) 0 (N+1)
  exact Small.congr
    (sub_valid (pairedDerivativeTailValue_valid z hz B hB)
      (ScalarSeries.block_valid _ (fun n => (pairedDerivativeTailTerm z hz B n).property) 0 (N+1)))
    (sub_valid (pairedDerivativeTailValue_valid z hz B hB) (pairedGlobalDerivativeTailMapPrefix_valid z hz B N))
    (FunctionTheory.sub_congr (equiv_refl _ (pairedDerivativeTailValue_valid z hz B hB)) (equiv_symm he))
    (pairedDerivativeTailValue_close z hz B hB N)

end ComputableAnalysis.ModularForms
