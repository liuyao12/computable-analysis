import ComputableAnalysis.ModularForms.PairedOffPoleTailDerivativeSeries

/-! Representation invariance of the actual off-pole derivative sum. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem pairedOffPoleTailDerivativeTerm_congr (B n : Nat) (z w : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (hw : LocalODE.interior (B:Rat) w)
    (he : z.val.Equiv w.val) :
    (pairedOffPoleTailDerivativeTerm B n z hz).val.Equiv
      (pairedOffPoleTailDerivativeTerm B n w hw).val :=
  equiv_trans (pairedOffPoleTailDerivativeTerm B n z hz).property
    ((pairedOffPoleTailTermMap_holomorphic B n).derivative z hz).property
    (pairedOffPoleTailDerivativeTerm B n w hw).property
    (equiv_symm (pairedOffPoleTailTermMap_derivative B n z hz))
    (equiv_trans ((pairedOffPoleTailTermMap_holomorphic B n).derivative z hz).property
      ((pairedOffPoleTailTermMap_holomorphic B n).derivative w hw).property
      (pairedOffPoleTailDerivativeTerm B n w hw).property
      ((pairedOffPoleTailTermMap_holomorphic B n).derivative_congr z w hz hw he)
      (pairedOffPoleTailTermMap_derivative B n w hw))

theorem pairedOffPoleTailDerivativeValue_congr (B : Nat) (z w : Scalar)
    (hz : LocalODE.interior (B:Rat) z) (hw : LocalODE.interior (B:Rat) w)
    (he : z.val.Equiv w.val) :
    (pairedOffPoleTailDerivativeValue B z hz).val.Equiv
      (pairedOffPoleTailDerivativeValue B w hw).val :=
  inverseSquareSeriesValue_congr _ _
    (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property)
    (fun n => (pairedOffPoleTailDerivativeTerm B n w hw).property)
    (pairedOffPoleTailDerivativeConstant B)
    (fun n => pairedOffPoleTailDerivativeTerm_bound B n z hz)
    (fun n => pairedOffPoleTailDerivativeTerm_bound B n w hw)
    (fun n => pairedOffPoleTailDerivativeTerm_congr B n z w hz hw he)

def pairedOffPoleTailDerivativeMap (B : Nat) : DomainFunctions.Map where
  domain := (pairedOffPoleTailMap B).domain
  eval := pairedOffPoleTailDerivativeValue B
  domain_congr := (pairedOffPoleTailMap B).domain_congr
  eval_congr z w hz hw he := pairedOffPoleTailDerivativeValue_congr B z w hz hw he

theorem pairedOffPoleTailDerivativeValue_bound (B : Nat) (z : Scalar)
    (hz : LocalODE.interior (B:Rat) z) :
    Small (pairedOffPoleTailDerivativeValue B z hz).val (2*(pairedOffPoleTailDerivativeConstant B:Rat)) :=
  inverseSquareSeriesValue_bound _
    (fun n => (pairedOffPoleTailDerivativeTerm B n z hz).property)
    (pairedOffPoleTailDerivativeConstant B) (fun n => pairedOffPoleTailDerivativeTerm_bound B n z hz)


def pairedOffPoleTailDerivativeTerm_continuous (B n : Nat) :
    ContinuousOn (pairedOffPoleTailMap B).domain (pairedOffPoleTailDerivativeTerm B n) where
  delta := (pairedOffPoleTailTermMap_holomorphic B n).continuousDerivative.delta
  estimate a ha eps z hz hd := by
    have hb := (pairedOffPoleTailTermMap_holomorphic B n).continuousDerivative.estimate a ha eps z hz hd
    exact Small.congr
      (sub_valid ((pairedOffPoleTailTermMap_holomorphic B n).derivative z hz).property
        ((pairedOffPoleTailTermMap_holomorphic B n).derivative a ha).property)
      (sub_valid (pairedOffPoleTailDerivativeTerm B n z hz).property
        (pairedOffPoleTailDerivativeTerm B n a ha).property)
      (FunctionTheory.sub_congr (pairedOffPoleTailTermMap_derivative B n z hz)
        (pairedOffPoleTailTermMap_derivative B n a ha)) hb

end ComputableAnalysis.ModularForms
