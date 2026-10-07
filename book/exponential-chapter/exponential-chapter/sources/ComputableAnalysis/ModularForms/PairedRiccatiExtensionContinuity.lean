import ComputableAnalysis.ModularForms.PairedRegularDivisionContinuity
import ComputableAnalysis.ModularForms.PairedRiccatiExtensionBound

/-! Continuity through zero of the constructed lattice Riccati expression. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedRiccatiExtension_continuous :
    ContinuousOn (LocalODE.interior (1/4)) pairedRiccatiExtension :=
  sumContinuous pairedRegularPartDerivative
    (fun z hz => DomainFunctions.scalarSum
      (DomainFunctions.scalarSum (pairedRegularDivisionMap.eval z hz) (pairedRegularDivisionMap.eval z hz))
      (DomainFunctions.scalarProduct (pairedRegularPartMap.eval z hz) (pairedRegularPartMap.eval z hz)))
    pairedRegularPartDerivative_continuous
    (sumContinuous
      (fun z hz => DomainFunctions.scalarSum (pairedRegularDivisionMap.eval z hz) (pairedRegularDivisionMap.eval z hz))
      (fun z hz => DomainFunctions.scalarProduct (pairedRegularPartMap.eval z hz) (pairedRegularPartMap.eval z hz))
      (sumContinuous pairedRegularDivisionMap.eval pairedRegularDivisionMap.eval
        pairedRegularDivisionMap_continuous pairedRegularDivisionMap_continuous)
      (productContinuous pairedRegularPartMap.eval pairedRegularPartMap.eval
        pairedRegularPartMap_holomorphic.continuous pairedRegularPartMap_holomorphic.continuous))

end ComputableAnalysis.ModularForms
