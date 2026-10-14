import ComputableAnalysis.ModularForms.PairedCutoffAgreement

/-! Paired partial-fraction values with an internal executable size bound. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

def pairedInternalBound (z : Scalar) : Nat :=
  RationalMajorant.factorialTailStart (LocalODE.boxCoordinateBound (z.val.compute 0))+1

theorem pairedInternalBound_small (z : Scalar) : Small z.val ((pairedInternalBound z):Rat) := by
  have hs := LocalODE.small_from_box z.val z.property 0
  apply hs.mono
  have h := RationalMajorant.factorialTailStart_satisfies (LocalODE.boxCoordinateBound (z.val.compute 0))
  have hp : (0:Rat)≤((pairedInternalBound z):Rat) := Rat.natCast_nonneg
  change LocalODE.boxCoordinateBound (z.val.compute 0)≤((pairedInternalBound z):Rat)/2 at h
  grind only

def pairedSeriesValue (z : Scalar) (hd : PairedSeriesDomain z) : ComplexRaw :=
  pairedFullValue z hd (pairedInternalBound z) (pairedInternalBound_small z)

theorem pairedSeriesValue_valid (z : Scalar) (hd : PairedSeriesDomain z) :
    (pairedSeriesValue z hd).Valid :=
  pairedFullValue_valid z hd (pairedInternalBound z) (pairedInternalBound_small z)

theorem pairedSeriesValue_agrees (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) : (pairedSeriesValue z hd).Equiv (pairedFullValue z hd B hz) :=
  pairedFullValue_cutoff z hd (pairedInternalBound z) B (pairedInternalBound_small z) hz

theorem pairedSeriesValue_congr (z w : Scalar) (hd : PairedSeriesDomain z)
    (hw : PairedSeriesDomain w) (he : z.val.Equiv w.val) :
    (pairedSeriesValue z hd).Equiv (pairedSeriesValue w hw) :=
  pairedFullValue_agreement z w hd hw (pairedInternalBound z) (pairedInternalBound w)
    (pairedInternalBound_small z) (pairedInternalBound_small w) he

def pairedPartialFractionValue (z : Scalar) (h0 : NonzeroBoxSearch.Nonzero z)
    (hd : PairedSeriesDomain z) : ComplexRaw :=
  add (RepresentedReciprocal.inverse z h0).val (pairedSeriesValue z hd)

theorem pairedPartialFractionValue_valid (z : Scalar) (h0 : NonzeroBoxSearch.Nonzero z)
    (hd : PairedSeriesDomain z) : (pairedPartialFractionValue z h0 hd).Valid :=
  add_valid (RepresentedReciprocal.inverse z h0).property (pairedSeriesValue_valid z hd)

theorem pairedPartialFractionValue_congr (z w : Scalar)
    (h0 : NonzeroBoxSearch.Nonzero z) (hw0 : NonzeroBoxSearch.Nonzero w)
    (hd : PairedSeriesDomain z) (hw : PairedSeriesDomain w) (he : z.val.Equiv w.val) :
    (pairedPartialFractionValue z h0 hd).Equiv (pairedPartialFractionValue w hw0 hw) :=
  add_equiv (RepresentedReciprocal.inverse_congr z w h0 hw0 he) (pairedSeriesValue_congr z w hd hw he)

end ComputableAnalysis.ModularForms
