import ComputableAnalysis.ModularForms.PairedRiccatiExtensionHolomorphic
import ComputableAnalysis.ModularForms.PairedRiccatiLaurentNormalization

/-! Holomorphic Riccati extensions at every integer lattice pole. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedIntegerRiccatiExtensionMap (k : Int) : DomainFunctions.Map :=
  compose pairedRiccatiExtensionMap (entireIntegerShiftMap (-k))

def pairedIntegerRiccatiExtensionMap_holomorphic (k : Int) :
    Holomorphic (pairedIntegerRiccatiExtensionMap k) :=
  pairedRiccatiExtensionMap_holomorphic.compose (entireIntegerShiftMap_holomorphic (-k))

theorem pairedIntegerLaurent_riccati_extension (k : Int) (z : Scalar)
    (hz : (pairedIntegerLaurentMap k).domain z) :
    (add ((pairedIntegerLaurentMap_holomorphic k).derivative z hz).val
      (mul ((pairedIntegerLaurentMap k).eval z hz).val ((pairedIntegerLaurentMap k).eval z hz).val)).Equiv
      ((pairedIntegerRiccatiExtensionMap k).eval z ⟨hz.1,hz.2.1⟩).val := by
  let w := integerShiftScalar z (-k)
  have hw := compose_outer_mem hz
  have he := pairedLaurent_riccati_extension w hw
  have hd : ((pairedIntegerLaurentMap_holomorphic k).derivative z hz).val.Equiv
      (pairedZeroLaurentMap_holomorphic.derivative w hw).val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((pairedIntegerLaurentMap_holomorphic k).derivative z hz).property)
      (hright := (pairedZeroLaurentMap_holomorphic.derivative w hw).property)
    let D := ComplexRawQuotient.ofRaw (pairedZeroLaurentMap_holomorphic.derivative w hw).val
      (pairedZeroLaurentMap_holomorphic.derivative w hw).property
    change D*ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩=D
    have ho : ComplexRawQuotient.ofQComplex ⟨(1:Rat),0⟩ = ((1:Int):ComplexRawQuotient.Value) := by
      simpa only [Rat.intCast_one] using integer_constant (1:Int)
    rw [ho]
    grind only
  exact equiv_trans
    (add_valid ((pairedIntegerLaurentMap_holomorphic k).derivative z hz).property
      (mul_valid ((pairedIntegerLaurentMap k).eval z hz).property ((pairedIntegerLaurentMap k).eval z hz).property))
    (add_valid (pairedZeroLaurentMap_holomorphic.derivative w hw).property
      (mul_valid (pairedZeroLaurentMap.eval w hw).property (pairedZeroLaurentMap.eval w hw).property))
    ((pairedIntegerRiccatiExtensionMap k).eval z ⟨hz.1,hz.2.1⟩).property
    (add_equiv hd (equiv_refl _ (mul_valid (pairedZeroLaurentMap.eval w hw).property
      (pairedZeroLaurentMap.eval w hw).property))) he

theorem pairedIntegerRiccatiExtension_at_integer (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z)
    (he : z.val.Equiv (rationalInteger k).val) :
    ((pairedIntegerRiccatiExtensionMap k).eval z hz).val.Equiv pairedRiccatiCenterConstant.val :=
  pairedRiccatiExtension_center_identity (integerShiftScalar z (-k))
    (compose_outer_mem hz) (integerShiftScalar_at_integer k z he)

end ComputableAnalysis.ModularForms
