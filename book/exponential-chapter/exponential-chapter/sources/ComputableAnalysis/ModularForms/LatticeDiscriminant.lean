import ComputableAnalysis.ModularForms.UpperLatticeHolomorphic
import ComputableAnalysis.ModularForms.UpperLatticeModularLaw

/-! The actual holomorphic lattice discriminant expression. Cusp normalization
and nonvanishing are separate theorems, not assumed here. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def constantUpper (c : Rat) : DomainFunctions.Map :=
  constantOn (fun z => InUpperHalfPlane z.val) upperOpenData.invariant
    ⟨ofQComplex ⟨c,0⟩,ofQComplex_valid _⟩

private def constantUpper_holomorphic (c : Rat) : Holomorphic (constantUpper c) :=
  constantOn_holomorphic upperOpenData ⟨ofQComplex ⟨c,0⟩,ofQComplex_valid _⟩

def latticeG2Map : DomainFunctions.Map :=
  productOn (constantUpper 60) upperWeightFourLatticeMap (fun _ hz => hz)

def latticeG3Map : DomainFunctions.Map :=
  productOn (constantUpper 140) upperWeightSixLatticeMap (fun _ hz => hz)

def latticeG2Map_holomorphic : Holomorphic latticeG2Map :=
  (constantUpper_holomorphic 60).productOn upperWeightFourLatticeMap_holomorphic (fun _ hz => hz)

def latticeG3Map_holomorphic : Holomorphic latticeG3Map :=
  (constantUpper_holomorphic 140).productOn upperWeightSixLatticeMap_holomorphic (fun _ hz => hz)

def latticeG2CubeMap : DomainFunctions.Map :=
  productOn (productOn latticeG2Map latticeG2Map (fun _ hz => hz)) latticeG2Map (fun _ hz => hz)

def latticeG3SquareMap : DomainFunctions.Map :=
  productOn latticeG3Map latticeG3Map (fun _ hz => hz)

def latticeG2CubeMap_holomorphic : Holomorphic latticeG2CubeMap :=
  (latticeG2Map_holomorphic.productOn latticeG2Map_holomorphic (fun _ hz => hz)).productOn
    latticeG2Map_holomorphic (fun _ hz => hz)

def latticeG3SquareMap_holomorphic : Holomorphic latticeG3SquareMap :=
  latticeG3Map_holomorphic.productOn latticeG3Map_holomorphic (fun _ hz => hz)

def latticeDiscriminantMap : DomainFunctions.Map :=
  sumOn latticeG2CubeMap (DomainFunctions.negate
    (productOn (constantUpper 27) latticeG3SquareMap (fun _ hz => hz))) (fun _ hz => hz)

def latticeDiscriminantMap_holomorphic : Holomorphic latticeDiscriminantMap :=
  latticeG2CubeMap_holomorphic.sumOn
    (((constantUpper_holomorphic 27).productOn latticeG3SquareMap_holomorphic (fun _ hz => hz)).negate)
    (fun _ hz => hz)

theorem latticeDiscriminantMap_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeDiscriminantMap.eval (fractionalLinear g z hz) (fractionalLinear_mem g z hz)).val.Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) 12) (latticeDiscriminantMap.eval z hz).val) := by
  let w := fractionalLinear g z hz
  let hw := fractionalLinear_mem g z hz
  let V4 := ComplexRawQuotient.ofRaw (upperWeightFourLatticeSum z hz) (upperWeightFourLatticeSum_valid z hz)
  let V6 := ComplexRawQuotient.ofRaw (upperWeightSixLatticeSum z hz) (upperWeightSixLatticeSum_valid z hz)
  let W4 := ComplexRawQuotient.ofRaw (upperWeightFourLatticeSum w hw) (upperWeightFourLatticeSum_valid w hw)
  let W6 := ComplexRawQuotient.ofRaw (upperWeightSixLatticeSum w hw) (upperWeightSixLatticeSum_valid w hw)
  let F := ComplexRawQuotient.ofRaw (integerAffine g.c g.d z.val) (integerAffine_valid _ _ z.property)
  have h4 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperWeightFourLatticeSum_valid w hw)
    (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)
      (upperWeightFourLatticeSum_valid z hz)) (upperWeightFourLatticeSum_action g z hz)
  have h6 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperWeightSixLatticeSum_valid w hw)
    (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 6)
      (upperWeightSixLatticeSum_valid z hz)) (upperWeightSixLatticeSum_action g z hz)
  change W4=ComplexRawQuotient.ofRaw (LocalODE.power (integerAffine g.c g.d z.val) 4)
    (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)*V4 at h4
  change W6=ComplexRawQuotient.ofRaw (LocalODE.power (integerAffine g.c g.d z.val) 6)
    (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 6)*V6 at h6
  rw [ScalarAlgebra.ofRaw_power] at h4 h6
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeDiscriminantMap.eval w hw).property)
    (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 12)
      (latticeDiscriminantMap.eval z hz).property)
  let C60 := ComplexRawQuotient.ofQComplex ⟨60,0⟩
  let C140 := ComplexRawQuotient.ofQComplex ⟨140,0⟩
  let C27 := ComplexRawQuotient.ofQComplex ⟨27,0⟩
  change ((C60*W4)*(C60*W4))*(C60*W4) + -(C27*((C140*W6)*(C140*W6))) =
    ComplexRawQuotient.ofRaw (LocalODE.power (integerAffine g.c g.d z.val) 12)
      (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 12)*
    (((C60*V4)*(C60*V4))*(C60*V4) + -(C27*((C140*V6)*(C140*V6))))
  rw [ScalarAlgebra.ofRaw_power]
  change ((C60*W4)*(C60*W4))*(C60*W4) + -(C27*((C140*W6)*(C140*W6))) =
    F^12*(((C60*V4)*(C60*V4))*(C60*V4) + -(C27*((C140*V6)*(C140*V6))))
  change W4=F^4*V4 at h4
  change W6=F^6*V6 at h6
  rw [h4,h6]
  grind only

theorem latticeG2CubeMap_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val) :
    (latticeG2CubeMap.eval (fractionalLinear g z hz) (fractionalLinear_mem g z hz)).val.Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) 12) (latticeG2CubeMap.eval z hz).val) := by
  let w := fractionalLinear g z hz
  let hw := fractionalLinear_mem g z hz
  let V4 := ComplexRawQuotient.ofRaw (upperWeightFourLatticeSum z hz) (upperWeightFourLatticeSum_valid z hz)
  let V6 := ComplexRawQuotient.ofRaw (upperWeightSixLatticeSum z hz) (upperWeightSixLatticeSum_valid z hz)
  let W4 := ComplexRawQuotient.ofRaw (upperWeightFourLatticeSum w hw) (upperWeightFourLatticeSum_valid w hw)
  let W6 := ComplexRawQuotient.ofRaw (upperWeightSixLatticeSum w hw) (upperWeightSixLatticeSum_valid w hw)
  let F := ComplexRawQuotient.ofRaw (integerAffine g.c g.d z.val) (integerAffine_valid _ _ z.property)
  have h4 := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := upperWeightFourLatticeSum_valid w hw)
    (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)
      (upperWeightFourLatticeSum_valid z hz)) (upperWeightFourLatticeSum_action g z hz)
  change W4=ComplexRawQuotient.ofRaw (LocalODE.power (integerAffine g.c g.d z.val) 4)
    (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)*V4 at h4
  rw [ScalarAlgebra.ofRaw_power] at h4
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeG2CubeMap.eval w hw).property)
    (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 12)
      (latticeG2CubeMap.eval z hz).property)
  let C60 := ComplexRawQuotient.ofQComplex ⟨60,0⟩
  let C140 := ComplexRawQuotient.ofQComplex ⟨140,0⟩
  let C27 := ComplexRawQuotient.ofQComplex ⟨27,0⟩
  change ((C60*W4)*(C60*W4))*(C60*W4) =
    ComplexRawQuotient.ofRaw (LocalODE.power (integerAffine g.c g.d z.val) 12)
      (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 12)*
    (((C60*V4)*(C60*V4))*(C60*V4))
  rw [ScalarAlgebra.ofRaw_power]
  change ((C60*W4)*(C60*W4))*(C60*W4) = F^12*(((C60*V4)*(C60*V4))*(C60*V4))
  change W4=F^4*V4 at h4
  rw [h4]
  grind only

end ComputableAnalysis.ModularForms
