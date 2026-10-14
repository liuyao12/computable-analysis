import ComputableAnalysis.ModularForms.UnitDiskEisenstein
import ComputableAnalysis.ModularForms.DiskLambertHolomorphic

/-! Full-unit-disk holomorphicity for the extensions of the primary rational
Eisenstein functions. Normalization preserves the rational evaluator and all
exact comparison identities. -/
namespace ComputableAnalysis.ModularForms.RationalEisenstein
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The extension of each rational Eisenstein function is holomorphic at
 every represented point of the open unit disk, in all complex directions. -/
noncomputable def unitDiskDerivedMap_holomorphic (w : Weight) : Holomorphic (unitDiskDerivedMap w) := by
  let L := DiskLambert.map (degree w)
  let HL := DiskLambert.holomorphic (degree w)
  let O := ScalarTopology.ofDomain L HL.openDomain
  let c : Scalar := ⟨scaleRat (coefficient w) one,scaleRat_valid (ofQComplex_valid _)⟩
  let C := constantOn L.domain L.domain_congr c
  let U := constantOn L.domain L.domain_congr oneScalar
  have HC : Holomorphic C := constantOn_holomorphic O c
  have HU : Holomorphic U := constantOn_holomorphic O oneScalar
  exact (HU.sumOn (HC.productOn HL (fun _ h => h)) (fun _ h => h)).transfer (unitDiskDerivedMap w)
    (fun _ h => h) ⟨HL.openDomain.radius,HL.openDomain.inside⟩ (fun q hq => by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid oneScalar.property (mul_valid c.property (L.eval q hq).property))
        (hright := (unitDiskDerivedValue w q hq).property)
      let V := ComplexRawQuotient.ofRaw (L.eval q hq).val (L.eval q hq).property
      change 1+ComplexRawQuotient.scaleRat (coefficient w) 1*V=1+ComplexRawQuotient.scaleRat (coefficient w) V
      rw [←ComplexRawQuotient.scaleRat_mul]
      have h : (1:ComplexRawQuotient.Value)*V=V := by grind only
      rw [h])

noncomputable def sampledEisensteinTwo_holomorphic : Holomorphic sampledEisensteinTwo := unitDiskDerivedMap_holomorphic .two
noncomputable def sampledEisensteinFour_holomorphic : Holomorphic sampledEisensteinFour := unitDiskDerivedMap_holomorphic .four
noncomputable def sampledEisensteinSix_holomorphic : Holomorphic sampledEisensteinSix := unitDiskDerivedMap_holomorphic .six

/-- Exact derivative agreement on the previous chart follows from actual
 derivative uniqueness, rather than from a chosen derivative formula. -/
theorem unitDiskDerived_derivative_smallChart_agreement (w : Weight) (q : Scalar) (hq : wideLambertFifthDomain q) :
    ((unitDiskDerivedMap_holomorphic w).derivative q (DiskLambert.wide_mem q hq)).val.Equiv
      ((derivedMap_holomorphic w).derivative q hq).val := by
  let H := (unitDiskDerivedMap_holomorphic w).transfer (derivedMap w)
    (fun z hz => DiskLambert.wide_mem z hz) (derivedMap_holomorphic w).openDomain
    (fun z hz => unitDiskDerived_smallChart_agreement w z hz)
  exact (H.atPoint q hq).unique ((derivedMap_holomorphic w).atPoint q hq) H.openDomain
end ComputableAnalysis.ModularForms.RationalEisenstein
