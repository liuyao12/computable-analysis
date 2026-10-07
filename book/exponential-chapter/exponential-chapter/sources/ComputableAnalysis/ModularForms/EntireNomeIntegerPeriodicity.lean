import ComputableAnalysis.ModularForms.EntireNomeCotangentEquation

/-! Exact integer periods of the entire nome and its pole-free quotients. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem entireNomeMap_period_one (z : Scalar) :
    (entireNomeMap.eval (integerShiftScalar z 1) (entireNomeMap_mem _)).val.Equiv
      (entireNomeMap.eval z (entireNomeMap_mem z)).val := by
  let a := (affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval z trivial
  let b : Scalar := ⟨add a.val nomeSlope.val,add_valid a.property nomeSlope.property⟩
  have ha : ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval
      (integerShiftScalar z 1) trivial).val.Equiv b.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((affine ⟨zero,ofQComplex_valid _⟩ nomeSlope).eval (integerShiftScalar z 1) trivial).property)
      (hright := b.property)
    let A := gridScalarValue nomeSlope
    let Z := gridScalarValue z
    change 0+A*ComplexRawQuotient.ofRaw (integerAffine 1 1 z.val)
      (integerAffine_valid _ _ z.property)=(0+A*Z)+A
    rw [integerAffine_class]
    have h1 : ((1:Int):ScalarAlgebra.Value)=(1:ScalarAlgebra.Value) := by
      change ComplexRawQuotient.scaleRat 1 1=1
      exact ComplexRawQuotient.scaleRat_one _
    rw [h1]
    change 0+A*(1*Z+1)=(0+A*Z)+A
    grind only
  let h : Scalar := ⟨GeometricPiRotation.imaginaryHalf,GeometricPiRotation.imaginaryHalf_valid⟩
  have hexp : (entireExponentialValue nomeSlope).val.Equiv
      (LocalODE.power (entireExponentialValue h).val 4) := by
    have ht := entireExponential_nat_multiple h 4
    have hc : ((4:Nat):Rat)=(4:Rat) := by decide +kernel
    simpa only [hc,h,nomeSlope,GeometricPiRotation.imaginaryHalf,imaginaryAxis] using ht
  have hphase := LocalODE.power_congr _ _ (entireExponentialValue h).property
    (ofQComplex_valid _) entireExponential_geometric_quarterTurn 4
  have hfour : (LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 4).Equiv
      (ofQComplex QComplex.one) := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    change ((LocalODE.power (ofQComplex RotationSeries.imaginaryUnit) 4).compute 0).Overlaps
      ((ofQComplex QComplex.one).compute 0)
    decide +kernel
  have hs : (entireExponentialValue nomeSlope).val.Equiv (ofQComplex QComplex.one) :=
    equiv_trans (entireExponentialValue nomeSlope).property
      (LocalODE.power_valid _ (entireExponentialValue h).property 4) (ofQComplex_valid _) hexp
      (equiv_trans (LocalODE.power_valid _ (entireExponentialValue h).property 4)
        (LocalODE.power_valid _ (ofQComplex_valid _) 4) (ofQComplex_valid _) hphase hfour)
  have hm := mul_equiv (entireExponentialValue a).property (entireExponentialValue a).property
    (entireExponentialValue nomeSlope).property (ofQComplex_valid _)
    (equiv_refl _ (entireExponentialValue a).property) hs
  exact equiv_trans (entireNomeMap.eval (integerShiftScalar z 1) (entireNomeMap_mem _)).property
    (entireExponentialValue b).property (entireExponentialValue a).property
    (entireExponentialValue_congr _ _ ha)
    (equiv_trans (entireExponentialValue b).property
      (mul_valid (entireExponentialValue a).property (entireExponentialValue nomeSlope).property)
      (entireExponentialValue a).property (equiv_symm (entireExponential_addition a nomeSlope))
      (equiv_trans (mul_valid (entireExponentialValue a).property (entireExponentialValue nomeSlope).property)
        (mul_valid (entireExponentialValue a).property (ofQComplex_valid _))
        (entireExponentialValue a).property hm (mul_one_equiv _ (entireExponentialValue a).property)))

def entireNomeClass (z : Scalar) : ScalarAlgebra.Value :=
  gridScalarValue (entireNomeMap.eval z (entireNomeMap_mem z))

theorem entireNomeClass_congr (z w : Scalar) (he : z.val.Equiv w.val) :
    entireNomeClass z=entireNomeClass w :=
  ComplexRawQuotient.ofRaw_eq_ofRaw (entireNomeMap.eval_congr z w _ _ he)

theorem entireNomeClass_period_nat (z : Scalar) (n : Nat) :
    entireNomeClass (integerShiftScalar z (n:Int))=entireNomeClass z := by
  induction n with
  | zero => exact entireNomeClass_congr _ _ (integerShiftScalar_zero_equiv z)
  | succ n ih =>
    have hc := entireNomeClass_congr _ _ (integerShiftScalar_composition z (n:Int) 1)
    have hp := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (entireNomeMap.eval (integerShiftScalar (integerShiftScalar z (n:Int)) 1) (entireNomeMap_mem _)).property)
      (hright := (entireNomeMap.eval (integerShiftScalar z (n:Int)) (entireNomeMap_mem _)).property)
      (entireNomeMap_period_one (integerShiftScalar z (n:Int)))
    change entireNomeClass (integerShiftScalar (integerShiftScalar z (n:Int)) 1)=
      entireNomeClass (integerShiftScalar z (n:Int)) at hp
    rw [show ((n+1:Nat):Int)=(n:Int)+1 by omega]
    exact hc.symm.trans (hp.trans ih)

theorem entireNomeClass_period_int (z : Scalar) (k : Int) :
    entireNomeClass (integerShiftScalar z k)=entireNomeClass z := by
  cases k with
  | ofNat n => exact entireNomeClass_period_nat z n
  | negSucc n =>
    let w := integerShiftScalar z (Int.negSucc n)
    have hp := entireNomeClass_period_nat w (n+1)
    have hc := entireNomeClass_congr (integerShiftScalar w ((n+1:Nat):Int)) (integerShiftScalar z 0) (by
      have h := integerShiftScalar_composition z (Int.negSucc n) ((n+1:Nat):Int)
      simpa only [show Int.negSucc n+((n+1:Nat):Int)=0 by omega] using h)
    have h0 := entireNomeClass_congr _ z (integerShiftScalar_zero_equiv z)
    exact hp.symm.trans (hc.trans h0)

theorem entireNomeMap_period_int (z : Scalar) (k : Int) :
    (entireNomeMap.eval (integerShiftScalar z k) (entireNomeMap_mem _)).val.Equiv
      (entireNomeMap.eval z (entireNomeMap_mem z)).val :=
  ComplexRawQuotient.equiv_of_ofRaw_eq (entireNomeClass_period_int z k)

theorem entireNomeCotangent_shift_mem (z : Scalar) (hz : entireNomeCotangentMap.domain z) (k : Int) :
    entireNomeCotangentMap.domain (integerShiftScalar z k) :=
  ⟨entireNomeMap_mem _,(cotangentRationalMap.domain_congr _ _ (entireNomeMap_period_int z k)).mpr
    (compose_outer_mem hz)⟩

theorem entireNomeCotangent_period_int (z : Scalar) (hz : entireNomeCotangentMap.domain z) (k : Int) :
    (entireNomeCotangentMap.eval (integerShiftScalar z k) (entireNomeCotangent_shift_mem z hz k)).val.Equiv
      (entireNomeCotangentMap.eval z hz).val :=
  cotangentRationalMap.eval_congr _ _ _ _ (entireNomeMap_period_int z k)

theorem entireNormalizedNomeCotangent_shift_mem (z : Scalar)
    (hz : entireNormalizedNomeCotangentMap.domain z) (k : Int) :
    entireNormalizedNomeCotangentMap.domain (integerShiftScalar z k) :=
  ⟨entireNomeCotangent_shift_mem z (compose_inner_mem hz) k,trivial⟩

theorem entireNormalizedNomeCotangent_period_int (z : Scalar)
    (hz : entireNormalizedNomeCotangentMap.domain z) (k : Int) :
    (entireNormalizedNomeCotangentMap.eval (integerShiftScalar z k)
      (entireNormalizedNomeCotangent_shift_mem z hz k)).val.Equiv
      (entireNormalizedNomeCotangentMap.eval z hz).val :=
  (affine ⟨zero,ofQComplex_valid _⟩ nomeCotangentScale).eval_congr _ _ trivial trivial
    (entireNomeCotangent_period_int z (compose_inner_mem hz) k)

theorem entireNormalizedNomeCotangent_halfInteger_zero (k : Int) :
    (entireNormalizedNomeCotangentMap.eval (integerShiftScalar latticeHalfPoint k)
      (entireNormalizedNomeCotangent_shift_mem latticeHalfPoint
        entireNormalizedNomeCotangent_halfPeriod_mem k)).val.Equiv zero :=
  equiv_trans (entireNormalizedNomeCotangentMap.eval (integerShiftScalar latticeHalfPoint k)
      (entireNormalizedNomeCotangent_shift_mem latticeHalfPoint
        entireNormalizedNomeCotangent_halfPeriod_mem k)).property
    (entireNormalizedNomeCotangentMap.eval latticeHalfPoint entireNormalizedNomeCotangent_halfPeriod_mem).property
    (ofQComplex_valid _)
    (entireNormalizedNomeCotangent_period_int latticeHalfPoint entireNormalizedNomeCotangent_halfPeriod_mem k)
    entireNormalizedNomeCotangent_halfPeriod_zero

end ComputableAnalysis.ModularForms
