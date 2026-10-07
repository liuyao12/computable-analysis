import ComputableAnalysis.ModularForms.NomeLocalInverseIntegerPeriods
import ComputableAnalysis.ModularForms.NomeIntegerReduction
import ComputableAnalysis.ModularForms.ExponentialKernelFourStrip
import ComputableAnalysis.ModularForms.EntireNomeIntegerPeriodicity
import ComputableAnalysis.ModularForms.NomeLocalInverse

/-! Classification of the entire nome kernel by an executable integer
selection, actual periodicity and proved fixed-strip kernel triviality. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

/-- The entire nome is the actual exponential of the actual slope product. -/
theorem entireNomeMap_exponent (z : Scalar) :
    (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv
      (entireExponentialValue (scalarProduct nomeSlope z)).val :=
  entireExponentialValue_congr _ _ (zero_add_equiv _ (mul_valid nomeSlope.property z.property))

private theorem remainder_shift (z : Scalar) :
    (nomeIntegerRemainder z).val.Equiv (integerShiftScalar z (-nomeReductionInteger z)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (nomeIntegerRemainder z).property)
    (hright := (integerShiftScalar z (-nomeReductionInteger z)).property)
  change gridScalarValue (nomeIntegerRemainder z)=
    ComplexRawQuotient.ofRaw (integerAffine 1 (-nomeReductionInteger z) z.val) (integerAffine_valid _ _ z.property)
  rw [integerAffine_class]
  have h1 : ((1:Int):ScalarAlgebra.Value)=(1:ScalarAlgebra.Value) := by
    change ComplexRawQuotient.scaleRat 1 1=1
    exact ComplexRawQuotient.scaleRat_one _
  rw [h1]
  have hi := integer_constant (nomeReductionInteger z)
  have hneg := integer_constant (-nomeReductionInteger z)
  let Z := gridScalarValue z
  let C := ComplexRawQuotient.ofQComplex ⟨(nomeReductionInteger z:Rat),0⟩
  change Z-C=(1:ScalarAlgebra.Value)*Z+((-nomeReductionInteger z:Int):ScalarAlgebra.Value)
  rw [← hneg]
  have hn : ComplexRawQuotient.ofQComplex ⟨((-nomeReductionInteger z:Int):Rat),0⟩= -C := by
    change ComplexRawQuotient.ofRaw (ofQComplex ⟨((-nomeReductionInteger z:Int):Rat),0⟩) _=
      ComplexRawQuotient.ofRaw (neg (ofQComplex ⟨(nomeReductionInteger z:Rat),0⟩)) _
    apply ComplexRawQuotient.ofRaw_eq_ofRaw
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    simp [ofQComplex,neg,QBox.neg,QComplex.neg,QBox.Overlaps,QComplex.le_def,Rat.intCast_neg]
  rw [hn]
  grind only

/-- Every actual entire-nome kernel input is the integer selected by the
constructed rational midpoint algorithm. No completion or branch choice
classification is supplied as a hypothesis. -/
theorem entireNome_kernel_selected_integer (z : Scalar)
    (he : (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv one) :
    z.val.Equiv (ofQComplex ⟨(nomeReductionInteger z:Rat),0⟩) := by
  let d := nomeIntegerRemainder z
  have hperiod : (entireNomeMap.eval d (entireNomeMap_mem d)).val.Equiv one :=
    equiv_trans (entireNomeMap.eval d (entireNomeMap_mem d)).property
      (entireNomeMap.eval (integerShiftScalar z (-nomeReductionInteger z)) (entireNomeMap_mem _)).property
      (ofQComplex_valid _)
      (entireNomeMap.eval_congr d _ _ _ (remainder_shift z))
      (equiv_trans
        (entireNomeMap.eval (integerShiftScalar z (-nomeReductionInteger z)) (entireNomeMap_mem _)).property
        (entireNomeMap.eval z (entireNomeMap_mem z)).property (ofQComplex_valid _)
        (entireNomeMap_period_int z (-nomeReductionInteger z)) he)
  have hexp : (entireExponentialValue (scalarProduct nomeSlope d)).val.Equiv one :=
    equiv_trans (entireExponentialValue (scalarProduct nomeSlope d)).property
      (entireNomeMap.eval d (entireNomeMap_mem d)).property (ofQComplex_valid _)
      (equiv_symm (entireNomeMap_exponent d)) hperiod
  have hb := nomeIntegerRemainder_exponent_bounds z
  have hz := entireExponential_kernel_four_strip (scalarProduct nomeSlope d) hb.1 hb.2 hexp
  let o : Scalar := ⟨zero,ofQComplex_valid _⟩
  have hd : d.val.Equiv zero := RepresentedReciprocal.mul_cancel nomeSlope nomeSlope_nonzero d o
    (equiv_trans (scalarProduct nomeSlope d).property (ofQComplex_valid _)
      (mul_valid nomeSlope.property o.property) hz (equiv_symm (mul_zero_equiv _ nomeSlope.property)))
  have hD := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := d.property) (hright := ofQComplex_valid _) hd
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := ofQComplex_valid _)
  let Z := gridScalarValue z
  let C := ComplexRawQuotient.ofQComplex ⟨(nomeReductionInteger z:Rat),0⟩
  change Z-C=0 at hD
  change Z=C
  grind only

/-- Exact classification of all actual entire-nome kernel inputs. -/
theorem entireNome_kernel_exists_integer (z : Scalar)
    (he : (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv one) :
    ∃ n : Int, z.val.Equiv (ofQComplex ⟨(n:Rat),0⟩) :=
  ⟨nomeReductionInteger z,entireNome_kernel_selected_integer z he⟩


/-- Equal entire nome values make the actual input difference a kernel input. -/
theorem entireNome_fiber_difference_kernel (z w : Scalar)
    (he : (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv
      (entireNomeMap.eval w (entireNomeMap_mem w)).val) :
    (entireNomeMap.eval ⟨sub z.val w.val,sub_valid z.property w.property⟩ (entireNomeMap_mem _)).val.Equiv one := by
  let A := scalarProduct nomeSlope z
  let B := scalarProduct nomeSlope w
  let D : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  let E : Scalar := ⟨sub A.val B.val,sub_valid A.property B.property⟩
  have hAB : (entireExponentialValue A).val.Equiv (entireExponentialValue B).val :=
    equiv_trans (entireExponentialValue A).property
      (entireNomeMap.eval z (entireNomeMap_mem z)).property (entireExponentialValue B).property
      (equiv_symm (entireNomeMap_exponent z))
      (equiv_trans (entireNomeMap.eval z (entireNomeMap_mem z)).property
        (entireNomeMap.eval w (entireNomeMap_mem w)).property (entireExponentialValue B).property
        he (entireNomeMap_exponent w))
  have hDE : (scalarProduct nomeSlope D).val.Equiv E.val := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scalarProduct nomeSlope D).property) (hright := E.property)
    let S := gridScalarValue nomeSlope
    let Z := gridScalarValue z
    let W := gridScalarValue w
    change S*(Z-W)=S*Z-S*W
    grind only
  exact equiv_trans (entireNomeMap.eval D (entireNomeMap_mem D)).property
    (entireExponentialValue (scalarProduct nomeSlope D)).property (ofQComplex_valid _)
    (entireNomeMap_exponent D)
    (equiv_trans (entireExponentialValue (scalarProduct nomeSlope D)).property
      (entireExponentialValue E).property (ofQComplex_valid _)
      (entireExponentialValue_congr _ _ hDE) (entireExponential_fiber_difference A B hAB))

/-- Every pair of equal-nome inputs differs by an integer, with the integer
constructed internally from their represented difference. -/
theorem entireNome_fiber_exists_integer (z w : Scalar)
    (he : (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv
      (entireNomeMap.eval w (entireNomeMap_mem w)).val) :
    ∃ n : Int, z.val.Equiv (translate (n:Rat) w.val) := by
  let D : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  let n := nomeReductionInteger D
  have hd := entireNome_kernel_selected_integer D (entireNome_fiber_difference_kernel z w he)
  have hD := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := D.property) (hright := ofQComplex_valid _) hd
  refine ⟨n,?_⟩
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := z.property) (hright := translate_valid (n:Rat) w.property)
  let Z := gridScalarValue z
  let W := gridScalarValue w
  let C := ComplexRawQuotient.ofQComplex ⟨(n:Rat),0⟩
  change Z-W=C at hD
  change Z=W+C
  grind only

/-- Exact integer-period classification for the actual upper-half-plane
nome, on arbitrary valid represented inputs. -/
theorem nome_fiber_exists_integer_translation (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val)
    (he : (nome.eval z hz).val.Equiv (nome.eval w hw).val) :
    ∃ n : Int, z.val.Equiv (fractionalLinear (SL2Z.translation n) w hw).val := by
  have hE : (entireNomeMap.eval z (entireNomeMap_mem z)).val.Equiv
      (entireNomeMap.eval w (entireNomeMap_mem w)).val :=
    equiv_trans (entireNomeMap.eval z (entireNomeMap_mem z)).property
      (nome.eval z hz).property (entireNomeMap.eval w (entireNomeMap_mem w)).property
      (entireNomeMap_upper_agreement z hz)
      (equiv_trans (nome.eval z hz).property (nome.eval w hw).property
        (entireNomeMap.eval w (entireNomeMap_mem w)).property he
        (equiv_symm (entireNomeMap_upper_agreement w hw)))
  obtain ⟨n,hn⟩ := entireNome_fiber_exists_integer z w hE
  exact ⟨n,equiv_trans z.property (translate_valid (n:Rat) w.property)
    (fractionalLinear (SL2Z.translation n) w hw).property hn
    (equiv_symm (fractionalLinear_translation n w hw))⟩

end ComputableAnalysis.ModularForms
