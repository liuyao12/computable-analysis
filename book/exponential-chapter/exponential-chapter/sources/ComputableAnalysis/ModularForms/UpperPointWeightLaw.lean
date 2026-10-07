import ComputableAnalysis.ModularForms.UpperLatticePointTerms
import ComputableAnalysis.ModularForms.UpperLatticeAction
import ComputableAnalysis.ModularForms.RepresentedSumFactor
import ComputableAnalysis.ModularForms.UpperBasisLimitComparison

/-! Modular weight laws for the total point evaluator and finite point lists. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163 ComplexRaw

theorem upperPointPower_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (u : QuadraticOrder163) :
    (upperPointPower (fractionalLinear g z hz) (fractionalLinear_mem g z hz) k u).Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) k)
        (upperPointPower z hz k (basisIndex (latticeIndexMatrix g) u))) := by
  by_cases hu : u≠QuadraticOrder163.zero
  · simp only [upperPointPower,dif_pos hu,dif_pos (basisIndex_nonzero _ u hu)]
    exact latticeInverse_power_action g z hz u hu k
  · have he : u=QuadraticOrder163.zero := by
      by_cases he : u=QuadraticOrder163.zero
      · exact he
      · exact False.elim (hu he)
    subst u
    have hi : basisIndex (latticeIndexMatrix g) QuadraticOrder163.zero=QuadraticOrder163.zero := by
      simp [basisIndex,QuadraticOrder163.zero]
    simp only [hi,upperPointPower,dif_neg (show ¬QuadraticOrder163.zero≠QuadraticOrder163.zero from fun h => h rfl)]
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ofQComplex_valid _)
      (hright := mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) k)
        (ofQComplex_valid _))
    change (0:ScalarAlgebra.Value)=ComplexRawQuotient.ofRaw
      (LocalODE.power (integerAffine g.c g.d z.val) k)
      (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) k)*0
    exact (ComplexRawQuotient.mul_zero _).symm

theorem upperPointList_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (us : List QuadraticOrder163) :
    (LocalODE.sum (us.map (upperPointPower (fractionalLinear g z hz)
      (fractionalLinear_mem g z hz) k))).Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) k)
        (LocalODE.sum ((us.map (basisIndex (latticeIndexMatrix g))).map (upperPointPower z hz k)))) := by
  let c := LocalODE.power (integerAffine g.c g.d z.val) k
  have hc : c.Valid := LocalODE.power_valid _ (integerAffine_valid _ _ z.property) k
  let f := fun u => upperPointPower z hz k (basisIndex (latticeIndexMatrix g) u)
  have hf : ∀ u, (f u).Valid := fun u => upperPointPower_valid z hz k _
  have hv (F : QuadraticOrder163 → ComplexRaw) (hF : ∀ u, (F u).Valid) :
      (LocalODE.sum (us.map F)).Valid := by
    apply LocalODE.sum_valid
    intro t ht
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
    exact hF u
  rw [List.map_map]
  exact equiv_trans
    (hv _ (upperPointPower_valid _ _ k))
    (hv _ (fun u => mul_valid hc (hf u)))
    (mul_valid hc (hv f hf))
    (representedSum_map_equiv us _ _ (upperPointPower_action g z hz k))
    (representedSum_factor c hc f hf us)

private theorem basisPrefixIndex_add_one (g : SL2Z) (n : Nat) :
    basisPrefixIndex g n+1=basisComparisonFactor g*(n+1) := by
  have hp : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
  have hm := Nat.mul_le_mul_right (n+1) hp
  unfold basisPrefixIndex
  omega

theorem upperWeightFourPrefix_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) :
    (upperWeightFourPrefix (fractionalLinear g z hz) (fractionalLinear_mem g z hz)
      (basisPrefixIndex (latticeIndexMatrix g) n)).Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) 4)
        (upperBasisReindexedPrefix z hz (latticeIndexMatrix g) 4 n)) := by
  have he := upperSquareWeightFour_prefix_equiv (fractionalLinear g z hz)
    (fractionalLinear_mem g z hz) (basisPrefixIndex (latticeIndexMatrix g) n)
  rw [basisPrefixIndex_add_one] at he
  exact equiv_trans (upperWeightFourPrefix_valid _ _ _)
    (LocalODE.sum_valid _ (by
      intro t ht
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
      exact upperPointPower_valid _ _ 4 u))
    (mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 4)
      (upperBasisReindexedPrefix_valid z hz _ 4 n))
    (equiv_symm he) (upperPointList_action g z hz 4 _)

theorem upperWeightSixPrefix_action (g : SL2Z) (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Nat) :
    (upperWeightSixPrefix (fractionalLinear g z hz) (fractionalLinear_mem g z hz)
      (basisPrefixIndex (latticeIndexMatrix g) n)).Equiv
      (mul (LocalODE.power (integerAffine g.c g.d z.val) 6)
        (upperBasisReindexedPrefix z hz (latticeIndexMatrix g) 6 n)) := by
  have he := upperSquareWeightSix_prefix_equiv (fractionalLinear g z hz)
    (fractionalLinear_mem g z hz) (basisPrefixIndex (latticeIndexMatrix g) n)
  rw [basisPrefixIndex_add_one] at he
  exact equiv_trans (upperWeightSixPrefix_valid _ _ _)
    (LocalODE.sum_valid _ (by
      intro t ht
      obtain ⟨u,_,rfl⟩ := List.mem_map.mp ht
      exact upperPointPower_valid _ _ 6 u))
    (mul_valid (LocalODE.power_valid _ (integerAffine_valid _ _ z.property) 6)
      (upperBasisReindexedPrefix_valid z hz _ 6 n))
    (equiv_symm he) (upperPointList_action g z hz 6 _)

end ComputableAnalysis.ModularForms
