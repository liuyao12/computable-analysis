import ComputableAnalysis.ModularForms.UpperBasisFiniteComparison
import ComputableAnalysis.ModularForms.LatticeBasisLimitComparison163
import ComputableAnalysis.ModularForms.UpperSquarePrefixAgreement

/-! Quantitative convergence of actual reindexed square prefixes to the general upper-half-plane sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

private theorem small_triangle (F p q : ComplexRaw) (hF : F.Valid) (hp : p.Valid) (hq : q.Valid)
    (a b : Rat) (h1 : Small (ComplexRaw.sub F p) a) (h2 : Small (ComplexRaw.sub p q) b) :
    Small (ComplexRaw.sub F q) (a+b) := by
  have he : (ComplexRaw.add (ComplexRaw.sub F p) (ComplexRaw.sub p q)).Equiv
      (ComplexRaw.sub F q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.add_valid (ComplexRaw.sub_valid hF hp) (ComplexRaw.sub_valid hp hq))
      (hright := ComplexRaw.sub_valid hF hq)
    change (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp)+
      (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq
    grind
  exact Small.congr
    (ComplexRaw.add_valid (ComplexRaw.sub_valid hF hp) (ComplexRaw.sub_valid hp hq))
    (ComplexRaw.sub_valid hF hq) he (LocalODE.small_add h1 h2)


private theorem basisPrefixIndex_spec (g : SL2Z) (n : Nat) :
    basisPrefixIndex g n+1=basisComparisonFactor g*(n+1) ∧ n≤basisPrefixIndex g n := by
  have hp : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
  have hm := Nat.mul_le_mul_right (n+1) hp
  unfold basisPrefixIndex
  omega

private theorem shrinks_basis_index (g : SL2Z) (e : Nat → Rat) (he : ShrinksToZero e) :
    ShrinksToZero (fun n => e (basisPrefixIndex g n)) := by
  intro eps
  obtain ⟨N,hN⟩ := he eps
  exact ⟨N,fun n hn => hN _ (Nat.le_trans hn (basisPrefixIndex_spec g n).2)⟩

def upperBasisReindexedPrefix (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (w n : Nat) : ComplexRaw :=
  LocalODE.sum (((squarePoints (basisComparisonFactor g*(n+1))).map (basisIndex g)).map (upperPointPower z hz w))

theorem upperBasisReindexedPrefix_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (w n : Nat) : (upperBasisReindexedPrefix z hz g w n).Valid := by
  apply LocalODE.sum_valid
  intro zz hzz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
  exact upperPointPower_valid z hz w u

def upperBasisWeightFourError (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (n : Nat) : Rat :=
  upperWeightFourTailRate z hz (basisPrefixIndex g n)+(upperWeightFourTailRate z hz n+upperWeightFourTailRate z hz n)

theorem upperBasisWeightFourError_shrinks (z : Scalar) (hz : InUpperHalfPlane z.val)
    (g : SL2Z) : ShrinksToZero (upperBasisWeightFourError z hz g) :=
  RepresentedCauchySum.sum_shrinks _ _
    (shrinks_basis_index g _ (upperWeightFourTailRate_shrinks z hz))
    (RepresentedCauchySum.sum_shrinks _ _
      (upperWeightFourTailRate_shrinks z hz) (upperWeightFourTailRate_shrinks z hz))

theorem upperWeightFourLatticeSum_close_reindexed (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub (upperWeightFourLatticeSum z hz) (upperBasisReindexedPrefix z hz g 4 n))
      (upperBasisWeightFourError z hz g n) := by
  let p := LocalODE.sum ((squarePoints (basisComparisonFactor g*(n+1))).map (upperPointPower z hz 4))
  have hp : p.Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
    exact upperPointPower_valid z hz 4 u
  have he := upperSquareWeightFour_prefix_equiv z hz (basisPrefixIndex g n)
  rw [(basisPrefixIndex_spec g n).1] at he
  have hc := Small.congr
    (ComplexRaw.sub_valid (upperWeightFourLatticeSum_valid z hz) (upperWeightFourPrefix_valid z hz _))
    (ComplexRaw.sub_valid (upperWeightFourLatticeSum_valid z hz) hp)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ (upperWeightFourLatticeSum_valid z hz))
      (ComplexRaw.equiv_symm he)) (upperWeightFourLatticeSum_close_prefix z hz (basisPrefixIndex g n))
  exact small_triangle _ p _ (upperWeightFourLatticeSum_valid z hz) hp
    (upperBasisReindexedPrefix_valid z hz g 4 n) _ _ hc (upperBasisWeightFour_finite_comparison z hz g (n+1) (by omega))

def upperBasisWeightSixError (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (n : Nat) : Rat :=
  upperWeightSixTailRate z hz (basisPrefixIndex g n)+(upperWeightSixTailRate z hz n+upperWeightSixTailRate z hz n)

theorem upperBasisWeightSixError_shrinks (z : Scalar) (hz : InUpperHalfPlane z.val)
    (g : SL2Z) : ShrinksToZero (upperBasisWeightSixError z hz g) :=
  RepresentedCauchySum.sum_shrinks _ _
    (shrinks_basis_index g _ (upperWeightSixTailRate_shrinks z hz))
    (RepresentedCauchySum.sum_shrinks _ _
      (upperWeightSixTailRate_shrinks z hz) (upperWeightSixTailRate_shrinks z hz))

theorem upperWeightSixLatticeSum_close_reindexed (z : Scalar) (hz : InUpperHalfPlane z.val) (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub (upperWeightSixLatticeSum z hz) (upperBasisReindexedPrefix z hz g 6 n))
      (upperBasisWeightSixError z hz g n) := by
  let p := LocalODE.sum ((squarePoints (basisComparisonFactor g*(n+1))).map (upperPointPower z hz 6))
  have hp : p.Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
    exact upperPointPower_valid z hz 6 u
  have he := upperSquareWeightSix_prefix_equiv z hz (basisPrefixIndex g n)
  rw [(basisPrefixIndex_spec g n).1] at he
  have hc := Small.congr
    (ComplexRaw.sub_valid (upperWeightSixLatticeSum_valid z hz) (upperWeightSixPrefix_valid z hz _))
    (ComplexRaw.sub_valid (upperWeightSixLatticeSum_valid z hz) hp)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ (upperWeightSixLatticeSum_valid z hz))
      (ComplexRaw.equiv_symm he)) (upperWeightSixLatticeSum_close_prefix z hz (basisPrefixIndex g n))
  exact small_triangle _ p _ (upperWeightSixLatticeSum_valid z hz) hp
    (upperBasisReindexedPrefix_valid z hz g 6 n) _ _ hc (upperBasisWeightSix_finite_comparison z hz g (n+1) (by omega))

end ComputableAnalysis.ModularForms
