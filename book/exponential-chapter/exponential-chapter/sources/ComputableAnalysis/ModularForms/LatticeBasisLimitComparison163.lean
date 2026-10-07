import ComputableAnalysis.ModularForms.LatticeBasisFiniteComparison163
import ComputableAnalysis.ModularForms.CMSquarePrefixAgreement163

/-! Quantitative convergence of actual reindexed square prefixes to the CM sums. -/
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

def basisPrefixIndex (g : SL2Z) (n : Nat) : Nat := basisComparisonFactor g*(n+1)-1

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

def basisReindexedPrefix (g : SL2Z) (w n : Nat) : ComplexRaw :=
  LocalODE.sum (((squarePoints (basisComparisonFactor g*(n+1))).map (basisIndex g)).map (pointPower w))

theorem basisReindexedPrefix_valid (g : SL2Z) (w n : Nat) : (basisReindexedPrefix g w n).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
  exact pointPower_valid w u

def basisWeightFourError (g : SL2Z) (n : Nat) : Rat :=
  weightFourTailRate (basisPrefixIndex g n)+(weightFourTailRate n+weightFourTailRate n)

theorem basisWeightFourError_shrinks (g : SL2Z) : ShrinksToZero (basisWeightFourError g) :=
  RepresentedCauchySum.sum_shrinks _ _ (shrinks_basis_index g _ weightFourTailRate_shrinks)
    (RepresentedCauchySum.sum_shrinks _ _ weightFourTailRate_shrinks weightFourTailRate_shrinks)

theorem weightFourLatticeSum163_close_reindexed (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub weightFourLatticeSum163 (basisReindexedPrefix g 4 n))
      (basisWeightFourError g n) := by
  let p := LocalODE.sum ((squarePoints (basisComparisonFactor g*(n+1))).map (pointPower 4))
  have hp : p.Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 4 u
  have he := squareWeightFour_prefix_equiv (basisPrefixIndex g n)
  rw [(basisPrefixIndex_spec g n).1] at he
  have hc := Small.congr
    (ComplexRaw.sub_valid weightFourLatticeSum163_valid (weightFourPrefix_valid _))
    (ComplexRaw.sub_valid weightFourLatticeSum163_valid hp)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ weightFourLatticeSum163_valid)
      (ComplexRaw.equiv_symm he)) (weightFourLatticeSum163_close_prefix (basisPrefixIndex g n))
  exact small_triangle _ p _ weightFourLatticeSum163_valid hp
    (basisReindexedPrefix_valid g 4 n) _ _ hc (basisWeightFour_finite_comparison g (n+1) (by omega))

def basisWeightSixError (g : SL2Z) (n : Nat) : Rat :=
  weightSixTailRate (basisPrefixIndex g n)+(weightSixTailRate n+weightSixTailRate n)

theorem basisWeightSixError_shrinks (g : SL2Z) : ShrinksToZero (basisWeightSixError g) :=
  RepresentedCauchySum.sum_shrinks _ _ (shrinks_basis_index g _ weightSixTailRate_shrinks)
    (RepresentedCauchySum.sum_shrinks _ _ weightSixTailRate_shrinks weightSixTailRate_shrinks)

theorem weightSixLatticeSum163_close_reindexed (g : SL2Z) (n : Nat) :
    Small (ComplexRaw.sub weightSixLatticeSum163 (basisReindexedPrefix g 6 n))
      (basisWeightSixError g n) := by
  let p := LocalODE.sum ((squarePoints (basisComparisonFactor g*(n+1))).map (pointPower 6))
  have hp : p.Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact pointPower_valid 6 u
  have he := squareWeightSix_prefix_equiv (basisPrefixIndex g n)
  rw [(basisPrefixIndex_spec g n).1] at he
  have hc := Small.congr
    (ComplexRaw.sub_valid weightSixLatticeSum163_valid (weightSixPrefix_valid _))
    (ComplexRaw.sub_valid weightSixLatticeSum163_valid hp)
    (FunctionTheory.sub_congr (ComplexRaw.equiv_refl _ weightSixLatticeSum163_valid)
      (ComplexRaw.equiv_symm he)) (weightSixLatticeSum163_close_prefix (basisPrefixIndex g n))
  exact small_triangle _ p _ weightSixLatticeSum163_valid hp
    (basisReindexedPrefix_valid g 6 n) _ _ hc (basisWeightSix_finite_comparison g (n+1) (by omega))

end ComputableAnalysis.ModularForms
