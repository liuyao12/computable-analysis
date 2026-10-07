import ComputableAnalysis.ModularForms.LatticeBasisLimitComparison163

/-! Monotone quantitative Cauchy bounds for the actual reindexed prefixes. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

theorem reciprocalSquare_antitone (k n : Nat) (hk : 0<k) (hkn : k≤n) :
    reciprocalSquare n≤reciprocalSquare k := by
  let a : Rat := k
  let b : Rat := n
  have ha : 0<a := by dsimp [a]; exact_mod_cast hk
  have hb : 0<b := by dsimp [b]; exact_mod_cast (show 0<n by omega)
  have hab : a≤b := by dsimp [a,b]; exact_mod_cast hkn
  have h1 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_of_lt ha)
  have h2 := Rat.mul_le_mul_of_nonneg_right hab (Rat.le_of_lt hb)
  have hsq : a*a≤b*b := by grind
  have hca := Rat.mul_inv_cancel (a*a) (Rat.ne_of_gt (Rat.mul_pos ha ha))
  have hcb := Rat.mul_inv_cancel (b*b) (Rat.ne_of_gt (Rat.mul_pos hb hb))
  change (b*b)⁻¹≤(a*a)⁻¹
  apply Rat.le_of_mul_le_mul_right (c := (a*a)*(b*b))
  · calc
      _ = a*a := by grind
      _ ≤ b*b := hsq
      _ = _ := by grind
  · exact Rat.mul_pos (Rat.mul_pos ha ha) (Rat.mul_pos hb hb)

private theorem small_via (p F q : ComplexRaw) (hp : p.Valid) (hF : F.Valid) (hq : q.Valid)
    (a b : Rat) (h1 : Small (ComplexRaw.sub p F) a) (h2 : Small (ComplexRaw.sub F q) b) :
    Small (ComplexRaw.sub p q) (a+b) := by
  have he : (ComplexRaw.add (ComplexRaw.sub p F) (ComplexRaw.sub F q)).Equiv
      (ComplexRaw.sub p q) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.add_valid (ComplexRaw.sub_valid hp hF) (ComplexRaw.sub_valid hF hq))
      (hright := ComplexRaw.sub_valid hp hq)
    change (ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw F hF)+
      (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq)=
      ComplexRawQuotient.ofRaw p hp-ComplexRawQuotient.ofRaw q hq
    grind
  exact Small.congr
    (ComplexRaw.add_valid (ComplexRaw.sub_valid hp hF) (ComplexRaw.sub_valid hF hq))
    (ComplexRaw.sub_valid hp hq) he (LocalODE.small_add h1 h2)

theorem weightFourTailRate_antitone (k n : Nat) (hkn : k≤n) :
    weightFourTailRate n≤weightFourTailRate k :=
  Rat.mul_le_mul_of_nonneg_left (reciprocalSquare_antitone (k+1) (n+1) (by omega) (by omega))
    (by unfold weightFourTailConstant; decide +kernel)

theorem basisWeightFourError_le (g : SL2Z) (n : Nat) :
    basisWeightFourError g n≤3*weightFourTailRate n := by
  have hp : n≤basisPrefixIndex g n := by
    have h : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
    have hm := Nat.mul_le_mul_right (n+1) h
    unfold basisPrefixIndex
    omega
  have ht := weightFourTailRate_antitone n _ hp
  unfold basisWeightFourError
  grind

theorem basisWeightFourPrefix_cauchy (g : SL2Z) (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (basisReindexedPrefix g 4 n) (basisReindexedPrefix g 4 k))
      (6*weightFourTailRate k) := by
  have hn := (weightFourLatticeSum163_close_reindexed g n).mono (basisWeightFourError_le g n)
  have hk := (weightFourLatticeSum163_close_reindexed g k).mono (basisWeightFourError_le g k)
  have hs := small_via _ weightFourLatticeSum163 _ (basisReindexedPrefix_valid g 4 n)
    weightFourLatticeSum163_valid (basisReindexedPrefix_valid g 4 k) _ _
    (RepresentedCauchySum.small_sub_symm _ _ _ hn) hk
  apply hs.mono
  have ht := weightFourTailRate_antitone k n hkn
  grind

theorem weightSixTailRate_antitone (k n : Nat) (hkn : k≤n) :
    weightSixTailRate n≤weightSixTailRate k :=
  Rat.mul_le_mul_of_nonneg_left (reciprocalSquare_antitone (k+1) (n+1) (by omega) (by omega))
    (by unfold weightSixTailConstant; decide +kernel)

theorem basisWeightSixError_le (g : SL2Z) (n : Nat) :
    basisWeightSixError g n≤3*weightSixTailRate n := by
  have hp : n≤basisPrefixIndex g n := by
    have h : 1≤basisComparisonFactor g := by unfold basisComparisonFactor; omega
    have hm := Nat.mul_le_mul_right (n+1) h
    unfold basisPrefixIndex
    omega
  have ht := weightSixTailRate_antitone n _ hp
  unfold basisWeightSixError
  grind

theorem basisWeightSixPrefix_cauchy (g : SL2Z) (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (basisReindexedPrefix g 6 n) (basisReindexedPrefix g 6 k))
      (6*weightSixTailRate k) := by
  have hn := (weightSixLatticeSum163_close_reindexed g n).mono (basisWeightSixError_le g n)
  have hk := (weightSixLatticeSum163_close_reindexed g k).mono (basisWeightSixError_le g k)
  have hs := small_via _ weightSixLatticeSum163 _ (basisReindexedPrefix_valid g 6 n)
    weightSixLatticeSum163_valid (basisReindexedPrefix_valid g 6 k) _ _
    (RepresentedCauchySum.small_sub_symm _ _ _ hn) hk
  apply hs.mono
  have ht := weightSixTailRate_antitone k n hkn
  grind

end ComputableAnalysis.ModularForms
