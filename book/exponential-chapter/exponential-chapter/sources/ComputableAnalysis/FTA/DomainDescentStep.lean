import ComputableAnalysis.FTA.NormDescent
import ComputableAnalysis.FTA.DescentDomain

namespace ComputableAnalysis.PolynomialDescentDomain

def combinedStep (delta C A T : Rat) (radius : QPos) (direction : QComplex) : Rat :=
  let descent := PolynomialNormDescent.step delta C A T
  let domain := safeStep radius direction
  if descent ≤ domain then descent else domain

theorem combinedStep_spec (delta C A T : Rat) (hd : 0 < delta)
    (radius : QPos) (direction : QComplex) :
    0 < combinedStep delta C A T radius direction ∧
      combinedStep delta C A T radius direction ≤ PolynomialNormDescent.step delta C A T ∧
      QComplex.normBound (QComplex.scaleRat (combinedStep delta C A T radius direction) direction) ≤ radius.val := by
  have hbase := PolynomialDescent.step_spec (-2*delta) [2*C*T+(A+T)^2] (by grind)
  have hpos : 0 < PolynomialNormDescent.step delta C A T := hbase.1
  have hs := safeStep_spec radius direction
  unfold combinedStep
  dsimp only
  split
  · refine ⟨hpos, Rat.le_refl, ?_⟩
    have hm := Rat.mul_le_mul_of_nonneg_right ‹PolynomialNormDescent.step delta C A T ≤ safeStep radius direction›
      (QComplex.normBound_nonneg direction)
    rw [QComplex.normBound_scaleRat, qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)]
    rw [QComplex.normBound_scaleRat, qabs_eq_self_of_nonneg (Rat.le_of_lt hs.1)] at hs
    exact Rat.le_trans hm hs.2.2
  · exact ⟨hs.1, by grind, hs.2.2⟩

/-- A single computed step both retains the domain and gives the quantitative
local norm decrease. The supplied coordinate margins are genuine hypotheses. -/
theorem combinedStep_retains_and_decreases (box : QBox) (x d c a tail : QComplex)
    (delta C A T : Rat) (order : Nat) (radius : QPos)
    (hd : 0 < delta) (hC : 0 ≤ C) (hA : 0 ≤ A) (hT : 0 ≤ T) (ho : 0 < order)
    (hc : QComplex.normBound c ≤ C) (ha : QComplex.normBound a ≤ A)
    (ht : QComplex.normBound tail ≤ T)
    (hinward : (QComplex.mul (QComplex.conj c) a).re ≤ -delta)
    (hlre : box.lo.re + radius.val ≤ x.re) (hhre : x.re + radius.val ≤ box.hi.re)
    (hlim : box.lo.im + radius.val ≤ x.im) (hhim : x.im + radius.val ≤ box.hi.im) :
    let t := combinedStep delta C A T radius d
    (box.lo ≤ QComplex.add x (QComplex.scaleRat t d) ∧
      QComplex.add x (QComplex.scaleRat t d) ≤ box.hi) ∧
    QComplex.normSq (QComplex.add c (QComplex.scaleRat (t^order)
      (QComplex.add a (QComplex.scaleRat t tail)))) ≤ QComplex.normSq c - t^order*delta := by
  have hs := combinedStep_spec delta C A T hd radius d
  have hn := PolynomialNormDescent.decrease_at_smaller_step c a tail delta C A T
    (combinedStep delta C A T radius d) order hd hC hA hT ho hc ha ht hinward hs.1 hs.2.1
  exact ⟨displacement_in_box box x _ radius.val hlre hhre hlim hhim hs.2.2, hn.2⟩

end ComputableAnalysis.PolynomialDescentDomain
