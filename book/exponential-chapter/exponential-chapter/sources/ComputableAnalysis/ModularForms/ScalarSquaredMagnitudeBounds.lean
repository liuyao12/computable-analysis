import ComputableAnalysis.ModularForms.SquaredMagnitudeCoordinateBound

namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Squared magnitude is nonnegative for every valid represented complex value. -/
theorem scalar_squared_magnitude_nonnegative (z : Scalar) :
    (RealRaw.ofRat 0).Le (mul z.val (conj z.val)).realPart := by
  intro n m
  let p := (z.val.compute m).center
  have hp := QBox.center_mem (valid_ordered z.property m)
  have hc := conjugate_contains z.val m p hp
  have hm := (QBox.mul_contains hp.1 hp.2 hc.1 hc.2).2.1
  have he : (QComplex.mul p (QComplex.conj p)).re = p.re*p.re+p.im*p.im := by
    simp only [QComplex.mul,QComplex.conj]
    grind only
  rw [he] at hm
  have hr : 0 ≤ p.re*p.re := by
    by_cases h : 0 ≤ p.re
    · exact Rat.mul_nonneg h h
    · have hn : 0 ≤ -p.re := by grind only
      have hs := Rat.mul_nonneg hn hn
      grind only
  have hi : 0 ≤ p.im*p.im := by
    by_cases h : 0 ≤ p.im
    · exact Rat.mul_nonneg h h
    · have hn : 0 ≤ -p.im := by grind only
      have hs := Rat.mul_nonneg hn hn
      grind only
  change (0:Rat) ≤ ((mul z.val (conj z.val)).compute m).hi.re
  exact Rat.le_trans (Rat.add_nonneg hr hi) hm

/-- Coordinate bounds give an upper bound for actual squared magnitude, even when boxes overshoot. -/
theorem scalar_squared_magnitude_upper (z : Scalar) (B : Rat) (hB : 0 ≤ B)
    (hz : Small z.val B) :
    (mul z.val (conj z.val)).realPart.Le (RealRaw.ofRat (2*B*B)) := by
  intro n m
  let K := z.val.compute n
  have ho := valid_ordered z.property n
  have hl := hz.1 0 n
  have hu := hz.2.1 n 0
  have il := hz.2.2.1 0 n
  have iu := hz.2.2.2 n 0
  change -B ≤ K.hi.re at hl
  change K.lo.re ≤ B at hu
  change -B ≤ K.hi.im at il
  change K.lo.im ≤ B at iu
  change K.lo.re ≤ K.hi.re ∧ K.lo.im ≤ K.hi.im at ho
  let p : QComplex := ⟨maxRat2 K.lo.re (-B),maxRat2 K.lo.im (-B)⟩
  have hp : K.lo ≤ p ∧ p ≤ K.hi := by
    dsimp [p,maxRat2]
    split <;> split <;> constructor <;> constructor <;> grind only
  have hr : -B ≤ p.re ∧ p.re ≤ B := by
    dsimp [p,maxRat2]
    split <;> constructor <;> grind only
  have hi : -B ≤ p.im ∧ p.im ≤ B := by
    dsimp [p,maxRat2]
    split <;> constructor <;> grind only
  have sr := Rat.mul_nonneg (show 0 ≤ B-p.re by grind only) (show 0 ≤ B+p.re by grind only)
  have si := Rat.mul_nonneg (show 0 ≤ B-p.im by grind only) (show 0 ≤ B+p.im by grind only)
  have hb : p.re*p.re+p.im*p.im ≤ 2*B*B := by grind only
  have hc := conjugate_contains z.val n p hp
  have hm := (QBox.mul_contains hp.1 hp.2 hc.1 hc.2).1.1
  have he : (QComplex.mul p (QComplex.conj p)).re = p.re*p.re+p.im*p.im := by
    simp only [QComplex.mul,QComplex.conj]
    grind only
  rw [he] at hm
  change ((mul z.val (conj z.val)).compute n).lo.re ≤ 2*B*B
  exact Rat.le_trans hm hb

end ComputableAnalysis.ModularForms
