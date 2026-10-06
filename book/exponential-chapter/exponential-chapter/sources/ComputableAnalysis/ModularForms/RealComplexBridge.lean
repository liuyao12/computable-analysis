import ComputableAnalysis.ModularForms.ImaginaryIdentity

/-! Real-coordinate bridges for positive-real division of complex values. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- A complex value with zero imaginary part agrees with its real embedding. -/
theorem equiv_real_embedding (z : Scalar)
    (hi : z.val.imagPart.Equiv (RealRaw.ofRat 0)) :
    z.val.Equiv (ofRealRaw z.val.realPart) := by
  intro k
  have hh := (RealRaw.compareAt_overlap_iff _ _ k k).mp (hi k)
  have ho := valid_ordered z.property k
  apply (compareAt_overlap_iff _ _ k k).mpr
  exact ⟨⟨ho.1, hh.1⟩, ⟨ho.1, hh.2⟩⟩

/-- Complex embedding respects real multiplication. -/
theorem real_embedding_mul (x y : RealRaw) (hx : x.Valid) (hy : y.Valid) :
    (mul (ofRealRaw x) (ofRealRaw y)).Equiv (ofRealRaw (RealRaw.mul x y)) := by
  intro k
  have ho := RealRaw.mul_valid hx hy
  apply (compareAt_overlap_iff _ _ k k).mpr
  simp only [mul, ofRealRaw, RealRaw.mul, RealRaw.mulCompute, QBox.mul,
    QBox.mulRealInterval_zero_left]
  have hz : QBox.mulRealInterval (x.compute k).lo (x.compute k).hi 0 0 =
      {lo := 0, hi := 0} := by
    simp [QBox.mulRealInterval, min4, max4, minRat, maxRat2, Rat.mul_zero]
  rw [hz]
  have hl : (QBox.mulRealInterval (x.compute k).lo (x.compute k).hi
    (y.compute k).lo (y.compute k).hi).lo ≤
    (QBox.mulRealInterval (x.compute k).lo (x.compute k).hi
    (y.compute k).lo (y.compute k).hi).hi := RealRaw.interval_order_of_valid _ ho k
  constructor <;> constructor <;> simp [Rat.sub_eq_add_neg, Rat.add_zero, hl]

/-- Multiplying by a strictly positive real value preserves positive imaginary part. -/
theorem mul_real_imag_positive (z : Scalar) (x : RealRaw) (hx : x.Valid)
    (hz : z.val.imagPart.Pos) (hp : x.Pos) :
    (mul z.val (ofRealRaw x)).imagPart.Pos := by
  obtain ⟨N,hN⟩ := hz
  obtain ⟨K,hK⟩ := hp
  let M := max N K
  have hzn := (imagPart_valid z.property).2.1 N M (Nat.le_max_left _ _)
  have hxn := hx.2.1 K M (Nat.le_max_right _ _)
  have hzp : 0 < (z.val.compute M).lo.im := by
    have hl := hzn.1
    change (z.val.compute N).lo.im ≤ (z.val.compute M).lo.im at hl
    change 0 < (z.val.compute N).lo.im at hN
    grind only
  have hxp : 0 < (x.compute M).lo := by grind only
  have hzo := (valid_ordered z.property M).2
  have hxo := RealRaw.interval_order_of_valid _ hx M
  have he := QBox.mulRealInterval_of_nonneg (Rat.le_of_lt hzp) hzo (Rat.le_of_lt hxp) hxo
  refine ⟨M, ?_⟩
  change 0 < ((QBox.mul (z.val.compute M)
    {lo := ⟨(x.compute M).lo,0⟩,hi := ⟨(x.compute M).hi,0⟩}).lo.im)
  simp only [QBox.mul, he]
  have hz0 : QBox.mulRealInterval (z.val.compute M).lo.re (z.val.compute M).hi.re 0 0 =
    {lo := 0, hi := 0} := by
    simp [QBox.mulRealInterval, min4, max4, minRat, maxRat2, Rat.mul_zero]
  rw [hz0]
  simp only [Rat.zero_add]
  exact Rat.mul_pos hzp hxp

end ComputableAnalysis.ModularForms
