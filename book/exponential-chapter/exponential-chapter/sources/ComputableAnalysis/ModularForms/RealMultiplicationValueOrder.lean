import ComputableAnalysis.ModularForms.RealPowerUpperBound

/-! Exact multiplication order from represented value bounds, with justified clipping beneath the theorem. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

/-- A nonnegative represented value does not decrease when multiplied by a represented value at least one. -/
theorem real_mul_ge_self_of_one_le (x y : RealRaw) (hx : x.Valid) (hy : y.Valid)
    (h0 : (RealRaw.ofRat 0).Le x) (h1 : (RealRaw.ofRat 1).Le y) : x.Le (RealRaw.mul x y) := by
  let a := RealRaw.lowerClip x 0
  let b := RealRaw.lowerClip y 1
  have ha : a.Valid := RealRaw.lowerClip_valid x 0 hx (fun n => h0 0 n)
  have hb : b.Valid := RealRaw.lowerClip_valid y 1 hy (fun n => h1 0 n)
  have hea : a.Equiv x := lowerClip_equiv x hx 0 h0
  have heb : b.Equiv y := lowerClip_equiv y hy 1 h1
  have hal (n : Nat) : 0≤(a.compute n).lo := by
    change 0≤maxRat2 (x.compute n).lo 0
    unfold maxRat2; split <;> grind only
  have hbl (n : Nat) : 1≤(b.compute n).lo := by
    change 1≤maxRat2 (y.compute n).lo 1
    unfold maxRat2; split <;> grind only
  have horder : a.Le (RealRaw.mul a b) := by
    intro i j
    have hao := RealRaw.interval_order_of_valid _ ha j
    have hbo := RealRaw.interval_order_of_valid _ hb j
    have hb0 : 0≤(b.compute j).lo := by have h := hbl j; grind only
    have hm := QBox.mulRealInterval_of_nonneg (hal j) hao hb0 hbo
    have har := RealRaw.le_refl a ha i j
    have hbhi := Rat.le_trans (hbl j) hbo
    have hah : 0≤(a.compute j).hi := Rat.le_trans (hal j) hao
    have hp := Rat.mul_le_mul_of_nonneg_left hbhi hah
    change (a.compute i).lo≤(QBox.mulRealInterval (a.compute j).lo (a.compute j).hi
      (b.compute j).lo (b.compute j).hi).hi
    rw [hm]
    grind only
  have heprod := RealRaw.mul_equiv ha hx hb hy hea heb
  exact RealRaw.le_trans ha (RealRaw.le_of_equiv hx ha (RealRaw.equiv_symm hea))
    (RealRaw.le_trans (RealRaw.mul_valid ha hb) horder
      (RealRaw.le_of_equiv (RealRaw.mul_valid ha hb) (RealRaw.mul_valid hx hy) heprod))

end ComputableAnalysis.ModularForms
