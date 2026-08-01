import ComputableAnalysis.Basic

/-!
# Finite interval multiplication for complex boxes

This module proves the order and containment facts for the literal four-corner
rational interval product used by `QBox.mul`.  It is deliberately only the
finite-box layer: turning a product of arbitrary `ComplexRaw` values into a
valid shrinking raw computation still needs its own width-modulus theorem.

No completed complex plane or imported real-analysis library is used here.
-/

namespace ComputableAnalysis

namespace QBox

private theorem minRat_le_left (a b : Rat) : minRat a b <= a := by
  unfold minRat
  split <;> grind

private theorem minRat_le_right (a b : Rat) : minRat a b <= b := by
  unfold minRat
  split <;> grind

private theorem le_minRat {x a b : Rat}
    (hxa : x <= a) (hxb : x <= b) : x <= minRat a b := by
  unfold minRat
  split <;> assumption

private theorem le_maxRat2_left (a b : Rat) : a <= maxRat2 a b := by
  unfold maxRat2
  split <;> grind

private theorem le_maxRat2_right (a b : Rat) : b <= maxRat2 a b := by
  unfold maxRat2
  split <;> grind

private theorem maxRat2_le {a b x : Rat}
    (hax : a <= x) (hbx : b <= x) : maxRat2 a b <= x := by
  unfold maxRat2
  split <;> assumption

private theorem min4_le_first (a b c d : Rat) : min4 a b c d <= a := by
  exact Rat.le_trans (minRat_le_left _ _) (minRat_le_left _ _)

private theorem min4_le_second (a b c d : Rat) : min4 a b c d <= b := by
  exact Rat.le_trans (minRat_le_left _ _) (minRat_le_right _ _)

private theorem min4_le_third (a b c d : Rat) : min4 a b c d <= c := by
  exact Rat.le_trans (minRat_le_right _ _) (minRat_le_left _ _)

private theorem min4_le_fourth (a b c d : Rat) : min4 a b c d <= d := by
  exact Rat.le_trans (minRat_le_right _ _) (minRat_le_right _ _)

private theorem first_le_max4 (a b c d : Rat) : a <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_left a b)
    (le_maxRat2_left (maxRat2 a b) (maxRat2 c d))

private theorem second_le_max4 (a b c d : Rat) : b <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_right a b)
    (le_maxRat2_left (maxRat2 a b) (maxRat2 c d))

private theorem third_le_max4 (a b c d : Rat) : c <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_left c d)
    (le_maxRat2_right (maxRat2 a b) (maxRat2 c d))

private theorem fourth_le_max4 (a b c d : Rat) : d <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_right c d)
    (le_maxRat2_right (maxRat2 a b) (maxRat2 c d))

private theorem le_min4 {x a b c d : Rat}
    (hxa : x <= a) (hxb : x <= b) (hxc : x <= c) (hxd : x <= d) :
    x <= min4 a b c d := by
  exact le_minRat (le_minRat hxa hxb) (le_minRat hxc hxd)

private theorem max4_le {a b c d x : Rat}
    (hax : a <= x) (hbx : b <= x) (hcx : c <= x) (hdx : d <= x) :
    max4 a b c d <= x := by
  exact maxRat2_le (maxRat2_le hax hbx) (maxRat2_le hcx hdx)

private theorem mul_le_mul_of_nonpos_left {a b c : Rat}
    (hab : a <= b) (hc : c <= 0) : c * b <= c * a := by
  have hnc : 0 <= -c := by grind
  have h := Rat.mul_le_mul_of_nonneg_left hab hnc
  grind [Rat.neg_mul]

private theorem mul_le_mul_of_nonpos_right {a b c : Rat}
    (hab : a <= b) (hc : c <= 0) : b * c <= a * c := by
  have h := mul_le_mul_of_nonpos_left hab hc
  simpa [Rat.mul_comm] using h

private theorem mul_nonpos_of_nonneg_of_nonpos {x y : Rat}
    (hx : 0 <= x) (hy : y <= 0) : x * y <= 0 := by
  have hny : 0 <= -y := by grind
  have h : 0 <= x * (-y) := Rat.mul_nonneg hx hny
  grind [Rat.mul_neg]

private theorem mul_nonneg_of_nonpos {x y : Rat}
    (hx : x <= 0) (hy : y <= 0) : 0 <= x * y := by
  have hnx : 0 <= -x := by grind
  have hny : 0 <= -y := by grind
  have h : 0 <= (-x) * (-y) := Rat.mul_nonneg hnx hny
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

/-- The literal four-corner product contains every product of two rational
points enclosed by its input intervals. -/
theorem mulRealInterval_contains {a b c d x y : Rat}
    (hax : a <= x) (hxb : x <= b)
    (hcy : c <= y) (hyd : y <= d) :
    (mulRealInterval a b c d).lo <= x * y /\
      x * y <= (mulRealInterval a b c d).hi := by
  unfold mulRealInterval
  constructor
  · by_cases hx : 0 <= x
    · by_cases hy : 0 <= y
      · by_cases hc : 0 <= c
        · calc
            min4 (a * c) (a * d) (b * c) (b * d) <= a * c :=
              min4_le_first _ _ _ _
            _ <= x * c := Rat.mul_le_mul_of_nonneg_right hax hc
            _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
        · have hc0 : c <= 0 := by grind
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= b * c :=
              min4_le_third _ _ _ _
            _ <= x * c := mul_le_mul_of_nonpos_right hxb hc0
            _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
      · have hy0 : y <= 0 := by grind
        have hc0 : c <= 0 := Rat.le_trans hcy hy0
        calc
          min4 (a * c) (a * d) (b * c) (b * d) <= b * c :=
            min4_le_third _ _ _ _
          _ <= x * c := mul_le_mul_of_nonpos_right hxb hc0
          _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
    · have hx0 : x <= 0 := by grind
      by_cases hy : 0 <= y
      · have hd0 : 0 <= d := Rat.le_trans hy hyd
        calc
          min4 (a * c) (a * d) (b * c) (b * d) <= a * d :=
            min4_le_second _ _ _ _
          _ <= x * d := Rat.mul_le_mul_of_nonneg_right hax hd0
          _ <= x * y := mul_le_mul_of_nonpos_left hyd hx0
      · have hy0 : y <= 0 := by grind
        by_cases hd : 0 <= d
        · have hdx : d * x <= 0 := mul_nonpos_of_nonneg_of_nonpos hd hx0
          have hxd : x * d <= 0 := by
            simpa [Rat.mul_comm] using hdx
          have hxy : 0 <= x * y := mul_nonneg_of_nonpos hx0 hy0
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= a * d :=
              min4_le_second _ _ _ _
            _ <= x * d := Rat.mul_le_mul_of_nonneg_right hax hd
            _ <= 0 := hxd
            _ <= x * y := hxy
        · have hd0 : d <= 0 := by grind
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= b * d :=
              min4_le_fourth _ _ _ _
            _ <= x * d := mul_le_mul_of_nonpos_right hxb hd0
            _ <= x * y := mul_le_mul_of_nonpos_left hyd hx0
  · by_cases hx : 0 <= x
    · by_cases hy : 0 <= y
      · calc
          x * y <= b * y := Rat.mul_le_mul_of_nonneg_right hxb hy
          _ <= b * d := Rat.mul_le_mul_of_nonneg_left hyd (by grind)
          _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
            fourth_le_max4 _ _ _ _
      · have hy0 : y <= 0 := by grind
        by_cases ha : 0 <= a
        · calc
            x * y <= a * y := mul_le_mul_of_nonpos_right hax hy0
            _ <= a * d := Rat.mul_le_mul_of_nonneg_left hyd ha
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              second_le_max4 _ _ _ _
        · by_cases hd : 0 <= d
          · have hxy : x * y <= 0 := mul_nonpos_of_nonneg_of_nonpos hx hy0
            have hb0 : 0 <= b := Rat.le_trans hx hxb
            have hbd : 0 <= b * d := Rat.mul_nonneg hb0 hd
            calc
              x * y <= 0 := hxy
              _ <= b * d := hbd
              _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
                fourth_le_max4 _ _ _ _
          · have hd0 : d <= 0 := by grind
            calc
              x * y <= x * d := Rat.mul_le_mul_of_nonneg_left hyd hx
              _ <= a * d := mul_le_mul_of_nonpos_right hax hd0
              _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
                second_le_max4 _ _ _ _
    · have hx0 : x <= 0 := by grind
      by_cases hy : 0 <= y
      · by_cases hc : 0 <= c
        · calc
            x * y <= x * c := mul_le_mul_of_nonpos_left hcy hx0
            _ <= b * c := Rat.mul_le_mul_of_nonneg_right hxb hc
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              third_le_max4 _ _ _ _
        · have hc0 : c <= 0 := by grind
          have hyx : y * x <= 0 := mul_nonpos_of_nonneg_of_nonpos hy hx0
          have hxy : x * y <= 0 := by
            simpa [Rat.mul_comm] using hyx
          have hac : 0 <= a * c :=
            mul_nonneg_of_nonpos (Rat.le_trans hax hx0) hc0
          calc
            x * y <= 0 := hxy
            _ <= a * c := hac
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              first_le_max4 _ _ _ _
      · have hy0 : y <= 0 := by grind
        calc
          x * y <= a * y := mul_le_mul_of_nonpos_right hax hy0
          _ <= a * c :=
            mul_le_mul_of_nonpos_left hcy (Rat.le_trans hax hx0)
          _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
            first_le_max4 _ _ _ _

/-- A four-corner product interval is ordered whenever its two input
intervals are ordered. -/
theorem mulRealInterval_ordered {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    (mulRealInterval a b c d).lo <= (mulRealInterval a b c d).hi := by
  have h := mulRealInterval_contains (a := a) (b := b) (c := c) (d := d)
    (x := a) (y := c) Rat.le_refl hab Rat.le_refl hcd
  exact Rat.le_trans h.1 h.2

/-- Refining both input intervals refines their literal four-corner product
interval.  This is the finite nesting fact required before a raw complex
product can be made valid. -/
theorem mulRealInterval_nested
    {a b c d a' b' c' d' : Rat}
    (haa' : a <= a') (ha'b' : a' <= b') (hb'b : b' <= b)
    (hcc' : c <= c') (hc'd' : c' <= d') (hd'd : d' <= d) :
    (mulRealInterval a b c d).lo <= (mulRealInterval a' b' c' d').lo /\
      (mulRealInterval a' b' c' d').hi <= (mulRealInterval a b c d).hi := by
  have h_ac := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := a') (y := c')
    haa' (Rat.le_trans ha'b' hb'b) hcc' (Rat.le_trans hc'd' hd'd)
  have h_ad := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := a') (y := d')
    haa' (Rat.le_trans ha'b' hb'b) (Rat.le_trans hcc' hc'd') hd'd
  have h_bc := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := b') (y := c')
    (Rat.le_trans haa' ha'b') hb'b hcc' (Rat.le_trans hc'd' hd'd)
  have h_bd := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := b') (y := d')
    (Rat.le_trans haa' ha'b') hb'b (Rat.le_trans hcc' hc'd') hd'd
  unfold mulRealInterval
  exact ⟨le_min4 h_ac.1 h_ad.1 h_bc.1 h_bd.1,
    max4_le h_ac.2 h_ad.2 h_bc.2 h_bd.2⟩

/-- The literal complex box product contains the ordinary rational complex
product of any two rational points enclosed by its input boxes. -/
theorem mul_contains {A B : QBox} {z w : QComplex}
    (hzlo : A.lo <= z) (hzhi : z <= A.hi)
    (hwlo : B.lo <= w) (hwhi : w <= B.hi) :
    (mul A B).lo <= QComplex.mul z w /\
      QComplex.mul z w <= (mul A B).hi := by
  have hrr := mulRealInterval_contains
    (a := A.lo.re) (b := A.hi.re) (c := B.lo.re) (d := B.hi.re)
    hzlo.1 hzhi.1 hwlo.1 hwhi.1
  have hii := mulRealInterval_contains
    (a := A.lo.im) (b := A.hi.im) (c := B.lo.im) (d := B.hi.im)
    hzlo.2 hzhi.2 hwlo.2 hwhi.2
  have hri := mulRealInterval_contains
    (a := A.lo.re) (b := A.hi.re) (c := B.lo.im) (d := B.hi.im)
    hzlo.1 hzhi.1 hwlo.2 hwhi.2
  have hir := mulRealInterval_contains
    (a := A.lo.im) (b := A.hi.im) (c := B.lo.re) (d := B.hi.re)
    hzlo.2 hzhi.2 hwlo.1 hwhi.1
  change
    ((mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      z.re * w.re - z.im * w.im /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      z.re * w.im + z.im * w.re) /\
    (z.re * w.re - z.im * w.im <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    z.re * w.im + z.im * w.re <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi)
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

/-- The literal product of two ordered complex boxes is ordered. -/
theorem mul_ordered {A B : QBox}
    (hA : A.Ordered) (hB : B.Ordered) : (mul A B).Ordered := by
  have hrr := mulRealInterval_ordered hA.1 hB.1
  have hii := mulRealInterval_ordered hA.2 hB.2
  have hri := mulRealInterval_ordered hA.1 hB.2
  have hir := mulRealInterval_ordered hA.2 hB.1
  change
    (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Refining two ordered complex boxes refines their literal product box. -/
theorem mul_nested {A B A' B' : QBox}
    (hA' : A'.Ordered) (hB' : B'.Ordered)
    (hA : A'.NestedIn A) (hB : B'.NestedIn B) :
    (mul A' B').NestedIn (mul A B) := by
  have hrr := mulRealInterval_nested
    hA.1.1 hA'.1 hA.2.1 hB.1.1 hB'.1 hB.2.1
  have hii := mulRealInterval_nested
    hA.1.2 hA'.2 hA.2.2 hB.1.2 hB'.2 hB.2.2
  have hri := mulRealInterval_nested
    hA.1.1 hA'.1 hA.2.1 hB.1.2 hB'.2 hB.2.2
  have hir := mulRealInterval_nested
    hA.1.2 hA'.2 hA.2.2 hB.1.1 hB'.1 hB.2.1
  change
    ((mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      (mulRealInterval A'.lo.re A'.hi.re B'.lo.re B'.hi.re).lo -
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.im B'.hi.im).hi /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      (mulRealInterval A'.lo.re A'.hi.re B'.lo.im B'.hi.im).lo +
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.re B'.hi.re).lo) /\
    ((mulRealInterval A'.lo.re A'.hi.re B'.lo.re B'.hi.re).hi -
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.im B'.hi.im).lo <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    (mulRealInterval A'.lo.re A'.hi.re B'.lo.im B'.hi.im).hi +
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.re B'.hi.re).hi <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi)
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

end QBox

namespace ComplexRaw

/-- The literal product of two valid complex raw stages is an ordered box.
This supplies the first component of raw-product validity. -/
theorem mul_compute_ordered {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) (n : Nat) :
    ((mul z w).compute n).Ordered := by
  change QBox.Ordered (QBox.mul (z.compute n) (w.compute n))
  exact QBox.mul_ordered (valid_ordered hz n) (valid_ordered hw n)

/-- The literal product boxes of two valid raw inputs refine stage by stage.
This supplies the nesting component of raw-product validity. -/
theorem mul_compute_nested {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid) {n m : Nat} (hnm : n <= m) :
    QBox.NestedIn ((mul z w).compute m) ((mul z w).compute n) := by
  change QBox.NestedIn (QBox.mul (z.compute m) (w.compute m))
    (QBox.mul (z.compute n) (w.compute n))
  exact QBox.mul_nested
    (valid_ordered hz m) (valid_ordered hw m)
    (valid_nestedIn hz hnm) (valid_nestedIn hw hnm)

/-- Once a concrete product algorithm supplies its rational width modulus,
the already-proved order and nesting facts assemble a valid raw complex
product.  The premise is the remaining general multiplication obligation. -/
theorem mul_valid_of_widthsShrink {z w : ComplexRaw}
    (hz : z.Valid) (hw : w.Valid)
    (hshrink : ComplexRaw.WidthsShrinkToZero (mul z w).compute) :
    (mul z w).Valid := by
  constructor
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1
      (mul_compute_ordered hz hw n)
  · constructor
    · intro n m hnm
      have hnest := mul_compute_nested hz hw hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact hshrink

end ComplexRaw

end ComputableAnalysis
