import ComputableAnalysis.RiemannHilbert.AffineSegments

/-! Uniqueness along a supplied covered affine segment. Domain coverage,
uniform errors and rational bounds imply equality; no neighborhood or
completed-number compactness argument is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.UniformSegment
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

abbrev Field (D : Scalar → Prop) := (z : Scalar) → D z → Fiber n
abbrev OperatorField (D : Scalar → Prop) := (z : Scalar) → D z → ValueMap (Fiber n) (Fiber n)

def remainder {D : Scalar → Prop} (A : OperatorField (n := n) D) (f : Field (n := n) D)
    (w z : Scalar) (hw : D w) (hz : D z) : Fiber n :=
  Fiber.sub (Fiber.sub (f z hz) (f w hw))
    (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩ ((A w hw).eval (f w hw)))

def pathValue {D : Scalar → Prop} (f : Field (n := n) D) (p q : Scalar)
    (coverage : ∀ t, UniformPath.unitInterval t → D (AffineSegment.point p q t)) (t : Rat) : Fiber n :=
  if ht : UniformPath.unitInterval t then f (AffineSegment.point p q t) (coverage t ht) else Fiber.zero n

def pathOperator {D : Scalar → Prop} (A : OperatorField (n := n) D) (p q : Scalar)
    (coverage : ∀ t, UniformPath.unitInterval t → D (AffineSegment.point p q t)) (t : Rat) :
    ValueMap (Fiber n) (Fiber n) :=
  if ht : UniformPath.unitInterval t then
    (A (AffineSegment.point p q t) (coverage t ht)).followedBy (Fiber.scaleMap (AffineSegment.displacement p q))
  else ValueMap.identity

theorem zero (D : Scalar → Prop) (p q : Scalar) (hp : D p) (hq : D q)
    (coverage : ∀ t, UniformPath.unitInterval t → D (AffineSegment.point p q t))
    (W : QPos) (hW : Small (AffineSegment.displacement p q).val W.val)
    (A : OperatorField (n := n) D) (f : Field (n := n) D)
    (P B : Rat) (hP : 0 ≤ P) (hsmall : 2*W.val*P ≤ (1 : Rat)/2) (hB : 0 ≤ B)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hf0 : f p hp ≈ Fiber.zero n)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (hA : ∀ z hz C, 0 ≤ C → ∀ x, CoordinateBound x C → CoordinateBound ((A z hz).eval x) (P*C))
    (delta : QPos → QPos)
    (hrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (delta eps).val →
      Small (sub z.val w.val) H.val → CoordinateBound (remainder A f w z hw hz) (eps.val*H.val)) :
    f q hq ≈ Fiber.zero n := by
  let y := pathValue f p q coverage
  let T := pathOperator A p q coverage
  let eta := fun eps : QPos => (⟨eps.val/W.val, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 W.property)⟩ : QPos)
  let d := fun eps : QPos => (⟨(delta (eta eps)).val/W.val, by
    rw [Rat.div_def]; exact Rat.mul_pos (delta (eta eps)).property ((Rat.inv_pos).2 W.property)⟩ : QPos)
  have hy0 : y 0 ≈ Fiber.zero n := by
    dsimp [y, pathValue]
    rw [dif_pos (by decide : UniformPath.unitInterval 0)]
    exact Setoid.trans (hfcongr _ p _ hp (AffineSegment.point_zero p q)) hf0
  have hyB : ∀ t, UniformPath.unitInterval t → CoordinateBound (y t) B := by
    intro t ht
    dsimp [y, pathValue]
    rw [dif_pos ht]
    exact hfB _ _
  have hT : ∀ t, UniformPath.unitInterval t → ∀ C, 0 ≤ C → ∀ x, CoordinateBound x C →
      CoordinateBound ((T t).eval x) ((2*W.val*P)*C) := by
    intro t ht C hC x hx
    dsimp [T, pathOperator]
    rw [dif_pos ht]
    have hs := bound_scale (c := AffineSegment.displacement p q)
      (x := (A (AffineSegment.point p q t) (coverage t ht)).eval x) (B := W.val) (C := P*C)
      (Rat.le_of_lt W.property) (Rat.mul_nonneg hP hC) hW (hA _ _ C hC x hx)
    have he : 2*W.val*(P*C)=(2*W.val*P)*C := by grind
    rw [he] at hs
    exact hs
  have hd : ∀ (eps : QPos) s t, UniformPath.unitInterval s → UniformPath.unitInterval t →
      0 ≤ t-s → t-s ≤ (d eps).val →
      CoordinateBound (Fiber.sub (Fiber.sub (y t) (y s)) (ratScale (t-s) ((T s).eval (y s))))
        (eps.val*(t-s)) := by
    intro eps s t hs ht hst hstep
    by_cases heq : t=s
    · subst t
      have hb := bound_ratScale (r := 0) (by decide) (hT s hs B hB (y s) (hyB s hs))
      simp only [Rat.zero_mul] at hb
      have hv := bound_sub (Fiber.sub_zero_bound (Setoid.refl (y s))) hb
      simpa only [Rat.sub_self, Rat.mul_zero, Rat.zero_add] using hv
    · have hstpos : 0 < t-s := by grind
      let H : QPos := ⟨(t-s)*W.val, Rat.mul_pos hstpos W.property⟩
      have hH : H.val ≤ (delta (eta eps)).val := by
        have he : W.val*(d eps).val=(delta (eta eps)).val := by
          dsimp [d]
          rw [Rat.mul_comm]
          exact Rat.div_mul_cancel (Rat.ne_of_gt W.property)
        have hh := Rat.mul_le_mul_of_nonneg_left hstep (Rat.le_of_lt W.property)
        change W.val*(t-s) ≤ W.val*(d eps).val at hh
        rw [he] at hh
        simpa only [H, Rat.mul_comm] using hh
      have hr := hrem (eta eps) H (AffineSegment.point p q s) (AffineSegment.point p q t)
        (coverage s hs) (coverage t ht) hH (AffineSegment.difference_bound p q W.val s t hW hst)
      have herror : (eta eps).val*H.val=eps.val*(t-s) := by
        have he : (eta eps).val*W.val=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt W.property)
        dsimp [H]
        calc
          _ = ((eta eps).val*W.val)*(t-s) := by grind
          _ = _ := by rw [he]
      rw [herror] at hr
      have hc := Fiber.sub_congr (Setoid.refl
        (Fiber.sub (f (AffineSegment.point p q t) (coverage t ht)) (f (AffineSegment.point p q s) (coverage s hs))))
        (AffineSegment.scale_difference p q s t ((A (AffineSegment.point p q s) (coverage s hs)).eval
          (f (AffineSegment.point p q s) (coverage s hs))))
      have hh := bound_congr hc hr
      simpa only [y, T, pathValue, pathOperator, dif_pos hs, dif_pos ht,
        ValueMap.followedBy, Fiber.scaleMap, remainder] using hh
  have hzero := UniformPath.zero y T (2*W.val*P) B
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt W.property)) hP) hsmall hB
    hy0 hyB hT d hd 1 (by decide)
  have hpoint : y 1 ≈ f q hq := by
    dsimp [y, pathValue]
    rw [dif_pos (by decide : UniformPath.unitInterval 1)]
    exact hfcongr _ q _ hq (AffineSegment.point_one p q)
  exact Setoid.trans (Setoid.symm hpoint) hzero

theorem remainder_difference {D : Scalar → Prop} (A : OperatorField (n := n) D)
    (hlinear : ∀ a ha, IsLinear (A a ha)) (f g : Field (n := n) D)
    (a z : Scalar) (ha : D a) (hz : D z) :
    remainder A (fun w hw => Fiber.sub (f w hw) (g w hw)) a z ha hz ≈
      Fiber.sub (remainder A f a z ha hz) (remainder A g a z ha hz) := by
  let c : Scalar := ⟨sub z.val a.val, sub_valid z.property a.property⟩
  let D := Fiber.sub ((A a ha).eval (f a ha)) ((A a ha).eval (g a ha))
  let r := Fiber.sub (Fiber.sub (Fiber.sub (f z hz) (g z hz)) (Fiber.sub (f a ha) (g a ha)))
    (Fiber.scale c D)
  have hr : remainder A (fun w hw => Fiber.sub (f w hw) (g w hw)) a z ha hz ≈ r :=
    Fiber.sub_congr (Setoid.refl _) (Fiber.scale_congr
      (a := c) (b := c) (equiv_refl _ c.property) ((hlinear a ha).sub (f a ha) (g a ha)))
  apply Setoid.trans hr
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := r.property i)
    (hright := (Fiber.sub (remainder A f a z ha hz) (remainder A g a z ha hz)).property i)
  change
    ((ComplexRawQuotient.ofRaw ((f z hz).val i) ((f z hz).property i)-
      ComplexRawQuotient.ofRaw ((g z hz).val i) ((g z hz).property i))-
     (ComplexRawQuotient.ofRaw ((f a ha).val i) ((f a ha).property i)-
      ComplexRawQuotient.ofRaw ((g a ha).val i) ((g a ha).property i)))-
      ComplexRawQuotient.ofRaw c.val c.property*
       (ComplexRawQuotient.ofRaw (((A a ha).eval (f a ha)).val i) (((A a ha).eval (f a ha)).property i)-
        ComplexRawQuotient.ofRaw (((A a ha).eval (g a ha)).val i) (((A a ha).eval (g a ha)).property i)) =
    ((ComplexRawQuotient.ofRaw ((f z hz).val i) ((f z hz).property i)-
      ComplexRawQuotient.ofRaw ((f a ha).val i) ((f a ha).property i))-
      ComplexRawQuotient.ofRaw c.val c.property*
       ComplexRawQuotient.ofRaw (((A a ha).eval (f a ha)).val i) (((A a ha).eval (f a ha)).property i))-
    ((ComplexRawQuotient.ofRaw ((g z hz).val i) ((g z hz).property i)-
      ComplexRawQuotient.ofRaw ((g a ha).val i) ((g a ha).property i))-
      ComplexRawQuotient.ofRaw c.val c.property*
       ComplexRawQuotient.ofRaw (((A a ha).eval (g a ha)).val i) (((A a ha).eval (g a ha)).property i))
  grind

/-- Two uniformly differentiable horizontal fields with the same initial value
agree exactly. No coefficient recurrence or equality conclusion is assumed. -/
theorem equal (D : Scalar → Prop) (p q : Scalar) (hp : D p) (hq : D q)
    (coverage : ∀ t, UniformPath.unitInterval t → D (AffineSegment.point p q t))
    (W : QPos) (hW : Small (AffineSegment.displacement p q).val W.val)
    (A : OperatorField (n := n) D) (f g : Field (n := n) D)
    (P B C : Rat) (hP : 0 ≤ P) (hsmall : 2*W.val*P ≤ (1 : Rat)/2) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f p hp ≈ g p hp)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (hlinear : ∀ z hz, IsLinear (A z hz))
    (hA : ∀ z hz C, 0 ≤ C → ∀ x, CoordinateBound x C → CoordinateBound ((A z hz).eval x) (P*C))
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A f a z ha hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A g a z ha hz) (eps.val*H.val))
    : f q hq ≈ g q hq := by
  let eta := fun eps : QPos => (⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩ : QPos)
  let delta := fun eps : QPos =>
    if (deltaF (eta eps)).val ≤ (deltaG (eta eps)).val then deltaF (eta eps) else deltaG (eta eps)
  have hdeltaF : ∀ eps, (delta eps).val ≤ (deltaF (eta eps)).val := by
    intro eps; dsimp [delta]; split <;> grind
  have hdeltaG : ∀ eps, (delta eps).val ≤ (deltaG (eta eps)).val := by
    intro eps; dsimp [delta]; split <;> grind
  let u := fun z hz => Fiber.sub (f z hz) (g z hz)
  have hu0 : u p hp ≈ Fiber.zero n := by
    intro i
    exact SeriesLimitLaws.equiv_of_small_sub_zero _ ComplexRaw.zero
      (by
        have hs := SeriesLimitLaws.small_sub (Fiber.sub_zero_bound hinitial i)
          (Small.zero (by decide : (0 : Rat) ≤ 0))
        simpa only [Rat.add_zero] using hs)
  have hurem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (delta eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A u a z ha hz) (eps.val*H.val) := by
    intro eps H a z ha hz hH hza
    have hs := bound_sub (hfrem (eta eps) H a z ha hz (Rat.le_trans hH (hdeltaF eps)) hza)
      (hgrem (eta eps) H a z ha hz (Rat.le_trans hH (hdeltaG eps)) hza)
    have he : (eta eps).val*H.val+(eta eps).val*H.val=eps.val*H.val := by dsimp [eta]; grind
    rw [he] at hs
    exact bound_congr (Setoid.symm (remainder_difference A hlinear f g a z ha hz)) hs
  have hu := zero D p q hp hq coverage W hW A u P (B+C) hP hsmall (Rat.add_nonneg hB hC)
    (fun z w hz hw hzw => Fiber.sub_congr (hfcongr z w hz hw hzw) (hgcongr z w hz hw hzw))
    hu0 (fun z hz => bound_sub (hfB z hz) (hgB z hz)) hA delta hurem
  intro i
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _ (by
    have hs := Small.congr (ofQComplex_valid _) ((u q hq).property i)
      (equiv_symm (hu i)) (Small.zero (by decide : (0 : Rat) ≤ 0))
    exact hs)


end ComputableAnalysis.RiemannHilbert.UniformSegment
