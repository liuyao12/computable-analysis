import ComputableAnalysis.RiemannHilbert.RadialSegments

/-! Exact local uniqueness from supplied uniform complex derivative errors.
The uniform errors are genuine mathematical hypotheses; they are not
inferred from pointwise holomorphicity or assumed uniqueness. -/
namespace ComputableAnalysis.RiemannHilbert.UniformLocal
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

abbrev Field (R : Rat) := (z : Scalar) → interior R z → Fiber n
abbrev OperatorField (R : Rat) := (z : Scalar) → interior R z → ValueMap (Fiber n) (Fiber n)

def remainder {R : Rat} (A : OperatorField (n := n) R) (f : Field (n := n) R)
    (a z : Scalar) (ha : interior R a) (hz : interior R z) : Fiber n :=
  Fiber.sub (Fiber.sub (f z hz) (f a ha))
    (Fiber.scale ⟨sub z.val a.val, sub_valid z.property a.property⟩ ((A a ha).eval (f a ha)))

def pathValue {R : Rat} (f : Field (n := n) R) (z : Scalar) (hz : interior R z) (t : Rat) : Fiber n :=
  if ht : 0 ≤ t ∧ t ≤ 1 then f (RadialSegment.point z t) (RadialSegment.mem R z hz t ht) else Fiber.zero n

def pathOperator {R : Rat} (A : OperatorField (n := n) R) (z : Scalar) (hz : interior R z) (t : Rat) :
    ValueMap (Fiber n) (Fiber n) :=
  if ht : 0 ≤ t ∧ t ≤ 1 then
    (A (RadialSegment.point z t) (RadialSegment.mem R z hz t ht)).followedBy (Fiber.scaleMap z)
  else ValueMap.identity

/-- A uniformly differentiable zero-initial horizontal field vanishes on a
small disk. Both the finite mesh and shrinking-bound argument are proved. -/
theorem zero (R : QPos) (A : OperatorField (n := n) R.val) (f : Field (n := n) R.val)
    (P B : Rat) (hP : 0 ≤ P) (hsmall : 2*R.val*P ≤ (1 : Rat)/2) (hB : 0 ≤ B)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hf0 : f ⟨ComplexRaw.zero, ofQComplex_valid _⟩ (interior_zero R.val R.property) ≈ Fiber.zero n)
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (hA : ∀ z hz C, 0 ≤ C → ∀ x, CoordinateBound x C → CoordinateBound ((A z hz).eval x) (P*C))
    (delta : QPos → QPos)
    (hrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (delta eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A f a z ha hz) (eps.val*H.val))
    (z : Scalar) (hz : interior R.val z) : f z hz ≈ Fiber.zero n := by
  let y := pathValue f z hz
  let T := pathOperator A z hz
  let eta := fun eps : QPos => (⟨eps.val/R.val, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 R.property)⟩ : QPos)
  let d := fun eps : QPos => (⟨(delta (eta eps)).val/R.val, by
    rw [Rat.div_def]; exact Rat.mul_pos (delta (eta eps)).property ((Rat.inv_pos).2 R.property)⟩ : QPos)
  have hy0 : y 0 ≈ Fiber.zero n := by
    dsimp [y, pathValue]
    rw [dif_pos (by decide : (0 : Rat) ≤ 0 ∧ (0 : Rat) ≤ 1)]
    exact Setoid.trans (hfcongr _ _ _ _ (RadialSegment.point_zero z)) hf0
  have hyB : ∀ t, UniformPath.unitInterval t → CoordinateBound (y t) B := by
    intro t ht
    dsimp [y, pathValue]
    rw [dif_pos ht]
    exact hfB _ _
  have hT : ∀ t, UniformPath.unitInterval t → ∀ C, 0 ≤ C → ∀ x, CoordinateBound x C →
      CoordinateBound ((T t).eval x) ((2*R.val*P)*C) := by
    intro t ht C hC x hx
    dsimp [T, pathOperator]
    rw [dif_pos ht]
    have hs := bound_scale
      (c := z) (x := (A (RadialSegment.point z t) (RadialSegment.mem R.val z hz t ht)).eval x)
      (B := R.val) (C := P*C) (Rat.le_of_lt R.property) (Rat.mul_nonneg hP hC)
      (interior_bound _ z hz) (hA _ _ C hC x hx)
    have he : 2*R.val*(P*C)=(2*R.val*P)*C := by grind
    rw [he] at hs; exact hs
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
      let H : QPos := ⟨(t-s)*R.val, Rat.mul_pos hstpos R.property⟩
      have hH : H.val ≤ (delta (eta eps)).val := by
        have he : R.val*(d eps).val=(delta (eta eps)).val := by
          dsimp [d]; rw [Rat.mul_comm]; exact Rat.div_mul_cancel (Rat.ne_of_gt R.property)
        have hh := Rat.mul_le_mul_of_nonneg_left hstep (Rat.le_of_lt R.property)
        change R.val*(t-s) ≤ R.val*(d eps).val at hh
        rw [he] at hh
        simpa only [H, Rat.mul_comm] using hh
      have hr := hrem (eta eps) H (RadialSegment.point z s) (RadialSegment.point z t)
        (RadialSegment.mem R.val z hz s hs) (RadialSegment.mem R.val z hz t ht) hH
        (RadialSegment.difference_bound z R.val s t (interior_bound _ z hz) hst)
      have herror : (eta eps).val*H.val=eps.val*(t-s) := by
        have he : (eta eps).val*R.val=eps.val := Rat.div_mul_cancel (Rat.ne_of_gt R.property)
        dsimp [H]
        calc
          _ = ((eta eps).val*R.val)*(t-s) := by grind
          _ = _ := by rw [he]
      rw [herror] at hr
      have hc := Fiber.sub_congr (Setoid.refl
        (Fiber.sub (f (RadialSegment.point z t) (RadialSegment.mem R.val z hz t ht))
          (f (RadialSegment.point z s) (RadialSegment.mem R.val z hz s hs))))
        (RadialSegment.scale_difference z s t
          ((A (RadialSegment.point z s) (RadialSegment.mem R.val z hz s hs)).eval
            (f (RadialSegment.point z s) (RadialSegment.mem R.val z hz s hs))))
      have hh := bound_congr hc hr
      simpa only [y, T, pathValue, pathOperator, dif_pos hs, dif_pos ht,
        ValueMap.followedBy, Fiber.scaleMap, remainder] using hh
  have hzero := UniformPath.zero y T (2*R.val*P) B
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt R.property)) hP) hsmall hB
    hy0 hyB hT d hd 1 (by decide)
  have hpoint : y 1 ≈ f z hz := by
    dsimp [y, pathValue]
    rw [dif_pos (by decide : (0 : Rat) ≤ 1 ∧ (1 : Rat) ≤ 1)]
    exact hfcongr _ _ _ _ (RadialSegment.point_one z)
  exact Setoid.trans (Setoid.symm hpoint) hzero



theorem remainder_difference {R : Rat} (A : OperatorField (n := n) R)
    (hlinear : ∀ a ha, IsLinear (A a ha)) (f g : Field (n := n) R)
    (a z : Scalar) (ha : interior R a) (hz : interior R z) :
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
theorem equal (R : QPos) (A : OperatorField (n := n) R.val) (f g : Field (n := n) R.val)
    (P B C : Rat) (hP : 0 ≤ P) (hsmall : 2*R.val*P ≤ (1 : Rat)/2) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hfcongr : ∀ z w hz hw, z.val.Equiv w.val → f z hz ≈ f w hw)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hinitial : f ⟨ComplexRaw.zero, ofQComplex_valid _⟩ (interior_zero R.val R.property) ≈
      g ⟨ComplexRaw.zero, ofQComplex_valid _⟩ (interior_zero R.val R.property))
    (hfB : ∀ z hz, CoordinateBound (f z hz) B)
    (hgB : ∀ z hz, CoordinateBound (g z hz) C)
    (hlinear : ∀ z hz, IsLinear (A z hz))
    (hA : ∀ z hz C, 0 ≤ C → ∀ x, CoordinateBound x C → CoordinateBound ((A z hz).eval x) (P*C))
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A f a z ha hz) (eps.val*H.val))
    (hgrem : ∀ (eps H : QPos) a z ha hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val a.val) H.val → CoordinateBound (remainder A g a z ha hz) (eps.val*H.val))
    (z : Scalar) (hz : interior R.val z) : f z hz ≈ g z hz := by
  let eta := fun eps : QPos => (⟨eps.val/2, by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩ : QPos)
  let delta := fun eps : QPos =>
    if (deltaF (eta eps)).val ≤ (deltaG (eta eps)).val then deltaF (eta eps) else deltaG (eta eps)
  have hdeltaF : ∀ eps, (delta eps).val ≤ (deltaF (eta eps)).val := by
    intro eps; dsimp [delta]; split <;> grind
  have hdeltaG : ∀ eps, (delta eps).val ≤ (deltaG (eta eps)).val := by
    intro eps; dsimp [delta]; split <;> grind
  let u := fun z hz => Fiber.sub (f z hz) (g z hz)
  have hu0 : u ⟨ComplexRaw.zero, ofQComplex_valid _⟩ (interior_zero R.val R.property) ≈ Fiber.zero n := by
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
  have hu := zero R A u P (B+C) hP hsmall (Rat.add_nonneg hB hC)
    (fun z w hz hw hzw => Fiber.sub_congr (hfcongr z w hz hw hzw) (hgcongr z w hz hw hzw))
    hu0 (fun z hz => bound_sub (hfB z hz) (hgB z hz)) hA delta hurem z hz
  intro i
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ _ (by
    have hs := Small.congr (ofQComplex_valid _) ((u z hz).property i)
      (equiv_symm (hu i)) (Small.zero (by decide : (0 : Rat) ≤ 0))
    exact hs)

end ComputableAnalysis.RiemannHilbert.UniformLocal
