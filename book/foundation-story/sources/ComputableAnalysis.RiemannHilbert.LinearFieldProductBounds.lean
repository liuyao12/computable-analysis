import ComputableAnalysis.RiemannHilbert.LinearFieldProduct
import ComputableAnalysis.RiemannHilbert.LocalGermAgreement

/-! Quantitative product differentiation for a supplied varying linear field.
Every error modulus is constructed from the justified input bounds and
moduli; the target derivative law is not an input certificate. -/
namespace ComputableAnalysis.RiemannHilbert.LinearField
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n m : Nat}

def errorShare (P B : Rat) (hP : 0 ≤ P) (hB : 0 ≤ B) (eps : QPos) : QPos :=
  ⟨eps.val/(4*(P+B+1)), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (Rat.mul_pos (by decide) (by grind)))⟩

def quadraticRadius (Q C : Rat) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (eps : QPos) : QPos :=
  ⟨eps.val/(4*(2*(2*Q+1)*C+1)), by
    have hQC : 0 ≤ 2*(2*Q+1)*C := Rat.mul_nonneg (by grind) hC
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (Rat.mul_pos (by decide) (by grind)))⟩

def productDelta (P Q B C : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (deltaF deltaG : QPos → QPos) (eps : QPos) : QPos :=
  smallerRadius (smallerRadius (deltaF (errorShare P B hP hB eps)) (deltaG (errorShare P B hP hB eps)))
    (smallerRadius (deltaG ⟨1,by decide⟩) (quadraticRadius Q C hQ hC eps))

theorem error_budget (P Q B C : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (eps H : QPos) (hH : H.val ≤ (quadraticRadius Q C hQ hC eps).val) :
    (P*(errorShare P B hP hB eps).val+(errorShare P B hP hB eps).val*B)*H.val+
      (2*(2*Q+1)*C)*H.val*H.val ≤ eps.val*H.val := by
  let eta := errorShare P B hP hB eps
  let r := quadraticRadius Q C hQ hC eps
  let K := 2*(2*Q+1)*C
  have hK : 0 ≤ K := Rat.mul_nonneg (by grind) hC
  have he : eta.val*(4*(P+B+1))=eps.val :=
    Rat.div_mul_cancel (by have hh : 0 < 4*(P+B+1) := Rat.mul_pos (by decide) (by grind); exact Rat.ne_of_gt hh)
  have hr : r.val*(4*(K+1))=eps.val :=
    Rat.div_mul_cancel (by have hh : 0 < 4*(K+1) := Rat.mul_pos (by decide) (by grind); exact Rat.ne_of_gt hh)
  have hEta := Rat.le_of_lt eta.property
  have hHpos := Rat.le_of_lt H.property
  have hshare : P*eta.val+eta.val*B ≤ eps.val/4 := by
    have hm := Rat.mul_le_mul_of_nonneg_right (show P+B ≤ P+B+1 by grind) hEta
    grind
  have hquadratic : K*H.val ≤ eps.val/4 := by
    have hm := Rat.mul_le_mul_of_nonneg_left hH (show 0 ≤ K+1 by grind)
    have hh := Rat.mul_le_mul_of_nonneg_right (show K ≤ K+1 by grind) hHpos
    change (K+1)*H.val ≤ (K+1)*r.val at hm
    grind
  have h1 := Rat.mul_le_mul_of_nonneg_right hshare hHpos
  have h2 := Rat.mul_le_mul_of_nonneg_right hquadratic hHpos
  have hE := Rat.mul_nonneg (Rat.le_of_lt eps.property) hHpos
  change (P*eta.val+eta.val*B)*H.val+K*H.val*H.val ≤ eps.val*H.val
  grind

theorem operator_difference_bound {D : Scalar → Prop} (G DG : Field (n := n) (m := m) D)
    (Q : Rat) (hQ : 0 ≤ Q)
    (hDG : ∀ z hz B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound ((DG z hz).eval x) (Q*B))
    (w z : Scalar) (hw : D w) (hz : D z) (H : QPos)
    (hzw : Small (sub z.val w.val) H.val)
    (hrem : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound (operatorRemainder G DG w z hw hz x) (H.val*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((ValueMap.difference (G z hz) (G w hw)).eval x) (((2*Q+1)*H.val)*B) := by
  let d : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  have hs := bound_scale (c := d) (x := (DG w hw).eval x) (B := H.val) (C := Q*B)
    (Rat.le_of_lt H.property) (Rat.mul_nonneg hQ hB) hzw (hDG w hw B hB x hx)
  have ht := bound_add hs (hrem B hB x hx)
  have he : 2*H.val*(Q*B)+H.val*B=((2*Q+1)*H.val)*B := by grind
  rw [he] at ht
  let a := Fiber.sub ((G z hz).eval x) ((G w hw).eval x)
  let b := Fiber.scale d ((DG w hw).eval x)
  have heq : Fiber.add b (Fiber.sub a b) ≈ a :=
    fun i => SeriesLimitLaws.add_difference (a.val i) (b.val i) (a.property i) (b.property i)
  exact bound_congr heq ht

/-- The derivative and uniform error of the product are derived from the
input functions' derivative data. All represented inputs and directions are
retained, and no norm or completed scalar is constructed. -/
theorem product_uniform_remainder {D : Scalar → Prop} (G DG : Field (n := n) (m := m) D)
    (f df : UniformSegment.Field (n := n) D) (hG : ∀ z hz, IsLinear (G z hz))
    (P Q B C : Rat) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((G z hz).eval x) (P*E))
    (hDGbound : ∀ z hz E, 0 ≤ E → ∀ x, CoordinateBound x E → CoordinateBound ((DG z hz).eval x) (Q*E))
    (hfB : ∀ z hz, CoordinateBound (f z hz) B) (hdfC : ∀ z hz, CoordinateBound (df z hz) C)
    (deltaF deltaG : QPos → QPos)
    (hfrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaF eps).val →
      Small (sub z.val w.val) H.val → CoordinateBound (vectorRemainder f df w z hw hz) (eps.val*H.val))
    (hGrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (deltaG eps).val →
      Small (sub z.val w.val) H.val → ∀ E, 0 ≤ E → ∀ x, CoordinateBound x E →
        CoordinateBound (operatorRemainder G DG w z hw hz x) ((eps.val*H.val)*E))
    (eps H : QPos) (w z : Scalar) (hw : D w) (hz : D z)
    (hH : H.val ≤ (productDelta P Q B C hP hQ hB hC deltaF deltaG eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (vectorRemainder (product G f) (slope G DG f df) w z hw hz) (eps.val*H.val) := by
  let eta := errorShare P B hP hB eps
  have hF : H.val ≤ (deltaF eta).val := Rat.le_trans
    (Rat.le_trans hH (smallerRadius_le_left _ _)) (smallerRadius_le_left _ _)
  have hGa : H.val ≤ (deltaG eta).val := Rat.le_trans
    (Rat.le_trans hH (smallerRadius_le_left _ _)) (smallerRadius_le_right _ _)
  have hG1 : H.val ≤ (deltaG ⟨1,by decide⟩).val := Rat.le_trans
    (Rat.le_trans hH (smallerRadius_le_right _ _)) (smallerRadius_le_left _ _)
  have hQuad : H.val ≤ (quadraticRadius Q C hQ hC eps).val := Rat.le_trans
    (Rat.le_trans hH (smallerRadius_le_right _ _)) (smallerRadius_le_right _ _)
  have h1 := hGbound z hz (eta.val*H.val) (Rat.mul_nonneg (Rat.le_of_lt eta.property) (Rat.le_of_lt H.property))
    (vectorRemainder f df w z hw hz) (hfrem eta H w z hw hz hF hzw)
  let d : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  have hscaled := bound_scale (c := d) (x := df w hw) (B := H.val) (C := C)
    (Rat.le_of_lt H.property) hC hzw (hdfC w hw)
  have h2 := operator_difference_bound G DG Q hQ hDGbound w z hw hz H hzw
    (by
      intro E hE x hx
      have hs := hGrem ⟨1,by decide⟩ H w z hw hz hG1 hzw E hE x hx
      simpa only [Rat.one_mul] using hs)
    (2*H.val*C) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) (Rat.le_of_lt H.property)) hC)
    (Fiber.scale d (df w hw)) hscaled
  have h3 := hGrem eta H w z hw hz hGa hzw B hB (f w hw) (hfB w hw)
  have hs := bound_congr (Setoid.symm (product_remainder G DG f df hG w z hw hz)) (bound_add (bound_add h1 h2) h3)
  intro i
  apply (hs i).mono
  have hb := error_budget P Q B C hP hQ hB hC eps H hQuad
  change P*(eta.val*H.val)+((2*Q+1)*H.val)*(2*H.val*C)+(eta.val*H.val)*B ≤ eps.val*H.val
  change (P*eta.val+eta.val*B)*H.val+(2*(2*Q+1)*C)*H.val*H.val ≤ eps.val*H.val at hb
  grind

end ComputableAnalysis.RiemannHilbert.LinearField
