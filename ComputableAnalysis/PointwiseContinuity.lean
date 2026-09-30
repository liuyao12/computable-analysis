import ComputableAnalysis.HolomorphicCalculus

/-! Arithmetic and composition preserve continuity at a single represented point.
These constructions do not require continuity elsewhere on the domain. -/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

private def one : QPos := ⟨1, by decide⟩
private def ratio (r s : QPos) : QPos :=
  ⟨r.val/s.val, Rat.mul_pos r.property (Rat.inv_pos.mpr s.property)⟩
private def meet (r s : QPos) : QPos :=
  ⟨min r.val s.val, by have := r.property; have := s.property; grind⟩
private theorem budget {x : Rat} (r s : QPos) (h : x ≤ (ratio r s).val) : x*s.val ≤ r.val := by
  have hm := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt s.property)
  have he : (ratio r s).val*s.val = r.val := Rat.div_mul_cancel (by have := s.property; grind)
  rw [he] at hm
  exact hm

private theorem add_difference (u v x y : ComplexRaw)
    (hu : u.Valid) (hv : v.Valid) (hx : x.Valid) (hy : y.Valid) :
    (ComplexRaw.sub (ComplexRaw.add u v) (ComplexRaw.add x y)).Equiv (ComplexRaw.add (ComplexRaw.sub u x) (ComplexRaw.sub v y)) := by
  let w : Nat → ComplexRaw := fun n => if n=0 then u else if n=1 then v else if n=2 then x else y
  have hw : ∀ n, (w n).Valid := by
    intro n; dsimp [w]; split <;> first | assumption | (split <;> first | assumption | (split <;> assumption))
  exact PolynomialExpr.identity
    (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
    (.add (.add (.var 0) (.neg (.var 2))) (.add (.var 1) (.neg (.var 3)))) w hw (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mk.injEq]
      constructor <;> grind)

def ContinuousAt.add {D : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw} {a : ComplexRaw}
    (hu : ∀ z, z.Valid → D z → (u z).Valid) (hv : ∀ z, z.Valid → D z → (v z).Valid)
    (cu : ContinuousAt D u a) (cv : ContinuousAt D v a) :
    ContinuousAt D (fun z => ComplexRaw.add (u z) (v z)) a where
  point_valid := cu.point_valid
  point_mem := cu.point_mem
  delta := fun eps => meet
    (cu.delta ⟨eps.val/2, by have := eps.property; grind⟩)
    (cv.delta ⟨eps.val/2, by have := eps.property; grind⟩)
  estimate := by
    intro eps z hz hDz hza
    have ha := cu.point_valid
    have hDa := cu.point_mem
    let eta : QPos := ⟨eps.val/2, by have := eps.property; grind⟩
    have h1 := cu.estimate eta z hz hDz (hza.mono (by dsimp [meet]; grind))
    have h2 := cv.estimate eta z hz hDz (hza.mono (by dsimp [meet]; grind))
    exact Small.congr (add_valid (sub_valid (hu z hz hDz) (hu a ha hDa))
      (sub_valid (hv z hz hDz) (hv a ha hDa)))
      (sub_valid (add_valid (hu z hz hDz) (hv z hz hDz)) (add_valid (hu a ha hDa) (hv a ha hDa)))
      (equiv_symm (add_difference _ _ _ _ (hu z hz hDz) (hv z hz hDz) (hu a ha hDa) (hv a ha hDa)))
      ((h1.add h2).mono (by dsimp [eta]; grind))

private theorem mul_difference (u v x y : ComplexRaw)
    (hu : u.Valid) (hv : v.Valid) (hx : x.Valid) (hy : y.Valid) :
    (ComplexRaw.sub (ComplexRaw.mul u v) (ComplexRaw.mul x y)).Equiv
      (ComplexRaw.add (ComplexRaw.add (ComplexRaw.mul (ComplexRaw.sub u x) y) (ComplexRaw.mul x (ComplexRaw.sub v y))) (ComplexRaw.mul (ComplexRaw.sub u x) (ComplexRaw.sub v y))) := by
  let w : Nat → ComplexRaw := fun n => if n=0 then u else if n=1 then v else if n=2 then x else y
  have hw : ∀ n, (w n).Valid := by
    intro n; dsimp [w]; split <;> first | assumption | (split <;> first | assumption | (split <;> assumption))
  let U : PolynomialExpr := .add (.var 0) (.neg (.var 2))
  let V : PolynomialExpr := .add (.var 1) (.neg (.var 3))
  exact PolynomialExpr.identity
    (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
    (.add (.add (.mul U (.var 3)) (.mul (.var 2) V)) (.mul U V)) w hw (by
      intro p; simp only [U,V,PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- Multiplication preserves supplied continuity, with a radius computed from base-point boxes. -/
def ContinuousAt.mul {D : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw} {a : ComplexRaw}
    (hu : ∀ z, z.Valid → D z → (u z).Valid) (hv : ∀ z, z.Valid → D z → (v z).Valid)
    (cu : ContinuousAt D u a) (cv : ContinuousAt D v a) :
    ContinuousAt D (fun z => ComplexRaw.mul (u z) (v z)) a := by
  let cost (a : ComplexRaw) : QPos := ⟨2*((valueBound (u a)).val+(valueBound (v a)).val+1), by
    have := (valueBound (u a)).property; have := (valueBound (v a)).property; grind⟩
  let eta (a : ComplexRaw) (eps : QPos) := meet one (ratio eps (cost a))
  refine {
    point_valid := cu.point_valid
    point_mem := cu.point_mem
    delta := fun eps => meet (cu.delta (eta a eps))
      (cv.delta (eta a eps))
    estimate := ?_ }
  intro eps z hz hDz hza
  have ha := cu.point_valid
  have hDa := cu.point_mem
  have hu' := hu a ha hDa
  have hv' := hv a ha hDa
  have huZ := hu z hz hDz
  have hvZ := hv z hz hDz
  have eu := cu.estimate (eta a eps) z hz hDz (hza.mono (by dsimp [meet]; grind))
  have ev := cv.estimate (eta a eps) z hz hDz (hza.mono (by dsimp [meet]; grind))
  have hpos := Rat.le_of_lt (eta a eps).property
  have h1 : (eta a eps).val ≤ 1 := by dsimp [eta,meet,one]; grind
  have hbud := budget eps (cost a) (show (eta a eps).val ≤ (ratio eps (cost a)).val by dsimp [eta,meet]; grind)
  have hsq := Rat.mul_le_mul_of_nonneg_left h1 hpos
  have b1 := eu.mul (sub_valid huZ hu') hv' hpos (Rat.le_of_lt (valueBound (v a)).property)
    (small_valueBound (v a) hv')
  have b2 := (small_valueBound (u a) hu').mul hu' (sub_valid hvZ hv')
    (Rat.le_of_lt (valueBound (u a)).property) hpos ev
  have b3 := eu.mul (sub_valid huZ hu') (sub_valid hvZ hv') hpos hpos ev
  apply Small.congr
    (add_valid (add_valid (mul_valid (sub_valid huZ hu') hv') (mul_valid hu' (sub_valid hvZ hv')))
      (mul_valid (sub_valid huZ hu') (sub_valid hvZ hv')))
    (sub_valid (mul_valid huZ hvZ) (mul_valid hu' hv'))
    (equiv_symm (mul_difference _ _ _ _ huZ hvZ hu' hv'))
  apply ((b1.add b2).add b3).mono
  change (eta a eps).val*(2*((valueBound (u a)).val+(valueBound (v a)).val+1)) ≤ eps.val at hbud
  grind only

def ContinuousAt.restrict {D E : ComplexRaw → Prop} {u : ComplexRaw → ComplexRaw}
    {a : ComplexRaw} (h : ContinuousAt D u a) (inc : ∀ z, E z → D z) (hEa : E a) :
    ContinuousAt E u a where
  point_valid := h.point_valid
  point_mem := hEa
  delta := h.delta
  estimate := fun eps z hz hEz hza => h.estimate eps z hz (inc z hEz) hza

def ContinuousAt.comp {D E : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw}
    {a : ComplexRaw} (hu : ∀ z, z.Valid → D z → (u z).Valid)
    (maps : ∀ z, z.Valid → D z → E (u z))
    (cu : ContinuousAt D u a) (cv : ContinuousAt E v (u a)) :
    ContinuousAt D (fun z => v (u z)) a where
  point_valid := cu.point_valid
  point_mem := cu.point_mem
  delta := fun eps => cu.delta (cv.delta eps)
  estimate := fun eps z hz hDz hza =>
    cv.estimate eps (u z) (hu z hz hDz) (maps z hz hDz)
      (cu.estimate (cv.delta eps) z hz hDz hza)

end ComputableAnalysis.FunctionTheory
