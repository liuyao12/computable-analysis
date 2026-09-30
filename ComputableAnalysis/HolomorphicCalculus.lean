import ComputableAnalysis.HolomorphicExamples
import ComputableAnalysis.Continuation.Derivative

/-!
# Calculus of represented holomorphic maps

The rules below construct error radii, continuity moduli, and domain
neighborhoods from the supplied witnesses. They apply to arbitrary valid
represented inputs and coefficients. No compactness or Cauchy formula is used.
-/
namespace ComputableAnalysis.FunctionTheory
open ComplexRaw Continuation

/-- A computable positive bound read from the first box. -/
def valueBound (z : ComplexRaw) : QPos :=
  ⟨(z.compute 0).coordinateRadius, QBox.coordinateRadius_pos _⟩

theorem small_valueBound (z : ComplexRaw) (hz : z.Valid) : Small z (valueBound z).val := by
  have box (n : Nat) := QBox.coordinateBounded_of_nested (valid_ordered hz n)
    (valid_nestedIn hz (Nat.zero_le n)) (QBox.coordinateBounded_radius (z.compute 0))
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro n m
  · exact Rat.le_trans (Rat.neg_le_neg (box m).2.1) (neg_qabs_le_self _)
  · exact Rat.le_trans (self_le_qabs _) (box n).1
  · exact Rat.le_trans (Rat.neg_le_neg (box m).2.2.2) (neg_qabs_le_self _)
  · exact Rat.le_trans (self_le_qabs _) (box n).2.2.1

private def one : QPos := ⟨1, by decide⟩
private def ratio (r s : QPos) : QPos :=
  ⟨r.val/s.val, Rat.mul_pos r.property (Rat.inv_pos.mpr s.property)⟩

private def meet (r s : QPos) : QPos :=
  ⟨min r.val s.val, by have := r.property; have := s.property; grind⟩

private theorem meet_left (r s : QPos) : (meet r s).val ≤ r.val := by
  change min r.val s.val ≤ r.val; grind
private theorem meet_right (r s : QPos) : (meet r s).val ≤ s.val := by
  change min r.val s.val ≤ s.val; grind

private theorem ratio_mul (r s : QPos) : (ratio r s).val * s.val = r.val :=
  Rat.div_mul_cancel (by have := s.property; grind)

private theorem budget {x : Rat} (r s : QPos) (h : x ≤ (ratio r s).val) : x*s.val ≤ r.val := by
  have hm := Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt s.property)
  rw [ratio_mul] at hm
  exact hm

private theorem restore_remainder (f : Map) (a d z : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (hz : z.Valid) (hfa : f.domain a) (hfz : f.domain z) :
    (ComplexRaw.add (remainder f a d z) (ComplexRaw.mul d (ComplexRaw.sub z a))).Equiv (ComplexRaw.sub (f.eval z) (f.eval a)) := by
  let v : Nat → ComplexRaw := fun n => if n=0 then f.eval z else if n=1 then f.eval a
    else ComplexRaw.mul d (ComplexRaw.sub z a)
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact f.valid z hz hfz
    · split
      · exact f.valid a ha hfa
      · exact mul_valid hd (sub_valid hz ha)
  exact PolynomialExpr.identity
    (.add (.add (.add (.var 0) (.neg (.var 1))) (.neg (.var 2))) (.var 2))
    (.add (.var 0) (.neg (.var 1))) v hv (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mk.injEq]
      constructor <;> grind)

/-- A derivative witness supplies a local linear bound from the base point from its unit-error radius. -/
def HasDerivativeAt.slopeBound {f : Map} {a d : ComplexRaw} (_h : HasDerivativeAt f a d) : QPos :=
  ⟨1+2*(valueBound d).val, by have := (valueBound d).property; grind⟩

theorem HasDerivativeAt.local_bound {f : Map} {a d : ComplexRaw}
    (h : HasDerivativeAt f a d) (H : QPos) (z : ComplexRaw) (hz : z.Valid)
    (hfz : f.domain z) (hH : H.val ≤ (h.delta one).val) (hza : Small (ComplexRaw.sub z a) H.val) :
    Small (ComplexRaw.sub (f.eval z) (f.eval a)) (h.slopeBound.val*H.val) := by
  have e := h.estimate one H z hz hfz hH hza
  have l := Small.mul h.derivative_valid (sub_valid hz h.point_valid)
    (Rat.le_of_lt (valueBound d).property) (Rat.le_of_lt H.property)
    (small_valueBound d h.derivative_valid) hza
  apply Small.congr
    (add_valid (remainder_valid f h.point_valid h.derivative_valid hz h.point_mem hfz)
      (mul_valid h.derivative_valid (sub_valid hz h.point_valid)))
    (sub_valid (f.valid z hz hfz) (f.valid a h.point_valid h.point_mem))
    (restore_remainder f a d z h.point_valid h.derivative_valid hz h.point_mem hfz)
  exact (e.add l).mono (by dsimp [one,HasDerivativeAt.slopeBound]; grind)

/-- Differentiability at one point constructs value continuity there.
No continuity of the derivative or open-domain hypothesis is needed. -/
def HasDerivativeAt.continuous {f : Map} {a d : ComplexRaw}
    (h : HasDerivativeAt f a d) : ContinuousAt f.domain f.eval a where
  point_valid := h.point_valid
  point_mem := h.point_mem
  delta := fun eps => meet (h.delta one) (ratio eps h.slopeBound)
  estimate := by
    intro eps z hz hfz hza
    let H := meet (h.delta one) (ratio eps h.slopeBound)
    have e := h.local_bound H z hz hfz (meet_left _ _) hza
    apply e.mono
    have hb : H.val ≤ eps.val/h.slopeBound.val := meet_right _ _
    have hp := h.slopeBound.property
    exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hb (Rat.le_of_lt hp)) (by
      rw [Rat.mul_comm, Rat.div_mul_cancel (by grind : h.slopeBound.val ≠ 0)]
      exact Rat.le_refl)

/-- Pointwise differentiability assembles continuity throughout the domain. -/
def Holomorphic.continuous {f : Map} (h : Holomorphic f) : ContinuousOn f.domain f.eval :=
  .ofAtPoint fun a ha hfa => (h.atPoint a ha hfa).continuous

def Map.add (f g : Map) : Map where
  domain := fun z => f.domain z ∧ g.domain z
  eval := fun z => ComplexRaw.add (f.eval z) (g.eval z)
  valid := fun z hz h => add_valid (f.valid z hz h.1) (g.valid z hz h.2)
  domain_congr := fun hz hw he => and_congr (f.domain_congr hz hw he) (g.domain_congr hz hw he)
  eval_congr := fun hz hw h1 h2 he => add_equiv
    (f.eval_congr hz hw h1.1 h2.1 he) (g.eval_congr hz hw h1.2 h2.2 he)

def Map.mul (f g : Map) : Map where
  domain := fun z => f.domain z ∧ g.domain z
  eval := fun z => ComplexRaw.mul (f.eval z) (g.eval z)
  valid := fun z hz h => mul_valid (f.valid z hz h.1) (g.valid z hz h.2)
  domain_congr := fun hz hw he => and_congr (f.domain_congr hz hw he) (g.domain_congr hz hw he)
  eval_congr := fun hz hw h1 h2 he => mul_equiv
    (f.valid _ hz h1.1) (f.valid _ hw h2.1) (g.valid _ hz h1.2) (g.valid _ hw h2.2)
    (f.eval_congr hz hw h1.1 h2.1 he) (g.eval_congr hz hw h1.2 h2.2 he)

private def intersectOpen {f g k : Map} (hf : OpenDomain f) (hg : OpenDomain g)
    (hk : ∀ z, k.domain z ↔ f.domain z ∧ g.domain z) : OpenDomain k where
  radius := fun a ha hka => meet (hf.radius a ha ((hk a).mp hka).1)
    (hg.radius a ha ((hk a).mp hka).2)
  inside := by
    intro a ha hka z hz hza
    apply (hk z).mpr
    exact ⟨hf.inside a ha ((hk a).mp hka).1 z hz (hza.mono (by dsimp [meet]; grind)),
      hg.inside a ha ((hk a).mp hka).2 z hz (hza.mono (by dsimp [meet]; grind))⟩

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

def ContinuousOn.add {D : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw}
    (hu : ∀ z, z.Valid → D z → (u z).Valid) (hv : ∀ z, z.Valid → D z → (v z).Valid)
    (cu : ContinuousOn D u) (cv : ContinuousOn D v) :
    ContinuousOn D (fun z => ComplexRaw.add (u z) (v z)) where
  delta := fun a ha hDa eps => meet
    (cu.delta a ha hDa ⟨eps.val/2, by have := eps.property; grind⟩)
    (cv.delta a ha hDa ⟨eps.val/2, by have := eps.property; grind⟩)
  estimate := by
    intro a ha hDa eps z hz hDz hza
    let eta : QPos := ⟨eps.val/2, by have := eps.property; grind⟩
    have h1 := cu.estimate a ha hDa eta z hz hDz (hza.mono (by dsimp [meet]; grind))
    have h2 := cv.estimate a ha hDa eta z hz hDz (hza.mono (by dsimp [meet]; grind))
    exact Small.congr (add_valid (sub_valid (hu z hz hDz) (hu a ha hDa))
      (sub_valid (hv z hz hDz) (hv a ha hDa)))
      (sub_valid (add_valid (hu z hz hDz) (hv z hz hDz)) (add_valid (hu a ha hDa) (hv a ha hDa)))
      (equiv_symm (add_difference _ _ _ _ (hu z hz hDz) (hv z hz hDz) (hu a ha hDa) (hv a ha hDa)))
      ((h1.add h2).mono (by dsimp [eta]; grind))

def ContinuousOn.restrict {D E : ComplexRaw → Prop} {u : ComplexRaw → ComplexRaw}
    (h : ContinuousOn D u) (inc : ∀ z, E z → D z) : ContinuousOn E u where
  delta := fun a ha hEa eps => h.delta a ha (inc a hEa) eps
  estimate := fun a ha hEa eps z hz hEz hza => h.estimate a ha (inc a hEa) eps z hz (inc z hEz) hza

private theorem add_remainder (f g : Map) (a d e z : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (he : e.Valid) (hz : z.Valid)
    (hfa : f.domain a) (hga : g.domain a) (hfz : f.domain z) (hgz : g.domain z) :
    (remainder (f.add g) a (ComplexRaw.add d e) z).Equiv
      (ComplexRaw.add (remainder f a d z) (remainder g a e z)) := by
  let v : Nat → ComplexRaw := fun n => if n=0 then f.eval z else if n=1 then g.eval z
    else if n=2 then f.eval a else if n=3 then g.eval a else if n=4 then d
    else if n=5 then e else ComplexRaw.sub z a
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact f.valid z hz hfz
    · split
      · exact g.valid z hz hgz
      · split
        · exact f.valid a ha hfa
        · split
          · exact g.valid a ha hga
          · split
            · exact hd
            · split
              · exact he
              · exact sub_valid hz ha
  exact PolynomialExpr.identity
    (.add (.add (.add (.var 0) (.var 1)) (.neg (.add (.var 2) (.var 3))))
      (.neg (.mul (.add (.var 4) (.var 5)) (.var 6))))
    (.add (.add (.add (.var 0) (.neg (.var 2))) (.neg (.mul (.var 4) (.var 6))))
      (.add (.add (.var 1) (.neg (.var 3))) (.neg (.mul (.var 5) (.var 6))))) v hv (by
      intro p; simp only [PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

def HasDerivativeAt.add {f g : Map} {a d e : ComplexRaw}
    (hf : HasDerivativeAt f a d) (hg : HasDerivativeAt g a e) :
    HasDerivativeAt (f.add g) a (ComplexRaw.add d e) where
  point_valid := hf.point_valid
  point_mem := ⟨hf.point_mem,hg.point_mem⟩
  derivative_valid := add_valid hf.derivative_valid hg.derivative_valid
  delta := fun eps => meet (hf.delta ⟨eps.val/2, by have := eps.property; grind⟩)
    (hg.delta ⟨eps.val/2, by have := eps.property; grind⟩)
  estimate := by
    intro eps H z hz hfgz hH hza
    let eta : QPos := ⟨eps.val/2, by have := eps.property; grind⟩
    have h1 := hf.estimate eta H z hz hfgz.1 (by change H.val ≤ min _ _ at hH; grind) hza
    have h2 := hg.estimate eta H z hz hfgz.2 (by change H.val ≤ min _ _ at hH; grind) hza
    exact Small.congr
      (add_valid (remainder_valid f hf.point_valid hf.derivative_valid hz hf.point_mem hfgz.1)
        (remainder_valid g hg.point_valid hg.derivative_valid hz hg.point_mem hfgz.2))
      (remainder_valid (f.add g) hf.point_valid (add_valid hf.derivative_valid hg.derivative_valid)
        hz ⟨hf.point_mem,hg.point_mem⟩ hfgz)
      (equiv_symm (add_remainder f g a d e z hf.point_valid hf.derivative_valid hg.derivative_valid
        hz hf.point_mem hg.point_mem hfgz.1 hfgz.2)) ((h1.add h2).mono (by dsimp [eta]; grind))

/-- Sum on the intersection of the two original open domains. -/
def Holomorphic.add {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g) : Holomorphic (f.add g) where
  openDomain := intersectOpen hf.openDomain hg.openDomain (fun _ => Iff.rfl)
  derivative := fun z => ComplexRaw.add (hf.derivative z) (hg.derivative z)
  atPoint := fun a ha h => (hf.atPoint a ha h.1).add (hg.atPoint a ha h.2)
  derivative_congr := fun ha hb haD hbD he => add_equiv
    (hf.derivative_congr ha hb haD.1 hbD.1 he) (hg.derivative_congr ha hb haD.2 hbD.2 he)
  continuousDerivative := ContinuousOn.add
    (fun z hz h => (hf.atPoint z hz h.1).derivative_valid)
    (fun z hz h => (hg.atPoint z hz h.2).derivative_valid)
    (hf.continuousDerivative.restrict (fun _ h => h.1))
    (hg.continuousDerivative.restrict (fun _ h => h.2))

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
def ContinuousOn.mul {D : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw}
    (hu : ∀ z, z.Valid → D z → (u z).Valid) (hv : ∀ z, z.Valid → D z → (v z).Valid)
    (cu : ContinuousOn D u) (cv : ContinuousOn D v) :
    ContinuousOn D (fun z => ComplexRaw.mul (u z) (v z)) := by
  let cost (a : ComplexRaw) : QPos := ⟨2*((valueBound (u a)).val+(valueBound (v a)).val+1), by
    have := (valueBound (u a)).property; have := (valueBound (v a)).property; grind⟩
  let eta (a : ComplexRaw) (eps : QPos) := meet one (ratio eps (cost a))
  refine {
    delta := fun a ha hDa eps => meet (cu.delta a ha hDa (eta a eps))
      (cv.delta a ha hDa (eta a eps))
    estimate := ?_ }
  intro a ha hDa eps z hz hDz hza
  have hu' := hu a ha hDa
  have hv' := hv a ha hDa
  have huZ := hu z hz hDz
  have hvZ := hv z hz hDz
  have eu := cu.estimate a ha hDa (eta a eps) z hz hDz (hza.mono (by dsimp [meet]; grind))
  have ev := cv.estimate a ha hDa (eta a eps) z hz hDz (hza.mono (by dsimp [meet]; grind))
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

private theorem mul_remainder (f g : Map) (a d e z : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (he : e.Valid) (hz : z.Valid)
    (hfa : f.domain a) (hga : g.domain a) (hfz : f.domain z) (hgz : g.domain z) :
    (remainder (f.mul g) a (ComplexRaw.add (ComplexRaw.mul d (g.eval a)) (ComplexRaw.mul (f.eval a) e)) z).Equiv
      (ComplexRaw.add (ComplexRaw.add (ComplexRaw.mul (remainder f a d z) (g.eval a)) (ComplexRaw.mul (f.eval a) (remainder g a e z)))
        (ComplexRaw.mul (ComplexRaw.sub (f.eval z) (f.eval a)) (ComplexRaw.sub (g.eval z) (g.eval a)))) := by
  let v : Nat → ComplexRaw := fun n => if n=0 then f.eval z else if n=1 then g.eval z
    else if n=2 then f.eval a else if n=3 then g.eval a else if n=4 then d
    else if n=5 then e else ComplexRaw.sub z a
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact f.valid z hz hfz
    · split
      · exact g.valid z hz hgz
      · split
        · exact f.valid a ha hfa
        · split
          · exact g.valid a ha hga
          · split
            · exact hd
            · split
              · exact he
              · exact sub_valid hz ha
  let U : PolynomialExpr := .add (.var 0) (.neg (.var 2))
  let V : PolynomialExpr := .add (.var 1) (.neg (.var 3))
  let R : PolynomialExpr := .add U (.neg (.mul (.var 4) (.var 6)))
  let S : PolynomialExpr := .add V (.neg (.mul (.var 5) (.var 6)))
  exact PolynomialExpr.identity
    (.add (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 2) (.var 3))))
      (.neg (.mul (.add (.mul (.var 4) (.var 3)) (.mul (.var 2) (.var 5))) (.var 6))))
    (.add (.add (.mul R (.var 3)) (.mul (.var 2) S)) (.mul U V)) v hv (by
      intro p; simp only [U,V,R,S,PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- The product rule controls the cross term using the two derived local bounds. -/
def HasDerivativeAt.mul {f g : Map} {a d e : ComplexRaw}
    (hf : HasDerivativeAt f a d) (hg : HasDerivativeAt g a e) :
    HasDerivativeAt (f.mul g) a (ComplexRaw.add (ComplexRaw.mul d (g.eval a)) (ComplexRaw.mul (f.eval a) e)) := by
  let A := valueBound (f.eval a)
  let B := valueBound (g.eval a)
  let L := hf.slopeBound
  let M := hg.slopeBound
  let cost : QPos := ⟨2*(A.val+B.val+L.val*M.val+1), by
    have := A.property; have := B.property; have := Rat.mul_pos L.property M.property; grind⟩
  let eta (eps : QPos) := ratio eps cost
  refine {
    point_valid := hf.point_valid
    point_mem := ⟨hf.point_mem,hg.point_mem⟩
    derivative_valid := add_valid (mul_valid hf.derivative_valid (g.valid a hg.point_valid hg.point_mem))
      (mul_valid (f.valid a hf.point_valid hf.point_mem) hg.derivative_valid)
    delta := fun eps => meet (meet (hf.delta (eta eps)) (hg.delta (eta eps)))
      (meet (meet (hf.delta one) (hg.delta one)) (eta eps))
    estimate := ?_ }
  intro eps H z hz hfgz hH hza
  have hfa := f.valid a hf.point_valid hf.point_mem
  have hga := g.valid a hg.point_valid hg.point_mem
  have hfz := f.valid z hz hfgz.1
  have hgz := g.valid z hz hfgz.2
  have left := Rat.le_trans hH (meet_left _ _)
  have right := Rat.le_trans hH (meet_right _ _)
  have middle := Rat.le_trans right (meet_left _ _)
  have e1 := hf.estimate (eta eps) H z hz hfgz.1 (Rat.le_trans left (meet_left _ _)) hza
  have e2 := hg.estimate (eta eps) H z hz hfgz.2 (Rat.le_trans left (meet_right _ _)) hza
  have l1 := hf.local_bound H z hz hfgz.1 (Rat.le_trans middle (meet_left _ _)) hza
  have l2 := hg.local_bound H z hz hfgz.2 (Rat.le_trans middle (meet_right _ _)) hza
  have hpos := Rat.le_of_lt (Rat.mul_pos (eta eps).property H.property)
  have b1 := e1.mul (remainder_valid f hf.point_valid hf.derivative_valid hz hf.point_mem hfgz.1)
    hga hpos (Rat.le_of_lt B.property) (small_valueBound _ hga)
  have b2 := (small_valueBound _ hfa).mul hfa
    (remainder_valid g hg.point_valid hg.derivative_valid hz hg.point_mem hfgz.2)
    (Rat.le_of_lt A.property) hpos e2
  have b3 := l1.mul (sub_valid hfz hfa) (sub_valid hgz hga)
    (Rat.le_of_lt (Rat.mul_pos L.property H.property))
    (Rat.le_of_lt (Rat.mul_pos M.property H.property)) l2
  apply Small.congr
    (add_valid (add_valid
      (mul_valid (remainder_valid f hf.point_valid hf.derivative_valid hz hf.point_mem hfgz.1) hga)
      (mul_valid hfa (remainder_valid g hg.point_valid hg.derivative_valid hz hg.point_mem hfgz.2)))
      (mul_valid (sub_valid hfz hfa) (sub_valid hgz hga)))
    (remainder_valid (f.mul g) hf.point_valid
      (add_valid (mul_valid hf.derivative_valid hga) (mul_valid hfa hg.derivative_valid))
      hz ⟨hf.point_mem,hg.point_mem⟩ hfgz)
    (equiv_symm (mul_remainder f g a d e z hf.point_valid hf.derivative_valid hg.derivative_valid
      hz hf.point_mem hg.point_mem hfgz.1 hfgz.2))
  apply ((b1.add b2).add b3).mono
  have hHeta : H.val ≤ (eta eps).val := Rat.le_trans right (meet_right _ _)
  have hs := Rat.mul_le_mul_of_nonneg_right hHeta
    (Rat.le_of_lt (Rat.mul_pos (Rat.mul_pos L.property M.property) H.property))
  have hc := ratio_mul eps cost
  change (eta eps).val*(2*(A.val+B.val+L.val*M.val+1))=eps.val at hc
  change 2*((eta eps).val*H.val)*B.val + 2*A.val*((eta eps).val*H.val) +
    2*(L.val*H.val)*(M.val*H.val) ≤ eps.val*H.val
  have hep := Rat.mul_pos (eta eps).property H.property
  have hcH := congrArg (fun t : Rat => t*H.val) hc
  have arithmetic (t h aa bb ll mm ee : Rat)
      (hs : h*(ll*mm*h) ≤ t*(ll*mm*h)) (hp : 0 < t*h)
      (hc : (t*(2*(aa+bb+ll*mm+1)))*h=ee*h) :
      2*(t*h)*bb+2*aa*(t*h)+2*(ll*h)*(mm*h) ≤ ee*h := by grind only
  exact arithmetic _ _ _ _ _ _ _ hs hep hcH

def Holomorphic.mul {f g : Map} (hf : Holomorphic f) (hg : Holomorphic g) : Holomorphic (f.mul g) where
  openDomain := intersectOpen hf.openDomain hg.openDomain (fun _ => Iff.rfl)
  derivative := fun z => ComplexRaw.add (ComplexRaw.mul (hf.derivative z) (g.eval z))
    (ComplexRaw.mul (f.eval z) (hg.derivative z))
  atPoint := fun a ha h => (hf.atPoint a ha h.1).mul (hg.atPoint a ha h.2)
  derivative_congr := by
    intro a b ha hb haD hbD he
    exact add_equiv
      (mul_equiv (hf.atPoint a ha haD.1).derivative_valid (hf.atPoint b hb hbD.1).derivative_valid
        (g.valid a ha haD.2) (g.valid b hb hbD.2) (hf.derivative_congr ha hb haD.1 hbD.1 he)
        (g.eval_congr ha hb haD.2 hbD.2 he))
      (mul_equiv (f.valid a ha haD.1) (f.valid b hb hbD.1)
        (hg.atPoint a ha haD.2).derivative_valid (hg.atPoint b hb hbD.2).derivative_valid
        (f.eval_congr ha hb haD.1 hbD.1 he) (hg.derivative_congr ha hb haD.2 hbD.2 he))
  continuousDerivative := ContinuousOn.add
    (fun z hz h => mul_valid (hf.atPoint z hz h.1).derivative_valid (g.valid z hz h.2))
    (fun z hz h => mul_valid (f.valid z hz h.1) (hg.atPoint z hz h.2).derivative_valid)
    (ContinuousOn.mul (fun z hz h => (hf.atPoint z hz h.1).derivative_valid) (fun z hz h => g.valid z hz h.2)
      (hf.continuousDerivative.restrict (fun _ h => h.1)) (hg.continuous.restrict (fun _ h => h.2)))
    (ContinuousOn.mul (fun z hz h => f.valid z hz h.1) (fun z hz h => (hg.atPoint z hz h.2).derivative_valid)
      (hf.continuous.restrict (fun _ h => h.1)) (hg.continuousDerivative.restrict (fun _ h => h.2)))

def Map.comp (g f : Map) : Map where
  domain := fun z => f.domain z ∧ g.domain (f.eval z)
  eval := fun z => g.eval (f.eval z)
  valid := fun z hz h => g.valid _ (f.valid z hz h.1) h.2
  domain_congr := by
    intro z w hz hw he
    constructor
    · intro h
      have hfw := (f.domain_congr hz hw he).mp h.1
      exact ⟨hfw, (g.domain_congr (f.valid z hz h.1) (f.valid w hw hfw)
        (f.eval_congr hz hw h.1 hfw he)).mp h.2⟩
    · intro h
      have hfz := (f.domain_congr hz hw he).mpr h.1
      exact ⟨hfz, (g.domain_congr (f.valid z hz hfz) (f.valid w hw h.1)
        (f.eval_congr hz hw hfz h.1 he)).mpr h.2⟩
  eval_congr := fun hz hw h1 h2 he => g.eval_congr (f.valid _ hz h1.1) (f.valid _ hw h2.1)
    h1.2 h2.2 (f.eval_congr hz hw h1.1 h2.1 he)

def ContinuousOn.comp {D E : ComplexRaw → Prop} {u v : ComplexRaw → ComplexRaw}
    (hu : ∀ z, z.Valid → D z → (u z).Valid) (maps : ∀ z, z.Valid → D z → E (u z))
    (cu : ContinuousOn D u) (cv : ContinuousOn E v) : ContinuousOn D (fun z => v (u z)) where
  delta := fun a ha hDa eps => cu.delta a ha hDa (cv.delta (u a) (hu a ha hDa) (maps a ha hDa) eps)
  estimate := fun a ha hDa eps z hz hDz hza =>
    cv.estimate (u a) (hu a ha hDa) (maps a ha hDa) eps (u z) (hu z hz hDz) (maps z hz hDz)
      (cu.estimate a ha hDa _ z hz hDz hza)

private theorem comp_remainder (f g : Map) (a d e z : ComplexRaw)
    (ha : a.Valid) (hd : d.Valid) (he : e.Valid) (hz : z.Valid)
    (hfa : f.domain a) (hga : g.domain (f.eval a)) (hfz : f.domain z) (hgz : g.domain (f.eval z)) :
    (remainder (g.comp f) a (ComplexRaw.mul e d) z).Equiv
      (ComplexRaw.add (remainder g (f.eval a) e (f.eval z)) (ComplexRaw.mul e (remainder f a d z))) := by
  let v : Nat → ComplexRaw := fun n => if n=0 then g.eval (f.eval z) else if n=1 then g.eval (f.eval a)
    else if n=2 then f.eval z else if n=3 then f.eval a else if n=4 then d
    else if n=5 then e else ComplexRaw.sub z a
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact g.valid _ (f.valid z hz hfz) hgz
    · split
      · exact g.valid _ (f.valid a ha hfa) hga
      · split
        · exact f.valid z hz hfz
        · split
          · exact f.valid a ha hfa
          · split
            · exact hd
            · split
              · exact he
              · exact sub_valid hz ha
  let U : PolynomialExpr := .add (.var 0) (.neg (.var 1))
  let V : PolynomialExpr := .add (.var 2) (.neg (.var 3))
  exact PolynomialExpr.identity
    (.add U (.neg (.mul (.mul (.var 5) (.var 4)) (.var 6))))
    (.add (.add U (.neg (.mul (.var 5) V)))
      (.mul (.var 5) (.add V (.neg (.mul (.var 4) (.var 6)))))) v hv (by
      intro p; simp only [U,V,PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul,QComplex.mk.injEq]
      constructor <;> grind)

/-- Chain rule on the genuine inverse-image domain, with explicit image control. -/
def HasDerivativeAt.comp {f g : Map} {a d e : ComplexRaw}
    (hg : HasDerivativeAt g (f.eval a) e) (hf : HasDerivativeAt f a d) :
    HasDerivativeAt (g.comp f) a (ComplexRaw.mul e d) := by
  let L := hf.slopeBound
  let B := valueBound e
  let cost : QPos := ⟨L.val+2*B.val+1, by have := L.property; have := B.property; grind⟩
  let eta (eps : QPos) := ratio eps cost
  refine {
    point_valid := hf.point_valid
    point_mem := ⟨hf.point_mem,hg.point_mem⟩
    derivative_valid := mul_valid hg.derivative_valid hf.derivative_valid
    delta := fun eps => meet (meet (hf.delta (eta eps)) (hf.delta one)) (ratio (hg.delta (eta eps)) L)
    estimate := ?_ }
  intro eps H z hz hfgz hH hza
  have left := Rat.le_trans hH (meet_left _ _)
  have right := Rat.le_trans hH (meet_right _ _)
  have rf := hf.estimate (eta eps) H z hz hfgz.1 (Rat.le_trans left (meet_left _ _)) hza
  have df := hf.local_bound H z hz hfgz.1 (Rat.le_trans left (meet_right _ _)) hza
  let J : QPos := ⟨L.val*H.val, Rat.mul_pos L.property H.property⟩
  have hJ : J.val ≤ (hg.delta (eta eps)).val := by
    have hb := budget (hg.delta (eta eps)) L right
    change L.val*H.val ≤ _
    rw [Rat.mul_comm]
    exact hb
  have rg := hg.estimate (eta eps) J (f.eval z) (f.valid z hz hfgz.1) hfgz.2 hJ df
  have rm := (small_valueBound e hg.derivative_valid).mul hg.derivative_valid
    (remainder_valid f hf.point_valid hf.derivative_valid hz hf.point_mem hfgz.1)
    (Rat.le_of_lt B.property) (Rat.le_of_lt (Rat.mul_pos (eta eps).property H.property)) rf
  apply Small.congr
    (add_valid (remainder_valid g hg.point_valid hg.derivative_valid (f.valid z hz hfgz.1) hg.point_mem hfgz.2)
      (mul_valid hg.derivative_valid (remainder_valid f hf.point_valid hf.derivative_valid hz hf.point_mem hfgz.1)))
    (remainder_valid (g.comp f) hf.point_valid (mul_valid hg.derivative_valid hf.derivative_valid)
      hz ⟨hf.point_mem,hg.point_mem⟩ hfgz)
    (equiv_symm (comp_remainder f g a d e z hf.point_valid hf.derivative_valid hg.derivative_valid
      hz hf.point_mem hg.point_mem hfgz.1 hfgz.2))
  apply (rg.add rm).mono
  have hc := ratio_mul eps cost
  change (eta eps).val*(L.val+2*B.val+1)=eps.val at hc
  have hcH := congrArg (fun t : Rat => t*H.val) hc
  have hp := Rat.mul_pos (eta eps).property H.property
  change (eta eps).val*(L.val*H.val)+2*B.val*((eta eps).val*H.val) ≤ eps.val*H.val
  have arithmetic (t h l b ee : Rat) (hp : 0 < t*h)
      (hc : (t*(l+2*b+1))*h=ee*h) : t*(l*h)+2*b*(t*h) ≤ ee*h := by grind only
  exact arithmetic _ _ _ _ _ hp hcH

def Holomorphic.comp {f g : Map} (hg : Holomorphic g) (hf : Holomorphic f) : Holomorphic (g.comp f) where
  openDomain := {
    radius := fun a ha h => meet (hf.openDomain.radius a ha h.1)
      (hf.continuous.delta a ha h.1 (hg.openDomain.radius (f.eval a) (f.valid a ha h.1) h.2))
    inside := by
      intro a ha h z hz hza
      have hfz := hf.openDomain.inside a ha h.1 z hz (hza.mono (meet_left _ _))
      exact ⟨hfz, hg.openDomain.inside (f.eval a) (f.valid a ha h.1) h.2 (f.eval z)
        (f.valid z hz hfz) (hf.continuous.estimate a ha h.1 _ z hz hfz (hza.mono (meet_right _ _)))⟩ }
  derivative := fun z => ComplexRaw.mul (hg.derivative (f.eval z)) (hf.derivative z)
  atPoint := fun a ha h => (hg.atPoint (f.eval a) (f.valid a ha h.1) h.2).comp (hf.atPoint a ha h.1)
  derivative_congr := by
    intro a b ha hb haD hbD he
    exact mul_equiv
      (hg.atPoint _ (f.valid a ha haD.1) haD.2).derivative_valid
      (hg.atPoint _ (f.valid b hb hbD.1) hbD.2).derivative_valid
      (hf.atPoint a ha haD.1).derivative_valid (hf.atPoint b hb hbD.1).derivative_valid
      (hg.derivative_congr (f.valid a ha haD.1) (f.valid b hb hbD.1) haD.2 hbD.2
        (f.eval_congr ha hb haD.1 hbD.1 he)) (hf.derivative_congr ha hb haD.1 hbD.1 he)
  continuousDerivative := ContinuousOn.mul
    (fun z hz h => (hg.atPoint _ (f.valid z hz h.1) h.2).derivative_valid)
    (fun z hz h => (hf.atPoint z hz h.1).derivative_valid)
    (ContinuousOn.comp (fun z hz h => f.valid z hz h.1) (fun _ _ h => h.2)
      (hf.continuous.restrict (fun _ h => h.1)) hg.continuousDerivative)
    (hf.continuousDerivative.restrict (fun _ h => h.1))

/-- Change the evaluator on the same represented domain. Equality is proved
at every valid point, so the original derivative and its radii are retained. -/
def Holomorphic.congr {f g : Map} (h : Holomorphic f)
    (domains : ∀ z, f.domain z ↔ g.domain z)
    (values : ∀ z, z.Valid → f.domain z → (f.eval z).Equiv (g.eval z)) : Holomorphic g where
  openDomain := {
    radius := fun a ha hga => h.openDomain.radius a ha ((domains a).mpr hga)
    inside := fun a ha hga z hz hza => (domains z).mp
      (h.openDomain.inside a ha ((domains a).mpr hga) z hz hza) }
  derivative := h.derivative
  atPoint := fun a ha hga => (h.atPoint a ha ((domains a).mpr hga)).congrMap
    (h.openDomain.radius a ha ((domains a).mpr hga)) (by
      intro z hz hza
      have hfz := h.openDomain.inside a ha ((domains a).mpr hga) z hz hza
      exact ⟨hfz,(domains z).mp hfz,values z hz hfz⟩)
  derivative_congr := fun ha hb haD hbD he =>
    h.derivative_congr ha hb ((domains _).mpr haD) ((domains _).mpr hbD) he
  continuousDerivative := h.continuousDerivative.restrict (fun z hz => (domains z).mpr hz)

end ComputableAnalysis.FunctionTheory
