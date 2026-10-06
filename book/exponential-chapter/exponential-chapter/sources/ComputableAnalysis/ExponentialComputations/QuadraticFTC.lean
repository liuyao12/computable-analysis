import ComputableAnalysis.IntegralFTC
import ComputableAnalysis.RiemannHilbert.LocalODEMajorant

/-! Finite subdivision turns a supplied, justified quadratic remainder into
rectangle bounds for endpoint increments. No integral identity is assumed. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

theorem remainder_order (p d : RealRaw) (hp : p.Valid) (hd : d.Valid)
    (h C l r : Rat) (hh : 0 ≤ h)
    (he : Small (ofRealRaw (RealRaw.sub p (RealRaw.scaleRat h d))) C)
    (hl : (RealRaw.ofRat l).Le d) (hr : d.Le (RealRaw.ofRat r)) :
    (RealRaw.ofRat (h*l-C)).Le p ∧ p.Le (RealRaw.ofRat (h*r+C)) := by
  have hsd := RealRaw.scaleRat_valid hd (r := h)
  have hlo := RealRaw.le_add_le_add he.1 (RealRaw.le_scaleRat_le_scaleRat hh hl)
  have hhi := RealRaw.le_add_le_add he.2.1 (RealRaw.le_scaleRat_le_scaleRat hh hr)
  have hv := RealRaw.add_valid (RealRaw.sub_valid hp hsd) hsd
  have hc := RealRaw.sub_add_cancel_equiv hp hsd
  have htlo := RealRaw.le_trans hv hlo (RealRaw.le_of_equiv hv hp hc)
  have hthi := RealRaw.le_trans hv (RealRaw.le_of_equiv hp hv (RealRaw.equiv_symm hc)) hhi
  constructor
  · intro n m
    have h := htlo n m
    simpa only [RealRaw.add,RealRaw.addCompute,RealRaw.ofRat,RealRaw.scaleRat,
      RealRaw.scaleRatCompute,if_pos hh,realPart,ofRealRaw,Rat.sub_eq_add_neg,Rat.add_comm] using h
  · intro n m
    have h := hthi n m
    simpa only [RealRaw.add,RealRaw.addCompute,RealRaw.ofRat,RealRaw.scaleRat,
      RealRaw.scaleRatCompute,if_pos hh,realPart,ofRealRaw,Rat.add_comm] using h

/-- Local quadratic estimates imply the cell-order laws used by the existing
FTC. The mesh restriction is eliminated by finite dyadic subdivision. -/
theorem cellBounds_of_quadratic (f : FunctionOnInterval) (P : Rat → RealRaw)
    (h0 : f.lower = 0) (h1 : f.upper = 1)
    (hv : ∀ x, 0 ≤ x → x ≤ 1 → (P x).Valid)
    (C : Rat) (hC : 0 ≤ C) (delta : QPos) (B : Rat)
    (hB : ∀ x (hx : inDomainInterval f.lower f.upper x) n,
      -B ≤ (f.compute x hx n).hi ∧ (f.compute x hx n).lo ≤ B)
    (he : ∀ u v (hu : inDomainInterval f.lower f.upper u),
      0 ≤ u → u ≤ v → v ≤ 1 → v-u ≤ delta.val →
      Small (ofRealRaw (RealRaw.sub (RealRaw.sub (P v) (P u))
        (RealRaw.scaleRat (v-u) {compute := f.compute u hu}))) (C*(v-u)^2)) :
    Integral.CellDerivativeBounds f P := by
  have localBounds (u v l r : Rat) (hu : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1)
      (hs : v-u ≤ delta.val)
      (hl : ∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
        ∀ n, l ≤ (f.compute x hx n).hi)
      (hr : ∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
        ∀ n, (f.compute x hx n).lo ≤ r) :
      (RealRaw.ofRat ((v-u)*l-C*(v-u)^2)).Le (P v-P u) ∧
        (P v-P u).Le (RealRaw.ofRat ((v-u)*r+C*(v-u)^2)) := by
    have hum : inDomainInterval f.lower f.upper u := by rw [h0,h1]; exact ⟨hu,by grind only⟩
    exact remainder_order _ _ (RealRaw.sub_valid (hv v (by grind only) hv1) (hv u hu (by grind only)))
      (show ({compute := f.compute u hum} : RealRaw).Valid from f.valid_on u (f.defined_on u hum)) (v-u) (C*(v-u)^2) l r (by grind only)
      (he u v hum hu huv hv1 hs) (fun _ n => hl u hum (Rat.le_refl) huv n)
      (fun n _ => hr u hum (Rat.le_refl) huv n)
  have dyadic : ∀ (n : Nat) (u v l r : Rat), 0 ≤ u → u ≤ v → v ≤ 1 →
      (v-u)*((1:Rat)/2)^n ≤ delta.val →
      (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
        ∀ k, l ≤ (f.compute x hx k).hi) →
      (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
        ∀ k, (f.compute x hx k).lo ≤ r) →
      (RealRaw.ofRat ((v-u)*l-C*(v-u)^2*((1:Rat)/2)^n)).Le (P v-P u) ∧
        (P v-P u).Le (RealRaw.ofRat ((v-u)*r+C*(v-u)^2*((1:Rat)/2)^n)) := by
    intro n
    induction n with
    | zero =>
      intro u v l r hu huv hv1 hs hl hr
      simpa only [Rat.pow_zero,Rat.mul_one] using localBounds u v l r hu huv hv1
        (by simpa only [Rat.pow_zero,Rat.mul_one] using hs) hl hr
    | succ n ih =>
      intro u v l r hu huv hv1 hs hl hr
      have hum : u ≤ (u+v)/2 := by grind only
      have hmv : (u+v)/2 ≤ v := by grind only
      have hm0 : 0 ≤ (u+v)/2 := by grind only
      have hm1 : (u+v)/2 ≤ 1 := by grind only
      have hleft := ih u ((u+v)/2) l r hu hum hm1
        (by rw [Rat.pow_succ] at hs; change _ ≤ delta.val; grind only)
        (fun x hx hxu hxm k => hl x hx hxu (Rat.le_trans hxm hmv) k)
        (fun x hx hxu hxm k => hr x hx hxu (Rat.le_trans hxm hmv) k)
      have hright := ih ((u+v)/2) v l r hm0 hmv hv1
        (by rw [Rat.pow_succ] at hs; change _ ≤ delta.val; grind only)
        (fun x hx hxm hxv k => hl x hx (Rat.le_trans hum hxm) hxv k)
        (fun x hx hxm hxv k => hr x hx (Rat.le_trans hum hxm) hxv k)
      have hsum := RealRaw.add_valid
        (RealRaw.sub_valid (hv _ hm0 hm1) (hv u hu (by grind only)))
        (RealRaw.sub_valid (hv v (by grind only) hv1) (hv _ hm0 hm1))
      have hend := RealRaw.sub_valid (hv v (by grind only) hv1) (hv u hu (by grind only))
      have ht := RealRaw.sub_add_sub_cancel_middle_equiv
        (hv u hu (by grind only)) (hv _ hm0 hm1) (hv v (by grind only) hv1)
      have hlo := RealRaw.le_trans hsum (RealRaw.le_add_le_add hleft.1 hright.1)
        (RealRaw.le_of_equiv hsum hend ht)
      have hhi := RealRaw.le_trans hsum (RealRaw.le_of_equiv hend hsum (RealRaw.equiv_symm ht))
        (RealRaw.le_add_le_add hleft.2 hright.2)
      constructor
      · intro i j
        have h := hlo i j
        change _ ≤ ((P v-P u).compute j).hi at h ⊢
        simp only [RealRaw.add,RealRaw.addCompute,RealRaw.ofRat] at h
        rw [Rat.pow_succ]
        simp only [Rat.pow_succ,Rat.pow_zero,Rat.mul_one] at h ⊢
        simp only [RealRaw.ofRat]
        grind only
      · intro i j
        have h := hhi i j
        change ((P v-P u).compute i).lo ≤ _ at h ⊢
        simp only [RealRaw.add,RealRaw.addCompute,RealRaw.ofRat] at h
        rw [Rat.pow_succ]
        simp only [Rat.pow_succ,Rat.pow_zero,Rat.mul_one] at h ⊢
        simp only [RealRaw.ofRat]
        grind only
  refine ⟨?_,?_,?_⟩
  · intro x hx; rw [h0,h1] at hx; exact hv x hx.1 hx.2
  · intro u v l hu huv hv1 hl i j
    rw [h0] at hu; rw [h1] at hv1
    apply Classical.byContradiction
    intro hnot
    have hg : 0 < (((v-u)*l)-((P v-P u).compute j).hi)/2 := by
      change ¬(v-u)*l ≤ ((P v-P u).compute j).hi at hnot
      grind only
    let eps : QPos := ⟨_,hg⟩
    let n := max (RationalMajorant.halfDecayShift (v-u) delta)
      (RationalMajorant.halfDecayShift (C*(v-u)^2) eps)
    have hs := RationalMajorant.halfDecayShift_spec_of_le (show 0 ≤ v-u by grind only) delta
      (show RationalMajorant.halfDecayShift (v-u) delta ≤ n from Nat.le_max_left _ _)
    have herr := RationalMajorant.halfDecayShift_spec_of_le
      (Rat.mul_nonneg hC (Rat.pow_nonneg (show 0 ≤ v-u by grind only))) eps
      (show RationalMajorant.halfDecayShift (C*(v-u)^2) eps ≤ n from Nat.le_max_right _ _)
    have hdlo := (dyadic n u v l B hu huv hv1 hs hl
      (fun x hx _ _ k => (hB x hx k).2)).1
    have hb := hdlo 0 j
    change (v-u)*l-C*(v-u)^2*((1:Rat)/2)^n ≤ ((P v-P u).compute j).hi at hb
    change C*(v-u)^2*((1:Rat)/2)^n ≤ (((v-u)*l)-((P v-P u).compute j).hi)/2 at herr
    grind only
  · intro u v r hu huv hv1 hr i j
    rw [h0] at hu; rw [h1] at hv1
    apply Classical.byContradiction
    intro hnot
    have hg : 0 < (((P v-P u).compute i).lo-(v-u)*r)/2 := by
      change ¬((P v-P u).compute i).lo ≤ (v-u)*r at hnot
      grind only
    let eps : QPos := ⟨_,hg⟩
    let n := max (RationalMajorant.halfDecayShift (v-u) delta)
      (RationalMajorant.halfDecayShift (C*(v-u)^2) eps)
    have hs := RationalMajorant.halfDecayShift_spec_of_le (show 0 ≤ v-u by grind only) delta
      (show RationalMajorant.halfDecayShift (v-u) delta ≤ n from Nat.le_max_left _ _)
    have herr := RationalMajorant.halfDecayShift_spec_of_le
      (Rat.mul_nonneg hC (Rat.pow_nonneg (show 0 ≤ v-u by grind only))) eps
      (show RationalMajorant.halfDecayShift (C*(v-u)^2) eps ≤ n from Nat.le_max_right _ _)
    have hdhi := (dyadic n u v (-B) r hu huv hv1 hs
      (fun x hx _ _ k => (hB x hx k).1) hr).2
    have hb := hdhi i 0
    change ((P v-P u).compute i).lo ≤ (v-u)*r+C*(v-u)^2*((1:Rat)/2)^n at hb
    change C*(v-u)^2*((1:Rat)/2)^n ≤ (((P v-P u).compute i).lo-(v-u)*r)/2 at herr
    grind only
end ComputableAnalysis.ExponentialComputations
