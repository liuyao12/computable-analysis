import ComputableAnalysis.ModularForms.DiskLambertTail
import ComputableAnalysis.RiemannHilbert.BoxApproximation

/-! The full open Euclidean unit disk, certified by a rational rectangle
 strictly inside it. Searching for that rectangle is executable. -/
namespace ComputableAnalysis.ModularForms.EisensteinUnitDisk
open ComplexRaw FunctionTheory RiemannHilbert CauchyTaylor
set_option maxHeartbeats 1000000

def reBound (B : QBox) : Rat := max (qabs B.lo.re) (qabs B.hi.re)
def imBound (B : QBox) : Rat := max (qabs B.lo.im) (qabs B.hi.im)
def bound (B : QBox) : Rat := reBound B*reBound B+imBound B*imBound B

theorem re_nonneg (B : QBox) : 0≤reBound B := by have := qabs_nonneg B.lo.re; unfold reBound; grind
theorem im_nonneg (B : QBox) : 0≤imBound B := by have := qabs_nonneg B.lo.im; unfold imBound; grind
theorem bound_nonneg (B : QBox) : 0≤bound B := Rat.add_nonneg (rat_square_nonneg_basic _) (rat_square_nonneg_basic _)

theorem coordinates (B : QBox) : -reBound B≤B.lo.re ∧ B.hi.re≤reBound B ∧ -imBound B≤B.lo.im ∧ B.hi.im≤imBound B := by
  unfold reBound imBound qabs
  split <;> split <;> split <;> split <;> grind

theorem square_mono (a b : Rat) (ha : 0≤a) (hab : a≤b) : a*a≤b*b := by
  have h1 := Rat.mul_le_mul_of_nonneg_right hab ha
  have h2 := Rat.mul_le_mul_of_nonneg_left hab (Rat.le_trans ha hab)
  grind

theorem bound_of_coordinates (B : QBox) (A C : Rat) (hA : 0≤A) (hC : 0≤C)
    (h : -A≤B.lo.re ∧ B.hi.re≤A ∧ -C≤B.lo.im ∧ B.hi.im≤C) (ho : B.lo≤B.hi) :
    reBound B≤A ∧ imBound B≤C := by
  unfold reBound imBound qabs
  change B.lo.re≤B.hi.re ∧ B.lo.im≤B.hi.im at ho
  split <;> split <;> split <;> split <;> grind

theorem nested_bound (A B : QBox) (h : B.NestedIn A) (ho : B.lo≤B.hi) : bound B≤bound A := by
  have hc := coordinates A
  have hn : -reBound A≤B.lo.re ∧ B.hi.re≤reBound A ∧ -imBound A≤B.lo.im ∧ B.hi.im≤imBound A := by
    change (A.lo.re≤B.lo.re ∧ A.lo.im≤B.lo.im) ∧ (B.hi.re≤A.hi.re ∧ B.hi.im≤A.hi.im) at h
    grind
  have hb := bound_of_coordinates B _ _ (re_nonneg A) (im_nonneg A) hn ho
  exact rat_add_le_add (square_mono _ _ (re_nonneg B) hb.1) (square_mono _ _ (im_nonneg B) hb.2)

theorem point_bound (B : QBox) (q : QComplex) (hq : B.lo≤q ∧ q≤B.hi) : QComplex.normSq q≤bound B := by
  have hc := coordinates B
  change (B.lo.re≤q.re ∧ B.lo.im≤q.im) ∧ (q.re≤B.hi.re ∧ q.im≤B.hi.im) at hq
  have hre : qabs q.re≤reBound B := by unfold qabs; split <;> grind
  have him : qabs q.im≤imBound B := by unfold qabs; split <;> grind
  have hr := square_mono _ _ (qabs_nonneg _) hre
  have hi := square_mono _ _ (qabs_nonneg _) him
  have he : ∀x:Rat, qabs x*qabs x=x*x := by intro x; unfold qabs; split <;> grind
  rw [he] at hr
  rw [he] at hi
  exact rat_add_le_add hr hi

/-- A valid name is in the open disk exactly when one of its shrinking
 rational boxes lies strictly inside the Euclidean unit circle. -/
def domain (z : Scalar) : Prop := ∃N, bound (z.val.compute N)<1

def good (z : Scalar) (N : Nat) : Bool := decide (bound (z.val.compute N)<1)

theorem eventually_good (z : Scalar) (hz : domain z) : ∃N, ∀n, N≤n → good z n=true := by
  obtain ⟨N,hN⟩ := hz
  refine ⟨N,fun n hn => ?_⟩
  simp only [good,decide_eq_true_eq]
  have := nested_bound _ _ (valid_nestedIn z.property hn) (valid_ordered z.property n)
  grind

def stage (z : Scalar) (hz : domain z) : Nat := PrecisionSearch.firstFrom (good z) (eventually_good z hz) 0

theorem stage_spec (z : Scalar) (hz : domain z) : bound (z.val.compute (stage z hz))<1 := by
  have h := (PrecisionSearch.firstFrom_spec (good z) (eventually_good z hz) 0).2
  simpa only [stage,good,decide_eq_true_eq] using h

def radius (z : Scalar) (hz : domain z) : Rat := (1+bound (z.val.compute (stage z hz)))/2

theorem radius_pos (z : Scalar) (hz : domain z) : 0<radius z hz := by
  have := bound_nonneg (z.val.compute (stage z hz)); dsimp [radius]; grind

theorem radius_lt_one (z : Scalar) (hz : domain z) : radius z hz<1 := by
  have := stage_spec z hz; dsimp [radius]; grind

theorem radius_square (z : Scalar) (hz : domain z) : bound (z.val.compute (stage z hz))≤radius z hz*radius z hz := by
  have h := rat_square_nonneg_basic (1-bound (z.val.compute (stage z hz)))
  dsimp [radius]
  grind

theorem centers_inside (z : Scalar) (hz : domain z) (n : Nat) (hn : stage z hz≤n) :
    InDisk (z.val.compute n).center (radius z hz) := by
  have hc := QBox.center_mem (valid_ordered z.property n)
  have h := valid_nestedIn z.property hn
  exact Rat.le_trans (point_bound _ _ ⟨QComplex.le_trans h.1 hc.1,QComplex.le_trans hc.2 h.2⟩) (radius_square z hz)

theorem rational_mem (q : QComplex) (hq : QComplex.normSq q<1) : domain (RationalLambert.point q) := by
  refine ⟨0,?_⟩
  have he : bound (QBox.point q)=QComplex.normSq q := by
    dsimp [bound,reBound,imBound,QBox.point]
    have hm : ∀a:Rat, max a a=a := by intro a; grind
    rw [hm,hm]
    unfold qabs QComplex.normSq
    split <;> split <;> grind
  exact he ▸ hq

theorem rational_mem_iff (q : QComplex) : domain (RationalLambert.point q) ↔ QComplex.normSq q<1 := by
  constructor
  · rintro ⟨N,hN⟩
    have := point_bound (QBox.point q) q ⟨QComplex.le_refl _,QComplex.le_refl _⟩
    change bound (QBox.point q)<1 at hN
    grind
  · exact rational_mem q

private theorem cross_overlap (z w : Scalar) (he : z.val.Equiv w.val) (i j : Nat) :
    (z.val.compute i).Overlaps (w.val.compute j) := by
  let N := max i j
  have h := (compareAt_overlap_iff _ _ N N).mp (he N)
  have hz := valid_nestedIn z.property (Nat.le_max_left i j)
  have hw := valid_nestedIn w.property (Nat.le_max_right i j)
  dsimp [N] at h
  simp only [QBox.Overlaps,QBox.NestedIn,QComplex.le_def] at *
  grind

/-- Disk membership is a property of the value, not of a selected name. -/
theorem invariant (z w : Scalar) (he : z.val.Equiv w.val) : domain z ↔ domain w := by
  have forward : ∀ (z w : Scalar), z.val.Equiv w.val → domain z → domain w := by
    intro z w he
    rintro ⟨N,hN⟩
    let B := z.val.compute N
    let A := reBound B
    let C := imBound B
    let D := 8*(A+C+1)
    have hA : 0≤A := re_nonneg B
    have hC : 0≤C := im_nonneg B
    have hB : 0≤bound B := bound_nonneg B
    have hg : 0<1-bound B := by change bound B<1 at hN; grind
    have hD : 0<D := by dsimp [D]; grind
    let eps : QPos := ⟨(1-bound B)/D,Rat.mul_pos hg (Rat.inv_pos.mpr hD)⟩
    have hi := Rat.mul_inv_cancel D (Rat.ne_of_gt hD)
    have heD : eps.val*D=1-bound B := by
      dsimp [eps]; rw [Rat.div_def,Rat.mul_assoc,Rat.inv_mul_cancel D (Rat.ne_of_gt hD),Rat.mul_one]
    have he1 : eps.val≤1 := by
      have h := eps.property
      dsimp [D] at heD
      have hm := Rat.mul_le_mul_of_nonneg_left (show (1:Rat)≤8*(A+C+1) by grind) (Rat.le_of_lt h)
      grind
    obtain ⟨M,hM⟩ := w.property.2.2 eps
    refine ⟨M,?_⟩
    have hw := hM M (Nat.le_refl _)
    have ho := valid_ordered w.property M
    have hov := cross_overlap z w he N M
    have hb := coordinates B
    have hs : - (A+eps.val)≤(w.val.compute M).lo.re ∧ (w.val.compute M).hi.re≤A+eps.val ∧
        -(C+eps.val)≤(w.val.compute M).lo.im ∧ (w.val.compute M).hi.im≤C+eps.val := by
      simp only [QBox.Overlaps,QComplex.le_def] at hov
      change (w.val.compute M).hi.re-(w.val.compute M).lo.re≤eps.val ∧
        (w.val.compute M).hi.im-(w.val.compute M).lo.im≤eps.val at hw
      dsimp [B,A,C] at *
      grind
    have hc := bound_of_coordinates _ _ _ (by have := eps.property; grind) (by have := eps.property; grind) hs ho
    have hsq := rat_add_le_add (square_mono _ _ (re_nonneg _) hc.1) (square_mono _ _ (im_nonneg _) hc.2)
    have hess := Rat.mul_le_mul_of_nonneg_right he1 (Rat.le_of_lt eps.property)
    have htarget : (A+eps.val)*(A+eps.val)+(C+eps.val)*(C+eps.val)<1 := by
      have hbEq : bound B=A*A+C*C := rfl
      rw [hbEq] at heD hg
      dsimp [D] at heD
      grind
    change bound (w.val.compute M)<1
    unfold bound
    grind only
  exact ⟨forward z w he,forward w z (equiv_symm he)⟩

end ComputableAnalysis.ModularForms.EisensteinUnitDisk
