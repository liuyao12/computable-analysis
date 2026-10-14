import ComputableAnalysis.ModularForms.DiskLambertLift
import ComputableAnalysis.RiemannHilbert.RectangularPoleSearch

/-! Rational rectangles compactly inside the disk provide local analytic
patches. Every full-disk name has such a patch; its rational samples eventually
lie in the same rectangle. -/
namespace ComputableAnalysis.ModularForms.EisensteinDiskPatches
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RectangularContour CauchyTaylor
set_option maxHeartbeats 1000000

structure Patch where
  A : Rat
  C : Rat
  re_nonneg : 0≤A
  im_nonneg : 0≤C
  inside : A*A+C*C<1

def rectangle (P : Patch) : QInterval × QInterval := (⟨-P.A,P.A⟩,⟨-P.C,P.C⟩)
def domain (P : Patch) := RectangularPoleSearch.domain true (rectangle P)
def openData (P : Patch) : ScalarTopology.OpenData (domain P) := RectangularPoleSearch.openData true (rectangle P)
def radius (P : Patch) : Rat := (1+P.A*P.A+P.C*P.C)/2

theorem radius_pos (P : Patch) : 0<(radius P) := by
  have := rat_square_nonneg_basic P.A; have := rat_square_nonneg_basic P.C
  dsimp [radius]; grind only
theorem radius_lt_one (P : Patch) : (radius P)<1 := by have := P.inside; dsimp [radius]; grind only
theorem radius_square (P : Patch) : P.A*P.A+P.C*P.C≤(radius P)*(radius P) := by
  have := rat_square_nonneg_basic (1-(P.A*P.A+P.C*P.C)); dsimp [radius]; grind only
theorem rational_inside (P : Patch) (p : QComplex)
    (h : -P.A≤p.re ∧ p.re≤P.A ∧ -P.C≤p.im ∧ p.im≤P.C) : InDisk p (radius P) := by
  have hr := Rat.mul_nonneg (show 0≤P.A-p.re by grind only) (show 0≤P.A+p.re by grind only)
  have hi := Rat.mul_nonneg (show 0≤P.C-p.im by grind only) (show 0≤P.C+p.im by grind only)
  have := radius_square P
  dsimp [InDisk,QComplex.normSq]; grind only

theorem included (P : Patch) (q : Scalar) (hq : (domain P) q) : EisensteinUnitDisk.domain q := by
  obtain ⟨N,hN⟩ := RectangularPoleSearch.eventually_inside (rectangle P) q hq
  refine ⟨N,?_⟩
  have h := hN N (Nat.le_refl _)
  have hc := EisensteinUnitDisk.bound_of_coordinates (q.val.compute N) P.A P.C P.re_nonneg P.im_nonneg
    (by dsimp [RectangularPoleSearch.InsideBox,rectangle] at h; grind only) (valid_ordered q.property N)
  have hb := rat_add_le_add
    (EisensteinUnitDisk.square_mono _ _ (EisensteinUnitDisk.re_nonneg _) hc.1)
    (EisensteinUnitDisk.square_mono _ _ (EisensteinUnitDisk.im_nonneg _) hc.2)
  have := P.inside
  dsimp [EisensteinUnitDisk.bound]; grind only

theorem samples_eventually_inside (P : Patch) (q : Scalar) (hq : (domain P) q) (hd : EisensteinUnitDisk.domain q) (k : Nat) :
    ∃N, ∀n, N≤n → InDisk (DiskLambert.samplePoint q hd k n) (radius P) := by
  obtain ⟨D,hD⟩ := (show RectanglePoleInterior (rectangle P) q from hq)
  let eps := halfError D
  obtain ⟨M,hM⟩ := q.property.2.2 eps
  obtain ⟨N,hN⟩ := RepresentedCauchySum.error_shrinks eps
  refine ⟨N,fun n hn => (rational_inside P) _ ?_⟩
  have hclose := (DiskLambert.sample_close q hd k n).mono
    (Rat.le_trans (DiskLambert.inputRadius_le_error q hd k n) (hN n hn))
  have h1 := hclose.1 0 M
  have h2 := hclose.2.1 M 0
  have h3 := hclose.2.2.1 0 M
  have h4 := hclose.2.2.2 M 0
  have hb1 := hD.1 0 M
  have hb2 := hD.2.1 M 0
  have hb3 := hD.2.2.1 0 M
  have hb4 := hD.2.2.2 M 0
  have hw := hM M (Nat.le_refl _)
  change -eps.val≤(DiskLambert.samplePoint q hd k n).re+ -(q.val.compute M).lo.re at h1
  change (DiskLambert.samplePoint q hd k n).re+ -(q.val.compute M).hi.re≤eps.val at h2
  change -eps.val≤(DiskLambert.samplePoint q hd k n).im+ -(q.val.compute M).lo.im at h3
  change (DiskLambert.samplePoint q hd k n).im+ -(q.val.compute M).hi.im≤eps.val at h4
  change -P.A+D.val≤(q.val.compute M).hi.re at hb1
  change (q.val.compute M).lo.re≤P.A-D.val at hb2
  change -P.C+D.val≤(q.val.compute M).hi.im at hb3
  change (q.val.compute M).lo.im≤P.C-D.val at hb4
  change (q.val.compute M).hi.re-(q.val.compute M).lo.re≤eps.val ∧
    (q.val.compute M).hi.im-(q.val.compute M).lo.im≤eps.val at hw
  have := halfError_identity D
  change 2*eps.val=D.val at this
  constructor
  · grind only
  constructor
  · grind only
  constructor <;> grind only

theorem covers (q : Scalar) (hq : EisensteinUnitDisk.domain q) : ∃P : Patch, (domain P) q := by
  let B := q.val.compute (EisensteinUnitDisk.stage q hq)
  let A := EisensteinUnitDisk.reBound B
  let C := EisensteinUnitDisk.imBound B
  let D := 8*(A+C+1)
  have hA : 0≤A := EisensteinUnitDisk.re_nonneg B
  have hC : 0≤C := EisensteinUnitDisk.im_nonneg B
  have hb : A*A+C*C<1 := EisensteinUnitDisk.stage_spec q hq
  have hg : 0<1-(A*A+C*C) := by grind only
  have hD : 0<D := by dsimp [D]; grind only
  let eps : QPos := ⟨(1-(A*A+C*C))/D,Rat.mul_pos hg (Rat.inv_pos.mpr hD)⟩
  have he : eps.val*D=1-(A*A+C*C) := by
    dsimp [eps]; rw [Rat.div_def,Rat.mul_assoc,Rat.inv_mul_cancel D (Rat.ne_of_gt hD),Rat.mul_one]
  have he1 : eps.val≤1 := by
    have hm := Rat.mul_le_mul_of_nonneg_left (show (1:Rat)≤D by dsimp [D]; grind only) (Rat.le_of_lt eps.property)
    have := rat_square_nonneg_basic A; have := rat_square_nonneg_basic C; grind only
  have he2 := Rat.mul_le_mul_of_nonneg_right he1 (Rat.le_of_lt eps.property)
  have hp : (A+eps.val)*(A+eps.val)+(C+eps.val)*(C+eps.val)<1 := by dsimp [D] at he; grind only
  let P : Patch := ⟨A+eps.val,C+eps.val,by have := eps.property; grind only,by have := eps.property; grind only,hp⟩
  refine ⟨P,eps,?_⟩
  have hc := EisensteinUnitDisk.coordinates B
  have lower (j : Nat) : -A≤(q.val.compute j).hi.re ∧ -C≤(q.val.compute j).hi.im := by
    have hn := valid_nestedIn q.property (Nat.le_max_left (EisensteinUnitDisk.stage q hq) j)
    have hj := valid_nestedIn q.property (Nat.le_max_right (EisensteinUnitDisk.stage q hq) j)
    have ho := valid_ordered q.property (max (EisensteinUnitDisk.stage q hq) j)
    simp only [QBox.NestedIn,QBox.Ordered,QComplex.le_def] at hn hj ho
    change -A≤B.lo.re ∧ B.hi.re≤A ∧ -C≤B.lo.im ∧ B.hi.im≤C at hc
    grind only
  have upper (i : Nat) : (q.val.compute i).lo.re≤A ∧ (q.val.compute i).lo.im≤C := by
    have hn := valid_nestedIn q.property (Nat.le_max_left (EisensteinUnitDisk.stage q hq) i)
    have hj := valid_nestedIn q.property (Nat.le_max_right (EisensteinUnitDisk.stage q hq) i)
    have ho := valid_ordered q.property (max (EisensteinUnitDisk.stage q hq) i)
    simp only [QBox.NestedIn,QBox.Ordered,QComplex.le_def] at hn hj ho
    change -A≤B.lo.re ∧ B.hi.re≤A ∧ -C≤B.lo.im ∧ B.hi.im≤C at hc
    grind only
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    change -(A+eps.val)+eps.val≤(q.val.compute j).hi.re
    have := lower j
    grind only
  · intro i j
    change (q.val.compute i).lo.re≤A+eps.val-eps.val
    have := upper i
    grind only
  · intro i j
    change -(C+eps.val)+eps.val≤(q.val.compute j).hi.im
    have := lower j
    grind only
  · intro i j
    change (q.val.compute i).lo.im≤C+eps.val-eps.val
    have := upper i
    grind only
end ComputableAnalysis.ModularForms.EisensteinDiskPatches
