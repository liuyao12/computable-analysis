import ComputableAnalysis.ModularForms.DiskLambertLift
import ComputableAnalysis.ModularForms.RationalLambertLift

/-! Exact compatibility with all existing small-chart represented evaluations. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor DomainFunctions
set_option maxHeartbeats 1000000

theorem small_mem (q : Scalar) (hq : Small q.val ((1:Rat)/64)) : EisensteinUnitDisk.domain q := by
  let eps : QPos := ⟨1/64,by decide +kernel⟩
  let N := PrecisionSearch.stage q.val q.property eps
  have hn := PrecisionSearch.stage_spec q.val q.property eps
  have h1 := hq.1 0 N
  have h2 := hq.2.1 N 0
  have h3 := hq.2.2.1 0 N
  have h4 := hq.2.2.2 N 0
  have hb : -((1:Rat)/32)≤(q.val.compute N).lo.re ∧ (q.val.compute N).hi.re≤(1:Rat)/32 ∧
      -((1:Rat)/32)≤(q.val.compute N).lo.im ∧ (q.val.compute N).hi.im≤(1:Rat)/32 := by
    change -((1:Rat)/64)≤(q.val.compute N).hi.re at h1
    change (q.val.compute N).lo.re≤(1:Rat)/64 at h2
    change -((1:Rat)/64)≤(q.val.compute N).hi.im at h3
    change (q.val.compute N).lo.im≤(1:Rat)/64 at h4
    change (q.val.compute N).hi.re-(q.val.compute N).lo.re≤(1:Rat)/64 ∧
      (q.val.compute N).hi.im-(q.val.compute N).lo.im≤(1:Rat)/64 at hn
    grind only
  have h := EisensteinUnitDisk.bound_of_coordinates _ (1/32) (1/32) (by decide +kernel) (by decide +kernel) hb (valid_ordered q.property N)
  have hr := EisensteinUnitDisk.square_mono _ _ (EisensteinUnitDisk.re_nonneg _) h.1
  have hi := EisensteinUnitDisk.square_mono _ _ (EisensteinUnitDisk.im_nonneg _) h.2
  refine ⟨N,?_⟩
  dsimp [EisensteinUnitDisk.bound]
  grind only

theorem wide_mem (q : Scalar) (hq : wideLambertFifthDomain q) : EisensteinUnitDisk.domain q :=
  small_mem q (LocalODE.interior_bound _ _ hq)

private theorem old_sample_disk (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    InDisk (RationalLambert.samplePoint q hq N) (1/32) := by
  have hs := LocalODE.interior_bound _ _ (RationalLambert.sample_inside q hq N)
  have h1 := hs.1 0 0
  have h2 := hs.2.1 0 0
  have h3 := hs.2.2.1 0 0
  have h4 := hs.2.2.2 0 0
  let p := RationalLambert.samplePoint q hq N
  change -((1:Rat)/64)≤p.re at h1
  change p.re≤(1:Rat)/64 at h2
  change -((1:Rat)/64)≤p.im at h3
  change p.im≤(1:Rat)/64 at h4
  have hr := Rat.mul_nonneg (show 0≤(1:Rat)/64-p.re by grind only) (show 0≤(1:Rat)/64+p.re by grind only)
  have hi := Rat.mul_nonneg (show 0≤(1:Rat)/64-p.im by grind only) (show 0≤(1:Rat)/64+p.im by grind only)
  dsimp [InDisk,QComplex.normSq]
  change p.re*p.re+p.im*p.im≤_
  grind only

private theorem old_input_error (q : Scalar) (hq : wideLambertFifthDomain q) (N : Nat) :
    (RationalLambert.inputRadius q hq N).val≤(RepresentedCauchySum.error N).val := by
  have hm := Rat.le_trans (minRadius_right (LocalODE.interiorRadius (1/64) q hq) _)
    (minRadius_right (⟨1,by decide +kernel⟩ : QPos) (divideRadius (RepresentedCauchySum.error N) ⟨139264,by decide +kernel⟩))
  have hx := Rat.mul_le_mul_of_nonneg_left hm (by decide +kernel : (0:Rat)≤139264)
  rw [divideRadius_identity (RepresentedCauchySum.error N) (⟨139264,by decide +kernel⟩ : QPos)] at hx
  have hpos := (RationalLambert.inputRadius q hq N).property
  change 139264*(RationalLambert.inputRadius q hq N).val≤_ at hx
  have hy := Rat.mul_le_mul_of_nonneg_right (by decide +kernel : (1:Rat)≤139264) (Rat.le_of_lt hpos)
  grind only

theorem value_legacy_agreement (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) :
    (value q (wide_mem q hq) k).Equiv (comparison q (LocalODE.interior_bound _ _ hq) k).val := by
  let hD := wide_mem q hq
  let r := max (EisensteinUnitDisk.radius q hD) (1/32:Rat)
  have hr : 0<r := by have := EisensteinUnitDisk.radius_pos q hD; dsimp [r]; grind
  have hr1 : r<1 := by
    have := EisensteinUnitDisk.radius_lt_one q hD
    have hrat : (1/32:Rat)<1 := by decide +kernel
    dsimp [r]
    grind
  have hL := continuityBound_nonneg r hr hr1 k
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => (3+4*continuityBound r k)*(RepresentedCauchySum.error N).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks _ (by grind only))
  intro N
  let p := RationalLambert.samplePoint q hq N
  have hp : InDisk p r := Rat.le_trans (old_sample_disk q hq N)
    (EisensteinUnitDisk.square_mono _ _ (by decide +kernel) (by dsimp [r]; grind))
  have hz : InDisk (samplePoint q hD k N) r := Rat.le_trans (sample_inside q hD k N)
    (EisensteinUnitDisk.square_mono _ _ (Rat.le_of_lt (EisensteinUnitDisk.radius_pos q hD)) (by dsimp [r]; grind))
  have hdist := triangle _ _ _ (ofQComplex_valid _) q.property (ofQComplex_valid _) _ _
    (sample_close q hD k N) (RepresentedCauchySum.small_sub_symm _ _ _ (RationalLambert.sample_close q hq N))
  have hb := rational_small_norm _ _ _ hdist
  have he1 := inputRadius_le_error q hD k N
  have he2 := old_input_error q hq N
  have hsum : 2*((inputRadius q hD k N).val+(RationalLambert.inputRadius q hq N).val)≤4*(RepresentedCauchySum.error N).val := by grind only
  have hml := Rat.mul_le_mul_of_nonneg_left hb hL
  have hs := Rat.mul_le_mul_of_nonneg_left hsum hL
  have hdiff := (rational_lipschitz _ p r hr hr1 hz hp k).mono (show continuityBound r k*(QComplex.sub (samplePoint q hD k N) p).normBound≤4*continuityBound r k*(RepresentedCauchySum.error N).val by grind only)
  have hsmall := LocalODE.interior_bound _ _ (RationalLambert.sample_inside q hq N)
  have hagree := rational_legacy_agreement p hsmall k hk
  have hcp := RationalLambert.input_error q hq k N
  have hcp' := Small.congr
    (sub_valid (comparison (point p) hsmall k).property (comparison q (LocalODE.interior_bound _ _ hq) k).property)
    (sub_valid (rationalValue_valid p (by have := old_sample_disk q hq N; change QComplex.normSq p≤(1/32:Rat)*(1/32:Rat) at this; grind only) k)
      (comparison q (LocalODE.interior_bound _ _ hq) k).property)
    (FunctionTheory.sub_congr (equiv_symm hagree) (equiv_refl _ (comparison q (LocalODE.interior_bound _ _ hq) k).property)) hcp
  have h1 := triangle _ _ _ (value_valid q hD k) (sampledValue_valid q hD k N)
    (rationalValue_valid p (by have := old_sample_disk q hq N; change QComplex.normSq p≤(1/32:Rat)*(1/32:Rat) at this; grind only) k)
    _ _ (value_close_sample q hD k N) hdiff
  have h2 := triangle _ _ _ (value_valid q hD k) (rationalValue_valid p (by have := old_sample_disk q hq N; change QComplex.normSq p≤(1/32:Rat)*(1/32:Rat) at this; grind only) k)
    (comparison q (LocalODE.interior_bound _ _ hq) k).property _ _ h1 hcp'
  exact h2.mono (by grind only)

end ComputableAnalysis.ModularForms.DiskLambert
