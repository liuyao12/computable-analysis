import ComputableAnalysis.ModularForms.DiskLambertAgreement
import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Derive values at every represented point of the open unit disk from
 primary rational Lambert samples and their quantitative continuity. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert RationalLambert CauchyTaylor DomainFunctions
set_option maxHeartbeats 1000000

def inputRadius (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) : QPos :=
  divideRadius (RepresentedCauchySum.error N)
    ⟨2*continuityBound (EisensteinUnitDisk.radius q hq) k+1, by
      have := continuityBound_nonneg _ (EisensteinUnitDisk.radius_pos q hq) (EisensteinUnitDisk.radius_lt_one q hq) k
      grind only⟩

def sampleStage (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) : Nat :=
  EisensteinUnitDisk.stage q hq+PrecisionSearch.stage q.val q.property (inputRadius q hq k N)
def samplePoint (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) : QComplex :=
  (q.val.compute (sampleStage q hq k N)).center

theorem sample_close (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) :
    Small (sub (ofQComplex (samplePoint q hq k N)) q.val) (inputRadius q hq k N).val := by
  let n := PrecisionSearch.stage q.val q.property (inputRadius q hq k N)
  have h := PrecisionSearch.stage_spec q.val q.property (inputRadius q hq k N)
  have hn := valid_nestedIn q.property (show n≤sampleStage q hq k N by dsimp [n,sampleStage]; omega)
  have hnlo : (q.val.compute n).lo.re≤(q.val.compute (sampleStage q hq k N)).lo.re ∧
      (q.val.compute n).lo.im≤(q.val.compute (sampleStage q hq k N)).lo.im := hn.1
  have hnhi : (q.val.compute (sampleStage q hq k N)).hi.re≤(q.val.compute n).hi.re ∧
      (q.val.compute (sampleStage q hq k N)).hi.im≤(q.val.compute n).hi.im := hn.2
  have hw : (q.val.compute (sampleStage q hq k N)).width≤(inputRadius q hq k N).val ∧
      (q.val.compute (sampleStage q hq k N)).height≤(inputRadius q hq k N).val := by
    change (q.val.compute n).hi.re-(q.val.compute n).lo.re≤_ ∧ (q.val.compute n).hi.im-(q.val.compute n).lo.im≤_ at h
    change (q.val.compute _).hi.re-(q.val.compute _).lo.re≤_ ∧ (q.val.compute _).hi.im-(q.val.compute _).lo.im≤_
    grind only
  exact RepresentedCauchySum.small_sub_symm _ _ _ (BoxApproximation.center_error q _ _
    (Rat.le_of_lt (inputRadius q hq k N).property) hw.1 hw.2)

theorem sample_inside (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) :
    InDisk (samplePoint q hq k N) (EisensteinUnitDisk.radius q hq) :=
  EisensteinUnitDisk.centers_inside q hq _ (by dsimp [sampleStage]; omega)

theorem sample_unit_disk (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) :
    QComplex.normSq (samplePoint q hq k N)<1 := by
  have h := sample_inside q hq k N
  have hr := EisensteinUnitDisk.radius_pos q hq
  have hr1 := EisensteinUnitDisk.radius_lt_one q hq
  have hh := Rat.mul_pos (show 0<1-EisensteinUnitDisk.radius q hq by grind only)
    (show 0<1+EisensteinUnitDisk.radius q hq by grind only)
  dsimp [InDisk] at h
  grind only

theorem inputRadius_le_error (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) :
    (inputRadius q hq k N).val≤(RepresentedCauchySum.error N).val := by
  have hL := continuityBound_nonneg _ (EisensteinUnitDisk.radius_pos q hq) (EisensteinUnitDisk.radius_lt_one q hq) k
  have hid := divideRadius_identity (RepresentedCauchySum.error N)
    (⟨2*continuityBound (EisensteinUnitDisk.radius q hq) k+1,by grind only⟩ : QPos)
  have hpos := (inputRadius q hq k N).property
  change (2*continuityBound (EisensteinUnitDisk.radius q hq) k+1)*(inputRadius q hq k N).val=_ at hid
  have hm := Rat.mul_le_mul_of_nonneg_right (show (1:Rat)≤2*continuityBound (EisensteinUnitDisk.radius q hq) k+1 by grind only) (Rat.le_of_lt hpos)
  grind only

theorem inputRadius_antitone (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k m n : Nat) (hmn : m≤n) :
    (inputRadius q hq k n).val≤(inputRadius q hq k m).val :=
  Rat.mul_le_mul_of_nonneg_right (RepresentedCauchySum.error_antitone m n hmn)
    (Rat.le_of_lt (Rat.inv_pos.mpr (by
      have := continuityBound_nonneg _ (EisensteinUnitDisk.radius_pos q hq) (EisensteinUnitDisk.radius_lt_one q hq) k
      grind only)))

theorem rational_small_norm (p q : QComplex) (H : Rat) (h : Small (sub (ofQComplex p) (ofQComplex q)) H) :
    (QComplex.sub p q).normBound≤2*H := by
  have hb := Small.congr (sub_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) (sub_constants p q) h
  have h1 := hb.1 0 0
  have h2 := hb.2.1 0 0
  have h3 := hb.2.2.1 0 0
  have h4 := hb.2.2.2 0 0
  change -H≤(QComplex.sub p q).re at h1
  change (QComplex.sub p q).re≤H at h2
  change -H≤(QComplex.sub p q).im at h3
  change (QComplex.sub p q).im≤H at h4
  unfold QComplex.normBound qabs
  split <;> split <;> grind only

def sampledValue (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) : ComplexRaw :=
  rationalValue (samplePoint q hq k N) k

theorem sampledValue_valid (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) : (sampledValue q hq k N).Valid :=
  rationalValue_valid _ (sample_unit_disk q hq k N) k

theorem samples_cauchy (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k m n : Nat) (hmn : m≤n) :
    Small (sub (sampledValue q hq k n) (sampledValue q hq k m)) (2*(RepresentedCauchySum.error m).val) := by
  have hc := triangle _ _ _ (ofQComplex_valid _) q.property (ofQComplex_valid _) _ _
    (sample_close q hq k n) (RepresentedCauchySum.small_sub_symm _ _ _ (sample_close q hq k m))
  have hdist := rational_small_norm _ _ _ hc
  have h := rational_lipschitz _ _ _ (EisensteinUnitDisk.radius_pos q hq) (EisensteinUnitDisk.radius_lt_one q hq)
    (sample_inside q hq k n) (sample_inside q hq k m) k
  apply h.mono
  have hL := continuityBound_nonneg _ (EisensteinUnitDisk.radius_pos q hq) (EisensteinUnitDisk.radius_lt_one q hq) k
  have hm := Rat.mul_le_mul_of_nonneg_left hdist hL
  have ha := inputRadius_antitone q hq k m n hmn
  have hid := divideRadius_identity (RepresentedCauchySum.error m)
    (⟨2*continuityBound (EisensteinUnitDisk.radius q hq) k+1,by grind only⟩ : QPos)
  change (2*continuityBound (EisensteinUnitDisk.radius q hq) k+1)*(inputRadius q hq k m).val=_ at hid
  have hp := (inputRadius q hq k m).property
  have hmul := Rat.mul_le_mul_of_nonneg_left ha (show 0≤2*continuityBound (EisensteinUnitDisk.radius q hq) k by grind only)
  grind only

def value (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k : Nat) : ComplexRaw :=
  RepresentedCauchySum.value (sampledValue q hq k) (sampledValue_valid q hq k)
    (fun N => 2*(RepresentedCauchySum.error N).val)

theorem value_valid (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k : Nat) : (value q hq k).Valid :=
  RepresentedCauchySum.value_valid _ _ _ (RepresentedCauchySum.twice_shrinks _ RepresentedCauchySum.error_shrinks)
    (samples_cauchy q hq k)

theorem value_close_sample (q : Scalar) (hq : EisensteinUnitDisk.domain q) (k N : Nat) :
    Small (sub (value q hq k) (sampledValue q hq k N)) (2*(RepresentedCauchySum.error N).val) :=
  RepresentedCauchySum.value_close_prefix _ _ _ (samples_cauchy q hq k) N

private theorem self_zero (q z : Scalar) (he : q.val.Equiv z.val) : Small (sub q.val z.val) 0 := by
  have hs : (sub q.val z.val).Equiv zero := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := sub_valid q.property z.property) (hright := ofQComplex_valid _)
    have h := ComplexRawQuotient.ofRaw_eq_ofRaw (hleft := q.property) (hright := z.property) he
    change ComplexRawQuotient.ofRaw q.val q.property-ComplexRawQuotient.ofRaw z.val z.property=0
    rw [h]; grind only
  exact Small.congr (ofQComplex_valid _) (sub_valid q.property z.property) (equiv_symm hs) (Small.zero (by decide +kernel))

theorem value_congr (q z : Scalar) (hq : EisensteinUnitDisk.domain q) (hz : EisensteinUnitDisk.domain z)
    (he : q.val.Equiv z.val) (k : Nat) : (value q hq k).Equiv (value z hz k) := by
  let r := max (EisensteinUnitDisk.radius q hq) (EisensteinUnitDisk.radius z hz)
  have hr : 0<r := by have := EisensteinUnitDisk.radius_pos q hq; dsimp [r]; grind
  have hr1 : r<1 := by have := EisensteinUnitDisk.radius_lt_one q hq; have := EisensteinUnitDisk.radius_lt_one z hz; dsimp [r]; grind
  have hL := continuityBound_nonneg r hr hr1 k
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => (4+4*continuityBound r k)*(RepresentedCauchySum.error N).val)
    (SeriesLimitLaws.shrinks_scale _ RepresentedCauchySum.error_shrinks _ (by grind only))
  intro N
  have hp : InDisk (samplePoint q hq k N) r := Rat.le_trans (sample_inside q hq k N)
    (EisensteinUnitDisk.square_mono _ _ (Rat.le_of_lt (EisensteinUnitDisk.radius_pos q hq)) (by dsimp [r]; grind))
  have hz' : InDisk (samplePoint z hz k N) r := Rat.le_trans (sample_inside z hz k N)
    (EisensteinUnitDisk.square_mono _ _ (Rat.le_of_lt (EisensteinUnitDisk.radius_pos z hz)) (by dsimp [r]; grind))
  have h1 := triangle _ _ _ (ofQComplex_valid _) q.property z.property _ _ (sample_close q hq k N) (self_zero q z he)
  have h2 := triangle _ _ _ (ofQComplex_valid _) z.property (ofQComplex_valid _) _ _ h1
    (RepresentedCauchySum.small_sub_symm _ _ _ (sample_close z hz k N))
  have hd := rational_small_norm _ _ _ h2
  have hm := Rat.mul_le_mul_of_nonneg_left hd hL
  have heq := inputRadius_le_error q hq k N
  have hez := inputRadius_le_error z hz k N
  have hsum : 2*((inputRadius q hq k N).val+0+(inputRadius z hz k N).val)≤4*(RepresentedCauchySum.error N).val := by grind only
  have hsumL := Rat.mul_le_mul_of_nonneg_left hsum hL
  have hs := (rational_lipschitz _ _ r hr hr1 hp hz' k).mono (show continuityBound r k*(QComplex.sub (samplePoint q hq k N) (samplePoint z hz k N)).normBound≤4*continuityBound r k*(RepresentedCauchySum.error N).val by dsimp [r] at hL hm; grind only)
  have ha := triangle _ _ _ (value_valid q hq k) (sampledValue_valid q hq k N) (sampledValue_valid z hz k N) _ _ (value_close_sample q hq k N) hs
  have hb := triangle _ _ _ (value_valid q hq k) (sampledValue_valid z hz k N) (value_valid z hz k) _ _ ha
    (RepresentedCauchySum.small_sub_symm _ _ _ (value_close_sample z hz k N))
  exact hb.mono (by grind only)

theorem value_rational_agreement (q : QComplex) (hq : QComplex.normSq q<1) (k : Nat) :
    (value (point q) (EisensteinUnitDisk.rational_mem q hq) k).Equiv (rationalValue q k) := by
  have hs : ∀N, samplePoint (point q) (EisensteinUnitDisk.rational_mem q hq) k N=q := by
    intro N
    change (QBox.point q).center=q
    cases q
    simp only [QBox.center,QBox.point,QComplex.mk.injEq]
    constructor <;> grind only
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => 2*(RepresentedCauchySum.error N).val)
    (RepresentedCauchySum.twice_shrinks _ RepresentedCauchySum.error_shrinks)
  intro N
  have h := value_close_sample (point q) (EisensteinUnitDisk.rational_mem q hq) k N
  dsimp [sampledValue] at h
  rw [hs] at h
  exact h.mono (by grind only)

end ComputableAnalysis.ModularForms.DiskLambert
