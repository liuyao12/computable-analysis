import ComputableAnalysis.ModularForms.HomogeneousZeroTransferNeighborhood

/-! Exact homogeneous zero propagation along a supplied covered represented segment. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 2000000

def segmentZeroTransferGood (f : DomainFunctions.Map) (p q : Scalar)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (I : QInterval) : Prop :=
  ∀ hI : I.lo≤I.hi, ∀ h0 : 0≤I.lo, ∀ h1 : I.hi≤1,
    (f.eval (AffineSegment.point p q I.lo)
      (affineSegment_domain_at f p q hdom I.lo h0 (Rat.le_trans hI h1))).val.Equiv zero →
    (f.eval (AffineSegment.point p q I.hi)
      (affineSegment_domain_at f p q hdom I.hi (Rat.le_trans h0 hI) h1)).val.Equiv zero

theorem segmentZeroTransferGood_join (f : DomainFunctions.Map) (p q : Scalar)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t)) (I : QInterval)
    (hl : segmentZeroTransferGood f p q hdom (bisectInterval I false))
    (hr : segmentZeroTransferGood f p q hdom (bisectInterval I true)) :
    segmentZeroTransferGood f p q hdom I := by
  intro hI h0 h1 hz
  have bl := bisectInterval_bounds I hI false
  have br := bisectInterval_bounds I hI true
  exact hr br.2.1 (Rat.le_trans h0 br.1) (Rat.le_trans br.2.2 h1)
    (hl bl.2.1 (Rat.le_trans h0 bl.1) (Rat.le_trans bl.2.2 h1) hz)

theorem homogeneous_segment_zero (f g : DomainFunctions.Map)
    (hf : Holomorphic f) (hg : Holomorphic g) (hfg : ∀ z, f.domain z → g.domain z)
    (heq : ∀ z hz, (hf.derivative z hz).val.Equiv
      (mul (g.eval z (hfg z hz)).val (f.eval z hz).val))
    (p q : Scalar) (hp : f.domain p) (hq : f.domain q)
    (hdom : ∀ t : UnitInterval.Point, f.domain (RepresentedAffineSegment.point p q t))
    (hzero : (f.eval p hp).val.Equiv zero) : (f.eval q hq).val.Equiv zero := by
  let v := AffineSegment.displacement p q
  let B := LocalODE.boxCoordinateBound (v.val.compute 0)
  let W : QPos := ⟨B+1,by have h := LocalODE.boxCoordinateBound_nonneg (v.val.compute 0); grind only⟩
  have hd : Small v.val W.val := (LocalODE.small_from_box v.val v.property 0).mono (by
    have h := LocalODE.boxCoordinateBound_nonneg (v.val.compute 0)
    dsimp [W,B]
    grind only)
  have good : segmentZeroTransferGood f p q hdom ⟨0,1⟩ := by
    apply bisection_cover_principle (segmentZeroTransferGood f p q hdom) ⟨0,1⟩
      (segmentZeroTransferGood_join f p q hdom)
    intro choice
    have hx := bisectionReal_enclosed (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0
    let t : UnitInterval.Point := ⟨bisectionReal ⟨0,1⟩ choice,
      bisectionReal_valid ⟨0,1⟩ (by decide +kernel) choice,hx.1,hx.2⟩
    let a := RepresentedAffineSegment.point p q t
    obtain ⟨D,hD⟩ := homogeneous_zero_transfer_neighborhood f g hf hg hfg heq a (hdom t)
    let N := RationalMajorant.natRateStage (2*W.val) D
    let J := bisectionInterval ⟨0,1⟩ choice N
    have hw : J.width=((1:Rat)/2)^N := by
      have h := bisectionInterval_width (⟨0,1⟩ : QInterval) choice N
      simpa only [QInterval.width,show (1:Rat)-0=1 by decide +kernel,Rat.one_mul] using h
    have hwpos : 0<J.width := by rw [hw]; exact Rat.pow_pos (by decide +kernel)
    have h2W : 0<2*W.val := Rat.mul_pos (by decide +kernel) W.property
    let H : QPos := ⟨2*W.val*J.width,Rat.mul_pos h2W hwpos⟩
    have hH : H.val≤D.val := by
      have hp := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ N)
        (Rat.le_of_lt h2W)
      have hr := RationalMajorant.natRateStage_spec_of_le (Rat.le_of_lt h2W) D (Nat.le_refl N)
      change 2*W.val*J.width≤D.val
      rw [hw]
      have he : 2*W.val*((1:Rat)/(N+1:Nat))=2*W.val/(N+1:Nat) := by
        rw [Rat.div_def,Rat.div_def,Rat.one_mul]
      rw [he] at hp
      exact Rat.le_trans hp hr
    have ho := bisectionInterval_ordered (⟨0,1⟩ : QInterval) (by decide +kernel) choice N
    have he := bisectionInterval_nested (⟨0,1⟩ : QInterval) (by decide +kernel) choice 0 N (Nat.zero_le N)
    have near (u : Rat) (hulo : J.lo≤u) (huhi : u≤J.hi) :
        Small (sub (AffineSegment.point p q u).val a.val) D.val := by
      have hn := bisectionReal_stage_neighborhood (⟨0,1⟩ : QInterval)
        (by decide +kernel) choice N u hulo huhi
      exact (representedAffine_rational_neighborhood p q t u
        (Rat.le_trans he.1 hulo) (Rat.le_trans huhi he.2.2) W.val J.width
        (Rat.le_of_lt W.property) (Rat.le_of_lt hwpos) hd hn.1 hn.2).mono hH
    refine ⟨N,?_⟩
    intro hJ hJ0 hJ1 hz
    exact hD (AffineSegment.point p q J.lo) (AffineSegment.point p q J.hi)
      (affineSegment_domain_at f p q hdom J.lo hJ0 (Rat.le_trans hJ hJ1))
      (affineSegment_domain_at f p q hdom J.hi (Rat.le_trans hJ0 hJ) hJ1)
      (near J.lo Rat.le_refl ho) (near J.hi ho Rat.le_refl) hz
  have hstart := equiv_trans
    (f.eval (AffineSegment.point p q 0) (affineSegment_domain_at f p q hdom 0 (by decide +kernel) (by decide +kernel))).property
    (f.eval p hp).property (ofQComplex_valid _)
    (f.eval_congr _ _ _ _ (AffineSegment.point_zero p q)) hzero
  have hend := good (by decide +kernel) (by decide +kernel) (by decide +kernel) hstart
  exact equiv_trans (f.eval q hq).property
    (f.eval (AffineSegment.point p q 1) (affineSegment_domain_at f p q hdom 1 (by decide +kernel) (by decide +kernel))).property
    (ofQComplex_valid _) (equiv_symm (f.eval_congr _ _ _ _ (AffineSegment.point_one p q))) hend

end ComputableAnalysis.ModularForms
