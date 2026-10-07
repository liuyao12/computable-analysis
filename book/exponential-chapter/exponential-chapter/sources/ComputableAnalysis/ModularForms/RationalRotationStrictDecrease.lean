import ComputableAnalysis.ModularForms.BisectionCoverPrinciple
import ComputableAnalysis.ModularForms.TwoPointStrictDecrease

/-! Global strict decrease on the rational quarter-angle chart, from actual
represented centers of bisection paths. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 2000000

def rationalAngleScalar (r : Rat) : Scalar := ⟨ofQComplex ⟨r,0⟩,ofQComplex_valid _⟩

def rationalRotationDecreaseGood (I : QInterval) : Prop :=
  I.lo<I.hi → 1≤I.lo → I.hi≤2 →
    (sub (angleRotationMap.eval (rationalAngleScalar I.hi) ⟨trivial,trivial⟩).val
      (angleRotationMap.eval (rationalAngleScalar I.lo) ⟨trivial,trivial⟩).val).realPart.Neg

theorem rationalRotationDecreaseGood_join (I : QInterval)
    (hl : rationalRotationDecreaseGood (bisectInterval I false))
    (hr : rationalRotationDecreaseGood (bisectInterval I true)) :
    rationalRotationDecreaseGood I := by
  intro hi h1 h2
  have hm := QInterval.midpoint_mem (Rat.le_of_lt hi)
  have hml : I.lo<I.midpoint := by dsimp [QInterval.midpoint]; grind only
  have hmh : I.midpoint<I.hi := by dsimp [QInterval.midpoint]; grind only
  have hl' := hl hml h1 (Rat.le_trans hm.2 h2)
  have hr' := hr hmh (Rat.le_trans h1 hm.1) h2
  exact strict_decrease_join
    (angleRotationMap.eval (rationalAngleScalar I.lo) ⟨trivial,trivial⟩)
    (angleRotationMap.eval (rationalAngleScalar I.midpoint) ⟨trivial,trivial⟩)
    (angleRotationMap.eval (rationalAngleScalar I.hi) ⟨trivial,trivial⟩) hl' hr'

theorem rational_rotation_strict_decrease (u v : Rat) (hu : 1≤u) (hv : v≤2)
    (huv : u<v) :
    (sub (angleRotationMap.eval (rationalAngleScalar v) ⟨trivial,trivial⟩).val
      (angleRotationMap.eval (rationalAngleScalar u) ⟨trivial,trivial⟩).val).realPart.Neg := by
  let I : QInterval := ⟨u,v⟩
  have hI : I.lo≤I.hi := Rat.le_of_lt huv
  have good : rationalRotationDecreaseGood I := by
    apply bisection_cover_principle rationalRotationDecreaseGood I rationalRotationDecreaseGood_join
    intro choice
    let A : BoundedAngle := {
      raw := bisectionReal I choice
      valid := bisectionReal_valid I hI choice
      bounds := fun n => by
        have hn := bisectionInterval_nested I hI choice 0 n (Nat.zero_le n)
        exact ⟨Rat.le_trans hu hn.1,Rat.le_trans hn.2.2 hv⟩ }
    obtain ⟨D,hD⟩ := two_point_strict_decrease angleRotationMap angleRotationMap_holomorphic
      A.scalar ⟨trivial,trivial⟩ A.rotation_derivative_negative
    let N := RationalMajorant.natRateStage I.width D
    let J := bisectionInterval I choice N
    have hw := bisectionInterval_width I choice N
    have hpos : 0<I.width := by change 0<v-u; grind only
    have hjpos : 0<J.width := by
      rw [hw]
      exact Rat.mul_pos hpos (Rat.pow_pos (by decide +kernel))
    let H : QPos := ⟨J.width,hjpos⟩
    have hH : H.val≤D.val := by
      have hb := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ N)
        (Rat.le_of_lt hpos)
      have hc := RationalMajorant.natRateStage_spec_of_le (Rat.le_of_lt hpos) D (Nat.le_refl N)
      change J.width≤D.val
      rw [hw]
      have he : I.width*((1:Rat)/(N+1:Nat))=I.width/(N+1:Nat) := by
        rw [Rat.div_def,Rat.div_def,Rat.one_mul]
      rw [he] at hb
      exact Rat.le_trans hb hc
    have ho := bisectionInterval_ordered I hI choice N
    have near (r : Rat) (hl : J.lo≤r) (hh : r≤J.hi) :
        Small (sub (rationalAngleScalar r).val A.scalar.val) H.val := by
      have hn := bisectionReal_stage_neighborhood I hI choice N r hl hh
      refine ⟨?_,?_,?_,?_⟩ <;> intro n m
      · have hb := hn.2 m n
        change (A.raw.compute m).lo≤r+J.width at hb
        change -J.width≤r+ -(A.raw.compute m).lo
        grind only
      · have hb := hn.1 m n
        change r-J.width≤(A.raw.compute n).hi at hb
        change r+ -(A.raw.compute n).hi≤J.width
        grind only
      · change -J.width≤(0:Rat)+ -0
        have hp := hjpos
        grind only
      · change (0:Rat)+ -0≤J.width
        have hp := hjpos
        grind only
    refine ⟨N,?_⟩
    intro hj h1 h2
    have hd : (sub (rationalAngleScalar J.hi).val (rationalAngleScalar J.lo).val).Equiv
        (ofQComplex ⟨H.val,0⟩) := by
      intro n
      apply (compareAt_overlap_iff _ _ n n).2
      simp only [rationalAngleScalar,sub,add,neg,ofQComplex,QBox.add,QBox.neg,QComplex.add,QComplex.neg,
        QBox.Overlaps,QComplex.le_def,H,QInterval.width,Rat.sub_eq_add_neg,Rat.neg_zero,Rat.add_zero]
      exact ⟨⟨Rat.le_refl,Rat.le_refl⟩,⟨Rat.le_refl,Rat.le_refl⟩⟩
    exact hD H (rationalAngleScalar J.hi) (rationalAngleScalar J.lo)
      ⟨trivial,trivial⟩ ⟨trivial,trivial⟩ hH (near J.hi ho Rat.le_refl)
      (near J.lo Rat.le_refl ho) hd
  exact good huv hu hv

end ComputableAnalysis.ModularForms
