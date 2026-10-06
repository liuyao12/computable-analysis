import ComputableAnalysis.ExponentialComputations.LogarithmIncrement
import ComputableAnalysis.RiemannHilbert.PrecisionSearch

/-! A literal positive segment from one to an arbitrary positive represented
real. A rational lower bound is found by a terminating box search. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000
abbrev RationalUnit := {t : Rat // 0 ≤ t ∧ t ≤ 1}

def eventually_positive (x : PositiveInput) : ∃ N, ∀ n, N≤n →
    decide (0<(x.val.val.compute n).lo)=true := by
  obtain ⟨N,hN⟩ := x.property
  refine ⟨N,fun n hn => ?_⟩
  have hh := (x.val.property.2.1 N n hn).1
  simp only [decide_eq_true_eq]
  change 0<(x.val.val.compute N).lo at hN
  grind only

def positiveStage (x : PositiveInput) : Nat := PrecisionSearch.firstFrom
  (fun n => decide (0<(x.val.val.compute n).lo)) (eventually_positive x) 0

theorem positiveStage_spec (x : PositiveInput) : 0<(x.val.val.compute (positiveStage x)).lo := by
  have h := (PrecisionSearch.firstFrom_spec
    (fun n => decide (0<(x.val.val.compute n).lo)) (eventually_positive x) 0).2
  simpa only [positiveStage,decide_eq_true_eq] using h

def segmentLower (x : PositiveInput) : QPos :=
  ⟨minRat 1 (x.val.val.compute (positiveStage x)).lo,by
    have h := positiveStage_spec x
    unfold minRat; split <;> grind only⟩

theorem segmentLower_le_one (x : PositiveInput) : (segmentLower x).val ≤ 1 := by
  dsimp [segmentLower]; unfold minRat; split <;> grind only

theorem segmentLower_le_input (x : PositiveInput) : (RealRaw.ofRat (segmentLower x).val).Le x.val.val := by
  intro n m
  have hh := RealRaw.le_refl _ x.val.property (positiveStage x) m
  change (segmentLower x).val ≤ (x.val.val.compute m).hi
  dsimp [segmentLower]; unfold minRat; split <;> grind only

theorem positive_of_lower (x : RealInput) (l : QPos) (hl : (RealRaw.ofRat l.val).Le x.val) : x.val.Pos := by
  let eps : QPos := ⟨l.val/2,by rw [Rat.div_def]; exact Rat.mul_pos l.property (by decide +kernel)⟩
  obtain ⟨N,hN⟩ := x.property.2.2 eps
  have hw := hN N (Nat.le_refl _)
  have hb := hl 0 N
  have hp := l.property
  refine ⟨N,?_⟩
  change l.val ≤ (x.val.compute N).hi at hb
  change (x.val.compute N).width ≤ l.val/2 at hw
  change 0 < (x.val.compute N).lo
  grind [QInterval.width]

def positiveSegment (x : PositiveInput) (t : RationalUnit) : RealInput :=
  ⟨RealRaw.add (RealRaw.ofRat (1-t.val)) (RealRaw.scaleRat t.val x.val.val),
    RealRaw.add_valid (RealRaw.ofRat_valid _) (RealRaw.scaleRat_valid x.val.property)⟩

theorem positiveSegment_lower (x : PositiveInput) (t : RationalUnit) :
    (RealRaw.ofRat (segmentLower x).val).Le (positiveSegment x t).val := by
  intro n m
  have hl := segmentLower_le_input x 0 m
  have h1 := segmentLower_le_one x
  have ht := t.property
  simp only [positiveSegment,RealRaw.add,RealRaw.addCompute,RealRaw.ofRat,RealRaw.scaleRat,
    RealRaw.scaleRatCompute,if_pos t.property.1]
  change (segmentLower x).val ≤ (1-t.val)+t.val*(x.val.val.compute m).hi
  change (segmentLower x).val ≤ (x.val.val.compute m).hi at hl
  have hprod := Rat.mul_le_mul_of_nonneg_left hl ht.1
  have hprod1 := Rat.mul_le_mul_of_nonneg_left h1 (show 0≤1-t.val by grind only)
  grind only

def positivePoint (x : PositiveInput) (t : RationalUnit) : PositiveInput :=
  ⟨positiveSegment x t,positive_of_lower _ (segmentLower x) (positiveSegment_lower x t)⟩

def segmentDisplacement (x : PositiveInput) : RealInput :=
  ⟨RealRaw.sub x.val.val (RealRaw.ofRat 1),RealRaw.sub_valid x.val.property (RealRaw.ofRat_valid _)⟩
def segmentBound (x : PositiveInput) : Rat := scalarBound (realAxis (segmentDisplacement x))
theorem segmentBound_pos (x : PositiveInput) : 0<segmentBound x := scalarBound_pos _

/-- The actual segment difference agrees with its affine displacement. -/
theorem positiveSegment_difference (x : PositiveInput) (u v : RationalUnit) :
    (sub (realAxis (positiveSegment x v)).val (realAxis (positiveSegment x u)).val).Equiv
      (scaleRat (v.val-u.val) (realAxis (segmentDisplacement x)).val) := by
  intro n
  apply (compareAt_overlap_iff _ _ n n).mpr
  have ho := RealRaw.interval_order_of_valid _ x.val.property n
  have hu := u.property
  have hv := v.property
  have hup := Rat.mul_le_mul_of_nonneg_left ho hu.1
  have hvp := Rat.mul_le_mul_of_nonneg_left ho hv.1
  simp only [realAxis,positiveSegment,segmentDisplacement,ofRealRaw,sub,add,neg,QBox.add,QBox.neg,
    QComplex.add,QComplex.neg,scaleRat,QBox.scaleRat,RealRaw.add,RealRaw.addCompute,RealRaw.ofRat,
    RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hu.1,if_pos hv.1,RealRaw.sub,RealRaw.subCompute]
  split <;> constructor <;> constructor <;> grind only

/-- Exact reciprocal comparison with the independently computed positive
real interval reciprocal. -/
theorem positive_inverse_agreement (c : PositiveInput) (l : QPos)
    (hl : (RealRaw.ofRat l.val).Le c.val.val) :
    (RepresentedReciprocal.inverse (realAxis c.val) (positive_real_nonzero c.val c.property)).val.Equiv
      (ofRealRaw (RealRaw.positiveReciprocal c.val.val l.val)) := by
  let r : Scalar := ⟨ofRealRaw (RealRaw.positiveReciprocal c.val.val l.val),
    ofRealRaw_valid _ (RealRaw.positiveReciprocal_valid _ _ c.val.property l.property (fun n => hl 0 n))⟩
  apply RepresentedReciprocal.inverse_unique (realAxis c.val) (positive_real_nonzero c.val c.property) r
  have hm := real_embedding_mul c.val.val (RealRaw.positiveReciprocal c.val.val l.val)
    c.val.property (RealRaw.positiveReciprocal_valid _ _ c.val.property l.property (fun n => hl 0 n))
  have hh := ofRealRaw_equiv_of_equiv (y := RealRaw.one)
    (RealRaw.mul_valid c.val.property (RealRaw.positiveReciprocal_valid _ _ c.val.property l.property (fun n => hl 0 n)))
    (RealRaw.ofRat_valid 1) (positiveReciprocal_mul_identity _ c.val.property l.val l.property hl)
  exact equiv_trans (mul_valid (realAxis c.val).property r.property)
    (ofRealRaw_valid _ (RealRaw.mul_valid c.val.property
      (RealRaw.positiveReciprocal_valid _ _ c.val.property l.property (fun n => hl 0 n))))
    (ofQComplex_valid _) hm hh

def segmentReciprocal (x : PositiveInput) (t : RationalUnit) : RealInput :=
  ⟨RealRaw.positiveReciprocal (positiveSegment x t).val (segmentLower x).val,
    RealRaw.positiveReciprocal_valid _ _ (positiveSegment x t).property (segmentLower x).property
      (fun n => positiveSegment_lower x t 0 n)⟩
def segmentIntegrandValue (x : PositiveInput) (t : RationalUnit) : RealInput :=
  ⟨RealRaw.mul (segmentDisplacement x).val (segmentReciprocal x t).val,
    RealRaw.mul_valid (segmentDisplacement x).property (segmentReciprocal x t).property⟩

end ComputableAnalysis.ExponentialComputations
