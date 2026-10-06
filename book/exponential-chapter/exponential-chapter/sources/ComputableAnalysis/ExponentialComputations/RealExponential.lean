import ComputableAnalysis.ModularForms.ExponentialSquaredMagnitude
import ComputableAnalysis.ModularForms.ExponentialFiberRealPart
import ComputableAnalysis.ModularForms.ScalarSquaredMagnitudeBounds

/-! The real exponential API on arbitrary valid represented inputs. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert LocalODE DomainFunctions ModularForms
set_option maxHeartbeats 1000000

theorem real_embedding_congr {x y : RealRaw} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    (ofRealRaw x).Equiv (ofRealRaw y) := ofRealRaw_equiv_of_equiv hx hy h

abbrev RealInput := {x : RealRaw // x.Valid}
def realAxis (x : RealInput) : Scalar := ⟨ofRealRaw x.val,ofRealRaw_valid _ x.property⟩
def exp (x : RealInput) : RealInput :=
  ⟨(entireExponentialValue (realAxis x)).val.realPart,realPart_valid (entireExponentialValue (realAxis x)).property⟩

theorem exp_congr (x y : RealInput) (h : x.val.Equiv y.val) : (exp x).val.Equiv (exp y).val :=
  realPart_equiv (entireExponentialValue_congr (realAxis x) (realAxis y) (real_embedding_congr x.property y.property h))

theorem exp_real_embedding (x : RealInput) :
    (entireExponentialValue (realAxis x)).val.Equiv (realAxis (exp x)).val :=
  entireExponential_real_embedding x.val x.property

/-- A strictly positive real name cannot represent zero. -/
theorem positive_real_nonzero (x : RealInput) (hx : x.val.Pos) : NonzeroBoxSearch.Nonzero (realAxis x) := by
  intro hzero
  have h := realPart_equiv hzero
  obtain ⟨k,hk⟩ := hx
  have hb := (RealRaw.compareAt_overlap_iff _ _ k k).mp (h k)
  change (x.val.compute k).lo≤(0:Rat) ∧ (0:Rat)≤(x.val.compute k).hi at hb
  change 0<(x.val.compute k).lo at hk
  grind only

set_option maxHeartbeats 0 in
/-- Exponential positivity on the entire represented real axis. -/
theorem exp_positive (x : RealInput) : (exp x).val.Pos := by
  let h : Scalar := realAxis ⟨RealRaw.scaleRat (1/2) x.val,RealRaw.scaleRat_valid x.property⟩
  have he : (ofRealRaw (RealRaw.scaleRat 2 h.val.realPart)).Equiv (realAxis x).val := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    have ho := RealRaw.interval_order_of_valid x.val x.property n
    simp only [h,realAxis,ofRealRaw,realPart,RealRaw.scaleRat,RealRaw.scaleRatCompute,
      if_pos (show (0:Rat)≤2 by decide +kernel),if_pos (show (0:Rat)≤1/2 by decide +kernel)]
    constructor <;> constructor <;> grind [Rat.div_def]
  have hmag := entireExponential_squared_magnitude_real h
  have hnonneg := scalar_squared_magnitude_nonnegative (entireExponentialValue h)
  have hv := realPart_valid (mul_valid (entireExponentialValue h).property (conj_valid _ (entireExponentialValue h).property))
  let r : Scalar := ⟨ofRealRaw (RealRaw.scaleRat 2 h.val.realPart),
    ofRealRaw_valid _ (RealRaw.scaleRat_valid (realPart_valid h.property))⟩
  have hvalue := realPart_equiv (entireExponentialValue_congr r (realAxis x) he)
  have h0 : (RealRaw.ofRat 0).Le (exp x).val :=
    RealRaw.le_trans hv hnonneg
      (RealRaw.le_of_equiv hv (exp x).property
        (RealRaw.equiv_trans hv (realPart_valid (entireExponentialValue _).property) (exp x).property hmag hvalue))
  apply Classical.byContradiction
  intro hp
  have hle : (exp x).val.Le (RealRaw.ofRat 0) := by
    intro n m
    have hn : ¬0<((exp x).val.compute n).lo := fun hn => hp ⟨n,hn⟩
    change ((exp x).val.compute n).lo≤(0:Rat)
    grind only
  have hz := RealRaw.le_antisymm hle h0
  have hzero := real_embedding_congr (x := (exp x).val) (y := RealRaw.ofRat 0)
    (exp x).property (RealRaw.ofRat_valid 0) hz
  have hzembed : (ofRealRaw (RealRaw.ofRat 0)).Equiv zero := by
    intro n
    apply (compareAt_overlap_iff _ _ n n).mpr
    constructor <;> exact QComplex.le_refl _
  have hc := equiv_trans (entireExponentialValue (realAxis x)).property
    (realAxis (exp x)).property (ofQComplex_valid QComplex.zero)
    (exp_real_embedding x) (equiv_trans (realAxis (exp x)).property
      (ofRealRaw_valid (RealRaw.ofRat 0) (RealRaw.ofRat_valid 0)) (ofQComplex_valid _) hzero hzembed)
  exact entireExponential_ne_zero (realAxis x) hc

/-- Real-axis injectivity, derived from the exact complex exponential fiber law. -/
theorem exp_injective (x y : RealInput) (h : (exp x).val.Equiv (exp y).val) : x.val.Equiv y.val := by
  have he := equiv_trans (entireExponentialValue (realAxis x)).property
    (realAxis (exp x)).property (entireExponentialValue (realAxis y)).property
    (exp_real_embedding x)
    (equiv_trans (realAxis (exp x)).property (realAxis (exp y)).property
      (entireExponentialValue (realAxis y)).property (real_embedding_congr (exp x).property (exp y).property h) (equiv_symm (exp_real_embedding y)))
  exact entireExponential_fiber_realPart (realAxis x) (realAxis y) he
end ComputableAnalysis.ExponentialComputations
