import ComputableAnalysis.ParametrizedContinuity
import ComputableAnalysis.Differential

/-! Existing interval regularity remains quantitative proof data. This module
constructs its parametrized continuity value, including represented irrational
inputs and closed-interval endpoints, by finite rational intersections. -/
namespace ComputableAnalysis
open RawLimit BracketDerivative BracketContinuity
set_option maxHeartbeats 3000000

/-- The primary rational-input evaluator. Behavior outside the interval is
irrelevant; the domain branch supplies the existing function's validity. -/
def FunctionOnInterval.rationalValue (F : FunctionOnInterval) (r : Rat) : RealRaw :=
  if hr : F.lower ≤ r ∧ r ≤ F.upper then
    { compute := F.compute r hr }
  else RealRaw.ofRat 0

theorem FunctionOnInterval.rationalValue_valid (F : FunctionOnInterval) (r : Rat) :
    (F.rationalValue r).Valid := by
  unfold FunctionOnInterval.rationalValue
  split
  · exact F.valid_on r (F.defined_on r ‹_›)
  · exact RealRaw.ofRat_valid 0

/-- An explicit input-stage schedule remains available for executable
implementations. No choice of an extension value is needed. -/
def ScheduledIntervalRegularOn.bracketCandidate {F : FunctionOnInterval}
    (h : ScheduledIntervalRegularOn F) {x A : RealRaw}
    (hA : Admissible (inDomainInterval F.lower F.upper) x A) (s : Nat → Nat) : RealRaw :=
  prefixRaw (fun k => h.evalInterval (A.compute (s k))
    ⟨(hA.2.2.2 (s k)).2 _ Rat.le_refl (Rat.le_of_lt (hA.2.2.2 (s k)).1) |>.1,
     Rat.le_of_lt (hA.2.2.2 (s k)).1,
     (hA.2.2.2 (s k)).2 _ (Rat.le_of_lt (hA.2.2.2 (s k)).1) Rat.le_refl |>.2⟩ k)

/-- All existing scheduled interval bounds certify the actual prefix
intersection computation, for any justified input refinement schedule. -/
theorem ScheduledIntervalRegularOn.bracketCandidate_hasEnclosureValue
    {F : FunctionOnInterval} (h : ScheduledIntervalRegularOn F) {x A : RealRaw}
    (hA : Admissible (inDomainInterval F.lower F.upper) x A) (s : Nat → Nat)
    (hs : ∀ k, k ≤ s k)
    (width : ∀ k, (A.compute (s k)).width ≤ 1 / ((h.inputPrecision k : Nat) : Rat)) :
    HasEnclosureValue (observations F.rationalValue A) (h.bracketCandidate hA s) := by
  apply prefix_hasEnclosureValue (observations_antitone hA.2.1)
    (observations_inhabited (fun r _ => F.rationalValue_valid r) hA) hs
  · rintro k y ⟨r,hl,hr,rfl⟩
    have hd := (hA.2.2.2 (s k)).2 r hl hr
    have hd' : F.lower ≤ r ∧ r ≤ F.upper := hd
    apply inInterval_of_contains_compute (F.rationalValue_valid r) (h.evalPrecision k)
    simpa only [FunctionOnInterval.rationalValue, dif_pos hd'] using
      h.contains_point_values (A.compute (s k)) _ r hd k hl hr
  · apply shrinksToZero_of_natOverSuccBound (C := 1)
    intro k
    exact (h.output_width (A.compute (s k)) _ k (width k)).2

/-- Existence of stage choices follows from input validity. This theorem is
logical existence; the preceding constructor preserves executable supplied
schedules and does not claim that `Classical.choose` is a runtime algorithm. -/
theorem ScheduledIntervalRegularOn.exists_bracketValue {F : FunctionOnInterval}
    (h : ScheduledIntervalRegularOn F) {x A : RealRaw}
    (hA : Admissible (inDomainInterval F.lower F.upper) x A) :
    ∃ c, HasEnclosureValue (observations F.rationalValue A) c := by
  classical
  let eps : Nat → QPos := fun k => ⟨1 / ((h.inputPrecision k : Nat) : Rat),
    one_div_nat_pos (h.inputPrecision_pos k)⟩
  let stage := fun k => Classical.choose (hA.2.1.2.2 (eps k))
  let s := fun k => max k (stage k)
  refine ⟨h.bracketCandidate hA s,h.bracketCandidate_hasEnclosureValue hA s
    (fun k => Nat.le_max_left _ _) (fun k => ?_)⟩
  exact Classical.choose_spec (hA.2.1.2.2 (eps k)) (s k) (Nat.le_max_right _ _)

theorem ScheduledIntervalRegularOn.exists_continuousAt {F : FunctionOnInterval}
    (h : ScheduledIntervalRegularOn F) {x : RealRaw} (hx : x.Valid)
    (hbracket : ∃ A, Admissible (inDomainInterval F.lower F.upper) x A) :
    ∃ c, HasContinuousAt (inDomainInterval F.lower F.upper) F.rationalValue x c :=
  exists_continuousAt_of_enclosures hx (fun r _ => F.rationalValue_valid r) hbracket
    (fun _ hA => h.exists_bracketValue hA)

theorem IntervalRegularOn.exists_continuousAt {F : FunctionOnInterval}
    (h : IntervalRegularOn F) {x : RealRaw} (hx : x.Valid)
    (hbracket : ∃ A, Admissible (inDomainInterval F.lower F.upper) x A) :
    ∃ c, HasContinuousAt (inDomainInterval F.lower F.upper) F.rationalValue x c :=
  h.toScheduledIntervalRegularOn_identity.exists_continuousAt hx hbracket

/-- Full closed-interval scope, including both endpoints and arbitrary valid
represented inputs. The clipped brackets are constructed internally. -/
theorem IntervalRegularOn.continuousAt_closed {F : FunctionOnInterval}
    (h : IntervalRegularOn F) (hab : F.lower < F.upper) {x : RealRaw} (hx : x.Valid)
    (ha : (RealRaw.ofRat F.lower).Le x) (hb : x.Le (RealRaw.ofRat F.upper)) :
    ∃ c, HasContinuousAt (inDomainInterval F.lower F.upper) F.rationalValue x c :=
  h.exists_continuousAt hx ⟨clipped F.lower F.upper x,clipped_admissible hx hab ha hb⟩

/-- Even a certificate without a whole-interval evaluator can build the
covered output boxes: evaluate one rational endpoint and enlarge by the
proved nearness bound. The final computation uses finite intersections. -/
theorem EpsilonDeltaContinuousOn.exists_bracketValue {F : FunctionOnInterval}
    (h : EpsilonDeltaContinuousOn F) {x A : RealRaw}
    (hA : Admissible (inDomainInterval F.lower F.upper) x A) :
    ∃ c, HasEnclosureValue (observations F.rationalValue A) c := by
  classical
  let error : Nat → QPos := fun k => ⟨RawLimit.allowance k,RawLimit.allowance_pos k⟩
  let delta := fun k => Classical.choose (h (error k))
  let precision := fun k => Classical.choose (Classical.choose_spec (h (error k)))
  have near := fun k => Classical.choose_spec (Classical.choose_spec (h (error k)))
  let stage := fun k => Classical.choose (hA.2.1.2.2 (delta k))
  let s := fun k => max k (stage k)
  have width : ∀ k, (A.compute (s k)).width ≤ (delta k).val :=
    fun k => Classical.choose_spec (hA.2.1.2.2 (delta k)) (s k) (Nat.le_max_right _ _)
  let base := fun k => (A.compute (s k)).lo
  have baseDomain : ∀ k, inDomainInterval F.lower F.upper (base k) :=
    fun k => (hA.2.2.2 (s k)).2 _ Rat.le_refl (Rat.le_of_lt (hA.2.2.2 (s k)).1)
  let B := fun k => QInterval.expand (F.compute (base k) (baseDomain k) (precision k))
    (2*(error k).val)
  refine ⟨prefixRaw B,prefix_hasEnclosureValue (s := s) (observations_antitone hA.2.1)
    (observations_inhabited (fun r _ => F.rationalValue_valid r) hA)
    (fun k => Nat.le_max_left _ _) (fun k y hy => ?_) ?_⟩
  · obtain ⟨r,hl,hr,rfl⟩ := hy
    have hd := (hA.2.2.2 (s k)).2 r hl hr
    have closeInput : qabs (r-base k) ≤ (delta k).val := by
      rw [qabs_eq_self_of_nonneg (by dsimp [base]; grind only)]
      have hw := width k
      dsimp [base]
      grind only [QInterval.width]
    have b := QInterval.expand_contains_right_of_near
      (near k (base k) r (baseDomain k) hd closeInput)
    have hd' : F.lower ≤ r ∧ r ≤ F.upper := hd
    apply inInterval_of_contains_compute (F.rationalValue_valid r) (precision k)
    simpa only [FunctionOnInterval.rationalValue,dif_pos hd'] using b
  · intro eps
    let fifth : QPos := ⟨eps.val/5,by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨N,hN⟩ := RawLimit.allowance_shrinks fifth
    refine ⟨N,fun k hk => ?_⟩
    have b := near k (base k) (base k) (baseDomain k) (baseDomain k)
      (by
        rw [Rat.sub_self]
        change (0 : Rat) ≤ (delta k).val
        exact Rat.le_of_lt (delta k).property)
    have w := b.2.2.1
    have dec := hN k hk
    change (B k).width ≤ eps.val
    dsimp [B,error,fifth] at w dec ⊢
    grind only [QInterval.expand,QInterval.width,Rat.div_def]

theorem EpsilonDeltaContinuousOn.exists_continuousAt {F : FunctionOnInterval}
    (h : EpsilonDeltaContinuousOn F) {x : RealRaw} (hx : x.Valid)
    (hbracket : ∃ A, Admissible (inDomainInterval F.lower F.upper) x A) :
    ∃ c, HasContinuousAt (inDomainInterval F.lower F.upper) F.rationalValue x c :=
  exists_continuousAt_of_enclosures hx (fun r _ => F.rationalValue_valid r) hbracket
    (fun _ hA => h.exists_bracketValue hA)

theorem tendsTo_of_eventually_near {u v : Nat → RealRaw} {c : RealRaw}
    (hu : ∀ j, (u j).Valid) (hv : TendsTo v c)
    (near : ∀ eps : QPos, ∃ N, ∀ j, N ≤ j →
      ∃ p, ((u j).compute p).NearAt ((v j).compute p) eps) : TendsTo u c := by
  refine ⟨hv.1,hu,fun k eps => ?_⟩
  let tau : QPos := ⟨eps.val/4,by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  obtain ⟨N,hN⟩ := hv.2.2 k tau
  obtain ⟨M,hM⟩ := near tau
  refine ⟨max N M,fun j hj => ?_⟩
  obtain ⟨p,hp⟩ := hM j (Nat.le_trans (Nat.le_max_right _ _) hj)
  have b := hN j (Nat.le_trans (Nat.le_max_left _ _) hj)
  rcases hp with ⟨hab,hba,huw,hvw⟩
  constructor
  · intro a t
    have hb := b.1 0 p
    have cross := RealRaw.le_refl _ (hu j) p t
    change (c.compute k).lo-eps.val ≤ ((u j).compute t).hi
    change (c.compute k).lo-tau.val ≤ ((v j).compute p).hi at hb
    dsimp [tau] at hab hba huw hvw hb
    grind only [QInterval.width,Rat.div_def]
  · intro a t
    have hb := b.2 p 0
    have cross := RealRaw.le_refl _ (hu j) a p
    change ((u j).compute a).lo ≤ (c.compute k).hi+eps.val
    change ((v j).compute p).lo ≤ (c.compute k).hi+tau.val at hb
    dsimp [tau] at hab hba huw hvw hb
    grind only [QInterval.width,Rat.div_def]

/-- The old finite-difference evidence publishes a derivative under the new
specification. Its radii must be genuinely positive, and its derivative
values must approach the supplied represented value. These are independent
mathematical hypotheses, not an assumed derivative identity. -/
theorem HasDerivativeOnInterval.toParametrizedDerivative {F G : FunctionOnInterval}
    (D : HasDerivativeOnInterval F G) (positive : ∀ n, 0 < D.stepPrecision n)
    {x d : RealRaw}
    (hG : HasContinuousAt (inDomainInterval G.lower G.upper) G.rationalValue x d) :
    HasDerivativeAt (inDomainInterval F.lower F.upper) F.rationalValue x d := by
  have same : inDomainInterval F.lower F.upper = inDomainInterval G.lower G.upper := by
    rw [D.same_lower,D.same_upper]
  have transport : ∀ A, Admissible (inDomainInterval F.lower F.upper) x A ↔
      Admissible (inDomainInterval G.lower G.upper) x A := fun _ => by rw [same]
  obtain ⟨A,hA⟩ := hG.2.2.2.1
  apply hasDerivative_iff_secantLimits.mpr
  refine ⟨hG.1,hG.2.1,fun r _ => F.rationalValue_valid r,
    ⟨A,(transport A).mpr hA⟩,fun B hB => ?_⟩
  have hBG := (transport B).mp hB
  have hv := values_tendTo hG hBG (fun j => (B.compute j).lo)
    (fun j => ⟨Rat.le_refl,Rat.le_of_lt (hB.2.2.2 j).1⟩)
  apply tendsTo_of_eventually_near (secants_valid (fun r _ => F.rationalValue_valid r) hB) hv
  intro eps
  let p := eps.val.den+1
  have hp : 0 < p := Nat.succ_pos _
  have htol : (precisionAtStage p).val ≤ eps.val := by
    simpa [precisionAtStage, p, Nat.ne_of_gt hp] using one_div_den_succ_le_of_pos eps.property
  let radius : QPos := ⟨1 / ((D.stepPrecision p : Nat) : Rat),one_div_nat_pos (positive p)⟩
  obtain ⟨N,hN⟩ := hB.2.1.2.2 radius
  refine ⟨N,fun j hj => ?_⟩
  let a := (B.compute j).lo
  let b := (B.compute j).hi
  let h := b-a
  have hab : a < b := (hB.2.2.2 j).1
  have ha := (hB.2.2.2 j).2 a Rat.le_refl (Rat.le_of_lt hab)
  have hb := (hB.2.2.2 j).2 b (Rat.le_of_lt hab) Rat.le_refl
  have haG := (hBG.2.2.2 j).2 a Rat.le_refl (Rat.le_of_lt hab)
  have eq : a+h=b := by dsimp [h]; grind only
  have hpos : 0<h := by dsimp [h]; grind only
  have small : qabs h ≤ 1 / ((D.stepPrecision p : Nat) : Rat) := by
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt hpos)]
    exact hN j hj
  have close := D.close a h p ha (eq ▸ hb) haG (Rat.ne_of_gt hpos) small
  simp only [eq] at close
  let k := D.evalPrecision a h p
  refine ⟨k,?_⟩
  have ha' : F.lower ≤ a ∧ a ≤ F.upper := ha
  have hb' : F.lower ≤ b ∧ b ≤ F.upper := hb
  have haG' : G.lower ≤ a ∧ a ≤ G.upper := haG
  have converted : ((secants F.rationalValue B j).compute k).NearAt
      ((G.rationalValue a).compute k) (precisionAtStage p) := by
    simpa only [secants,secant,FunctionOnInterval.rationalValue,dif_pos ha',dif_pos hb',
      dif_pos haG',RealRaw.scaleRat,RealRaw.scaleRatCompute,HSub.hSub,
      RealRaw.sub,RealRaw.subCompute,
      QInterval.differenceQuotient,QInterval.divRat,QInterval.scaleRat,QInterval.sub,
      intervalNearAtPrecision,k,a,b,h] using close
  rcases converted with ⟨h1,h2,h3,h4⟩
  exact ⟨by have h := htol; grind only,
    by have h := htol; grind only,Rat.le_trans h3 htol,Rat.le_trans h4 htol⟩

end ComputableAnalysis
