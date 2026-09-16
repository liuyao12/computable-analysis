import ComputableAnalysis.DovetailedFTC

/-! A supplied joint schedule and its certificate, not an integrability predicate.
The generic bounds must be justified separately for their intended integrand.
Neither a successful schedule nor an endpoint value is obtained by choice. -/
namespace ComputableAnalysis.Integral.ScheduledBounds

structure JointSchedule where
  meshStage : Nat → Nat
  evaluationStage : Nat → Nat

def selected (B : Nat → Nat → QInterval) (s : JointSchedule) (k : Nat) : QInterval :=
  B (s.meshStage k) (s.evaluationStage k)

/-- Only the prescribed pairs are read; old pairs are not reevaluated. -/
def raw (B : Nat → Nat → QInterval) (s : JointSchedule) : RealRaw :=
  Dovetail.ofBoxes (fun k _ => selected B s k)

/-- The certificate concerns this chosen schedule. It asserts no success for
other schedules and does not assert an antiderivative formula. -/
structure Certificate (B : Nat → Nat → QInterval) (s : JointSchedule) : Prop where
  compatible : ∀ k l, (selected B s k).lo ≤ (selected B s l).hi
  shrinking : RealRaw.WidthsShrinkToZero (selected B s)

theorem valid {B : Nat → Nat → QInterval} {s : JointSchedule}
    (h : Certificate B s) : (raw B s).Valid := by
  apply Dovetail.ofBoxes_valid
  · intro k l q t
    exact h.compatible k l
  · intro k q t _
    exact ⟨Rat.le_refl, Rat.le_refl⟩
  · intro eps
    obtain ⟨K, hK⟩ := h.shrinking eps
    exact ⟨K, 0, fun _ _ => hK K (Nat.le_refl K)⟩

private theorem overlap_prefix (J : Nat → QInterval) (I : QInterval)
    (h : ∀ k, I.Overlaps (J k)) (q n : Nat) :
    I.Overlaps (Dovetail.intersectMeshes (fun k _ => J k) q n) := by
  induction n with
  | zero => exact h 0
  | succ n ih =>
    have hn := h (n+1)
    change I.lo ≤ min _ _ ∧ max _ _ ≤ I.hi
    unfold QInterval.Overlaps at ih hn
    constructor <;> grind

/-- Schedule independence needs cross-compatibility for the SAME mathematical
quantity. Validity alone would not identify arbitrary unrelated programs. -/
theorem equivalent {B D : Nat → Nat → QInterval} {s t : JointSchedule}
    (_hs : Certificate B s) (_ht : Certificate D t)
    (sameBounds : ∀ k l, (selected B s k).Overlaps (selected D t l)) :
    (raw B s).Equiv (raw D t) := by
  apply Dovetail.ofBoxes_equiv
  intro k q n
  exact overlap_prefix (selected D t) (selected B s k) (sameBounds k) n n

end ComputableAnalysis.Integral.ScheduledBounds
