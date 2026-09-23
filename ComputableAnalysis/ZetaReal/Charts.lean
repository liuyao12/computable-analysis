import ComputableAnalysis.ZetaReal.Continuity

namespace ComputableAnalysis.ZetaReal

/-- Every output box contains all sufficiently large finite rectangles. -/
theorem raw_contains_rectangles {q m : Nat} (hq : 0 < q) {s : Rat} (hs : InChart q m s)
    (n : Nat) : ∃ K₀ N₀, ∀ K N, K₀ ≤ K → N₀ ≤ N →
    ((raw q m hq s).compute n).ContainsInterval ⟨rectangle s K N, rectangle s K N⟩ := by
  have current (i K N : Nat) (hK : outerCutoff q m hq i ≤ K)
      (hN : innerCutoff m (outerCutoff q m hq i) i ≤ N) :
      (QInterval.expand ((candidate q m hq s).compute i) (4*(budget i).val)).ContainsInterval
        ⟨rectangle s K N, rectangle s K N⟩ := by
    have h := approx_rectangle hq hs i K N hK hN
    have hl := neg_qabs_le_self (rectangle s K N-approx q m hq s i)
    have hh := self_le_qabs (rectangle s K N-approx q m hq s i)
    have hp := (budget i).property
    constructor <;> dsimp [candidate, QInterval.expand] <;> grind only
  induction n with
  | zero => exact ⟨outerCutoff q m hq 0, innerCutoff m (outerCutoff q m hq 0) 0, current 0⟩
  | succ n ih =>
    obtain ⟨K₀,N₀,h⟩ := ih
    refine ⟨max K₀ (outerCutoff q m hq (n+1)), max N₀ (innerCutoff m (outerCutoff q m hq (n+1)) (n+1)), ?_⟩
    intro K N hK hN
    apply QInterval.intersection_contains
    · exact h K N (by omega) (by omega)
    · exact current (n+1) K N (by omega) (by omega)

theorem raw_chart_equiv {q m r l : Nat} (hq : 0 < q) (hr : 0 < r) {s : Rat}
    (hs : InChart q m s) (ht : InChart r l s) : (raw q m hq s).Equiv (raw r l hr s) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  obtain ⟨K,N,h⟩ := raw_contains_rectangles hq hs n
  obtain ⟨L,M,g⟩ := raw_contains_rectangles hr ht n
  have hh := h (max K L) (max N M) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hg := g (max K L) (max N M) (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  exact ⟨Rat.le_trans hh.1 hg.2, Rat.le_trans hg.1 hh.2⟩

/-- Changing both chart and implementation leaves the represented answer unchanged. -/
theorem atReal_chart_equiv {q m r l : Nat} (hq : 0 < q) (hr : 0 < r) {s t : Real}
    (hst : s.Equiv t)
    (hs : ∀ n, subintervalOf (s.compute n) (lower q) ((m : Rat)+2))
    (ht : ∀ n, subintervalOf (t.compute n) (lower r) ((l : Rat)+2)) :
    (atReal q m hq s hs).Equiv (atReal r l hr t ht) := by
  let F := continuous q m hq
  let G := continuous r l hr
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  let i := F.inputStage s.preferred s.valid n
  let j := G.inputStage t.preferred t.valid n
  have hover := (RealRaw.compareAt_overlap_iff _ _ i j).1
    (RealRaw.allStagesOverlap_of_equiv s.valid t.valid hst i j)
  let I := QInterval.intersection (s.compute i) (t.compute j)
  have horder := QInterval.intersection_ordered_of_overlaps (hs i).2.1 (ht j).2.1 hover
  have hleft := QInterval.intersection_contained_left (s.compute i) (t.compute j)
  have hright := QInterval.intersection_contained_right (s.compute i) (t.compute j)
  have hsi : InChart q m I.lo := ⟨Rat.le_trans (hs i).1 hleft.1,
    Rat.le_trans (Rat.le_trans horder hleft.2) (hs i).2.2⟩
  have hti : InChart r l I.lo := ⟨Rat.le_trans (ht j).1 hright.1,
    Rat.le_trans (Rat.le_trans horder hright.2) (ht j).2.2⟩
  have heq := raw_chart_equiv hq hr hsi hti
  have hpoint := (RealRaw.compareAt_overlap_iff _ _ n n).1 (heq n)
  have hf := imageBox_contains hq (s.compute i) (hs i) hsi n hleft.1 (Rat.le_trans horder hleft.2)
  have hg := imageBox_contains hr (t.compute j) (ht j) hti n hright.1 (Rat.le_trans horder hright.2)
  have hfs := F.applyRealRaw_contains_candidate s.preferred s.valid hs n
  have hgs := G.applyRealRaw_contains_candidate t.preferred t.valid ht n
  exact ⟨Rat.le_trans hfs.1 (Rat.le_trans hf.1 (Rat.le_trans hpoint.1 (Rat.le_trans hg.2 hgs.2))),
    Rat.le_trans hgs.1 (Rat.le_trans hg.1 (Rat.le_trans hpoint.2 (Rat.le_trans hf.2 hfs.2)))⟩

/-- Strictly above one means that a finite input box certifies the separation. -/
def AboveOne (s : Real) : Prop := ∃ n, 1 < (s.compute n).lo

private theorem aboveOne_eventual (s : Real) (hs : AboveOne s) :
    ∃ N, ∀ n, N ≤ n → 1 < (s.compute n).lo := by
  obtain ⟨N,hN⟩ := hs
  exact ⟨N, fun n hn => by have h := (s.valid.2.1 N n hn).1; change (s.compute N).lo ≤ (s.compute n).lo at h; grind⟩

def domainStage (s : Real) (hs : AboveOne s) : Nat :=
  (firstWitness (fun n => 1 < (s.compute n).lo) (aboveOne_eventual s hs)).val

def domainLower (s : Real) (hs : AboveOne s) : QPos :=
  ⟨(s.compute (domainStage s hs)).lo-1, by
    have h := (firstWitness (fun n => 1 < (s.compute n).lo) (aboveOne_eventual s hs)).property
    change 1 < (s.compute (domainStage s hs)).lo at h
    grind⟩

def chartQ (s : Real) (hs : AboveOne s) : Nat :=
  (firstWitness (fun j => 1/((j+1 : Nat) : Rat) ≤ (domainLower s hs).val)
    (shrinksToZero_of_natOverSuccBound (C := 1) (fun _ => Rat.le_refl) (domainLower s hs))).val+1

def chartM (s : Real) (hs : AboveOne s) : Nat :=
  RationalMajorant.factorialTailStart (s.compute (domainStage s hs)).hi+1

def domainSchedule (s : Real) (hs : AboveOne s) : RealRaw.StageSchedule where
  stage n := domainStage s hs+n
  monotone := by intros; omega
  cofinal := fun n => ⟨n, by omega⟩

def domainReal (s : Real) (hs : AboveOne s) : Real :=
  Real.ofRaw (RealRaw.schedule (domainSchedule s hs) s.preferred)
    (RealRaw.schedule_valid _ s.valid _)

theorem domainReal_inChart (s : Real) (hs : AboveOne s) (n : Nat) :
    subintervalOf ((domainReal s hs).compute n) (lower (chartQ s hs)) ((chartM s hs : Rat)+2) := by
  have hnest := s.valid.2.1 (domainStage s hs) (domainStage s hs+n) (by omega)
  have hb := (firstWitness (fun j => 1/((j+1 : Nat) : Rat) ≤ (domainLower s hs).val)
    (shrinksToZero_of_natOverSuccBound (C := 1) (fun _ => Rat.le_refl) (domainLower s hs))).property
  change 1/(chartQ s hs : Rat) ≤ (s.compute (domainStage s hs)).lo-1 at hb
  have hu := RationalMajorant.factorialTailStart_satisfies (s.compute (domainStage s hs)).hi
  change (s.compute (domainStage s hs)).hi ≤ (chartM s hs : Rat)/2 at hu
  have hm := Rat.natCast_nonneg (a := chartM s hs)
  have hq : 0 < (chartQ s hs : Rat) := Rat.natCast_pos.mpr (Nat.zero_lt_succ _)
  have hqi := Rat.inv_pos.mpr hq
  have hqj := Rat.inv_pos.mpr (by grind : 0 < (chartQ s hs : Rat)+1)
  have he1 := Rat.mul_inv_cancel (chartQ s hs : Rat) (Rat.ne_of_gt hq)
  have he2 := Rat.mul_inv_cancel ((chartQ s hs : Rat)+1) (by grind)
  have hrecip : 1/((chartQ s hs : Rat)+1) ≤ 1/(chartQ s hs : Rat) := by
    have hprod := Rat.mul_nonneg (Rat.le_of_lt hqi) (Rat.le_of_lt hqj)
    rw [Rat.div_def, Rat.div_def]
    have ha := congrArg (fun z : Rat => z*((chartQ s hs : Rat)+1)⁻¹) he1
    have hb := congrArg (fun z : Rat => z*(chartQ s hs : Rat)⁻¹) he2
    grind only
  change lower (chartQ s hs) ≤ (s.compute (domainStage s hs+n)).lo ∧
    (s.compute (domainStage s hs+n)).lo ≤ (s.compute (domainStage s hs+n)).hi ∧
    (s.compute (domainStage s hs+n)).hi ≤ (chartM s hs : Rat)+2
  unfold lower
  change (s.compute (domainStage s hs)).lo ≤ (s.compute (domainStage s hs+n)).lo ∧ (s.compute (domainStage s hs+n)).lo ≤ (s.compute (domainStage s hs+n)).hi ∧ (s.compute (domainStage s hs+n)).hi ≤ (s.compute (domainStage s hs)).hi at hnest
  exact ⟨by grind only, hnest.2.1, by grind⟩

/-- The zeta evaluator on the whole represented-real half-line `s > 1`.
It finds a separated input box, selects a rational chart, and uses the
canonical adaptive application of the certified interval function. -/
def zeta (s : Real) (hs : AboveOne s) : Real :=
  atReal (chartQ s hs) (chartM s hs) (Nat.zero_lt_succ _) (domainReal s hs) (domainReal_inChart s hs)

theorem zeta_valid (s : Real) (hs : AboveOne s) : (zeta s hs).preferred.Valid := (zeta s hs).valid

theorem zeta_equiv {s t : Real} (hs : AboveOne s) (ht : AboveOne t) (hst : s.Equiv t) :
    (zeta s hs).Equiv (zeta t ht) := by
  apply atReal_chart_equiv
  have hs' := RealRaw.schedule_equiv s.preferred s.valid (domainSchedule s hs)
  have ht' := RealRaw.schedule_equiv t.preferred t.valid (domainSchedule t ht)
  exact RealRaw.equiv_trans (domainReal s hs).valid s.valid (domainReal t ht).valid
    (RealRaw.equiv_symm hs')
    (RealRaw.equiv_trans s.valid t.valid (domainReal t ht).valid hst ht')

end ComputableAnalysis.ZetaReal
