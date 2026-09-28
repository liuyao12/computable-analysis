import ComputableAnalysis.RationalSampleLimits

/-! Executable extension of a justified rational-input computation to every
valid represented real. Precision searches use validity only for termination;
the runtime reads rational intervals until their widths meet the target. -/
namespace ComputableAnalysis.RationalLipschitzLift
open ClosedArctanInverse IntervalSelections RationalSampleLimits

structure Data where
  raw : Rat → RealRaw
  valid : ∀ t, (raw t).Valid
  bound : Rat
  bound_nonneg : 0≤bound
  lipschitz : ∀ a b n m, ((raw a).compute n).lo≤((raw b).compute m).hi+bound*qabs (a-b)

def precisionFrom (x : RealRaw) (hx : x.Valid) (eps : QPos) (n : Nat) : Nat :=
  if (x.compute n).width≤eps.val then n else precisionFrom x hx eps (n+1)
termination_by Classical.choose (hx.2.2 eps)-n
decreasing_by
  have h:=Classical.choose_spec (hx.2.2 eps)
  have hn : n<Classical.choose (hx.2.2 eps) := by
    by_cases hn : n<Classical.choose (hx.2.2 eps)
    · exact hn
    · have hle : Classical.choose (hx.2.2 eps)≤n := by omega
      exact False.elim (‹¬(x.compute n).width≤eps.val› (h n hle))
  omega

theorem precisionFrom_spec (x : RealRaw) (hx : x.Valid) (eps : QPos) (n : Nat) :
    (x.compute (precisionFrom x hx eps n)).width≤eps.val := by
  rw [precisionFrom]
  split
  · assumption
  · exact precisionFrom_spec x hx eps (n+1)
termination_by Classical.choose (hx.2.2 eps)-n
decreasing_by
  have h:=Classical.choose_spec (hx.2.2 eps)
  have hn : n<Classical.choose (hx.2.2 eps) := by
    by_cases hn : n<Classical.choose (hx.2.2 eps)
    · exact hn
    · have hle : Classical.choose (hx.2.2 eps)≤n := by omega
      exact False.elim (‹¬(x.compute n).width≤eps.val› (h n hle))
  omega

namespace Data

def stage (D : Data) (t : Rat) (q : Nat) : Nat :=
  precisionFrom (D.raw t) (D.valid t) ⟨meshRadius q,meshRadius_pos q⟩ 0

def sample (D : Data) (t : Rat) (q : Nat) : Rat := ((D.raw t).compute (D.stage t q)).lo

theorem selected_width (D : Data) (t : Rat) (q : Nat) :
    ((D.raw t).compute (D.stage t q)).width≤meshRadius q :=
  precisionFrom_spec _ _ _ _

theorem sample_difference (D : Data) (a b : Rat) (n m : Nat) :
    qabs (D.sample a n-D.sample b m)≤D.bound*qabs (a-b)+meshRadius n+meshRadius m := by
  have h1:=D.lipschitz a b (D.stage a n) (D.stage b m)
  have h2:=D.lipschitz b a (D.stage b m) (D.stage a n)
  have w1:=D.selected_width a n;have w2:=D.selected_width b m
  have he : qabs (b-a)=qabs (a-b) := by rw [show b-a= -(a-b) by grind,qabs_neg]
  rw [he] at h2
  have hn:=meshRadius_pos n;have hm:=meshRadius_pos m
  unfold sample QInterval.width at *
  apply qabs_le_of_neg_le_le <;> grind only

def candidate (D : Data) (x : RealRaw) : RealRaw where
  compute := fun n=>let a:=D.sample (x.compute n).lo n; {lo:=a,hi:=a}

def radius (D : Data) (x : RealRaw) (n : Nat) : Rat := D.bound*(x.compute n).width+2*meshRadius n

theorem future (D : Data) (x : RealRaw) (hx : x.Valid) (n m : Nat) (hnm : n≤m) :
    (QInterval.expand ((D.candidate x).compute n) (D.radius x n)).ContainsInterval ((D.candidate x).compute m) := by
  have he:=hx.2.1 n m hnm
  have ho:=RealRaw.interval_order_of_valid x hx m
  have hdiff : qabs ((x.compute n).lo-(x.compute m).lo)≤(x.compute n).width := by
    apply qabs_le_of_neg_le_le <;> unfold QInterval.width <;> grind only
  have h:=D.sample_difference (x.compute n).lo (x.compute m).lo n m
  have hs:=Rat.mul_le_mul_of_nonneg_left hdiff D.bound_nonneg
  have hm:=meshRadius_antitone hnm
  have hp:=self_le_qabs (D.sample (x.compute n).lo n-D.sample (x.compute m).lo m)
  have hn:=neg_qabs_le_self (D.sample (x.compute n).lo n-D.sample (x.compute m).lo m)
  change D.sample (x.compute n).lo n-D.radius x n≤D.sample (x.compute m).lo m ∧
    D.sample (x.compute m).lo m≤D.sample (x.compute n).lo n+D.radius x n
  unfold radius;constructor <;> grind only

theorem radius_small (D : Data) (x : RealRaw) (hx : x.Valid) : Small (D.radius x) := by
  have hw : Small (fun n=>(x.compute n).width) := by
    intro eps
    obtain ⟨N,hN⟩:=hx.2.2 eps
    exact ⟨N,fun n hn=>by rw [qabs_eq_self_of_nonneg (hx.1 n)];exact hN n hn⟩
  have hm : Small (fun n=>meshRadius n) :=
    small_of_geometric_bound 1 (by decide +kernel) (fun n=>by
      rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (meshRadius_pos n)),Rat.one_mul];exact Rat.le_refl)
  exact small_add (small_bounded_mul (qabs_nonneg D.bound) (bounded_const _) hw)
    (small_bounded_mul (by decide +kernel : (0:Rat)≤2) (show Bounded (fun _=>(2:Rat)) 2 from
      fun n=>by exact (by decide +kernel : qabs (2:Rat)≤2)) hm)

def extend (D : Data) (x : RealRaw) : RealRaw := RealRaw.prefixStabilize (D.candidate x) (D.radius x)

theorem extend_valid (D : Data) (x : RealRaw) (hx : x.Valid) : (D.extend x).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
  · intro n;change 0≤D.sample (x.compute n).lo n-D.sample (x.compute n).lo n;grind
  · intro eps;exact ⟨0,fun n hn=>by change D.sample (x.compute n).lo n-D.sample (x.compute n).lo n≤eps.val;have h:=eps.property;grind⟩
  · exact D.future x hx
  · intro eps
    obtain ⟨N,hN⟩:=D.radius_small x hx eps
    exact ⟨N,fun n hn=>Rat.le_trans (self_le_qabs _) (hN n hn)⟩

theorem sample_mem (D : Data) (x : RealRaw) (hx : x.Valid) (n : Nat) :
    InBox (D.sample (x.compute n).lo n) ((D.extend x).compute n) := by
  have h:=RealRaw.prefixStabilize_contains_current_of_future (D.future x hx) n
  exact h

/-- Equal rational-input values give equal extensions, even with different
algorithms, bounds, and precision searches. -/
theorem congr (D E : Data) (h : ∀ t, (D.raw t).Equiv (E.raw t)) (x : RealRaw) (hx : x.Valid) :
    (D.extend x).Equiv (E.extend x) := by
  apply equiv_of_close (D.extend_valid x hx) (E.extend_valid x hx)
    (fun n=>D.sample (x.compute n).lo n) (fun n=>E.sample (x.compute n).lo n)
    (D.sample_mem x hx) (E.sample_mem x hx)
  apply small_of_geometric_bound 2 (by decide +kernel)
  intro n
  let t:Rat:=(x.compute n).lo
  have ho:=(RealRaw.compareAt_overlap_iff _ _ (D.stage t n) (E.stage t n)).1
    (RealRaw.allStagesOverlap_of_sameStageOverlap (D.valid t) (E.valid t) (h t) (D.stage t n) (E.stage t n))
  have hw:=D.selected_width t n;have hv:=E.selected_width t n
  unfold QInterval.Overlaps QInterval.width at *
  change qabs (D.sample t n-E.sample t n)≤_
  unfold sample
  apply qabs_le_of_neg_le_le <;> grind only

/-- Transport a Lipschitz law through exact rational-input agreement. -/
def transport (D : Data) (F : Rat → RealRaw) (hF : ∀ t,(F t).Valid)
    (h : ∀ t,(F t).Equiv (D.raw t)) : Data where
  raw := F
  valid := hF
  bound := D.bound
  bound_nonneg := D.bound_nonneg
  lipschitz := by
    intro a b n m
    by_cases he : ((F a).compute n).lo≤((F b).compute m).hi+D.bound*qabs (a-b)
    · exact he
    exfalso
    let eps : QPos := ⟨(((F a).compute n).lo-(((F b).compute m).hi+D.bound*qabs (a-b)))/4,by
      simp only [Rat.div_def];grind⟩
    obtain ⟨N,hN⟩:=(D.valid a).2.2 eps
    obtain ⟨M,hM⟩:=(D.valid b).2.2 eps
    have hw1:=hN N (Nat.le_refl _);have hw2:=hM M (Nat.le_refl _)
    have ha:=(RealRaw.compareAt_overlap_iff _ _ n N).1
      (RealRaw.allStagesOverlap_of_sameStageOverlap (hF a) (D.valid a) (h a) n N)
    have hb:=(RealRaw.compareAt_overlap_iff _ _ m M).1
      (RealRaw.allStagesOverlap_of_sameStageOverlap (hF b) (D.valid b) (h b) m M)
    have hbound:=D.lipschitz a b N M
    unfold QInterval.Overlaps QInterval.width at *
    dsimp [eps] at hw1 hw2
    simp only [Rat.div_def] at hw1 hw2
    grind only

theorem representation_equiv (D : Data) {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (he : x.Equiv y) :
    (D.extend x).Equiv (D.extend y) := by
  apply equiv_of_close (D.extend_valid x hx) (D.extend_valid y hy)
    (fun n=>D.sample (x.compute n).lo n) (fun n=>D.sample (y.compute n).lo n)
    (D.sample_mem x hx) (D.sample_mem y hy)
  have hs:=small_add (D.radius_small x hx) (D.radius_small y hy)
  intro eps
  obtain ⟨N,hN⟩:=hs eps
  refine ⟨N,fun n hn=>?_⟩
  have ho:=(RealRaw.compareAt_overlap_iff _ _ n n).1 (he n)
  have hd : qabs ((x.compute n).lo-(y.compute n).lo)≤(x.compute n).width+(y.compute n).width := by
    have hxo:=hx.1 n;have hyo:=hy.1 n
    unfold QInterval.Overlaps QInterval.width at *
    apply qabs_le_of_neg_le_le <;> grind only
  have h:=D.sample_difference (x.compute n).lo (y.compute n).lo n n
  have hm:=Rat.mul_le_mul_of_nonneg_left hd D.bound_nonneg
  have hb:=self_le_qabs (D.radius x n+D.radius y n)
  have hsmall:=hN n hn
  have hp:=meshRadius_pos n
  unfold radius at hb hsmall
  grind only

theorem at_rational (D : Data) (t : Rat) : (D.extend (RealRaw.ofRat t)).Equiv (D.raw t) := by
  apply equiv_of_close (D.extend_valid _ (RealRaw.ofRat_valid t)) (D.valid t)
    (D.sample t) (fun n=>((D.raw t).compute n).lo)
    (D.sample_mem (RealRaw.ofRat t) (RealRaw.ofRat_valid t))
    (fun n=>⟨Rat.le_refl,RealRaw.interval_order_of_valid _ (D.valid t) n⟩)
  have hw : Small (fun n=>((D.raw t).compute n).width) := by
    intro eps
    obtain ⟨N,hN⟩:=(D.valid t).2.2 eps
    exact ⟨N,fun n hn=>by rw [qabs_eq_self_of_nonneg ((D.valid t).1 n)];exact hN n hn⟩
  have hm : Small (fun n=>meshRadius n) := small_of_geometric_bound 1 (by decide +kernel) (fun n=>by
    rw [qabs_eq_self_of_nonneg (Rat.le_of_lt (meshRadius_pos n)),Rat.one_mul];exact Rat.le_refl)
  intro eps
  obtain ⟨N,hN⟩:=small_add hm hw eps
  refine ⟨N,fun n hn=>?_⟩
  have ho:=(RealRaw.compareAt_overlap_iff _ _ (D.stage t n) n).1
    (RealRaw.allStagesOverlap_refl (D.raw t) (D.valid t) (D.stage t n) n)
  have hw1:=D.selected_width t n
  have hs:=hN n hn
  have hp:=self_le_qabs (meshRadius n+((D.raw t).compute n).width)
  have hnmesh:=meshRadius_pos n
  have hnwidth:=(D.valid t).1 n
  unfold QInterval.Overlaps QInterval.width at *
  change qabs (D.sample t n-((D.raw t).compute n).lo)≤eps.val
  unfold sample
  apply qabs_le_of_neg_le_le <;> grind only

end Data
end ComputableAnalysis.RationalLipschitzLift
