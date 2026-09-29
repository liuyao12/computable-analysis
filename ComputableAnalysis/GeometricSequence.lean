import ComputableAnalysis.GeometricSeriesCalculus
import ComputableAnalysis.ImproperIntegralBounds

/-! Finite-prefix interval computations for explicitly controlled rational
sequences. There is no abstract completion or selected real limit. -/
namespace ComputableAnalysis.GeometricSequence
open FormalPowerSeries Integral

def candidate (f : Nat → Rat) : RealRaw where
  compute n := ⟨f n,f n⟩

def raw (f : Nat → Rat) (R : Rat) : RealRaw :=
  RealRaw.prefixStabilize (candidate f) (fun n => R*((1 : Rat)/2)^n)

theorem shrinks {R : Rat} (hR : 0 ≤ R) : ShrinksToZero (fun n => R*((1 : Rat)/2)^n) := by
  intro eps
  refine ⟨RationalMajorant.halfDecayShift R eps, ?_⟩
  intro n hn
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (half_pow_antitone hn) hR)
    (RationalMajorant.halfDecayShift_spec hR eps)

theorem raw_valid {f : Nat → Rat} {R : Rat} (hR : 0 ≤ R)
    (hf : ∀ n K, n ≤ K → qabs (f K-f n) ≤ R*((1 : Rat)/2)^n) : (raw f R).Valid := by
  apply RealRaw.prefixStabilize_valid_of_future
  · intro n; dsimp [candidate,QInterval.width]; grind
  · intro eps; refine ⟨0, ?_⟩; intro n _; dsimp [candidate,QInterval.width]; have := eps.property; grind
  · intro n K hnK
    have h := hf n K hnK
    have hl := neg_qabs_le_self (f K-f n)
    have hh := self_le_qabs (f K-f n)
    constructor <;> dsimp [candidate,QInterval.expand] <;> grind only
  · exact shrinks hR

theorem raw_contains {f : Nat → Rat} {R v : Rat} {n : Nat}
    (hv : ∀ j, j ≤ n → qabs (v-f j) ≤ R*((1 : Rat)/2)^j) :
    ((raw f R).compute n).lo ≤ v ∧ v ≤ ((raw f R).compute n).hi := by
  have hc (j : Nat) (hj : j ≤ n) :
      (QInterval.expand ((candidate f).compute j) (R*((1 : Rat)/2)^j)).ContainsInterval ⟨v,v⟩ := by
    have he := hv j hj
    have hl := neg_qabs_le_self (v-f j)
    have hh := self_le_qabs (v-f j)
    constructor <;> dsimp [candidate,QInterval.expand] <;> grind only
  have aux (j : Nat) (hj : j ≤ n) : ((raw f R).compute j).ContainsInterval ⟨v,v⟩ := by
    induction j with
    | zero => exact hc 0 (Nat.zero_le n)
    | succ j ih =>
      apply QInterval.intersection_contains
      · exact ih (by omega)
      · exact hc (j+1) hj
  exact aux n (Nat.le_refl _)

theorem raw_enclosure (f : Nat → Rat) (R : Rat) (n : Nat) :
    f n-R*((1 : Rat)/2)^n ≤ ((raw f R).compute n).lo ∧
      ((raw f R).compute n).hi ≤ f n+R*((1 : Rat)/2)^n :=
  RealRaw.prefixStabilize_contained_in_current_expand (candidate f) (fun n => R*((1 : Rat)/2)^n) n

theorem raw_within {f : Nat → Rat} {R : Rat} (hv : (raw f R).Valid) (n : Nat) :
    Within (raw f R) (RealRaw.ofRat (f n)) (R*((1 : Rat)/2)^n) := by
  intro i j
  have ho := (RealRaw.compareAt_overlap_iff _ _ i n).1 (RealRaw.allStagesOverlap_refl _ hv i n)
  have he := raw_enclosure f R n
  change ((raw f R).compute i).lo ≤ ((raw f R).compute n).hi ∧
    ((raw f R).compute n).lo ≤ ((raw f R).compute i).hi at ho
  change ((raw f R).compute i).lo ≤ f n+R*((1 : Rat)/2)^n ∧
    f n ≤ ((raw f R).compute i).hi+R*((1 : Rat)/2)^n
  constructor <;> grind only

theorem raw_width {f : Nat → Rat} {R : Rat} (hv : (raw f R).Valid) (n : Nat) :
    0 ≤ ((raw f R).compute n).width ∧ ((raw f R).compute n).width ≤ 2*R*((1 : Rat)/2)^n := by
  have he := raw_enclosure f R n
  refine ⟨hv.1 n, ?_⟩
  unfold QInterval.width
  grind only

end ComputableAnalysis.GeometricSequence
