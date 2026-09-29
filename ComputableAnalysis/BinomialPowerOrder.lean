import ComputableAnalysis.PowerInfinityIntegral

/-! Algebra and order for the independently computed binomial powers. -/
namespace ComputableAnalysis
open FormalPowerSeries ZetaReal Integral

namespace Integral
theorem equiv_of_within_shrinking {X Y : RealRaw} {e : Nat → Rat}
    (he : ShrinksToZero e) (h : ∀ n, Within X Y (e n)) : X.Equiv Y := by
  have remove (a b : Rat) (hab : ∀ n, a ≤ b+e n) : a ≤ b := by
    by_cases hh : a ≤ b
    · exact hh
    exfalso
    let eps : QPos := ⟨(a-b)/2,by grind⟩
    obtain ⟨N,hN⟩ := he eps
    have heps := hN N (Nat.le_refl _)
    have hh := hab N
    change e N ≤ (a-b)/2 at heps
    grind only
  intro i
  apply (RealRaw.compareAt_overlap_iff _ _ i i).2
  exact ⟨remove _ _ (fun n => (h n i i).1),remove _ _ (fun n => (h n i i).2)⟩
end Integral

namespace BinomialPower.Global

theorem Chart.shift_identity (A : Chart) {p : Real} (hp : A.BoundsParameter p)
    {x : Rat} (hx : 0 ≤ x) (hxA : x ≤ A.radius) :
    (A.next.value (shiftParameter p) x).Equiv (RealRaw.scaleRat (1-x) (A.value p x)) := by
  have hx1 : x < 1 := by have := A.belowOne; grind
  have hr : 0 ≤ 1-x := by grind
  apply equiv_of_within_shrinking (GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 2))
  intro n i j
  let q := shiftParameter p
  let N := max (A.observation p j) (A.next.observation q i)
  let K := max (A.cutoff j) (max (A.next.cutoff i) (A.cutoff n))
  let s := (p.compute N).lo
  have obs (k : Nat) (hk : k ≤ N) : (p.compute k).lo ≤ s ∧ s ≤ (p.compute k).hi := by
    have h := p.valid.2.1 k N hk
    exact ⟨h.1,Rat.le_trans h.2.1 h.2.2⟩
  have hs := obs (A.observation p j) (Nat.le_max_left _ _)
  have hq : (q.compute (A.next.observation q i)).lo ≤ s+1 ∧ s+1 ≤ (q.compute (A.next.observation q i)).hi := by
    have h := obs (A.next.observation q i) (Nat.le_max_right _ _)
    change (p.compute (A.next.observation q i)).lo+1 ≤ s+1 ∧ s+1 ≤ (p.compute (A.next.observation q i)).hi+1
    constructor <;> grind only
  have hs0 := obs 0 (Nat.zero_le _)
  have hsb := hp s hs0.1 hs0.2
  have hV := A.value_contains hp hx hxA (show A.cutoff j ≤ K by dsimp [K]; omega) hs
  have hW := A.next.value_contains (A.next_bounds hp) hx hxA (show A.next.cutoff i ≤ K+1 by dsimp [K]; omega) hq
  have hT := A.polynomial_tail hsb hx hxA (show A.cutoff n ≤ K by dsimp [K]; omega)
  have hU := A.polynomial_tail hsb hx hxA (show A.cutoff n ≤ K+1 by dsimp [K]; omega)
  have ht := qabs_sub_le (powerPolynomial s (K+1) x-powerPolynomial s (A.cutoff n) x)
    (powerPolynomial s K x-powerPolynomial s (A.cutoff n) x)
  rw [show (powerPolynomial s (K+1) x-powerPolynomial s (A.cutoff n) x)-
    (powerPolynomial s K x-powerPolynomial s (A.cutoff n) x)=powerPolynomial s (K+1) x-powerPolynomial s K x by grind only] at ht
  have hid : powerPolynomial s (K+1) x-powerPolynomial s K x=coefficient s K*x^K := by
    unfold powerPolynomial
    rw [sumBelow_succ]
    grind only
  rw [hid] at ht
  have hlo := neg_qabs_le_self (coefficient s K*x^K)
  have hhi := self_le_qabs (coefficient s K*x^K)
  have halg := powerPolynomial_parameter_succ s x K
  have hl := Rat.mul_le_mul_of_nonneg_left hV.1 hr
  have hh := Rat.mul_le_mul_of_nonneg_left hV.2 hr
  simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
  change ((A.next.value q x).compute i).lo ≤ (1-x)*((A.value p x).compute j).hi+_ ∧
    (1-x)*((A.value p x).compute j).lo ≤ ((A.next.value q x).compute i).hi+_
  constructor <;> grind only

/-- Exact exponent shift, independent of internal compact charts. -/
theorem canonical_shift (p : Real) {x : Rat} (hx : 0 ≤ x) (hx1 : x < 1) :
    (canonicalValue (shiftParameter p) x).Equiv (RealRaw.scaleRat (1-x) (canonicalValue p x)) := by
  let A := chart p x hx hx1
  have hp := chart_bounds p x hx hx1
  have hq := A.next_bounds hp
  have hv := canonicalValue_valid p hx hx1
  have hV := A.value_valid hp hx (Rat.le_refl)
  have hw := canonicalValue_valid (shiftParameter p) hx hx1
  have hW := A.next.value_valid hq hx (Rat.le_refl)
  have h1 := canonicalValue_agrees A.next hq hx (Rat.le_refl)
  have h2 := A.shift_identity hp hx (Rat.le_refl)
  have h3 := RealRaw.scaleRat_equiv (r := 1-x) (RealRaw.equiv_symm (canonicalValue_agrees A hp hx (Rat.le_refl)))
  exact RealRaw.equiv_trans hw hW (RealRaw.scaleRat_valid hv) h1
    (RealRaw.equiv_trans hW (RealRaw.scaleRat_valid hV) (RealRaw.scaleRat_valid hv) h2 h3)


private theorem coefficient_nonneg {s : Rat} (hs : s ≤ 2) (k : Nat) : 0 ≤ coefficient s k := by
  induction k with
  | zero => exact (by decide : (0 : Rat) ≤ 1)
  | succ k ih =>
    have hk := Rat.natCast_nonneg (a := k)
    unfold coefficient
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.mul_nonneg ih (by grind))
      (Rat.le_of_lt (Rat.inv_pos.mpr (by grind)))

private theorem polynomial_nonneg {s x : Rat} (hs : s ≤ 2) (hx : 0 ≤ x) (K : Nat) :
    0 ≤ powerPolynomial s K x := by
  induction K with
  | zero => exact Rat.le_refl
  | succ K ih =>
    have h := Rat.mul_nonneg (coefficient_nonneg hs K) (Rat.pow_nonneg hx (n := K))
    unfold powerPolynomial at *
    rw [sumBelow_succ]
    grind only

def lowerParameter (p : Real) : Real :=
  Real.ofRaw (RealRaw.sub p.preferred (RealRaw.ofRat 1)) (RealRaw.sub_valid p.valid (RealRaw.ofRat_valid 1))

theorem shift_lower_equiv (p : Real) : (shiftParameter (lowerParameter p)).Equiv p := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have ho := RealRaw.interval_order_of_valid _ p.valid n
  change (p.compute n).lo ≤ (p.compute n).hi at ho
  change ((p.compute n).lo-1)+1 ≤ (p.compute n).hi ∧ (p.compute n).lo ≤ ((p.compute n).hi-1)+1
  constructor <;> grind only

private theorem canonical_nonneg_bounded (m : Nat) (p : Real)
    (hp : ∀ n, (p.compute n).lo ≤ (m : Rat)+2) {x : Rat} (hx : 0 ≤ x) (hx1 : x < 1) :
    (RealRaw.ofRat 0).Le (canonicalValue p x) := by
  induction m generalizing p with
  | zero =>
    intro i j
    let A := chart p x hx hx1
    have hs := hp (A.observation p j)
    have hn0 : ((0 : Nat) : Rat)=0 := by decide
    rw [hn0] at hs
    let t := (p.compute (A.observation p j)).lo
    have ht : (p.compute (A.observation p j)).lo ≤ t ∧ t ≤ (p.compute (A.observation p j)).hi :=
      ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ p.valid _⟩
    have h := A.value_contains (chart_bounds p x hx hx1) hx (Rat.le_refl) (Nat.le_refl (A.cutoff j)) ht
    have hnon := polynomial_nonneg (show t ≤ 2 by dsimp [t]; grind) hx (A.cutoff j)
    rw [canonicalValue,dif_pos (And.intro hx hx1)]
    change 0 ≤ ((A.value p x).compute j).hi
    exact Rat.le_trans hnon h.2
  | succ m ih =>
    let q := lowerParameter p
    have hq : ∀ n, (q.compute n).lo ≤ (m : Rat)+2 := by
      intro n
      have h := hp n
      simp only [Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] at h
      change (p.compute n).lo-1 ≤ (m : Rat)+2
      grind only
    have hn := ih q hq
    have he1 := canonicalValue_equiv (shift_lower_equiv p) hx hx1
    have he2 := canonical_shift q hx hx1
    have hvq := canonicalValue_valid q hx hx1
    have hvs := canonicalValue_valid (shiftParameter q) hx hx1
    have hvp := canonicalValue_valid p hx hx1
    have he := RealRaw.equiv_trans (RealRaw.scaleRat_valid hvq) hvs hvp (RealRaw.equiv_symm he2) he1
    have hscale : (RealRaw.ofRat 0).Le (RealRaw.scaleRat (1-x) (canonicalValue q x)) := by
      intro i j
      have hh := hn i j
      change 0 ≤ ((canonicalValue q x).compute j).hi at hh
      have hr : 0 ≤ 1-x := by grind
      simp only [RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos hr]
      exact Rat.mul_nonneg hr hh
    exact RealRaw.le_trans (RealRaw.scaleRat_valid hvq) hscale
      (RealRaw.le_of_equiv (RealRaw.scaleRat_valid hvq) hvp he)

/-- Binomial powers are nonnegative for every represented exponent throughout
 their positive-base domain. Integer shifts reduce the proof to finite sums
 with nonnegative coefficients. -/
theorem canonical_nonneg (p : Real) {x : Rat} (hx : 0 ≤ x) (hx1 : x < 1) :
    (RealRaw.ofRat 0).Le (canonicalValue p x) := by
  apply canonical_nonneg_bounded (endpointM p) p (fun n => ?_) hx hx1
  have hn := p.valid.2.1 0 n (Nat.zero_le _)
  have hu := rational_upper_natural (p.compute 0).hi
  change (p.compute 0).lo ≤ (p.compute n).lo ∧ (p.compute n).lo ≤ (p.compute n).hi ∧
    (p.compute n).hi ≤ (p.compute 0).hi at hn
  unfold endpointM
  simp only [Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide]
  grind only

end BinomialPower.Global
end ComputableAnalysis
