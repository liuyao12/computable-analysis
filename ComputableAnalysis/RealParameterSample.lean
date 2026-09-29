import ComputableAnalysis.ComputableCoefficientApproximation
import ComputableAnalysis.GeometricSeriesCalculus

/-! Executable rational samples of arbitrary valid represented parameters,
with one explicit geometric error and no equality or sign decision. -/
namespace ComputableAnalysis.RealParameterSample

def tolerance (n : Nat) : QPos := ⟨((1 : Rat)/2)^n, Rat.pow_pos (by decide +kernel)⟩

def stage (p : Real) : Nat → Nat
  | 0 => ComputableCoefficient.widthStage p (tolerance 0)
  | n+1 => max (stage p n) (ComputableCoefficient.widthStage p (tolerance (n+1)))

theorem widthStage_le (p : Real) (n : Nat) :
    ComputableCoefficient.widthStage p (tolerance n) ≤ stage p n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_max_right _ _

theorem stage_mono (p : Real) {k n : Nat} (hkn : k ≤ n) : stage p k ≤ stage p n := by
  induction hkn with
  | refl => exact Nat.le_refl _
  | @step n hkn ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

def sample (p : Real) (n : Nat) : Rat := (p.compute (stage p n)).lo

theorem width (p : Real) (n : Nat) :
    (p.compute (stage p n)).width ≤ ((1 : Rat)/2)^n := by
  have hn := p.valid.2.1 _ _ (widthStage_le p n)
  have hw := ComputableCoefficient.widthStage_spec p (tolerance n)
  unfold QInterval.width at *
  change _ ≤ ((1 : Rat)/2)^n at hw
  change (p.preferred.compute _).hi-(p.preferred.compute _).lo ≤ _ at hw ⊢
  grind only

theorem sample_mem (p : Real) {k n : Nat} (hkn : k ≤ n) :
    (p.compute (stage p k)).lo ≤ sample p n ∧ sample p n ≤ (p.compute (stage p k)).hi := by
  have hn := p.valid.2.1 _ _ (stage_mono p hkn)
  exact ⟨hn.1, Rat.le_trans hn.2.1 hn.2.2⟩

theorem sample_initial (p : Real) (n : Nat) :
    (p.compute 0).lo ≤ sample p n ∧ sample p n ≤ (p.compute 0).hi := by
  have hn := p.valid.2.1 0 (stage p n) (Nat.zero_le _)
  exact ⟨hn.1, Rat.le_trans hn.2.1 hn.2.2⟩

theorem sample_future (p : Real) {k n : Nat} (hkn : k ≤ n) :
    qabs (sample p n-sample p k) ≤ ((1 : Rat)/2)^k := by
  have hx := sample_mem p hkn
  have hy := sample_mem p (Nat.le_refl k)
  have hd := qabs_sub_le_of_common_bounds hx.1 hx.2 hy.1 hy.2
  exact Rat.le_trans hd (width p k)

/-- Every rational point in the parameter box is close to the chosen sample.
This is also used to prove invariance under a different real representation. -/
theorem point_sample (p : Real) {n : Nat} {s : Rat}
    (hs : (p.compute (stage p n)).lo ≤ s ∧ s ≤ (p.compute (stage p n)).hi) :
    qabs (s-sample p n) ≤ ((1 : Rat)/2)^n := by
  have hp := sample_mem p (Nat.le_refl n)
  exact Rat.le_trans (qabs_sub_le_of_common_bounds hs.1 hs.2 hp.1 hp.2) (width p n)

end ComputableAnalysis.RealParameterSample
