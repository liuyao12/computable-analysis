import ComputableAnalysis.PowerSeriesFinite

/-! A computable sum of reciprocal powers at every represented exponent above
one. Finite independent summands, the integral tail, and rational width searches
produce nested lower and upper estimates. -/
namespace ComputableAnalysis.PowerIntegral
open Integral FormalPowerSeries BinomialPower BinomialPower.Global

def partialSum (p : Real) (N : Nat) : RealRaw := sumFrom p 1 N

theorem partialSum_valid (p : Real) (N : Nat) : (partialSum p N).Valid := sumFrom_valid p (by decide) N

theorem sumFrom_split (p : Real) (N d e stage : Nat) :
    ((sumFrom p N (d+e)).compute stage).lo=((sumFrom p N d).compute stage).lo+((sumFrom p (N+d) e).compute stage).lo ∧
    ((sumFrom p N (d+e)).compute stage).hi=((sumFrom p N d).compute stage).hi+((sumFrom p (N+d) e).compute stage).hi := by
  induction e with
  | zero =>
    change ((sumFrom p N (d+0)).compute stage).lo=((sumFrom p N d).compute stage).lo+0 ∧
      ((sumFrom p N (d+0)).compute stage).hi=((sumFrom p N d).compute stage).hi+0
    simp only [Nat.add_zero,Rat.add_zero]
    exact ⟨True.intro,True.intro⟩
  | succ e ih =>
    rw [show d+(e+1)=(d+e)+1 by omega]
    change ((sumFrom p N (d+e)).compute stage).lo+((infinityValue p ((N+(d+e) : Nat) : Rat)).compute stage).lo =
      ((sumFrom p N d).compute stage).lo+(((sumFrom p (N+d) e).compute stage).lo+((infinityValue p ((N+d+e : Nat) : Rat)).compute stage).lo) ∧
      ((sumFrom p N (d+e)).compute stage).hi+((infinityValue p ((N+(d+e) : Nat) : Rat)).compute stage).hi =
      ((sumFrom p N d).compute stage).hi+(((sumFrom p (N+d) e).compute stage).hi+((infinityValue p ((N+d+e : Nat) : Rat)).compute stage).hi)
    rw [show N+(d+e)=N+d+e by omega,ih.1,ih.2]
    constructor <;> grind only

theorem partialSum_tail (p : Real) (hp : AboveOne p) (j N M : Nat) (hN : 0 < N) (hNM : N ≤ M)
    (hcut : (N : Rat)⁻¹ ≤ endpointCutoff (endpointM p) j) :
    Within (partialSum p N) (partialSum p M) (2*endpointError (endpointQ p hp) (endpointM p) j) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hNM
  have ht := sumFrom_tail p hp j N d hN hcut
  intro i k
  have ho := (RealRaw.compareAt_overlap_iff _ _ i k).1
    (RealRaw.allStagesOverlap_refl _ (partialSum_valid p N) i k)
  have hs := sumFrom_split p 1 N d k
  have hh := ht 0 k
  rw [show 1+N=N+1 by omega] at hs
  change ((partialSum p N).compute i).lo ≤ ((partialSum p N).compute k).hi ∧
    ((partialSum p N).compute k).lo ≤ ((partialSum p N).compute i).hi at ho
  change ((partialSum p (N+d)).compute k).lo=((partialSum p N).compute k).lo+((sumFrom p (N+1) d).compute k).lo ∧
    ((partialSum p (N+d)).compute k).hi=((partialSum p N).compute k).hi+((sumFrom p (N+1) d).compute k).hi at hs
  change 0 ≤ ((sumFrom p (N+1) d).compute k).hi+_ ∧ ((sumFrom p (N+1) d).compute k).lo ≤ 0+_ at hh
  constructor <;> grind only

def seriesTailStage (p : Real) (hp : AboveOne p) (n : Nat) : Nat :=
  (firstCertified (fun j => endpointError (endpointQ p hp) (endpointM p) j ≤ ((1 : Rat)/2)^n)
    (endpointError_shrinks _ _ (RealParameterSample.tolerance n))).val

theorem seriesTailStage_spec (p : Real) (hp : AboveOne p) (n : Nat) :
    endpointError (endpointQ p hp) (endpointM p) (seriesTailStage p hp n) ≤ ((1 : Rat)/2)^n :=
  (firstCertified (fun j => endpointError (endpointQ p hp) (endpointM p) j ≤ ((1 : Rat)/2)^n)
    (endpointError_shrinks _ _ (RealParameterSample.tolerance n))).property

def seriesRequest (p : Real) (hp : AboveOne p) (n : Nat) : Nat :=
  (infinityCutoff p (seriesTailStage p hp n)).num.natAbs+1

def seriesCutoff (p : Real) (hp : AboveOne p) : Nat → Nat
  | 0 => seriesRequest p hp 0
  | n+1 => max (seriesCutoff p hp n) (seriesRequest p hp (n+1))

theorem seriesCutoff_request (p : Real) (hp : AboveOne p) (n : Nat) :
    seriesRequest p hp n ≤ seriesCutoff p hp n := by
  cases n with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_max_right _ _

theorem seriesCutoff_mono (p : Real) (hp : AboveOne p) {n m : Nat} (hnm : n ≤ m) :
    seriesCutoff p hp n ≤ seriesCutoff p hp m := by
  induction hnm with
  | refl => exact Nat.le_refl _
  | @step m _ ih => exact Nat.le_trans ih (Nat.le_max_left _ _)

theorem seriesCutoff_pos (p : Real) (hp : AboveOne p) (n : Nat) : 0 < seriesCutoff p hp n := by
  have h := seriesCutoff_request p hp n
  unfold seriesRequest at h
  omega

theorem seriesCutoff_tail (p : Real) (hp : AboveOne p) (n : Nat) :
    ((seriesCutoff p hp n : Nat) : Rat)⁻¹ ≤ endpointCutoff (endpointM p) (seriesTailStage p hp n) := by
  have h1 := rational_upper_natural (infinityCutoff p (seriesTailStage p hp n))
  have h2 : (seriesRequest p hp n : Rat) ≤ (seriesCutoff p hp n : Rat) := by
    exact_mod_cast seriesCutoff_request p hp n
  have hr : infinityCutoff p (seriesTailStage p hp n) ≤ (seriesRequest p hp n : Rat) := by
    simpa only [seriesRequest,Rat.natCast_add,show ((1 : Nat) : Rat)=1 by decide] using h1
  have he := IntegerPowerIntegral.inverse_antitone
    (show 0 < infinityCutoff p (seriesTailStage p hp n) by have := infinityCutoff_ge p (seriesTailStage p hp n); grind)
    (Rat.le_trans hr h2)
  simpa only [infinityCutoff,Rat.inv_inv] using he

def seriesPartial (p : Real) (hp : AboveOne p) (n : Nat) : Real :=
  Real.ofRaw (partialSum p (seriesCutoff p hp n)) (partialSum_valid p _)

def seriesCandidate (p : Real) (hp : AboveOne p) (n : Nat) : Rat :=
  RealParameterSample.sample (seriesPartial p hp n) n

theorem seriesCandidate_future (p : Real) (hp : AboveOne p) (n m : Nat) (hnm : n ≤ m) :
    qabs (seriesCandidate p hp m-seriesCandidate p hp n) ≤ 3*((1 : Rat)/2)^n := by
  have ht := partialSum_tail p hp (seriesTailStage p hp n) (seriesCutoff p hp n) (seriesCutoff p hp m)
    (seriesCutoff_pos p hp n) (seriesCutoff_mono p hp hnm) (seriesCutoff_tail p hp n)
  let i := RealParameterSample.stage (seriesPartial p hp n) n
  let j := RealParameterSample.stage (seriesPartial p hp m) m
  have hh := ht i j
  have hn := RealParameterSample.width (seriesPartial p hp n) n
  have hm := RealParameterSample.width (seriesPartial p hp m) m
  have he := seriesTailStage_spec p hp n
  have hpow := half_pow_antitone hnm
  change ((partialSum p (seriesCutoff p hp n)).compute i).hi-seriesCandidate p hp n ≤ ((1 : Rat)/2)^n at hn
  change ((partialSum p (seriesCutoff p hp m)).compute j).hi-seriesCandidate p hp m ≤ ((1 : Rat)/2)^m at hm
  change seriesCandidate p hp n ≤ ((partialSum p (seriesCutoff p hp m)).compute j).hi+_ ∧
    seriesCandidate p hp m ≤ ((partialSum p (seriesCutoff p hp n)).compute i).hi+_ at hh
  apply qabs_le_of_neg_le_le <;> grind only

/-- Executable nested rational estimates for the series. -/
def series (p : Real) (hp : AboveOne p) : RealRaw := GeometricSequence.raw (seriesCandidate p hp) 3

theorem series_valid (p : Real) (hp : AboveOne p) : (series p hp).Valid :=
  GeometricSequence.raw_valid (by decide : (0 : Rat) ≤ 3) (seriesCandidate_future p hp)

def SumsTo (p : Real) (I : RealRaw) : Prop :=
  I.Valid ∧ ∀ eps : QPos, ∃ N, ∀ n, N ≤ n → Within I (partialSum p n) eps.val

theorem series_within_partial (p : Real) (hp : AboveOne p) (j M : Nat) (hM : seriesCutoff p hp j ≤ M) :
    Within (series p hp) (partialSum p M) (6*((1 : Rat)/2)^j) := by
  have ht := partialSum_tail p hp (seriesTailStage p hp j) (seriesCutoff p hp j) M
    (seriesCutoff_pos p hp j) hM (seriesCutoff_tail p hp j)
  have hs := GeometricSequence.raw_within (series_valid p hp) j
  have he := seriesTailStage_spec p hp j
  have hw := RealParameterSample.width (seriesPartial p hp j) j
  let t := RealParameterSample.stage (seriesPartial p hp j) j
  change ((partialSum p (seriesCutoff p hp j)).compute t).hi-seriesCandidate p hp j ≤ ((1 : Rat)/2)^j at hw
  intro i k
  have h := ht t k
  have hraw := hs i 0
  change seriesCandidate p hp j ≤ ((partialSum p M).compute k).hi+_ ∧
    ((partialSum p M).compute k).lo ≤ ((partialSum p (seriesCutoff p hp j)).compute t).hi+_ at h
  change ((series p hp).compute i).lo ≤ seriesCandidate p hp j+3*((1 : Rat)/2)^j ∧
    seriesCandidate p hp j ≤ ((series p hp).compute i).hi+3*((1 : Rat)/2)^j at hraw
  have hpos := Rat.pow_nonneg (by decide +kernel : (0 : Rat) ≤ 1/2) (n := j)
  constructor <;> grind only

/-- Convergence of the independently evaluated `p`-series, derived from the
actual improper integral and its finite sum–integral comparison. -/
theorem series_sumsTo (p : Real) (hp : AboveOne p) : SumsTo p (series p hp) := by
  refine ⟨series_valid p hp,?_⟩
  intro eps
  obtain ⟨j,hj⟩ := GeometricSequence.shrinks (by decide : (0 : Rat) ≤ 6) eps
  refine ⟨seriesCutoff p hp j,fun M hM => ?_⟩
  have h := series_within_partial p hp j M hM
  have he := hj j (Nat.le_refl _)
  intro n m
  have hh := h n m
  constructor <;> grind only

/-- Explicit stage estimates: candidate minus/plus `3·2⁻ⁿ`, intersected with
all earlier estimates; the output width is at most `6·2⁻ⁿ`. -/
theorem series_stage_bounds (p : Real) (hp : AboveOne p) (n : Nat) :
    seriesCandidate p hp n-3*((1 : Rat)/2)^n ≤ ((series p hp).compute n).lo ∧
    ((series p hp).compute n).hi ≤ seriesCandidate p hp n+3*((1 : Rat)/2)^n ∧
    ((series p hp).compute n).width ≤ 6*((1 : Rat)/2)^n := by
  have h := GeometricSequence.raw_enclosure (seriesCandidate p hp) 3 n
  have hw := GeometricSequence.raw_width (series_valid p hp) n
  exact ⟨h.1,h.2,by simpa only [series,show (2 : Rat)*3=6 by decide +kernel] using hw.2⟩


theorem sumFrom_equiv {p q : Real} (heq : p.Equiv q) {N : Nat} (hN : 0 < N) (d : Nat) :
    (sumFrom p N d).Equiv (sumFrom q N d) := by
  induction d with
  | zero => exact RealRaw.equiv_refl _ (RealRaw.ofRat_valid 0)
  | succ d ih =>
    have hx : 1 ≤ ((N+d : Nat) : Rat) := by exact_mod_cast (show 1 ≤ N+d by omega)
    exact RealRaw.add_equiv (sumFrom_valid p hN d) (sumFrom_valid q hN d)
      (infinityValue_valid p hx) (infinityValue_valid q hx) ih (infinityValue_equiv heq hx)

theorem SumsTo.unique {p : Real} {I J : RealRaw} (hI : SumsTo p I) (hJ : SumsTo p J) : I.Equiv J := by
  have le (X Y : RealRaw) (hX : SumsTo p X) (hY : SumsTo p Y) : X.Le Y := by
    intro i j
    by_cases hh : (X.compute i).lo ≤ (Y.compute j).hi
    · exact hh
    exfalso
    let eps : QPos := ⟨((X.compute i).lo-(Y.compute j).hi)/4,by grind⟩
    obtain ⟨N,hN⟩ := hX.2 eps
    obtain ⟨M,hM⟩ := hY.2 eps
    let K := max N M
    obtain ⟨r,hr⟩ := (partialSum_valid p K).2.2 eps
    have hw := hr r (Nat.le_refl _)
    have hx := (hN K (Nat.le_max_left _ _) i r).1
    have hy := (hM K (Nat.le_max_right _ _) j r).2
    change ((partialSum p K).compute r).hi-((partialSum p K).compute r).lo ≤
      ((X.compute i).lo-(Y.compute j).hi)/4 at hw
    change (X.compute i).lo ≤ ((partialSum p K).compute r).hi+((X.compute i).lo-(Y.compute j).hi)/4 at hx
    change ((partialSum p K).compute r).lo ≤ (Y.compute j).hi+((X.compute i).lo-(Y.compute j).hi)/4 at hy
    grind only
  exact RealRaw.equiv_of_le_of_ge (le I J hI hJ) (le J I hJ hI)

theorem SumsTo.congr_parameter {p q : Real} {I : RealRaw} (heq : p.Equiv q) (hI : SumsTo p I) : SumsTo q I := by
  refine ⟨hI.1,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := hI.2 eps
  refine ⟨N,fun n hn => ?_⟩
  exact ((hN n hn).symm.congr_left (partialSum_valid q n) (partialSum_valid p n)
    (RealRaw.equiv_symm (sumFrom_equiv heq (by decide : 0 < 1) n))).symm

/-- Neither the exponent name nor any internal cutoff/precision choices
change the exact series value. -/
theorem series_equiv {p q : Real} (hp : AboveOne p) (hq : AboveOne q) (heq : p.Equiv q) :
    (series p hp).Equiv (series q hq) :=
  (series_sumsTo p hp).unique ((series_sumsTo q hq).congr_parameter (RealRaw.equiv_symm heq))

end ComputableAnalysis.PowerIntegral
