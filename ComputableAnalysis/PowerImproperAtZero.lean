import ComputableAnalysis.BinomialEndpointChart

/-! The improper reciprocal-power integral at zero, for every represented
exponent strictly below one. Its finite integral witnesses and a quantitative
endpoint bound are constructed independently of any infinite series. -/
namespace ComputableAnalysis
open FormalPowerSeries ZetaReal Integral BinomialPower BinomialPower.Global

namespace RealRaw
/-- A later positive input enclosure supplies a point in every earlier output
box of the executable reciprocal algorithm. -/
theorem positiveInv_contains_later {x : RealRaw} {N i n : Nat} {t : Rat}
    (hx : x.Valid) (hpos : 0 < (x.compute N).lo) (hN : N ≤ n) (hi : i ≤ n)
    (ht : (x.compute n).lo ≤ t ∧ t ≤ (x.compute n).hi) :
    ((positiveInv x N).compute i).lo ≤ 1/t ∧ 1/t ≤ ((positiveInv x N).compute i).hi := by
  have hn := hx.2.1 N n hN
  have hlow : 0 < (x.compute n).lo := by grind
  have htpos : 0 < t := by grind
  have h1 := QInterval.one_div_le_one_div_of_pos htpos ht.2
  have h2 := QInterval.one_div_le_one_div_of_pos hlow ht.1
  have ho := (positiveInv_valid hx hpos).2.1 i n hi
  have hc : (positiveInv x N).compute n=QInterval.inv (x.compute n) := by
    simp only [positiveInv,positiveInvCompute,if_neg (show ¬n<N by omega)]
  rw [hc,QInterval.inv_of_pos hlow] at ho
  change ((positiveInv x N).compute i).lo ≤ 1/(x.compute n).hi ∧
    1/(x.compute n).hi ≤ 1/(x.compute n).lo ∧
    1/(x.compute n).lo ≤ ((positiveInv x N).compute i).hi at ho
  constructor <;> grind only

/-- Reciprocal evaluation is independent of both the name and separation stage. -/
theorem positiveInv_equiv_names {x y : RealRaw} {N M : Nat}
    (hx : x.Valid) (hy : y.Valid) (heq : x.Equiv y)
    (hN : 0 < (x.compute N).lo) (hM : 0 < (y.compute M).lo) :
    (positiveInv x N).Equiv (positiveInv y M) := by
  let K := max N M
  have hxK : 0 < (x.compute K).lo := by have := (hx.2.1 N K (Nat.le_max_left _ _)).1; grind only
  have hyK : 0 < (y.compute K).lo := by have := (hy.2.1 M K (Nat.le_max_right _ _)).1; grind only
  exact equiv_trans (positiveInv_valid hx hN) (positiveInv_valid hx hxK) (positiveInv_valid hy hM)
    (positiveInv_equiv_of_stages hx hN hxK)
    (equiv_trans (positiveInv_valid hx hxK) (positiveInv_valid hy hyK) (positiveInv_valid hy hM)
      (positiveInv_equiv_of_input hx hy heq hxK hyK) (positiveInv_equiv_of_stages hy hyK hM))

end RealRaw

namespace BinomialPower

def endpointTotal (s : Real) (hs : AboveOne s) : RealRaw :=
  RealRaw.positiveInv (RealRaw.sub s.preferred (RealRaw.ofRat 1)) (separationStage s hs)

theorem endpointTotal_valid (s : Real) (hs : AboveOne s) : (endpointTotal s hs).Valid := by
  apply RealRaw.positiveInv_valid (RealRaw.sub_valid s.valid (RealRaw.ofRat_valid 1))
  change 0 < (s.compute (separationStage s hs)).lo-1
  have h := separationStage_spec s hs
  grind only

theorem integrated_zero (s : Rat) (K : Nat) : integratedPowerPolynomial s K 0=0 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    unfold integratedPowerPolynomial at *
    rw [sumBelow_succ,Rat.pow_succ,Rat.mul_zero,Rat.mul_zero,Rat.div_def,Rat.zero_mul,ih,Rat.add_zero]

/-- Tail control between the independent reciprocal computation and an actual
compact binomial integral. The error is uniform in both evaluation stages. -/
theorem endpointTotal_within_cutoff (s : Real) (hs : AboveOne s) (j : Nat) {a : Rat}
    (ha0 : 0 < a) (hac : a ≤ endpointCutoff (endpointM s) j) :
    Within (endpointTotal s hs)
      (canonicalIntegral s 0 (1-a) (by decide)
        (by have := endpointCutoff_bounds (endpointM s) j; grind)
        (by have := endpointCutoff_bounds (endpointM s) j; grind))
      (endpointError (endpointQ s hs) (endpointM s) j) := by
  have ha : 0 < a ∧ a ≤ 1 := ⟨ha0,Rat.le_trans hac (endpointCutoff_bounds (endpointM s) j).2⟩
  let A := chart s (1-a) (by grind) (by grind)
  have hp := chart_bounds s (1-a) (by grind) (by grind)
  intro i k
  let n := max (separationStage s hs) (max i (A.observation s k))
  let t := (s.compute n).lo
  have ht : (s.compute n).lo ≤ t ∧ t ≤ (s.compute n).hi :=
    ⟨Rat.le_refl,RealRaw.interval_order_of_valid _ s.valid n⟩
  have hchart := endpoint_chart s hs (show separationStage s hs ≤ n by exact Nat.le_max_left _ _) ht
  have hn := s.valid.2.1 (A.observation s k) n (by dsimp [n]; omega)
  have htA : (s.compute (A.observation s k)).lo ≤ t ∧ t ≤ (s.compute (A.observation s k)).hi := by
    change (s.compute (A.observation s k)).lo ≤ (s.compute n).lo ∧
      (s.compute n).lo ≤ (s.compute n).hi ∧ (s.compute n).hi ≤ (s.compute (A.observation s k)).hi at hn
    constructor <;> grind only
  let L := max (A.cutoff k) (ZetaReal.cutoff (endpointM s) j)
  have hI := A.integral_contains hp (show (0 : Rat) ≤ 0 by decide) (show 0 ≤ 1-a by grind)
    (show 1-a ≤ A.radius by exact Rat.le_refl) (show A.cutoff k ≤ L by exact Nat.le_max_left _ _) htA
  rw [integrated_prefix_eq,integrated_prefix_eq,integrated_zero] at hI
  have hpos : 0 < ((RealRaw.sub s.preferred (RealRaw.ofRat 1)).compute (separationStage s hs)).lo := by
    change 0 < (s.compute (separationStage s hs)).lo-1
    have := separationStage_spec s hs
    grind only
  have hT := RealRaw.positiveInv_contains_later
    (x := RealRaw.sub s.preferred (RealRaw.ofRat 1)) (N := separationStage s hs) (i := i) (n := n) (t := t-1)
    (RealRaw.sub_valid s.valid (RealRaw.ofRat_valid 1)) hpos
    (by dsimp [n]; omega) (by dsimp [n]; omega) (by
      change (s.compute n).lo-1 ≤ t-1 ∧ t-1 ≤ (s.compute n).hi-1
      constructor <;> grind only)
  have he := integrated_endpoint_error_le_cutoff hchart j L (Nat.le_max_right _ _) (Rat.le_of_lt ha0) hac
  have hlo := neg_qabs_le_self (integratedPowerPolynomial t L (1-a)-1/(t-1))
  have hhi := self_le_qabs (integratedPowerPolynomial t L (1-a)-1/(t-1))
  change ((endpointTotal s hs).compute i).lo ≤ 1/(t-1) ∧ 1/(t-1) ≤ ((endpointTotal s hs).compute i).hi at hT
  change ((endpointTotal s hs).compute i).lo ≤ ((A.integral s 0 (1-a)).compute k).hi+_ ∧
    ((A.integral s 0 (1-a)).compute k).lo ≤ ((endpointTotal s hs).compute i).hi+_
  change qabs (integratedPowerPolynomial t L (1-a)-1/(t-1)) ≤ _ at he
  constructor <;> grind only

theorem endpointTotal_within (s : Real) (hs : AboveOne s) (j : Nat) :
    Within (endpointTotal s hs)
      (canonicalIntegral s 0 (1-endpointCutoff (endpointM s) j) (by decide)
        (by have := endpointCutoff_bounds (endpointM s) j; grind)
        (by have := endpointCutoff_bounds (endpointM s) j; grind))
      (endpointError (endpointQ s hs) (endpointM s) j) :=
  endpointTotal_within_cutoff s hs j (endpointCutoff_bounds (endpointM s) j).1 (Rat.le_refl)

end BinomialPower

namespace PowerIntegral

/-- Constructive strict inequality, witnessed by one finite enclosure. -/
def BelowOne (p : Real) : Prop := ∃ n, (p.compute n).hi < 1

theorem parameter_aboveOne {p : Real} (hp : BelowOne p) : AboveOne (parameter p) := by
  obtain ⟨n,hn⟩ := hp
  refine ⟨n,?_⟩
  change 1 < 2-(p.compute n).hi
  grind only

/-- The computation of `1/(1-p)`, with its separation stage found by search. -/
def zeroIntegral (p : Real) (hp : BelowOne p) : RealRaw :=
  endpointTotal (parameter p) (parameter_aboveOne hp)

def zeroCutoff (p : Real) (j : Nat) : Rat := endpointCutoff (endpointM (parameter p)) j

def zeroError (p : Real) (hp : BelowOne p) (j : Nat) : Rat :=
  endpointError (endpointQ (parameter p) (parameter_aboveOne hp)) (endpointM (parameter p)) j

theorem zeroCutoff_bounds (p : Real) (j : Nat) : 0 < zeroCutoff p j ∧ zeroCutoff p j ≤ 1 :=
  endpointCutoff_bounds _ _

def zeroExhaustion (p : Real) (j : Nat) : FunctionOnInterval :=
  function p (zeroCutoff p j) 1 (zeroCutoff_bounds p j).1 (Rat.le_refl)

theorem zero_compact (p : Real) (j : Nat) :
    HasIntegral (zeroExhaustion p j)
      (compact p (zeroCutoff p j) 1 (zeroCutoff_bounds p j).1 (zeroCutoff_bounds p j).2 (Rat.le_refl)) :=
  compact_hasIntegral p (zeroCutoff_bounds p j).1 (zeroCutoff_bounds p j).2 (Rat.le_refl)

theorem zero_tail (p : Real) (hp : BelowOne p) (j : Nat) :
    Within (zeroIntegral p hp)
      (compact p (zeroCutoff p j) 1 (zeroCutoff_bounds p j).1 (zeroCutoff_bounds p j).2 (Rat.le_refl))
      (zeroError p hp j) := by
  have h := endpointTotal_within (parameter p) (parameter_aboveOne hp) j
  simpa only [compact,zeroIntegral,zeroCutoff,zeroError,show (1 : Rat)-1=0 by decide +kernel] using h

/-- The improper integral is a limit of constructed compact integrals, with a
function-specific executable exhaustion and tail schedule. -/
theorem zero_hasIntegralLimit (p : Real) (hp : BelowOne p) :
    HasIntegralLimit (zeroExhaustion p) (zeroIntegral p hp) := by
  have hv := endpointTotal_valid (parameter p) (parameter_aboveOne hp)
  refine ⟨hv,fun j => ⟨_,zero_compact p j⟩,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := endpointError_shrinks (endpointQ (parameter p) (parameter_aboveOne hp)) (endpointM (parameter p)) eps
  refine ⟨N,fun j hj J hJ => ?_⟩
  have hc := zero_compact p j
  have ht := (zero_tail p hp j).symm.congr_left hJ.valid hc.valid (hJ.unique hc)
  have hh := ht.symm
  have he := hN j hj
  intro n m
  have h := hh n m
  change zeroError p hp j ≤ eps.val at he
  constructor <;> grind only

/-- The lower endpoints approach zero; thus the supplied compact intervals
cover every positive point of the requested integration domain. -/
theorem zero_exhausts (p : Real) : ShrinksToZero (zeroCutoff p) := endpointCutoff_shrinks _


/-- Exact identity with the ordinary reciprocal algorithm, not merely an
endpoint candidate or a numerical coincidence. -/
theorem zero_closedForm (p : Real) (hp : BelowOne p) :
    (zeroIntegral p hp).Equiv
      (RealRaw.positiveInv (RealRaw.sub (RealRaw.ofRat 1) p.preferred)
        (separationStage (parameter p) (parameter_aboveOne hp))) := by
  have hpos := separationStage_spec (parameter p) (parameter_aboveOne hp)
  change 1 < 2-(p.compute (separationStage (parameter p) (parameter_aboveOne hp))).hi at hpos
  apply RealRaw.positiveInv_equiv_of_input
    (RealRaw.sub_valid (parameter p).valid (RealRaw.ofRat_valid 1))
    (RealRaw.sub_valid (RealRaw.ofRat_valid 1) p.valid)
  · exact RealRaw.equiv_symm (parameter_factor p)
  · change 0 < (2-(p.compute (separationStage (parameter p) (parameter_aboveOne hp))).hi)-1
    grind only
  · change 0 < 1-(p.compute (separationStage (parameter p) (parameter_aboveOne hp))).hi
    grind only

theorem zero_equiv {p q : Real} (hp : BelowOne p) (hq : BelowOne q) (heq : p.Equiv q) :
    (zeroIntegral p hp).Equiv (zeroIntegral q hq) := by
  have hpar := RealRaw.sub_equiv (RealRaw.ofRat_valid 2) (RealRaw.ofRat_valid 2) p.valid q.valid
    (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 2)) heq
  have he := RealRaw.sub_equiv (parameter p).valid (parameter q).valid (RealRaw.ofRat_valid 1) (RealRaw.ofRat_valid 1)
    hpar (RealRaw.equiv_refl _ (RealRaw.ofRat_valid 1))
  apply RealRaw.positiveInv_equiv_names
    (RealRaw.sub_valid (parameter p).valid (RealRaw.ofRat_valid 1))
    (RealRaw.sub_valid (parameter q).valid (RealRaw.ofRat_valid 1)) he
  · change 0 < ((parameter p).compute (separationStage (parameter p) (parameter_aboveOne hp))).lo-1
    have := separationStage_spec (parameter p) (parameter_aboveOne hp)
    grind only
  · change 0 < ((parameter q).compute (separationStage (parameter q) (parameter_aboveOne hq))).lo-1
    have := separationStage_spec (parameter q) (parameter_aboveOne hq)
    grind only

end PowerIntegral
end ComputableAnalysis
