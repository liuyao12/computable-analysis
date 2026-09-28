import ComputableAnalysis.CosineSquareData

/-! The complementary rectangle computation. Its centres are literal sine-square
sums, by the exact circle identity at every finite sample. No integral value
is used in this construction. -/
namespace ComputableAnalysis.SineSquare
open ClosedArctanInverse ClockTrigonometry MonotoneAverage IntervalSelections

abbrev sample (t : Rat) (q : Nat) : Rat := s t q*s t q

theorem sample_complement (t : Rat) (q : Nat) :
    sample t q=1-CosineSquare.sample t q := by
  have h:=ClockTrigonometry.sample_unit t q
  dsimp [sample,CosineSquare.sample]; grind only

private theorem left_constant (v a b : Rat) (n : Nat) : left (fun _=>v) a b n=v := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def];grind

theorem left_complement (a b : Rat) (d q : Nat) :
    left (fun t=>sample t q) a b d=1-left (fun t=>CosineSquare.sample t q) a b d := by
  have he : (fun t=>sample t q)=(fun t=>1-CosineSquare.sample t q) := funext (fun t=>sample_complement t q)
  rw [he]
  rw [left_sub,left_constant]

def quarterIntegral : RealRaw := RealRaw.sub (RealRaw.ofRat 1) CosineSquare.quarterIntegral
def integral : RealRaw := RealRaw.scaleRat (1/2) quarterIntegral
def sumSample (q : Nat) : Rat := left (fun t=>sample t q) 0 1 q

theorem sumSample_complement (q : Nat) : sumSample q=1-CosineSquare.sumSample q :=
  left_complement 0 1 q q

theorem quarterIntegral_valid : quarterIntegral.Valid :=
  RealRaw.sub_valid (RealRaw.ofRat_valid _) CosineSquare.quarterIntegral_valid

theorem integral_valid : integral.Valid := RealRaw.scaleRat_valid quarterIntegral_valid

theorem sample_mem (t : Rat) (ht : Unit t) (q : Nat) :
    InBox (sample t q) ((RealRaw.mul (sine t) (sine t)).compute q) :=
  mul_mem (s_mem ht q) (s_mem ht q)

theorem sumSample_mem (q : Nat) : InBox (sumSample q) (quarterIntegral.compute q) := by
  rw [sumSample_complement]
  exact sub_mem (rat_mem 1 q) (CosineSquare.sumSample_mem q)

theorem mesh_comparison (d q : Nat) (hdq : d≤q) :
    qabs (sumSample q-left (fun t=>sample t q) 0 1 d) ≤ meshRadius d := by
  rw [sumSample_complement,left_complement]
  have he : (1-CosineSquare.sumSample q)-(1-left (fun t=>CosineSquare.sample t q) 0 1 d)=
      -(CosineSquare.sumSample q-left (fun t=>CosineSquare.sample t q) 0 1 d) := by grind only
  rw [he,qabs_neg]
  exact CosineSquare.mesh_comparison d q hdq

theorem normalize_value (h : quarterIntegral.Equiv (RealRaw.ofRat (1/2))) :
    integral.Equiv (RealRaw.ofRat (1/4)) := by
  have hs:=RealRaw.scaleRat_equiv (r:=1/2) h
  intro n
  have ho:=(RealRaw.compareAt_overlap_iff _ _ n n).1 (hs n)
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hp : (0:Rat)≤1/2 := by decide +kernel
  have he : (1/2:Rat)*(1/2)=1/4 := by decide +kernel
  simpa only [integral,RealRaw.scaleRat,RealRaw.scaleRatCompute,RealRaw.ofRat,
    if_pos hp,QInterval.Overlaps,he] using ho

end ComputableAnalysis.SineSquare
