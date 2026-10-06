import ComputableAnalysis.ExponentialComputations.QuadraticFTC
import ComputableAnalysis.ComputableCoefficientApproximation
import ComputableAnalysis.RiemannHilbert.PrecisionSearch

/-! Literal finite rectangle bounds for a supplied represented Lipschitz
integrand. Width searches inspect rational boxes and are executable. -/
namespace ComputableAnalysis.ExponentialComputations
open ComplexRaw FunctionTheory RiemannHilbert
set_option maxHeartbeats 1000000

private def pointRaw (f : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) : RealRaw := {compute := f.compute x hx}
private theorem point_valid (f : FunctionOnInterval) (x : Rat)
    (hx : inDomainInterval f.lower f.upper x) : (pointRaw f x hx).Valid :=
  f.valid_on x (f.defined_on x hx)

private theorem gridEventually (L : Rat) (eps : QPos) : ∃ N : Nat, ∀ n : Nat, N≤n →
    decide (4*qabs L*(1/2:Rat)^n≤eps.val)=true := by
  refine ⟨RationalMajorant.halfDecayShift (4*qabs L) eps,fun n hn => ?_⟩
  simp only [decide_eq_true_eq]
  exact RationalMajorant.halfDecayShift_spec_of_le
    (Rat.mul_nonneg (by decide +kernel) (qabs_nonneg L)) eps hn

/-- Find the first adequate binary mesh, rather than exponentiating a loose
existence bound. The latter is used only in the termination proof. -/
private def gridShift (L : Rat) (eps : QPos) : Nat := PrecisionSearch.firstFrom
  (fun n => decide (4*qabs L*(1/2:Rat)^n≤eps.val)) (gridEventually L eps) 0

private theorem gridShift_spec (L : Rat) (eps : QPos) :
    4*qabs L*(1/2:Rat)^gridShift L eps≤eps.val := by
  have h := (PrecisionSearch.firstFrom_spec
    (fun n => decide (4*qabs L*(1/2:Rat)^n≤eps.val)) (gridEventually L eps) 0).2
  simpa only [gridShift,decide_eq_true_eq] using h

private def grid (f : FunctionOnInterval) (h0 : f.lower=0) (h1 : f.upper=1)
    (L : Rat) (eps : QPos) : RationalPartition f.lower f.upper :=
  RationalPartition.uniform f.lower f.upper (2^gridShift L eps)
    (Nat.pow_pos (by decide)) (by rw [h0,h1]; decide +kernel)
private def mesh (L : Rat) (eps : QPos) : Rat := (1/2:Rat)^gridShift L eps
private theorem grid_width (f : FunctionOnInterval) (h0 : f.lower=0) (h1 : f.upper=1)
    (L : Rat) (eps : QPos) (k : Nat) :
    (grid f h0 h1 L eps).point (k+1)-(grid f h0 h1 L eps).point k = mesh L eps := by
  change leftPoint f.lower f.upper (2^gridShift L eps) (k+1)-
    leftPoint f.lower f.upper (2^gridShift L eps) k = _
  rw [leftPoint_step,h0,h1]
  simp only [ComputableAnalysis.mesh, if_neg (Nat.ne_of_gt (Nat.pow_pos (by decide : 0 < (2:Nat)) (n := gridShift L eps))),
    show (1:Rat)-0=1 by decide +kernel]
  exact (RationalMajorant.half_pow_eq_one_div_nat_two_pow _).symm
private def tolerance (eps : QPos) : QPos := ⟨eps.val/2,by
  rw [Rat.div_def]; exact Rat.mul_pos eps.property (by decide +kernel)⟩

private def sampleBox (f : FunctionOnInterval) (P : RationalPartition f.lower f.upper)
    (eps : QPos) (k : Nat) : QInterval :=
  if hk : k<P.pieces then
    let X := Real.ofRaw (pointRaw f (P.point k) (P.point_in_bounds (Nat.le_of_lt hk)))
      (point_valid f _ _)
    X.compute (ComputableCoefficient.widthStage X (tolerance eps))
  else {lo := 0,hi := 0}

/-- Actual point boxes widened by a justified variation bound on the cell. -/
def lipschitzBounds (f : FunctionOnInterval) (h0 : f.lower=0) (h1 : f.upper=1)
    (L : Rat) (hL : 0 ≤ L)
    (hlip : ∀ x y (hx : inDomainInterval f.lower f.upper x)
      (hy : inDomainInterval f.lower f.upper y),
      Small (ofRealRaw (RealRaw.sub (pointRaw f x hx) (pointRaw f y hy))) (L*qabs (x-y)))
    (eps : QPos) : Integral.Bounds f := by
  let P := grid f h0 h1 L eps
  refine { partition := P
           lower := fun k => (sampleBox f P eps k).lo - L * mesh L eps
           upper := fun k => (sampleBox f P eps k).hi + L * mesh L eps
           lower_le := ?_
           upper_ge := ?_ }
  all_goals
    intro k hk x hx n
    let c := P.point k
    have hc : inDomainInterval f.lower f.upper c := P.point_in_bounds (Nat.le_of_lt hk)
    have hxm := (P.cell k hk).contains_inDomain hx
    let X := Real.ofRaw (pointRaw f c hc) (point_valid f c hc)
    let s := ComputableCoefficient.widthStage X (tolerance eps)
    have hd : qabs (x-c) ≤ mesh L eps := by
      have hg := grid_width f h0 h1 L eps k
      have hxlo := hx.1
      have hxhi := hx.2
      change P.point k≤x at hxlo
      change x≤P.point (k+1) at hxhi
      rw [qabs_eq_self_of_nonneg (show 0 ≤ x-c by dsimp [c]; grind only)]
      change P.point (k+1)-P.point k=mesh L eps at hg
      dsimp [c]; grind only
    have hm : 0≤mesh L eps := Rat.pow_nonneg (by decide +kernel)
    have hE : 0 ≤ L*mesh L eps := Rat.mul_nonneg hL hm
    have hh := (hlip x c hxm hc).mono (Rat.mul_le_mul_of_nonneg_left hd hL)
    have hh' : Small (ofRealRaw (RealRaw.sub (pointRaw f x hxm)
        (RealRaw.scaleRat 1 (pointRaw f c hc)))) (L*mesh L eps) := by
      simpa only [Small,RealRaw.Le,ofRealRaw,realPart,imagPart,RealRaw.sub,RealRaw.subCompute,
        RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (show (0:Rat)≤1 by decide +kernel),Rat.one_mul] using hh
    have hlo : (RealRaw.ofRat (X.compute s).lo).Le (pointRaw f c hc) :=
      fun _ m => RealRaw.le_refl _ (point_valid f c hc) s m
    have hhi : (pointRaw f c hc).Le (RealRaw.ofRat (X.compute s).hi) :=
      fun m _ => RealRaw.le_refl _ (point_valid f c hc) m s
    have h := remainder_order (pointRaw f x hxm) (pointRaw f c hc)
      (point_valid f x hxm) (point_valid f c hc) 1 (L*mesh L eps)
      (X.compute s).lo (X.compute s).hi (by decide +kernel) hh' hlo hhi
    simp only [Rat.one_mul] at h
    first
    | simpa only [sampleBox,dif_pos hk,X,s,c,RealRaw.ofRat,pointRaw] using h.1 0 n
    | simpa only [sampleBox,dif_pos hk,X,s,c,RealRaw.ofRat,pointRaw] using h.2 n 0

private theorem sum_sub (f g : Nat → Rat) (n : Nat) :
    Integral.rectangleSum f n-Integral.rectangleSum g n = Integral.rectangleSum (fun k => f k-g k) n := by
  induction n with
  | zero => simp only [Integral.rectangleSum]; grind only
  | succ n ih => simp only [Integral.rectangleSum]; grind only

/-- The computed finite bounds become arbitrarily tight. -/
theorem lipschitzBounds_gap (f : FunctionOnInterval) (h0 : f.lower=0) (h1 : f.upper=1)
    (L : Rat) (hL : 0≤L) (hlip) (eps : QPos) :
    (lipschitzBounds f h0 h1 L hL hlip eps).upperSum-
      (lipschitzBounds f h0 h1 L hL hlip eps).lowerSum ≤ eps.val := by
  let B := lipschitzBounds f h0 h1 L hL hlip eps
  let P := B.partition
  have hg : ∀ k, k<P.pieces → B.upper k-B.lower k ≤ eps.val/2+2*L*mesh L eps := by
    intro k hk
    have hs := ComputableCoefficient.widthStage_spec
      (Real.ofRaw (pointRaw f (P.point k) (P.point_in_bounds (Nat.le_of_lt hk))) (point_valid f _ _))
      (tolerance eps)
    change (sampleBox f P eps k).hi+L*mesh L eps-
      ((sampleBox f P eps k).lo-L*mesh L eps) ≤ _
    have hbox : sampleBox f P eps k =
        (Real.ofRaw (pointRaw f (P.point k) (P.point_in_bounds (Nat.le_of_lt hk))) (point_valid f _ _)).compute
          (ComputableCoefficient.widthStage
            (Real.ofRaw (pointRaw f (P.point k) (P.point_in_bounds (Nat.le_of_lt hk))) (point_valid f _ _)) (tolerance eps)) := by
      simp only [sampleBox,dif_pos hk]
    rw [hbox]
    change _- _ ≤ eps.val/2 at hs
    grind only
  have hm := gridShift_spec L eps
  rw [qabs_eq_self_of_nonneg hL] at hm
  change 4*L*mesh L eps ≤ eps.val at hm
  have hh : eps.val/2+2*L*mesh L eps ≤ eps.val := by grind only
  change Integral.rectangleSum (fun k => (P.point (k+1)-P.point k)*B.upper k) P.pieces-
    Integral.rectangleSum (fun k => (P.point (k+1)-P.point k)*B.lower k) P.pieces≤_
  rw [sum_sub]
  calc
    _ ≤ Integral.rectangleSum (fun k => (P.point (k+1)-P.point k)*eps.val) P.pieces := by
      apply Integral.rectangleSum_mono
      intro k hk
      have hc := P.monotone k (k+1) (by omega) (by omega)
      have hs := Rat.mul_le_mul_of_nonneg_left (Rat.le_trans (hg k hk) hh)
        (show 0≤P.point (k+1)-P.point k by grind only)
      grind only
    _ = eps.val := by
      rw [Integral.rectangleSum_scale,Integral.rectangleSum_telescope,P.right_endpoint,P.left_endpoint,h0,h1]
      grind only

end ComputableAnalysis.ExponentialComputations
