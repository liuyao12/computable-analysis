import ComputableAnalysis.RealSecantDerivative
import ComputableAnalysis.RealSecantCalculus
import ComputableAnalysis.BracketDerivativeExamples

/-! Actual convex and concave constructions under the shrinking real secant
box condition, including represented coefficients and closed-domain endpoints. -/
namespace ComputableAnalysis.RealSecantDerivativeExamples
open BracketDerivative BracketDerivativeExamples
open RawLimit (cofinal_id inInterval_congr inInterval_of_contains_compute)
open RealSecantDerivative
set_option maxHeartbeats 2000000

theorem squareDerivative_shrinkingBoxes {x : RealRaw} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) square x (squareDerivative x) := by
  apply RealSecantDerivative.outerDerivative_hasDerivative (f:=square)
    (fun n => (x.compute n).lo-2*allowance n)
    (fun n => (x.compute n).lo-allowance n)
    (fun n => (x.compute n).hi+allowance n)
    (fun n => (x.compute n).hi+2*allowance n) (fun n => n)
    hx (fun q _ => RealRaw.ofRat_valid (q*q)) ⟨enlarged x,enlarged_admissible hx⟩
    (squareDerivative_valid hx)
  · intro _; exact ⟨True.intro,True.intro,True.intro,True.intro⟩
  · intro w a b z _ _ _ _ hwa hab hbz
    exact square_secant_order w a b z hwa hab hbz
  · intro n
    have hp := allowance_pos n
    exact ⟨by grind only,by grind only,n,by grind only,by grind only⟩

theorem square_closed {a b : Rat} {x : RealRaw} (hab : a<b) (hx : x.Valid)
    (ha : (RealRaw.ofRat a).Le x) (hb : x.Le (RealRaw.ofRat b)) :
    RealSecantDerivative.HasDerivativeAt (fun q => a≤q ∧ q≤b) square x (squareDerivative x) :=
  RealSecantDerivative.restrict (squareDerivative_shrinkingBoxes hx) (fun _ _ => True.intro)
    ⟨clipped a b x,clipped_admissible hx hab ha hb⟩

theorem affine_shrinkingBoxes {c x : RealRaw} (hc : c.Valid) (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) (affine c) x c := by
  refine ⟨hx,hc,fun r _ => RealRaw.scaleRat_valid hc,
    ⟨enlarged x,enlarged_admissible hx⟩,fun A hA => ?_⟩
  refine ⟨hc,(fun _ m => c.compute m),(fun n => n),(fun n => n),
    cofinal_id,cofinal_id,hc,RealRaw.equiv_refl c hc,?_⟩
  rintro k y ⟨a,b,ha,hab,hb,rfl⟩
  have hs : (secant (affine c) a b).Valid := secant_valid
    (RealRaw.scaleRat_valid (r:=a) hc) (RealRaw.scaleRat_valid (r:=b) hc)
  exact inInterval_congr hc hs (RealRaw.equiv_symm (affine_secant_equiv hc hab))
    (inInterval_of_contains_compute hc k ⟨Rat.le_refl,Rat.le_refl⟩)

theorem square_centered_shrinkingBoxes :
    RealSecantDerivative.HasDerivativeAt (fun q => (0:Rat)≤q ∧ q≤2) square (RealRaw.ofRat 1)
      squarePointwise.raw := by
  have h := square_closed (a:=0) (b:=2) (x:=RealRaw.ofRat 1)
    (by decide +kernel) (RealRaw.ofRat_valid 1)
    (by intro _ _; change (0:Rat)≤1; decide +kernel)
    (by intro _ _; change (1:Rat)≤2; decide +kernel)
  have he := BracketDerivative.unique h.bracket squarePointwise_hasDerivative
  exact RealSecantDerivative.congr_value h (ConvexDerivative.Pointwise.raw_valid squarePointwise) he

theorem affine_centered_shrinkingBoxes {c : RealRaw} (hc : c.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun q => (-1:Rat)≤q ∧ q≤1) (affine c) (RealRaw.ofRat 0)
      (affinePointwise c hc).raw := by
  have h := RealSecantDerivative.restrict (affine_shrinkingBoxes (x:=RealRaw.ofRat 0) hc (RealRaw.ofRat_valid 0))
    (fun _ _ => True.intro)
    ⟨clipped (-1) 1 (RealRaw.ofRat 0),clipped_admissible (RealRaw.ofRat_valid 0)
      (by decide +kernel) (by intro _ _; change (-1:Rat)≤0; decide +kernel)
      (by intro _ _; change (0:Rat)≤1; decide +kernel)⟩
  exact RealSecantDerivative.congr_value h (ConvexDerivative.Pointwise.raw_valid (affinePointwise c hc))
    (BracketDerivative.unique h.bracket (affinePointwise_hasDerivative hc))

/-- A nonlinear concave primary rational-input function. -/
def negativeSquare (q : Rat) : RealRaw := -(square q)

def negativeSquareDerivative (x : RealRaw) : RealRaw :=
  outerDerivative negativeSquare
    (fun n => (x.compute n).lo-2*allowance n)
    (fun n => (x.compute n).lo-allowance n)
    (fun n => (x.compute n).hi+allowance n)
    (fun n => (x.compute n).hi+2*allowance n) (fun n => n)

theorem negativeSquare_secant_compute {a b : Rat} (hab : a<b) (k : Nat) :
    (secant negativeSquare a b).compute k={lo:=-(a+b),hi:=-(a+b)} := by
  rw [show negativeSquare=(fun q => -(square q)) from rfl,secant_neg_compute square hab]
  change ({lo:= -((secant square a b).compute k).hi,hi:= -((secant square a b).compute k).lo}:QInterval)=_
  rw [square_secant_compute hab]

theorem negativeSquare_secant_order (w a b z : Rat) (hwa : w<a) (hab : a≤b) (hbz : b<z) :
    (secant negativeSquare b z).Le (secant negativeSquare w a) := by
  intro n m
  rw [negativeSquare_secant_compute hbz,negativeSquare_secant_compute hwa]
  change -(b+z)≤-(w+a)
  grind only

theorem negativeSquareDerivative_compute {x : RealRaw} (hx : x.Valid) (n : Nat) :
    (negativeSquareDerivative x).compute n=
      {lo:= -(2*(x.compute n).hi+3*allowance n),hi:= -(2*(x.compute n).lo-3*allowance n)} := by
  have hp := allowance_pos n
  have ho := RealRaw.interval_order_of_valid x hx n
  dsimp [negativeSquareDerivative,outerDerivative]
  rw [negativeSquare_secant_compute (by grind only),negativeSquare_secant_compute (by grind only)]
  dsimp [QInterval.hull]
  congr 1 <;> grind

theorem negativeSquareDerivative_valid {x : RealRaw} (hx : x.Valid) :
    (negativeSquareDerivative x).Valid := by
  have hc := RealRaw.neg_valid (squareDerivative_valid hx)
  have he : (negativeSquareDerivative x).compute=(-squareDerivative x).compute := by
    funext n
    rw [negativeSquareDerivative_compute hx]
    change _=({lo:= -((squareDerivative x).compute n).hi,hi:= -((squareDerivative x).compute n).lo}:QInterval)
    rw [squareDerivative_compute hx]
  change RealRaw.ValidCompute (negativeSquareDerivative x).compute
  rw [he]
  exact hc

theorem negativeSquareDerivative_shrinkingBoxes {x : RealRaw} (hx : x.Valid) :
    RealSecantDerivative.HasDerivativeAt (fun _ => True) negativeSquare x (negativeSquareDerivative x) := by
  apply RealSecantDerivative.concave_outerDerivative_hasDerivative (f:=negativeSquare)
    (fun n => (x.compute n).lo-2*allowance n)
    (fun n => (x.compute n).lo-allowance n)
    (fun n => (x.compute n).hi+allowance n)
    (fun n => (x.compute n).hi+2*allowance n) (fun n => n)
    hx (fun q _ => RealRaw.neg_valid (RealRaw.ofRat_valid (q*q)))
    ⟨enlarged x,enlarged_admissible hx⟩ (negativeSquareDerivative_valid hx)
  · intro _; exact ⟨True.intro,True.intro,True.intro,True.intro⟩
  · intro w a b z _ _ _ _ hwa hab hbz
    exact negativeSquare_secant_order w a b z hwa hab hbz
  · intro n
    have hp := allowance_pos n
    exact ⟨by grind only,by grind only,n,by grind only,by grind only⟩

/-- Exact derivative identity for the concave computation at every represented
real input. The value is compared with the existing convex computation. -/
theorem negativeSquareDerivative_equiv {x : RealRaw} (hx : x.Valid) :
    (negativeSquareDerivative x).Equiv (-(RealRaw.scaleRat 2 x)) := by
  have he := RealSecantDerivative.unique (negativeSquareDerivative_shrinkingBoxes hx)
    (squareDerivative_shrinkingBoxes hx).negate
  exact RealRaw.equiv_trans (negativeSquareDerivative_valid hx)
    (RealRaw.neg_valid (squareDerivative_valid hx)) (RealRaw.neg_valid (RealRaw.scaleRat_valid hx))
    he (RealRaw.neg_equiv (squareDerivative_equiv hx))

def negativeSquareFunction : RealFunRaw where
  domain := fun _ => True
  compute q := (negativeSquare q).compute

def negativeSquareCurvature : CurvatureOnSubinterval negativeSquareFunction squareCell where
  kind := .concave
  evalPrecision := fun n => n
  domain_on := fun _ _ => True.intro
  secant_slope_order := by
    intro n w a b z _ _ _ _ hwa hab hbz
    change ((secant negativeSquare b z).compute n).lo≤((secant negativeSquare w a).compute n).hi
    exact negativeSquare_secant_order w a b z hwa hab hbz n n

private theorem negativeSquare_centered_compute {h : Rat} (hh : 0<h) (k : Nat) :
    ConcaveDerivative.centeredInterval negativeSquareFunction 1 h k = {lo:= -2-h,hi:= -2+h} := by
  change QInterval.hull ((secant negativeSquare (1-h) 1).compute k)
    ((secant negativeSquare 1 (1+h)).compute k)=_
  rw [negativeSquare_secant_compute (by grind only),negativeSquare_secant_compute (by grind only)]
  dsimp [QInterval.hull]
  congr 1 <;> grind

/-- The existing concave centered-secant interface, now instantiated with a
nonlinear computation whose derivative has been proved by all-pair coverage. -/
def negativeSquarePointwise : ConcaveDerivative.Pointwise negativeSquareCurvature 1 where
  concave := rfl
  interior := squarePointwise.interior
  step := allowance
  step_pos := allowance_pos
  step_le_radius := squarePointwise.step_le_radius
  valid := by
    change RealRaw.ValidCompute (fun n => ConcaveDerivative.centeredInterval negativeSquareFunction 1 (allowance n) n)
    have he : (fun n => ConcaveDerivative.centeredInterval negativeSquareFunction 1 (allowance n) n)=
      (enlarged (RealRaw.ofRat (-2))).compute := by
      funext n; rw [negativeSquare_centered_compute (allowance_pos n)]; rfl
    rw [he]
    exact enlarged_valid (RealRaw.ofRat_valid (-2))

theorem negativeSquare_centered_shrinkingBoxes :
    RealSecantDerivative.HasDerivativeAt (fun q => (0:Rat)≤q ∧ q≤2) negativeSquare (RealRaw.ofRat 1)
      negativeSquarePointwise.raw := by
  have hx : (RealRaw.ofRat 1).Valid := RealRaw.ofRat_valid (1:Rat)
  have h := RealSecantDerivative.restrict (negativeSquareDerivative_shrinkingBoxes hx)
    (fun _ _ => True.intro)
    ⟨clipped 0 2 (RealRaw.ofRat 1),clipped_admissible hx (by decide +kernel)
      (by intro _ _; change (0:Rat)≤1; decide +kernel)
      (by intro _ _; change (1:Rat)≤2; decide +kernel)⟩
  have he : (negativeSquareDerivative (RealRaw.ofRat 1)).Equiv negativeSquarePointwise.raw := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).mpr
    rw [negativeSquareDerivative_compute hx]
    change ({lo:= -(2*1+3*allowance n),hi:= -(2*1-3*allowance n)} : QInterval).Overlaps
      (ConcaveDerivative.centeredInterval negativeSquareFunction 1 (allowance n) n)
    rw [negativeSquare_centered_compute (allowance_pos n)]
    have hp := allowance_pos n
    constructor <;> grind only
  exact RealSecantDerivative.congr_value h (ConcaveDerivative.Pointwise.raw_valid negativeSquarePointwise) he

theorem affine_finite_shrinkingBoxes {a b m c : Rat} {x : RealRaw} (hx : x.Valid)
    (hbracket : ∃ A, Admissible (inDomainInterval a b) x A) :
    RealSecantDerivative.HasDerivativeAt (inDomainInterval a b)
      (FunctionOnInterval.exactRat (fun r => m*r+c) a b).rationalValue x (RealRaw.ofRat m) := by
  let G := FunctionOnInterval.exactRat (fun _ => m) a b
  have hG : BracketContinuity.HasContinuousAt (inDomainInterval a b) G.rationalValue x (RealRaw.ofRat m) := by
    apply BracketContinuity.congr_function
      (BracketContinuity.constant (c := RealRaw.ofRat m) hx (RealRaw.ofRat_valid m) hbracket)
      (fun r _ => G.rationalValue_valid r)
    intro r hr
    have hr' : a ≤ r ∧ r ≤ b := hr
    unfold FunctionOnInterval.rationalValue
    split
    · exact RealRaw.equiv_refl (RealRaw.ofRat m) (RealRaw.ofRat_valid m)
    · rename_i hn
      exact False.elim (hn hr')
  exact (FunctionOnInterval.exactRatAffineDerivative a b m c).toShrinkingSecantDerivative
    (fun _ => by change 0 < (1 : Nat); exact Nat.zero_lt_one) hG

end ComputableAnalysis.RealSecantDerivativeExamples
