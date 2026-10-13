import ComputableAnalysis.BracketDerivativeConstruction
import ComputableAnalysis.MonotonicityConvexity

/-! Concrete bridges, including arbitrary represented inputs, closed-domain
endpoints, and a genuinely represented (possibly irrational) coefficient.
The legacy convex centered-secant computation is instantiated and its
mathematical derivative role is proved, rather than assumed in a record. -/
namespace ComputableAnalysis.BracketDerivativeExamples
open BracketDerivative
set_option maxHeartbeats 2000000

def square (q : Rat) : RealRaw := RealRaw.ofRat (q*q)

theorem square_secant_compute {a b : Rat} (hab : a<b) (k : Nat) :
    (secant square a b).compute k = {lo:=a+b,hi:=a+b} := by
  have hp : 0<b-a := by grind only
  have hi : 0≤1/(b-a) := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hc := Rat.mul_inv_cancel (b-a) (Rat.ne_of_gt hp)
  dsimp [secant,square,RealRaw.scaleRat,RealRaw.scaleRatCompute,RealRaw.instHSub,RealRaw.sub,RealRaw.subCompute,RealRaw.ofRat]
  simp only [if_pos hi]
  have he : (1/(b-a))*(b*b-a*a) = a+b := by
    simp only [Rat.div_def,Rat.one_mul]
    grind only [Rat.mul_assoc,Rat.mul_comm]
  change ({lo:=(1/(b-a))*(b*b-a*a),hi:=(1/(b-a))*(b*b-a*a)} : QInterval) = {lo:=a+b,hi:=a+b}
  rw [he]

theorem square_secant_order (w a b z : Rat) (hwa : w<a) (hab : a≤b) (hbz : b<z) :
    (secant square w a).Le (secant square b z) := by
  intro n m
  rw [square_secant_compute hwa,square_secant_compute hbz]
  change w+a≤b+z
  grind only

/-- Outer secants computed exclusively at rational points surrounding the
input's current box. The formula for the derivative is not used here. -/
def squareDerivative (x : RealRaw) : RealRaw :=
  outerDerivative square
    (fun n => (x.compute n).lo-2*allowance n)
    (fun n => (x.compute n).lo-allowance n)
    (fun n => (x.compute n).hi+allowance n)
    (fun n => (x.compute n).hi+2*allowance n) (fun n => n)

theorem squareDerivative_compute {x : RealRaw} (hx : x.Valid) (n : Nat) :
    (squareDerivative x).compute n =
      {lo:=2*(x.compute n).lo-3*allowance n,hi:=2*(x.compute n).hi+3*allowance n} := by
  have hp := allowance_pos n
  have ho := hx.1 n
  dsimp [squareDerivative,outerDerivative]
  rw [square_secant_compute (by grind only),square_secant_compute (by grind only)]
  dsimp [QInterval.hull]
  have h : ((x.compute n).lo-2*allowance n)+((x.compute n).lo-allowance n)≤
    ((x.compute n).hi+allowance n)+((x.compute n).hi+2*allowance n) := by grind only [QInterval.width]
  congr 1 <;> grind

theorem squareDerivative_valid {x : RealRaw} (hx : x.Valid) : (squareDerivative x).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro n
    rw [squareDerivative_compute hx]
    have ho := hx.1 n
    have hp := allowance_pos n
    change 0≤(2*(x.compute n).hi+3*allowance n)-(2*(x.compute n).lo-3*allowance n)
    grind only [QInterval.width]
  · intro n m hnm
    rw [squareDerivative_compute hx,squareDerivative_compute hx]
    have nest := hx.2.1 n m hnm
    have hs := allowance_antitone hnm
    have hp := allowance_pos m
    constructor
    · grind only
    constructor <;> grind only
  · intro eps
    let e : QPos := ⟨eps.val/16,by rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨N,hN⟩ := hx.2.2 e
    obtain ⟨M,hM⟩ := allowance_shrinks e
    refine ⟨max N M,fun n hn => ?_⟩
    rw [squareDerivative_compute hx]
    have h1 := hN n (Nat.le_trans (Nat.le_max_left N M) hn)
    have h2 := hM n (Nat.le_trans (Nat.le_max_right N M) hn)
    dsimp [e] at h1 h2
    have := eps.property
    change (2*(x.compute n).hi+3*allowance n)-(2*(x.compute n).lo-3*allowance n)≤eps.val
    grind only [QInterval.width,Rat.div_def]

theorem squareDerivative_equiv {x : RealRaw} (hx : x.Valid) :
    (squareDerivative x).Equiv (RealRaw.scaleRat 2 x) := by
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  rw [squareDerivative_compute hx]
  have ho := hx.1 n
  have hp := allowance_pos n
  dsimp [RealRaw.scaleRat,RealRaw.scaleRatCompute]
  simp only [if_pos (by decide +kernel : (0:Rat)≤2)]
  constructor <;> grind only [QInterval.width]

/-- All valid represented inputs, with rational-input square primary. -/
theorem squareDerivative_hasDerivative {x : RealRaw} (hx : x.Valid) :
    HasDerivativeAt (fun _ => True) square x (squareDerivative x) := by
  apply outerDerivative_hasDerivative (f:=square)
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

/-- Domain restriction preserves the common-limit law once an admissible
family has actually been constructed. -/
theorem restrict {domain small : Rat → Prop} {f : Rat → RealRaw} {x d : RealRaw}
    (h : HasDerivativeAt domain f x d) (hs : ∀ q, small q → domain q)
    (hA : ∃ A, Admissible small x A) : HasDerivativeAt small f x d := by
  refine ⟨h.1,h.2.1,fun q hq => h.2.2.1 q (hs q hq),hA,?_⟩
  intro A hAd
  apply h.2.2.2.2 A
  exact ⟨hAd.1,hAd.2.1,hAd.2.2.1,fun n => ⟨(hAd.2.2.2 n).1,fun q hlo hhi => hs q ((hAd.2.2.2 n).2 q hlo hhi)⟩⟩

/-- Includes BOTH endpoints and arbitrary irrational represented inputs. -/
theorem square_closed_interval {a b : Rat} {x : RealRaw} (hab : a<b) (hx : x.Valid)
    (ha : (RealRaw.ofRat a).Le x) (hb : x.Le (RealRaw.ofRat b)) :
    HasDerivativeAt (fun q => a≤q ∧ q≤b) square x (squareDerivative x) :=
  restrict (squareDerivative_hasDerivative hx) (fun _ _ => True.intro)
    ⟨clipped a b x,clipped_admissible hx hab ha hb⟩

def affine (c : RealRaw) (q : Rat) : RealRaw := RealRaw.scaleRat q c

private theorem scaled_contains_midpoint {c : RealRaw} (hc : c.Valid) (q : Rat) (k : Nat) :
    ((affine c q).compute k).lo ≤ q*(c.compute k).midpoint ∧
      q*(c.compute k).midpoint ≤ ((affine c q).compute k).hi := by
  have hm := QInterval.midpoint_mem (RealRaw.interval_order_of_valid c hc k)
  dsimp [affine,RealRaw.scaleRat,RealRaw.scaleRatCompute]
  split
  · next h => exact ⟨Rat.mul_le_mul_of_nonneg_left hm.1 h,Rat.mul_le_mul_of_nonneg_left hm.2 h⟩
  · next h =>
    have hn : 0≤-q := by grind only
    have hl := Rat.mul_le_mul_of_nonneg_left hm.2 hn
    have hu := Rat.mul_le_mul_of_nonneg_left hm.1 hn
    constructor <;> grind only

private theorem affine_secant_contains {c : RealRaw} (hc : c.Valid) {a b : Rat}
    (hab : a<b) (k : Nat) :
    ((secant (affine c) a b).compute k).lo ≤ (c.compute k).midpoint ∧
      (c.compute k).midpoint ≤ ((secant (affine c) a b).compute k).hi := by
  have ha := scaled_contains_midpoint hc a k
  have hb := scaled_contains_midpoint hc b k
  have hp : 0<b-a := by grind only
  have hi : 0≤1/(b-a) := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hp)
  have hcancel := Rat.mul_inv_cancel (b-a) (Rat.ne_of_gt hp)
  have hlow := Rat.mul_le_mul_of_nonneg_left
    (show ((affine c b).compute k).lo-((affine c a).compute k).hi≤(b-a)*(c.compute k).midpoint by grind only)
    hi
  have hhigh := Rat.mul_le_mul_of_nonneg_left
    (show (b-a)*(c.compute k).midpoint≤((affine c b).compute k).hi-((affine c a).compute k).lo by grind only)
    hi
  simp only [secant,RealRaw.scaleRat,RealRaw.scaleRatCompute,RealRaw.instHSub,RealRaw.sub,RealRaw.subCompute,if_pos hi]
  change (1/(b-a))*(((affine c b).compute k).lo-((affine c a).compute k).hi)≤_ ∧
    _≤(1/(b-a))*(((affine c b).compute k).hi-((affine c a).compute k).lo)
  have he : (1/(b-a))*((b-a)*(c.compute k).midpoint) = (c.compute k).midpoint := by
    rw [Rat.div_def,Rat.one_mul,← Rat.mul_assoc,Rat.inv_mul_cancel (b-a) (Rat.ne_of_gt hp),Rat.one_mul]
  rw [he] at hlow hhigh
  exact ⟨hlow,hhigh⟩

theorem affine_secant_equiv {c : RealRaw} (hc : c.Valid) {a b : Rat} (hab : a<b) :
    (secant (affine c) a b).Equiv c := by
  intro k
  apply (RealRaw.compareAt_overlap_iff _ _ k k).2
  have hs := affine_secant_contains hc hab k
  have hm := QInterval.midpoint_mem (RealRaw.interval_order_of_valid c hc k)
  exact ⟨Rat.le_trans hs.1 hm.2,Rat.le_trans hm.1 hs.2⟩

/-- The endpoint values may be irrational. Each secant has its own independent
refinement index, and no coupling with the input bracket stage is required. -/
theorem affine_hasDerivative {c x : RealRaw} (hc : c.Valid) (hx : x.Valid) :
    HasDerivativeAt (fun _ => True) (affine c) x c := by
  refine ⟨hx,hc,fun q _ => RealRaw.scaleRat_valid hc,
    ⟨enlarged x,enlarged_admissible hx⟩,fun A hA => ?_⟩
  apply RawLimit.congr_sequence (RawLimit.constant c hc)
    (secants_valid (fun _ _ => RealRaw.scaleRat_valid hc) hA)
  intro n
  exact RealRaw.equiv_symm (affine_secant_equiv hc (hA.2.2.2 n).1)

/-- The OLD centered convex computation, on the rational-input affine
function with an arbitrary valid represented coefficient. -/
def affineFunction (c : RealRaw) : RealFunRaw where
  compute q k := (affine c q).compute k

def cell : RationalSubinterval (-1) 1 :=
  ⟨-1,1,by decide +kernel,by decide +kernel,by decide +kernel⟩

def affineCurvature (c : RealRaw) (hc : c.Valid) : CurvatureOnSubinterval (affineFunction c) cell where
  kind := .convex
  evalPrecision := fun n => n
  domain_on := fun _ _ => True.intro
  secant_slope_order := by
    intro n w a b z _ _ _ _ hwa _ hbz
    change ((secant (affine c) w a).compute n).lo ≤ ((secant (affine c) b z).compute n).hi
    have hl := affine_secant_contains hc hwa n
    have hr := affine_secant_contains hc hbz n
    exact Rat.le_trans hl.1 hr.2

private theorem affine_centered_compute {c : RealRaw} (hc : c.Valid) {h : Rat}
    (hh : 0<h) (k : Nat) :
    ConvexDerivative.centeredInterval (affineFunction c) 0 h k = c.compute k := by
  have hi : 0≤1/h := by rw [Rat.div_def,Rat.one_mul]; exact Rat.le_of_lt (Rat.inv_pos.mpr hh)
  have hcanc := Rat.mul_inv_cancel h (Rat.ne_of_gt hh)
  have hn : ¬0≤-h := by grind only
  dsimp [ConvexDerivative.centeredInterval,secantSlopeIntervalOfRealFun,affineFunction,
    QInterval.slopeBetween,QInterval.divByRat,QInterval.scaleByRat,QInterval.subInterval,
    affine,RealRaw.scaleRat,RealRaw.scaleRatCompute]
  simp only [Rat.sub_eq_add_neg,Rat.add_zero,Rat.zero_add,Rat.neg_zero,Rat.neg_neg,if_pos hi,if_pos (Rat.le_refl : (0:Rat)≤0),if_pos (Rat.le_of_lt hh),if_neg hn,Rat.zero_mul]
  have hl : (1/h)*(0-(-h*(c.compute k).lo)) = (c.compute k).lo := by simp only [Rat.div_def,Rat.one_mul]; grind only [Rat.mul_assoc,Rat.mul_comm]
  have hu : (1/h)*(0-(-h*(c.compute k).hi)) = (c.compute k).hi := by simp only [Rat.div_def,Rat.one_mul]; grind only [Rat.mul_assoc,Rat.mul_comm]
  have hl' : (1/h)*(h*(c.compute k).lo-0) = (c.compute k).lo := by simp only [Rat.div_def,Rat.one_mul]; grind only [Rat.mul_assoc,Rat.mul_comm]
  have hu' : (1/h)*(h*(c.compute k).hi-0) = (c.compute k).hi := by simp only [Rat.div_def,Rat.one_mul]; grind only [Rat.mul_assoc,Rat.mul_comm]
  simp only [Rat.sub_eq_add_neg,Rat.zero_add,Rat.add_zero,Rat.neg_zero,Rat.neg_neg] at hl hu hl' hu'
  rw [hl,hu,hl',hu']
  dsimp [QInterval.hull]
  congr 1 <;> grind

def affinePointwise (c : RealRaw) (hc : c.Valid) : ConvexDerivative.Pointwise (affineCurvature c hc) 0 where
  convex := rfl
  interior := ⟨1,by decide +kernel,by change (-1:Rat)≤0-1 ∧ 0-1≤1; decide +kernel,
    by change (-1:Rat)≤0 ∧ 0≤1; decide +kernel,
    by change (-1:Rat)≤0+1 ∧ 0+1≤1; decide +kernel⟩
  step := allowance
  step_pos := allowance_pos
  step_le_radius := fun n => by simpa only [allowance,Rat.pow_zero] using allowance_antitone (Nat.zero_le n)
  valid := by
    change RealRaw.ValidCompute (fun n => ConvexDerivative.centeredInterval (affineFunction c) 0 (allowance n) n)
    have he : (fun n => ConvexDerivative.centeredInterval (affineFunction c) 0 (allowance n) n) = c.compute := by
      funext n; exact affine_centered_compute hc (allowance_pos n) n
    rw [he]
    exact hc

theorem affinePointwise_hasDerivative {c : RealRaw} (hc : c.Valid) :
    HasDerivativeAt (fun q => (-1:Rat)≤q ∧ q≤1) (affine c) (RealRaw.ofRat 0)
      (affinePointwise c hc).raw := by
  have h := restrict (affine_hasDerivative (x:=RealRaw.ofRat 0) hc (RealRaw.ofRat_valid 0)) (fun _ _ => True.intro)
    ⟨clipped (-1) 1 (RealRaw.ofRat 0),clipped_admissible (RealRaw.ofRat_valid 0)
      (by decide +kernel) (by intro _ _; change (-1:Rat)≤0; decide +kernel)
      (by intro _ _; change (0:Rat)≤1; decide +kernel)⟩
  apply congr_value h (ConvexDerivative.Pointwise.raw_valid (affinePointwise c hc))
  apply RealRaw.equiv_symm
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change (ConvexDerivative.centeredInterval (affineFunction c) 0 (allowance n) n).Overlaps (c.compute n)
  rw [affine_centered_compute hc (allowance_pos n)]
  have ho := RealRaw.interval_order_of_valid c hc n
  exact ⟨ho,ho⟩


def squareFunction : RealFunRaw := RealFunRaw.exact (fun q => q*q)

def squareCell : RationalSubinterval 0 2 :=
  ⟨0,2,by decide +kernel,by decide +kernel,by decide +kernel⟩

def squareCurvature : CurvatureOnSubinterval squareFunction squareCell where
  kind := .convex
  evalPrecision := fun n => n
  domain_on := fun _ _ => True.intro
  secant_slope_order := by
    intro n w a b z _ _ _ _ hwa hab hbz
    change ((secant square w a).compute n).lo ≤ ((secant square b z).compute n).hi
    exact square_secant_order w a b z hwa hab hbz n n

private theorem square_centered_compute {h : Rat} (hh : 0<h) (k : Nat) :
    ConvexDerivative.centeredInterval squareFunction 1 h k = {lo:=2-h,hi:=2+h} := by
  change QInterval.hull ((secant square (1-h) 1).compute k)
    ((secant square 1 (1+h)).compute k) = {lo:=2-h,hi:=2+h}
  rw [square_secant_compute (by grind only),square_secant_compute (by grind only)]
  dsimp [QInterval.hull]
  congr 1 <;> grind

/-- A nonlinear instance of the original convex centered-secant algorithm. -/
def squarePointwise : ConvexDerivative.Pointwise squareCurvature 1 where
  convex := rfl
  interior := ⟨1,by decide +kernel,by change (0:Rat)≤1-1 ∧ 1-1≤2; decide +kernel,
    by change (0:Rat)≤1 ∧ 1≤2; decide +kernel,
    by change (0:Rat)≤1+1 ∧ 1+1≤2; decide +kernel⟩
  step := allowance
  step_pos := allowance_pos
  step_le_radius := fun n => by simpa only [allowance,Rat.pow_zero] using allowance_antitone (Nat.zero_le n)
  valid := by
    change RealRaw.ValidCompute (fun n => ConvexDerivative.centeredInterval squareFunction 1 (allowance n) n)
    have he : (fun n => ConvexDerivative.centeredInterval squareFunction 1 (allowance n) n) =
        (enlarged (RealRaw.ofRat 2)).compute := by
      funext n; rw [square_centered_compute (allowance_pos n)]; rfl
    rw [he]
    exact enlarged_valid (RealRaw.ofRat_valid 2)

theorem squarePointwise_hasDerivative :
    HasDerivativeAt (fun q => (0:Rat)≤q ∧ q≤2) square (RealRaw.ofRat 1) squarePointwise.raw := by
  have hx : (RealRaw.ofRat 1).Valid := RealRaw.ofRat_valid (1:Rat)
  have h := square_closed_interval (a:=0) (b:=2) (x:=RealRaw.ofRat 1)
    (by decide +kernel) hx
    (by intro _ _; change (0:Rat)≤1; decide +kernel)
    (by intro _ _; change (1:Rat)≤2; decide +kernel)
  have hd := squareDerivative_valid (x:=RealRaw.ofRat 1) hx
  have he : (squareDerivative (RealRaw.ofRat 1)).Equiv (RealRaw.ofRat 2) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    rw [squareDerivative_compute (x:=RealRaw.ofRat 1) hx]
    have hp := allowance_pos n
    change (2:Rat)*1-3*allowance n≤2 ∧ 2≤2*1+3*allowance n
    constructor <;> grind only
  have hold := ConvexDerivative.Pointwise.raw_valid squarePointwise
  have heold : squarePointwise.raw.Equiv (RealRaw.ofRat 2) := by
    intro n
    apply (RealRaw.compareAt_overlap_iff _ _ n n).2
    change (ConvexDerivative.centeredInterval squareFunction 1 (allowance n) n).Overlaps
      ({lo:=2,hi:=2}:QInterval)
    rw [square_centered_compute (allowance_pos n)]
    have hp := allowance_pos n
    constructor <;> grind only
  exact congr_value h hold (RealRaw.equiv_trans (x:=squareDerivative (RealRaw.ofRat 1)) (y:=RealRaw.ofRat 2) (z:=squarePointwise.raw) hd (RealRaw.ofRat_valid 2) hold he
    (RealRaw.equiv_symm heold))

end ComputableAnalysis.BracketDerivativeExamples
