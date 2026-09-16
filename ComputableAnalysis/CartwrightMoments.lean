import ComputableAnalysis.CartwrightClockBounds
import ComputableAnalysis.CartwrightArithmetic

/-!
# The independently computed weighted cosine moments

The stage is prescribed: 2^k domain cells and evaluation stage 3*k+10.
The output is the monotone endpoint rectangle interval. Coordinatewise
monotonicity gives nesting; an explicit uniform estimate proves shrinking.
Neither the moment recurrence nor a primitive supplies this construction.
-/
namespace ComputableAnalysis.CartwrightMoments
open CartwrightClockBounds ClosedArctanInverse IntervalSelections
open FiniteRiemannAlgebra Integral

abbrev Unit := CartwrightClockBounds.Unit

def weight (n : Nat) (t : Rat) : Rat := (1-t*t)^n

theorem weight_bounds {t : Rat} (ht : Unit t) (n : Nat) :
    0 ≤ weight n t ∧ weight n t ≤ 1 := by
  have ht2 := Rat.mul_le_mul_of_nonneg_left ht.2 ht.1
  have ht0 := Rat.mul_nonneg ht.1 ht.1
  have hu : 0 ≤ 1-t*t ∧ 1-t*t ≤ 1 := by constructor <;> grind
  induction n with
  | zero => simp only [weight,Rat.pow_zero]; constructor <;> decide +kernel
  | succ n ih =>
    rw [weight, Rat.pow_succ]
    exact ⟨Rat.mul_nonneg ih.1 hu.1,
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hu.2 ih.1) (by simpa only [Rat.mul_one,weight] using ih.2)⟩

theorem weight_difference {a b : Rat} (ha : Unit a) (hb : Unit b)
    (hab : a ≤ b) (n : Nat) :
    0 ≤ weight n a-weight n b ∧ weight n a-weight n b ≤ 2*(n:Rat)*(b-a) := by
  have h0 : 0 ≤ b-a := by grind
  have aa := Rat.mul_nonneg ha.1 ha.1
  have bb := Rat.mul_nonneg hb.1 hb.1
  have a1 := Rat.mul_le_mul_of_nonneg_left ha.2 ha.1
  have b1 := Rat.mul_le_mul_of_nonneg_left hb.2 hb.1
  have hs : 0 ≤ b*b-a*a ∧ b*b-a*a ≤ 2*(b-a) := by
    have hsum : 0 ≤ a+b ∧ a+b ≤ 2 := by constructor <;> grind
    have hm0 := Rat.mul_nonneg h0 hsum.1
    have hm1 := Rat.mul_le_mul_of_nonneg_left hsum.2 h0
    constructor <;> grind
  induction n with
  | zero => simp only [weight,Rat.pow_zero,Rat.sub_self,show ((0:Nat):Rat)=0 by decide +kernel,Rat.mul_zero,Rat.zero_mul]; constructor <;> decide +kernel
  | succ n ih =>
    have wa := weight_bounds ha n
    have wb := weight_bounds hb n
    have id : weight (n+1) a-weight (n+1) b =
        (1-a*a)*(weight n a-weight n b)+(b*b-a*a)*weight n b := by
      simp only [weight,Rat.pow_succ]; grind
    rw [id]
    have t0 := Rat.mul_nonneg (show 0 ≤ 1-a*a by grind) ih.1
    have t1 := Rat.mul_nonneg hs.1 wb.1
    have u0 := Rat.mul_le_mul_of_nonneg_right (show 1-a*a ≤ 1 by grind) ih.1
    have u1 := Rat.mul_le_mul_of_nonneg_left wb.2 hs.1
    have hc : ((n+1:Nat):Rat)=(n:Rat)+1 := by simp
    rw [hc]
    constructor <;> grind

def value (n : Nat) (t : Rat) : RealRaw :=
  RealRaw.scaleRat (weight n t) (ClockTrigonometry.cosine t)

theorem value_valid {t : Rat} (ht : Unit t) (n : Nat) : (value n t).Valid :=
  RealRaw.scaleRat_valid (ClockTrigonometry.cosine_valid ht)

theorem value_compute {t : Rat} (ht : Unit t) (n q : Nat) :
    (value n t).compute q =
    {lo:=weight n t*((ClockTrigonometry.cosine t).compute q).lo,
     hi:=weight n t*((ClockTrigonometry.cosine t).compute q).hi} := by
  simp only [value,RealRaw.scaleRat,RealRaw.scaleRatCompute,if_pos (weight_bounds ht n).1]

theorem value_bounds {t : Rat} (ht : Unit t) (n q : Nat) :
    0 ≤ ((value n t).compute q).lo ∧ ((value n t).compute q).hi ≤ 1 := by
  rw [value_compute ht]
  have w := weight_bounds ht n
  have c := cosine_box_bounds ht q
  have co := RealRaw.interval_order_of_valid _ (ClockTrigonometry.cosine_valid ht) q
  exact ⟨Rat.mul_nonneg w.1 c.1,
    Rat.le_trans (Rat.mul_le_mul_of_nonneg_left c.2 w.1) (by simpa [Rat.mul_one] using w.2)⟩

theorem value_antitone {a b : Rat} (ha : Unit a) (hb : Unit b)
    (hab : a ≤ b) (n q : Nat) :
    ((value n b).compute q).lo ≤ ((value n a).compute q).lo ∧
    ((value n b).compute q).hi ≤ ((value n a).compute q).hi := by
  rw [value_compute ha, value_compute hb]
  have wa := weight_bounds ha n; have wb := weight_bounds hb n
  have hd := (weight_difference ha hb hab n).1
  have hc := cosine_endpoints_antitone ha hb hab q
  have ca := cosine_box_bounds ha q; have cb := cosine_box_bounds hb q
  have co := RealRaw.interval_order_of_valid _ (ClockTrigonometry.cosine_valid ha) q
  have wle : weight n b ≤ weight n a := by grind
  constructor
  · exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hc.1 wb.1)
      (Rat.mul_le_mul_of_nonneg_right wle ca.1)
  · exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hc.2 wb.1)
      (Rat.mul_le_mul_of_nonneg_right wle (Rat.le_trans ca.1 co))

theorem value_cell_width {a b : Rat} (ha : Unit a) (hb : Unit b)
    (hab : a ≤ b) (n q : Nat) :
    ((value n a).compute q).hi-((value n b).compute q).lo ≤
      (2*(n:Rat)+8)*(b-a)+528*delta q := by
  rw [value_compute ha, value_compute hb]
  have wa := weight_bounds ha n; have wb := weight_bounds hb n
  have wd := weight_difference ha hb hab n
  have ca := cosine_box_bounds ha q; have cb := cosine_box_bounds hb q
  have co := RealRaw.interval_order_of_valid _ (ClockTrigonometry.cosine_valid ha) q
  have hd := cosine_endpoints_antitone ha hb hab q
  have hc := cosine_box_distance ha hb q
  rw [qabs_eq_self_of_nonneg (by grind : 0 ≤ b-a)] at hc
  have hgap : 0 ≤ ((ClockTrigonometry.cosine a).compute q).hi-
    ((ClockTrigonometry.cosine b).compute q).lo := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_right wa.2 hgap
  have h2 := Rat.mul_le_mul_of_nonneg_left
    (show ((ClockTrigonometry.cosine b).compute q).lo ≤ 1 from
      Rat.le_trans (RealRaw.interval_order_of_valid _ (ClockTrigonometry.cosine_valid hb) q) cb.2) wd.1
  grind

def function (n : Nat) : FunctionOnInterval :=
  FunctionOnInterval.ofRealFunRaw
    {domain:=Unit, compute:=fun t q => (value n t).compute q}
    0 1 (fun _ h=>h) (fun t ht=>value_valid ht n)

theorem function_compute (n q : Nat) (t : Rat) (ht : Unit t) :
    (function n).compute t ht q = (value n t).compute q := rfl

def ordered (n : Nat) : EndpointOrderedNonincreasingOnInterval (function n) where
  lower_mono := fun _ _ ha hb hab q => (value_antitone ha hb hab n q).1
  upper_mono := fun _ _ ha hb hab q => (value_antitone ha hb hab n q).2

/-- A supplied joint stage plan, not a tolerance search. -/
def sampleStage (k : Nat) : Nat := 3*k+10

def integral (n : Nat) : RealRaw where
  compute := nonincreasingDarbouxDyadicStage (function n) (by change (0:Rat) ≤ 1; decide) sampleStage

theorem stage_width (n k : Nat) :
    ((integral n).compute k).width ≤ (2*(n:Rat)+536)*delta k := by
  have hf : (function n).lower=0 := rfl
  have hg : (function n).upper=1 := rfl
  let P := RationalPartition.uniform 0 1 (2^k) (Nat.two_pow_pos k) (by decide : (0:Rat)≤1)
  have he : mesh 0 1 (2^k)=delta k := by
    unfold mesh
    rw [if_neg (Nat.ne_of_gt (Nat.two_pow_pos k))]
    simp only [show (1:Rat)-0=1 by decide +kernel, Rat.natCast_pow,
      show ((2:Nat):Rat)=2 by decide +kernel, delta,meshRadius]
  have bound := RationalPartition.uniform_boundIntegralSum_width_le
    (a:=0) (b:=1) (2^k) (Nat.two_pow_pos k) (by decide)
    (fun i hi => nonincreasingDarbouxRange (function n) P i hi (sampleStage k))
    ((2*(n:Rat)+8)*delta k+528*delta (sampleStage k)) (by
      intro i hi
      have ha : Unit (P.cell i hi).lower :=
        ⟨(P.cell i hi).lower_mem,Rat.le_trans (P.cell i hi).ordered (P.cell i hi).upper_mem⟩
      have hb : Unit (P.cell i hi).upper :=
        ⟨Rat.le_trans (P.cell i hi).lower_mem (P.cell i hi).ordered,(P.cell i hi).upper_mem⟩
      have hc := value_cell_width ha hb (P.cell i hi).ordered n (sampleStage k)
      have hw : (P.cell i hi).upper-(P.cell i hi).lower=delta k := by
        exact (RationalPartition.uniform_cell_width 0 1 (2^k) (Nat.two_pow_pos k) (by decide) i hi).trans he
      change ((value n (P.cell i hi).lower).compute (sampleStage k)).hi-
        ((value n (P.cell i hi).upper).compute (sampleStage k)).lo ≤ _
      rw [hw] at hc
      exact hc)
  change ((integral n).compute k).width ≤ (1-0)*_ at bound
  have hd := meshRadius_antitone (n:=k) (m:=sampleStage k) (by unfold sampleStage; omega)
  grind

theorem integral_valid (n : Nat) : (integral n).Valid := by
  refine ⟨?_,?_,?_⟩
  · intro k
    exact nonincreasingDarbouxStage_width_nonneg (function n) (ordered n).toNonincreasing _ _
  · intro k l hkl
    have h := endpointOrderedNonincreasingDarbouxDyadicStage_contains_of_stage_of_precision_mono
      (function n) (ordered n) (by change (0:Rat) ≤ 1; decide) sampleStage
      (by intro a b hab; unfold sampleStage; omega) hkl
    have ho := nonincreasingDarbouxStage_width_nonneg (function n) (ordered n).toNonincreasing
      (RationalPartition.uniform 0 1 (2^l) (Nat.two_pow_pos l) (by decide)) (sampleStage l)
    change 0 ≤ ((integral n).compute l).width at ho
    exact ⟨h.1,by unfold QInterval.width at ho; grind,h.2⟩
  · have hs : ShrinksToZero (fun k => (2*(n:Rat)+536)*delta k) := by
      apply shrinksToZero_of_natOverSuccBound (C:=2*n+536)
      intro k
      have hh := Rat.mul_le_mul_of_nonneg_left (meshRadius_le k)
        (show 0 ≤ 2*(n:Rat)+536 by have h:=Rat.natCast_nonneg (a:=n); grind)
      simpa only [Rat.natCast_add,Rat.natCast_mul,show ((2:Nat):Rat)=2 by decide +kernel,
        show ((536:Nat):Rat)=536 by decide +kernel,Rat.div_def,Rat.one_mul,Rat.mul_assoc] using hh
    intro eps
    obtain ⟨K,hK⟩ := hs eps
    exact ⟨K,fun k hk=>Rat.le_trans (stage_width n k) (hK k hk)⟩

end ComputableAnalysis.CartwrightMoments
