import ComputableAnalysis.CartwrightMoments

/-! Finite sums used to inspect and compare the independently defined moments. -/
namespace ComputableAnalysis.CartwrightFiniteSums
open FiniteRiemannAlgebra

theorem sum_congr {f g : Nat → Rat} {N : Nat} (h : ∀ i, i<N → f i=g i) : sum f N=sum g N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [sum_succ,sum_succ,ih (fun i hi=>h i (by omega)),h N (by omega)]

theorem sum_add (f g : Nat → Rat) (N : Nat) : sum (fun i=>f i+g i) N=sum f N+sum g N := by
  induction N with
  | zero => simp only [sum_zero,Rat.add_zero]
  | succ N ih => rw [sum_succ,sum_succ,sum_succ,ih]; grind

theorem sum_sub (f g : Nat → Rat) (N : Nat) : sum (fun i=>f i-g i) N=sum f N-sum g N := by
  induction N with
  | zero => simp only [sum_zero,Rat.sub_self]
  | succ N ih => rw [sum_succ,sum_succ,sum_succ,ih]; grind

theorem sum_mul (a : Rat) (f : Nat → Rat) (N : Nat) : sum (fun i=>a*f i) N=a*sum f N := by
  induction N with
  | zero => simp only [sum_zero,Rat.mul_zero]
  | succ N ih => rw [sum_succ,sum_succ,ih]; grind

theorem sum_const (a : Rat) (N : Nat) : sum (fun _=>a) N=(N:Rat)*a := by
  induction N with
  | zero => simp only [sum_zero,show ((0:Nat):Rat)=0 by decide +kernel,Rat.zero_mul]
  | succ N ih => rw [sum_succ,ih]; simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]; grind

theorem sum_mono {f g : Nat → Rat} {N : Nat} (h : ∀ i,i<N → f i≤g i) : sum f N≤sum g N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih =>
    have hh:=ih (fun i hi=>h i (by omega)); have hn:=h N (by omega)
    rw [sum_succ,sum_succ]; grind

theorem sum_bound {f : Nat → Rat} {N : Nat} {a : Rat} (h : ∀i,i<N→qabs (f i)≤a) :
    qabs (sum f N)≤(N:Rat)*a := by
  induction N with
  | zero => simp only [sum_zero,show ((0:Nat):Rat)=0 by decide +kernel,Rat.zero_mul]; decide +kernel
  | succ N ih =>
    have hh:=ih (fun i hi=>h i (by omega)); have hn:=h N (by omega)
    have ht:=qabs_add_le (sum f N) (f N)
    rw [sum_succ]
    simp only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel]
    grind

theorem sum_shift (f : Nat → Rat) (N : Nat) : sum (fun i=>f (i+1)) N=sum f N+f N-f 0 := by
  induction N with
  | zero => simp only [sum_zero,Rat.zero_add,Rat.sub_self]
  | succ N ih => rw [sum_succ,sum_succ,ih]; grind

theorem interval_fold (xs : List Nat) (term : Nat → QInterval) :
    xs.foldl (fun acc i=>QInterval.addInterval acc (term i)) {lo:=0,hi:=0} =
      {lo:=ratListSum (xs.map (fun i=>(term i).lo)),hi:=ratListSum (xs.map (fun i=>(term i).hi))} := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl,QInterval.zero_addInterval,List.map_cons,ratListSum]
    rw [QInterval.addInterval_fold_initial,ih]
    rfl

theorem interval_sum_congr (xs : List Nat) (f g : Nat → QInterval)
    (h : ∀i,i∈xs→f i=g i) :
    xs.foldl (fun acc i=>QInterval.addInterval acc (f i)) {lo:=0,hi:=0}=
    xs.foldl (fun acc i=>QInterval.addInterval acc (g i)) {lo:=0,hi:=0} := by
  rw [interval_fold,interval_fold]
  have hh : xs.map (fun i=>(f i).lo)=xs.map (fun i=>(g i).lo) := List.map_congr_left (fun i hi=>congrArg QInterval.lo (h i hi))
  have ht : xs.map (fun i=>(f i).hi)=xs.map (fun i=>(g i).hi) := List.map_congr_left (fun i hi=>congrArg QInterval.hi (h i hi))
  rw [hh,ht]

end ComputableAnalysis.CartwrightFiniteSums

namespace ComputableAnalysis.CartwrightMoments
open Integral FiniteRiemannAlgebra CartwrightFiniteSums CartwrightClockBounds

def cells (k : Nat) : Nat := 2^k
def step (k : Nat) : Rat := mesh 0 1 (cells k)
def grid (k j : Nat) : Rat := leftPoint 0 1 (cells k) j

theorem step_eq (k : Nat) : step k=delta k := by
  unfold step cells mesh
  rw [if_neg (Nat.ne_of_gt (Nat.two_pow_pos k))]
  simp only [show (1:Rat)-0=1 by decide +kernel,Rat.natCast_pow,
    show ((2:Nat):Rat)=2 by decide +kernel,delta,ClosedArctanInverse.meshRadius]

theorem step_pos (k : Nat) : 0<step k := by rw [step_eq]; exact ClosedArctanInverse.meshRadius_pos k

theorem cells_step (k : Nat) : (cells k:Rat)*step k=1 := by
  have h:=natCast_mul_mesh_eq_sub (a:=0) (b:=1) (Nat.two_pow_pos k)
  unfold step cells
  exact h.trans (show (1:Rat)-0=1 by decide +kernel)

theorem grid_unit (k j : Nat) (hj : j≤cells k) : Unit (grid k j) :=
  grid_mem ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩
    (by decide +kernel) (Nat.two_pow_pos k) hj

theorem grid_step (k j : Nat) : grid k (j+1)-grid k j=step k := leftPoint_step 0 1 (cells k) j

theorem grid_zero (k : Nat) : grid k 0=0 := leftPoint_zero 0 1 (cells k)
theorem grid_last (k : Nat) : grid k (cells k)=1 := leftPoint_endpoint (Nat.two_pow_pos k)

/-- Literal lower-right and upper-left rectangle sums of the moment program. -/
theorem integral_compute (n k : Nat) : (integral n).compute k =
    {lo:=sum (fun j=>step k*((value n (grid k (j+1))).compute (sampleStage k)).lo) (cells k),
     hi:=sum (fun j=>step k*((value n (grid k j)).compute (sampleStage k)).hi) (cells k)} := by
  let P:=RationalPartition.uniform 0 1 (cells k) (Nat.two_pow_pos k) (by decide : (0:Rat)≤1)
  let b:=(fun j hj=>nonincreasingDarbouxRange (function n) P j hj (sampleStage k))
  change P.boundIntegralSum b = _
  unfold RationalPartition.boundIntegralSum
  have he : (List.range (cells k)).foldl (fun acc j=>QInterval.addInterval acc (P.boundIntegralTerm b j)) {lo:=0,hi:=0} =
      (List.range (cells k)).foldl (fun acc j=>QInterval.addInterval acc
        {lo:=step k*((value n (grid k (j+1))).compute (sampleStage k)).lo,
         hi:=step k*((value n (grid k j)).compute (sampleStage k)).hi}) {lo:=0,hi:=0} := by
    apply interval_sum_congr
    intro j hj
    have hlt : j< P.pieces := List.mem_range.mp hj
    simp only [RationalPartition.boundIntegralTerm,dif_pos hlt,RationalSubinterval.scaleBound]
    have hw : (P.cell j hlt).width=step k :=
      RationalPartition.uniform_cell_width 0 1 (cells k) (Nat.two_pow_pos k) (by decide) j hlt
    rw [hw]
    simp only [QInterval.scaleByRat,if_pos (Rat.le_of_lt (step_pos k))]
    rfl
  change _ = _ at he
  change (List.range (cells k)).foldl (fun acc j=>QInterval.addInterval acc (P.boundIntegralTerm b j)) {lo:=0,hi:=0} = _
  rw [he,interval_fold]
  rfl

theorem integral_bounds (n k : Nat) : 0≤((integral n).compute k).lo ∧ ((integral n).compute k).hi≤1 := by
  rw [integral_compute]
  have hn:=step_pos k
  have lo := sum_mono (N:=cells k) (f:=fun _=>0)
    (g:=fun j=>step k*((value n (grid k (j+1))).compute (sampleStage k)).lo) (by
      intro j hj; exact Rat.mul_nonneg (Rat.le_of_lt hn) (value_bounds (grid_unit k (j+1) (by omega)) n _).1)
  have hi:=sum_mono (N:=cells k) (f:=fun j=>step k*((value n (grid k j)).compute (sampleStage k)).hi)
    (g:=fun _=>step k) (by
      intro j hj
      have h:=Rat.mul_le_mul_of_nonneg_left (value_bounds (grid_unit k j (by omega)) n (sampleStage k)).2 (Rat.le_of_lt hn)
      simpa only [Rat.mul_one] using h)
  rw [sum_const,Rat.mul_zero] at lo
  rw [sum_const,cells_step] at hi
  exact ⟨lo,hi⟩

end ComputableAnalysis.CartwrightMoments
