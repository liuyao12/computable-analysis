import ComputableAnalysis.CartwrightFiniteSums

/-!
# Algebra of rational errors tending to zero

This is proof-side bookkeeping for explicit rational sequences, not a new
real-number type or completion. All final statements return to RealRaw.Equiv.
-/
namespace ComputableAnalysis.RationalErrorCalculus

abbrev Sequence := Nat → Rat

def Near (x y : Sequence) : Prop :=
  ∀ eps : QPos, ∃ N, ∀ k, N≤k → qabs (x k-y k)≤eps.val

def Bounded (x : Sequence) : Prop :=
  ∃ B : Rat, 0≤B ∧ ∀k,qabs (x k)≤B

namespace Near

theorem refl (x : Sequence) : Near x x := by
  intro eps;refine ⟨0,fun k _=>?_⟩
  rw [Rat.sub_self,show qabs (0:Rat)=0 by decide +kernel]
  exact Rat.le_of_lt eps.property

theorem of_eq {x y : Sequence} (h : ∀k,x k=y k) : Near x y := by
  have he : x=y := funext h
  rw [he]; exact refl y

theorem symm {x y : Sequence} (h : Near x y) : Near y x := by
  intro eps;obtain ⟨N,hN⟩:=h eps;refine ⟨N,fun k hk=>?_⟩
  rw [show y k-x k= -(x k-y k) by grind,qabs_neg]
  exact hN k hk

private def half (eps : QPos) : QPos := ⟨eps.val/2,by
  rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide +kernel))⟩

theorem trans {x y z : Sequence} (h1 : Near x y) (h2 : Near y z) : Near x z := by
  intro eps
  obtain ⟨N,hN⟩:=h1 (half eps);obtain ⟨M,hM⟩:=h2 (half eps)
  refine ⟨max N M,fun k hk=>?_⟩
  have a:=hN k (by omega);have b:=hM k (by omega)
  have ht:=qabs_add_le (x k-y k) (y k-z k)
  rw [show x k-y k+(y k-z k)=x k-z k by grind] at ht
  dsimp [half] at a b
  simp only [Rat.div_def] at a b
  grind

theorem add {x y u v : Sequence} (h1 : Near x y) (h2 : Near u v) :
    Near (fun k=>x k+u k) (fun k=>y k+v k) := by
  intro eps
  obtain ⟨N,hN⟩:=h1 (half eps);obtain ⟨M,hM⟩:=h2 (half eps)
  refine ⟨max N M,fun k hk=>?_⟩
  have a:=hN k (by omega);have b:=hM k (by omega)
  have ht:=qabs_add_le (x k-y k) (u k-v k)
  have he : x k-y k+(u k-v k)=(x k+u k)-(y k+v k) := by grind
  rw [he] at ht
  dsimp only
  dsimp [half] at a b
  simp only [Rat.div_def] at a b
  grind

theorem sub {x y u v : Sequence} (h1 : Near x y) (h2 : Near u v) :
    Near (fun k=>x k-u k) (fun k=>y k-v k) := by
  intro eps
  obtain ⟨N,hN⟩:=h1 (half eps);obtain ⟨M,hM⟩:=h2 (half eps)
  refine ⟨max N M,fun k hk=>?_⟩
  have a:=hN k (by omega);have b:=hM k (by omega)
  have ht:=qabs_sub_le (x k-y k) (u k-v k)
  have he : (x k-y k)-(u k-v k)=(x k-u k)-(y k-v k) := by grind
  rw [he] at ht
  dsimp only
  dsimp [half] at a b
  simp only [Rat.div_def] at a b
  grind

/-- Scaling the requested tolerance is a proof step, not runtime rescheduling. -/
theorem scaled_error {x y : Sequence} (h : Near x y) (C : Rat) (hC : 0≤C) (eps : QPos) :
    ∃N,∀k,N≤k→C*qabs (x k-y k)≤eps.val := by
  have hp : 0<C+1 := by grind
  let eta : QPos:=⟨eps.val/(C+1),by
    rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hp)⟩
  obtain ⟨N,hN⟩:=h eta
  refine ⟨N,fun k hk=>?_⟩
  have hh:=hN k hk
  have ht:=Rat.mul_le_mul_of_nonneg_left hh hC
  have hc:=Rat.mul_inv_cancel (C+1) (Rat.ne_of_gt hp)
  have he : (C+1)*eta.val=eps.val := by dsimp [eta];simp only [Rat.div_def];grind
  have h0:=Rat.le_of_lt eta.property
  grind

theorem mul {x y u v : Sequence} (hx : Bounded x) (hv : Bounded v)
    (h1 : Near x y) (h2 : Near u v) : Near (fun k=>x k*u k) (fun k=>y k*v k) := by
  obtain ⟨A,hA,ha⟩:=hx;obtain ⟨B,hB,hb⟩:=hv
  intro eps
  obtain ⟨N,hN⟩:=scaled_error h2 A hA (half eps)
  obtain ⟨M,hM⟩:=scaled_error h1 B hB (half eps)
  refine ⟨max N M,fun k hk=>?_⟩
  have aa:=hN k (by omega);have bb:=hM k (by omega)
  have hmul1:=Rat.mul_le_mul_of_nonneg_right (ha k) (qabs_nonneg (u k-v k))
  have hmul2:=Rat.mul_le_mul_of_nonneg_left (hb k) (qabs_nonneg (x k-y k))
  have ht:=qabs_add_le (x k*(u k-v k)) ((x k-y k)*v k)
  rw [show x k*(u k-v k)+(x k-y k)*v k=x k*u k-y k*v k by grind,
    qabs_mul,qabs_mul] at ht
  dsimp only
  dsimp [half] at aa bb
  simp only [Rat.div_def] at aa bb
  grind

theorem geometric {x y : Sequence} (C : Rat) (hC : 0≤C)
    (h : ∀k,qabs (x k-y k)≤C*ClosedArctanInverse.meshRadius k) : Near x y := by
  have shrink : ShrinksToZero ClosedArctanInverse.meshRadius := by
    apply shrinksToZero_of_natOverSuccBound (C:=1)
    intro k;simpa only [show ((1:Nat):Rat)=1 by decide +kernel] using ClosedArctanInverse.meshRadius_le k
  have hz : Near ClosedArctanInverse.meshRadius (fun _=>0) := by
    intro eps;obtain ⟨N,hN⟩:=shrink eps;refine ⟨N,fun k hk=>?_⟩
    rw [show ClosedArctanInverse.meshRadius k-0=ClosedArctanInverse.meshRadius k by grind,
      qabs_eq_self_of_nonneg (Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos k))]
    exact hN k hk
  intro eps
  obtain ⟨N,hN⟩:=scaled_error hz C hC eps
  refine ⟨N,fun k hk=>?_⟩
  have hh:=hN k hk
  rw [show ClosedArctanInverse.meshRadius k-0=ClosedArctanInverse.meshRadius k by grind,
    qabs_eq_self_of_nonneg (Rat.le_of_lt (ClosedArctanInverse.meshRadius_pos k))] at hh
  exact Rat.le_trans (h k) hh

/-- A constant near an eventually bounded sequence inherits those rational bounds. -/
theorem constant_bounds {x : Sequence} {r A B : Rat} (h : Near x (fun _=>r))
    (N : Nat) (hb : ∀k,N≤k→A≤x k ∧ x k≤B) : A≤r ∧ r≤B := by
  have slack (eps : QPos) : A≤r+eps.val ∧ r≤B+eps.val := by
    obtain ⟨M,hM⟩:=h eps
    have h1:=hM (max N M) (by omega)
    have h2:=hb (max N M) (by omega)
    have hneg:=neg_qabs_le_self (x (max N M)-r)
    have hpos:=self_le_qabs (x (max N M)-r)
    constructor <;> grind
  have le_slack {a b : Rat} (hh : ∀eps:QPos,a≤b+eps.val) : a≤b := by
    by_cases hab : a≤b
    · exact hab
    · let e : QPos:=⟨(a-b)/2,by rw [Rat.div_def];exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide +kernel))⟩
      have hh0:=hh e
      dsimp [e] at hh0
      simp only [Rat.div_def] at hh0
      grind
  exact ⟨le_slack (fun e=>(slack e).1),le_slack (fun e=>(slack e).2)⟩

end Near

namespace Bounded

theorem constant (a : Rat) : Bounded (fun _=>a) := ⟨qabs a,qabs_nonneg a,fun _=>Rat.le_refl⟩

theorem add {x y : Sequence} (hx : Bounded x) (hy : Bounded y) : Bounded (fun k=>x k+y k) := by
  obtain ⟨A,hA,ha⟩:=hx;obtain ⟨B,hB,hb⟩:=hy
  refine ⟨A+B,Rat.add_nonneg hA hB,fun k=>?_⟩
  have hh:=qabs_add_le (x k) (y k);have h1:=ha k;have h2:=hb k;grind

theorem sub {x y : Sequence} (hx : Bounded x) (hy : Bounded y) : Bounded (fun k=>x k-y k) := by
  obtain ⟨A,hA,ha⟩:=hx;obtain ⟨B,hB,hb⟩:=hy
  refine ⟨A+B,Rat.add_nonneg hA hB,fun k=>?_⟩
  have hh:=qabs_sub_le (x k) (y k);have h1:=ha k;have h2:=hb k;grind

theorem mul {x y : Sequence} (hx : Bounded x) (hy : Bounded y) : Bounded (fun k=>x k*y k) := by
  obtain ⟨A,hA,ha⟩:=hx;obtain ⟨B,hB,hb⟩:=hy
  refine ⟨A*B,Rat.mul_nonneg hA hB,fun k=>?_⟩
  rw [qabs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (ha k) (qabs_nonneg (y k)))
    (Rat.mul_le_mul_of_nonneg_left (hb k) hA)

theorem pow {x : Sequence} (hx : Bounded x) (n : Nat) : Bounded (fun k=>(x k)^n) := by
  induction n with
  | zero => simpa only [Rat.pow_zero] using constant 1
  | succ n ih => simpa only [Rat.pow_succ] using mul ih hx

end Bounded

namespace Near

theorem scale {x y : Sequence} (h : Near x y) (a : Rat) : Near (fun k=>a*x k) (fun k=>a*y k) := by
  intro eps
  obtain ⟨N,hN⟩:=scaled_error h (qabs a) (qabs_nonneg a) eps
  refine ⟨N,fun k hk=>?_⟩
  change qabs (a*x k-a*y k)≤eps.val
  rw [show a*x k-a*y k=a*(x k-y k) by grind,qabs_mul]
  exact hN k hk

theorem mul_left {x y u : Sequence} (hu : Bounded u) (h : Near x y) :
    Near (fun k=>u k*x k) (fun k=>u k*y k) := by
  obtain ⟨B,hB,hb⟩:=hu
  intro eps
  obtain ⟨N,hN⟩:=scaled_error h B hB eps
  refine ⟨N,fun k hk=>?_⟩
  change qabs (u k*x k-u k*y k)≤eps.val
  rw [show u k*x k-u k*y k=u k*(x k-y k) by grind,qabs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (hb k) (qabs_nonneg (x k-y k))) (hN k hk)

theorem of_difference {x y : Sequence} (h : Near (fun k=>x k-y k) (fun _=>0)) : Near x y := by
  intro eps
  obtain ⟨N,hN⟩:=h eps
  refine ⟨N,fun k hk=>?_⟩
  have hh:=hN k hk
  simpa only [show ∀a:Rat,a-0=a by intro a;grind] using hh

theorem pow {x y : Sequence} (hx : Bounded x) (hy : Bounded y)
    (h : Near x y) (n : Nat) : Near (fun k=>(x k)^n) (fun k=>(y k)^n) := by
  induction n with
  | zero => simpa only [Rat.pow_zero] using refl (fun _=>(1:Rat))
  | succ n ih => simpa only [Rat.pow_succ] using mul (Bounded.pow hx n) hy ih h

theorem of_equiv {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid) (he : X.Equiv Y)
    {x y : Sequence}
    (hx : ∀k,IntervalSelections.InBox (x k) (X.compute k))
    (hy : ∀k,IntervalSelections.InBox (y k) (Y.compute k)) : Near x y := by
  intro eps
  obtain ⟨N,hN⟩:=hX.2.2 (half eps);obtain ⟨M,hM⟩:=hY.2.2 (half eps)
  refine ⟨max N M,fun k hk=>?_⟩
  have wx:=hN k (by omega);have wy:=hM k (by omega)
  have a:=hx k;have b:=hy k
  have ov:=(RealRaw.compareAt_overlap_iff _ _ k k).1 (he k)
  unfold IntervalSelections.InBox at a b
  unfold QInterval.width at wx wy
  unfold QInterval.Overlaps at ov
  dsimp [half] at wx wy
  simp only [Rat.div_def] at wx wy
  apply qabs_le_of_neg_le_le <;> grind

theorem to_equiv {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    {x y : Sequence}
    (hx : ∀k,IntervalSelections.InBox (x k) (X.compute k))
    (hy : ∀k,IntervalSelections.InBox (y k) (Y.compute k)) (he : Near x y) : X.Equiv Y :=
  ClockTrigonometry.equiv_of_samples hX hY x y hx hy he

end Near
end ComputableAnalysis.RationalErrorCalculus
