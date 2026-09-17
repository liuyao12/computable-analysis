import ComputableAnalysis.FiniteRationalPowers
import ComputableAnalysis.ClockTrigonometry

/-! Elementary error bookkeeping for rational samples. These predicates do
not introduce a completed number type or numerical choice of a limit. -/
namespace ComputableAnalysis.RationalSampleLimits
open ClosedArctanInverse

abbrev Seq := Nat → Rat

def Small (e : Seq) : Prop :=
  ∀ eps : QPos, ∃ N, ∀ q, N ≤ q → qabs (e q) ≤ eps.val

def Close (x y : Seq) : Prop := Small (fun q => x q-y q)

def Bounded (x : Seq) (K : Rat) : Prop := ∀ q, qabs (x q) ≤ K

theorem small_zero : Small (fun _ => 0) := by
  intro eps
  exact ⟨0,fun q _ => by change qabs (0:Rat) ≤ eps.val; rw [qabs_eq_self_of_nonneg (by decide)]; exact Rat.le_of_lt eps.property⟩

theorem close_refl (x : Seq) : Close x x := by
  change Small (fun q => x q-x q)
  simpa only [Rat.sub_self] using small_zero

theorem small_neg {x : Seq} (h : Small x) : Small (fun q => -x q) := by
  intro eps
  obtain ⟨N,hN⟩:=h eps
  exact ⟨N,fun q hq => by rw [qabs_neg]; exact hN q hq⟩

theorem close_symm {x y : Seq} (h : Close x y) : Close y x := by
  have he : (fun q => y q-x q)=(fun q => -(x q-y q)) := by funext q; grind
  unfold Close
  rw [he]
  exact small_neg h

theorem small_add {x y : Seq} (hx : Small x) (hy : Small y) : Small (fun q => x q+y q) := by
  intro eps
  let eta : QPos := ⟨eps.val/2,by rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩:=hx eta
  obtain ⟨M,hM⟩:=hy eta
  refine ⟨max N M,fun q hq => ?_⟩
  have h1:=hN q (by omega);have h2:=hM q (by omega)
  have ht:=qabs_add_le (x q) (y q)
  dsimp [eta] at h1 h2
  simp only [Rat.div_def] at h1 h2
  grind

theorem small_sub {x y : Seq} (hx : Small x) (hy : Small y) : Small (fun q => x q-y q) := by
  have h:=small_add hx (small_neg hy)
  simpa only [Rat.sub_eq_add_neg] using h

theorem close_trans {x y z : Seq} (hxy : Close x y) (hyz : Close y z) : Close x z := by
  have h:=small_add hxy hyz
  have he : (fun q => (x q-y q)+(y q-z q))=(fun q => x q-z q) := by funext q; grind
  rw [he] at h
  exact h

instance : Trans Close Close Close where trans := close_trans

private theorem budget (K : Rat) (hK : 0 ≤ K) (eps : QPos) :
    K*(eps.val/(K+1)) ≤ eps.val := by
  have hi : 0 < (K+1)⁻¹ := (Rat.inv_pos).2 (by grind)
  have hc := Rat.mul_inv_cancel (K+1) (Rat.ne_of_gt (by grind : 0<K+1))
  have hnon := Rat.mul_nonneg (Rat.le_of_lt eps.property) (Rat.le_of_lt hi)
  have he : K*(eps.val*(K+1)⁻¹)+eps.val*(K+1)⁻¹ = eps.val := by
    calc
      _ = eps.val*((K+1)*(K+1)⁻¹) := by grind
      _ = eps.val := by rw [hc,Rat.mul_one]
  simp only [Rat.div_def]
  grind only

theorem small_of_geometric_bound {e : Seq} (K : Rat) (hK : 0 ≤ K)
    (he : ∀ q, qabs (e q) ≤ K*meshRadius q) : Small e := by
  have hs : ShrinksToZero meshRadius := by
    apply shrinksToZero_of_natOverSuccBound (C:=1)
    intro n
    simpa only [show ((1:Nat):Rat)=1 by decide] using meshRadius_le n
  intro eps
  let eta : QPos := ⟨eps.val/(K+1),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by grind))⟩
  obtain ⟨N,hN⟩:=hs eta
  refine ⟨N,fun q hq => ?_⟩
  have h:=he q
  have hm:=Rat.mul_le_mul_of_nonneg_left (hN q hq) hK
  have hb := budget K hK eps
  change K*(eps.val/(K+1)) ≤ eps.val at hb
  dsimp [eta] at hm
  exact Rat.le_trans h (Rat.le_trans hm hb)

theorem small_mul_bounded {x y : Seq} (hx : Small x) {K : Rat}
    (hK : 0 ≤ K) (hy : Bounded y K) : Small (fun q => x q*y q) := by
  intro eps
  let eta : QPos := ⟨eps.val/(K+1),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by grind))⟩
  obtain ⟨N,hN⟩:=hx eta
  refine ⟨N,fun q hq => ?_⟩
  rw [qabs_mul]
  have h1:=Rat.mul_le_mul_of_nonneg_right (hN q hq) (qabs_nonneg (y q))
  have h2:=Rat.mul_le_mul_of_nonneg_left (hy q) (Rat.le_of_lt eta.property)
  have hb := budget K hK eps
  change K*eta.val ≤ eps.val at hb
  have hcomm : eta.val*K=K*eta.val := Rat.mul_comm _ _
  rw [hcomm] at h2
  exact Rat.le_trans h1 (Rat.le_trans h2 hb)

theorem small_bounded_mul {x y : Seq} {K : Rat} (hK : 0 ≤ K)
    (hx : Bounded x K) (hy : Small y) : Small (fun q => x q*y q) := by
  simpa only [Rat.mul_comm] using small_mul_bounded hy hK hx

theorem bounded_const (a : Rat) : Bounded (fun _ => a) (qabs a) := fun _ => Rat.le_refl

theorem bounded_add {x y : Seq} {K L : Rat} (hx : Bounded x K) (hy : Bounded y L) :
    Bounded (fun q => x q+y q) (K+L) := by
  intro q
  have h1:=hx q;have h2:=hy q;have h:=qabs_add_le (x q) (y q)
  grind

theorem bounded_sub {x y : Seq} {K L : Rat} (hx : Bounded x K) (hy : Bounded y L) :
    Bounded (fun q => x q-y q) (K+L) := by
  intro q
  have h1:=hx q;have h2:=hy q;have h:=qabs_sub_le (x q) (y q)
  grind

theorem bounded_mul {x y : Seq} {K L : Rat} (hK : 0 ≤ K) (hx : Bounded x K) (hy : Bounded y L) :
    Bounded (fun q => x q*y q) (K*L) := by
  intro q
  rw [qabs_mul]
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (hx q) (qabs_nonneg (y q)))
    (Rat.mul_le_mul_of_nonneg_left (hy q) hK)

theorem close_add {x y u v : Seq} (h : Close x y) (g : Close u v) :
    Close (fun q => x q+u q) (fun q => y q+v q) := by
  have hh:=small_add h g
  have he : (fun q => (x q-y q)+(u q-v q))=(fun q => (x q+u q)-(y q+v q)) := by funext q; grind
  rw [he] at hh
  exact hh

theorem close_sub {x y u v : Seq} (h : Close x y) (g : Close u v) :
    Close (fun q => x q-u q) (fun q => y q-v q) := by
  have hh:=small_sub h g
  have he : (fun q => (x q-y q)-(u q-v q))=(fun q => (x q-u q)-(y q-v q)) := by funext q; grind
  rw [he] at hh
  exact hh

theorem close_mul {x y u v : Seq} (h : Close x y) (g : Close u v)
    {K L : Rat} (hK : 0 ≤ K) (hL : 0 ≤ L) (hx : Bounded x K) (hv : Bounded v L) :
    Close (fun q => x q*u q) (fun q => y q*v q) := by
  have hh:=small_add (small_bounded_mul hK hx g) (small_mul_bounded h hL hv)
  have he : (fun q => x q*(u q-v q)+(x q-y q)*v q)=(fun q => x q*u q-y q*v q) := by funext q; grind
  rw [he] at hh
  exact hh

theorem close_scale (a : Rat) {x y : Seq} (h : Close x y) :
    Close (fun q => a*x q) (fun q => a*y q) := by
  have hh:=small_bounded_mul (qabs_nonneg a) (bounded_const a) h
  have he : (fun q => a*(x q-y q))=(fun q => a*x q-a*y q) := by funext q; grind
  rw [he] at hh
  exact hh

/-- Transfer an eventual rational inequality through a vanishing residual. -/
theorem const_le_of_close {x : Seq} {a b : Rat}
    (h : Close (fun _ => a) x) (upper : ∃ N, ∀ q, N≤q → x q≤b) : a≤b := by
  by_cases hab : a≤b
  · exact hab
  · let eps : QPos := ⟨(a-b)/2,by rw [Rat.div_def]; exact Rat.mul_pos (by grind) ((Rat.inv_pos).2 (by decide))⟩
    obtain ⟨N,hN⟩:=h eps
    obtain ⟨M,hM⟩:=upper
    have hi:=hN (max N M) (by omega)
    have hu:=hM (max N M) (by omega)
    have hp:=self_le_qabs (a-x (max N M))
    dsimp [eps] at hi
    simp only [Rat.div_def] at hi
    grind

theorem le_const_of_close {x : Seq} {a b : Rat}
    (h : Close (fun _ => a) x) (lower : ∃ N, ∀ q, N≤q → b≤x q) : b≤a := by
  have hh:=close_scale (-1) h
  have upper : ∃ N, ∀ q, N≤q → (-1)*x q ≤ -b := by
    obtain ⟨N,hN⟩:=lower
    exact ⟨N,fun q hq => by have h:=hN q hq; grind⟩
  have hl:=const_le_of_close hh upper
  grind

theorem equiv_of_close {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (x y : Seq) (hx : ∀ q, IntervalSelections.InBox (x q) (X.compute q))
    (hy : ∀ q, IntervalSelections.InBox (y q) (Y.compute q))
    (h : Close x y) : X.Equiv Y :=
  ClockTrigonometry.equiv_of_samples hX hY x y hx hy h

theorem close_of_pointwise {x y : Seq} (h : ∀ q, x q=y q) : Close x y := by
  have he : x=y := funext h
  rw [he]
  exact close_refl y

theorem small_of_close_zero {x : Seq} (h : Close x (fun _=>0)) : Small x := by
  have he : (fun q=>x q-0)=x := by funext q;grind
  unfold Close at h
  rw [he] at h
  exact h

theorem close_zero_of_small {x : Seq} (h : Small x) : Close x (fun _=>0) := by
  have he : (fun q=>x q-0)=x := by funext q;grind
  unfold Close
  rw [he]
  exact h

theorem close_bounded_mul {x y z : Seq} (h : Close x y) {K : Rat}
    (hK : 0≤K) (hz : Bounded z K) :
    Close (fun q=>z q*x q) (fun q=>z q*y q) := by
  have hh:=small_bounded_mul hK hz h
  have he : (fun q=>z q*(x q-y q))=(fun q=>z q*x q-z q*y q) := by funext q;grind
  rw [he] at hh
  exact hh

theorem close_mul_bounded {x y z : Seq} (h : Close x y) {K : Rat}
    (hK : 0≤K) (hz : Bounded z K) :
    Close (fun q=>x q*z q) (fun q=>y q*z q) := by
  simpa only [Rat.mul_comm] using close_bounded_mul h hK hz

theorem bounded_power {x : Seq} {K : Rat} (hK : 0≤K) (hx : Bounded x K) (n : Nat) :
    Bounded (fun q=>x q^n) (K^n) := by
  intro q
  rw [FiniteRationalPowers.abs_pow]
  exact FiniteRationalPowers.pow_mono (qabs_nonneg _) (hx q) n

theorem close_power {x y : Seq} (h : Close x y) {K L : Rat}
    (hK : 0≤K) (hL : 0≤L) (hx : Bounded x K) (hy : Bounded y L) (n : Nat) :
    Close (fun q=>x q^n) (fun q=>y q^n) := by
  induction n with
  | zero => simpa only [Rat.pow_zero] using close_refl (fun _=>(1:Rat))
  | succ n ih =>
    simpa only [Rat.pow_succ] using close_mul ih h
      (FiniteRationalPowers.pow_nonneg hK n) hL (bounded_power hK hx n) hy

/-- Equivalent valid boxes give asymptotically agreeing rational selections. -/
theorem close_of_equiv {X Y : RealRaw} (hX : X.Valid) (hY : Y.Valid)
    (x y : Seq) (hx : ∀ q, IntervalSelections.InBox (x q) (X.compute q))
    (hy : ∀ q, IntervalSelections.InBox (y q) (Y.compute q))
    (h : X.Equiv Y) : Close x y := by
  intro eps
  let eta : QPos := ⟨eps.val/2,by rw [Rat.div_def];exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide))⟩
  obtain ⟨N,hN⟩:=hX.2.2 eta
  obtain ⟨M,hM⟩:=hY.2.2 eta
  refine ⟨max N M,fun q hq => ?_⟩
  have h1:=hN q (by omega);have h2:=hM q (by omega)
  have hxq:=hx q;have hyq:=hy q
  have ho:=(RealRaw.compareAt_overlap_iff _ _ q q).1 (h q)
  dsimp [eta] at h1 h2
  unfold IntervalSelections.InBox at hxq hyq
  unfold QInterval.Overlaps at ho
  unfold QInterval.width at h1 h2
  simp only [Rat.div_def] at h1 h2
  apply qabs_le_of_neg_le_le <;> grind only


end ComputableAnalysis.RationalSampleLimits
