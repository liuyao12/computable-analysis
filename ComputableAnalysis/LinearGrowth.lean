import ComputableAnalysis.PeanoBaker

/-! Differential growth estimates using only finite rational boxes and steps.
Solutions are defined by a vanishing first-order ODE residual on each closed
rational interval away from zero. No growth bound is part of that definition. -/
namespace ComputableAnalysis.LinearODE
open DiscreteLinearSystem

def boxNearestZero (I : QInterval) : Rat :=
  if 0 < I.lo then I.lo else if I.hi < 0 then I.hi else 0

theorem boxNearestZero_mem {I : QInterval} (hI : I.lo ≤ I.hi) :
    I.lo ≤ boxNearestZero I ∧ boxNearestZero I ≤ I.hi := by
  unfold boxNearestZero
  split <;> (try split) <;> grind

theorem boxNearestZero_min {I : QInterval} {v : Rat}
    (hv : I.lo ≤ v ∧ v ≤ I.hi) : qabs (boxNearestZero I) ≤ qabs v := by
  unfold boxNearestZero qabs
  split <;> (try split) <;> grind

abbrev BoxVector (d : Nat) := Fin d → RealRaw

def InBoxes {d : Nat} (V : BoxVector d) (n : Nat) (v : RatVector d) : Prop :=
  ∀ i, ((V i).compute n).lo ≤ v i ∧ v i ≤ ((V i).compute n).hi

def nearestVector {d : Nat} (V : BoxVector d) (n : Nat) : RatVector d :=
  fun i => boxNearestZero ((V i).compute n)

/-- A rational lower bound for the norm of any value enclosed by these boxes. -/
def normFloor {d : Nat} (V : BoxVector d) (n : Nat) : Rat :=
  vectorAbsSum (nearestVector V n)

/-- Every stage is consistent with the closed norm ball of radius `M`.
This does not require coarse enclosures themselves to fit inside that ball. -/
def NormBound {d : Nat} (V : BoxVector d) (M : Rat) : Prop :=
  ∀ n, normFloor V n ≤ M

theorem nearestVector_mem {d : Nat} {V : BoxVector d}
    (hV : ∀ i, (V i).Valid) (n : Nat) : InBoxes V n (nearestVector V n) := by
  intro i
  exact boxNearestZero_mem (RealRaw.interval_order_of_valid _ (hV i) n)

theorem normFloor_le {d : Nat} {V : BoxVector d} {n : Nat} {v : RatVector d}
    (hv : InBoxes V n v) : normFloor V n ≤ vectorAbsSum v :=
  finiteSum_le (fun i => boxNearestZero_min (hv i))

theorem inBoxes_of_later {d : Nat} {V : BoxVector d}
    (hV : ∀ i, (V i).Valid) {n m : Nat} (hnm : n ≤ m)
    {v : RatVector d} (hv : InBoxes V m v) : InBoxes V n v := by
  intro i
  have h := (hV i).2.1 n m hnm
  exact ⟨Rat.le_trans h.1 (hv i).1, Rat.le_trans (hv i).2 h.2.2⟩

def normCeiling {d : Nat} (V : BoxVector d) (n : Nat) : Rat :=
  finiteSum (fun i => qabs ((V i).compute n).lo + qabs ((V i).compute n).hi)

/-- A single computed box gives the required outer norm bound. There is no
existence assumption about an unknown supremum of solution values. -/
theorem normBound_from_initial_boxes {d : Nat} {V : BoxVector d}
    (hV : ∀ i, (V i).Valid) : NormBound V (normCeiling V 0) := by
  intro n
  have hv := inBoxes_of_later hV (Nat.zero_le n) (nearestVector_mem hV n)
  apply finiteSum_le
  intro i
  apply qabs_le_of_neg_le_le
  · have h1 := neg_qabs_le_self ((V i).compute 0).lo
    have h2 := qabs_nonneg ((V i).compute 0).hi
    have h3 := (hv i).1
    grind
  · have h1 := self_le_qabs ((V i).compute 0).hi
    have h2 := qabs_nonneg ((V i).compute 0).lo
    have h3 := (hv i).2
    grind

theorem normBound_exact {d : Nat} (v : RatVector d) (M : Rat) :
    NormBound (fun i => RealRaw.ofRat (v i)) M ↔ vectorAbsSum v ≤ M := by
  have he (n : Nat) : normFloor (fun i => RealRaw.ofRat (v i)) n = vectorAbsSum v := by
    apply congrArg vectorAbsSum
    funext i
    change boxNearestZero ⟨v i, v i⟩ = v i
    have h := boxNearestZero_mem (I := ⟨v i, v i⟩) Rat.le_refl
    exact Rat.le_antisymm h.2 h.1
  constructor
  · intro h
    have := h 0
    rwa [he] at this
  · intro h n
    rwa [he]

theorem vectorAbsSum_scale {d : Nat} (a : Rat) (v : RatVector d) :
    vectorAbsSum (fun i => a * v i) = qabs a * vectorAbsSum v := by
  unfold vectorAbsSum
  simp only [qabs_mul]
  exact (finiteSum_mul_left _ _).symm

/-- Uniform effective differentiability on every annulus, with derivative
`A(t)Y(t)`. The residual is measured on actual rational samples from refined
output boxes; the radius is strictly positive and precision may depend on
the step. This is a local ODE condition, independent of growth or a solver. -/
structure LinearSolution {d : Nat} (A : Rat → RatMatrix d) (R : Rat) where
  value : Rat → BoxVector d
  valid : ∀ t, 0 < t → t ≤ R → ∀ i, (value t i).Valid
  radius : Rat → Rat → QPos → QPos
  stage : Rat → Rat → QPos → Rat → Rat → Nat
  residual : ∀ a b (eps : QPos) x h n (v w : RatVector d),
    0 < a → a ≤ x → x ≤ b → a ≤ x+h → x+h ≤ b → b ≤ R →
    h ≠ 0 → qabs h ≤ (radius a b eps).val → stage a b eps x h ≤ n →
    InBoxes (value x) n v → InBoxes (value (x+h)) n w →
    vectorAbsSum (fun i => w i - v i - h * matrixApply (A x) v i) ≤
      eps.val * qabs h

theorem inBoxes_exact {d : Nat} {v w : RatVector d} {n : Nat}
    (h : InBoxes (fun i => RealRaw.ofRat (v i)) n w) : w = v := by
  funext i
  have hi := h i
  change v i ≤ w i ∧ w i ≤ v i at hi
  exact Rat.le_antisymm hi.2 hi.1

/-- Exact rational samples can supply the same local derivative condition. -/
def LinearSolution.ofExact {d : Nat} {A : Rat → RatMatrix d} {R : Rat}
    (v : Rat → RatVector d) (radius : Rat → Rat → QPos → QPos)
    (herr : ∀ a b (eps : QPos) x h,
      0 < a → a ≤ x → x ≤ b → a ≤ x+h → x+h ≤ b → b ≤ R →
      h ≠ 0 → qabs h ≤ (radius a b eps).val →
      vectorAbsSum (fun i => v (x+h) i-v x i-h*matrixApply (A x) (v x) i) ≤
        eps.val*qabs h) : LinearSolution A R where
  value t i := RealRaw.ofRat (v t i)
  valid _ _ _ _ := RealRaw.ofRat_valid _
  radius := radius
  stage _ _ _ _ _ := 0
  residual a b eps x h n v w ha hax hxb haxh hxhb hb hh hdelta _ hv hw := by
    have hv' := inBoxes_exact hv
    have hw' := inBoxes_exact hw
    subst v
    subst w
    exact herr a b eps x h ha hax hxb haxh hxhb hb hh hdelta

/-- A genuinely boxed constant, with an executable precision schedule,
is a solution of `Y'=0`. No singleton-box restriction is imposed. -/
def LinearSolution.constant (c : RealRaw) (hc : c.Valid)
    (precision : QPos → Nat)
    (hprecision : ∀ eps n, precision eps ≤ n → (c.compute n).width ≤ eps.val)
    (R : Rat) : LinearSolution (fun _ => (fun _ _ => 0 : RatMatrix 1)) R where
  value _ _ := c
  valid _ _ _ _ := hc
  radius _ _ _ := ⟨1, by decide⟩
  stage _ _ eps _ h := if hp : 0 < eps.val*qabs h then precision ⟨_, hp⟩ else 0
  residual a b eps x h n v w _ _ _ _ _ _ hh _ hn hv hw := by
    have hp : 0 < eps.val*qabs h := Rat.mul_pos eps.property (qabs_pos_of_ne hh)
    simp only [dif_pos hp] at hn
    have hwid := hprecision ⟨_, hp⟩ n hn
    have hv0 := hv 0
    have hw0 := hw 0
    change (c.compute n).hi-(c.compute n).lo ≤ eps.val*qabs h at hwid
    change (c.compute n).lo ≤ v 0 ∧ v 0 ≤ (c.compute n).hi at hv0
    change (c.compute n).lo ≤ w 0 ∧ w 0 ≤ (c.compute n).hi at hw0
    change qabs (w 0-v 0-h*(0*v 0+0))+0 ≤ eps.val*qabs h
    simp only [Rat.zero_mul, Rat.add_zero, Rat.mul_zero]
    rw [show w 0-v 0-0 = w 0-v 0 by grind]
    apply qabs_le_of_neg_le_le <;> grind only

/-- Finite stage synchronization; it is an algorithm, not a compactness step. -/
def maxBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => max (maxBelow f n) (f n)

theorem le_maxBelow (f : Nat → Nat) {k n : Nat} (hk : k < n) :
    f k ≤ maxBelow f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      simp only [maxBelow]
      by_cases h : k < n
      · exact Nat.le_trans (ih h) (Nat.le_max_left _ _)
      · have : k = n := by omega
        subst k
        exact Nat.le_max_right _ _

theorem pow_mono_base {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have h1 := Rat.mul_le_mul_of_nonneg_right ih ha
      have h2 := Rat.mul_le_mul_of_nonneg_left hab
        (Rat.pow_nonneg (n := n) (show 0 ≤ b by grind))
      grind

/-- The polynomial weight absorbs one inward Euler step. -/
theorem weighted_step_factor {s t : Rat} (hs : 0 ≤ s) (hst : s ≤ t) (N : Nat) :
    s ^ N * (t + (N : Rat) * (t-s)) ≤ t ^ (N+1) := by
  have ht : 0 ≤ t := by grind
  induction N with
  | zero => simp; grind
  | succ N ih =>
      have hd : 0 ≤ (t-s)*(t-s) := Rat.mul_nonneg (by grind) (by grind)
      have hN : (0 : Rat) ≤ (N : Rat) := Rat.natCast_nonneg
      have hNd := Rat.mul_nonneg (show 0 ≤ (N : Rat)+1 by grind) hd
      have hf : s * (t + ((N+1 : Nat) : Rat) * (t-s)) ≤
          t * (t + (N : Rat) * (t-s)) := by
        simp only [Rat.natCast_add]
        grind
      have hmul := Rat.mul_le_mul_of_nonneg_left hf (Rat.pow_nonneg (n := N) hs)
      have hi := Rat.mul_le_mul_of_nonneg_left ih ht
      rw [Rat.pow_succ s, Rat.pow_succ t]
      grind

theorem norm_inward_step {d : Nat} {A : RatMatrix d} {v w : RatVector d}
    {t h eps : Rat} {N : Nat} (ht : 0 < t) (hh : 0 ≤ h)
    (hA : ∀ j, t * matrixColumnAbsSum A j ≤ (N : Rat))
    (herr : vectorAbsSum (fun i => w i - v i + h * matrixApply A v i) ≤ eps*h) :
    t * vectorAbsSum w ≤ (t + (N : Rat)*h) * vectorAbsSum v + t*eps*h := by
  have hb : t * vectorAbsSum (matrixApply A v) ≤ (N : Rat)*vectorAbsSum v := by
    have hp := Rat.mul_le_mul_of_nonneg_left (matrixApply_vectorAbsSum_le A v)
      (Rat.le_of_lt ht)
    have hc := finiteSum_le (fun j =>
      Rat.mul_le_mul_of_nonneg_right (hA j) (qabs_nonneg (v j)))
    have heq : (fun j => t * matrixColumnAbsSum A j * qabs (v j)) =
        (fun j => t * (matrixColumnAbsSum A j * qabs (v j))) := by
      funext j; grind
    rw [heq, ← finiteSum_mul_left, ← finiteSum_mul_left] at hc
    exact Rat.le_trans hp hc
  have hs : vectorAbsSum w ≤ vectorAbsSum v +
      h * vectorAbsSum (matrixApply A v) + eps*h := by
    have htri := vectorAbsSum_add_le
      (fun i => v i - h * matrixApply A v i)
      (fun i => w i - v i + h * matrixApply A v i)
    have htri2 := vectorAbsSum_add_le v (fun i => -h * matrixApply A v i)
    have heq : vectorAdd (fun i => v i - h * matrixApply A v i)
        (fun i => w i - v i + h * matrixApply A v i) = w := by
      funext i; simp only [vectorAdd]; grind
    have heq2 : vectorAdd v (fun i => -h * matrixApply A v i) =
        (fun i => v i - h * matrixApply A v i) := by
      funext i; simp only [vectorAdd]; grind
    rw [heq] at htri
    rw [heq2, vectorAbsSum_scale, qabs_neg, qabs_eq_self_of_nonneg hh] at htri2
    grind
  have hm := Rat.mul_le_mul_of_nonneg_left hs (Rat.le_of_lt ht)
  have hb' := Rat.mul_le_mul_of_nonneg_left hb hh
  grind

theorem weighted_norm_step {d : Nat} {A : RatMatrix d} {v w : RatVector d}
    {s t b eps : Rat} {N : Nat} (hs : 0 < s) (hst : s ≤ t) (htb : t ≤ b)
    (heps : 0 ≤ eps) (hA : ∀ j, t * matrixColumnAbsSum A j ≤ (N : Rat))
    (herr : vectorAbsSum (fun i => w i-v i+(t-s)*matrixApply A v i) ≤ eps*(t-s)) :
    s^N * vectorAbsSum w ≤ t^N * vectorAbsSum v + eps*b^N*(t-s) := by
  have ht : 0 < t := by grind
  have hstep := norm_inward_step ht (show 0 ≤ t-s by grind) hA herr
  have hw := weighted_step_factor (Rat.le_of_lt hs) hst N
  have hpow := pow_mono_base (Rat.le_of_lt hs) (show s ≤ b by grind) N
  have hmul := Rat.mul_le_mul_of_nonneg_left hstep (Rat.pow_nonneg (n := N) (Rat.le_of_lt hs))
  have hf := Rat.mul_le_mul_of_nonneg_right hw (vectorAbsSum_nonneg v)
  have he := Rat.mul_le_mul_of_nonneg_right hpow
    (Rat.mul_nonneg (Rat.le_of_lt ht) (Rat.mul_nonneg heps (show 0 ≤ t-s by grind)))
  rw [Rat.pow_succ] at hf
  apply Rat.le_of_mul_le_mul_right (c := t)
  · grind
  · exact ht

theorem finite_grid_growth {d : Nat} {A : Rat → RatMatrix d}
    (t : Nat → Rat) (v : Nat → RatVector d) (b h eps M : Rat) (N m : Nat)
    (h0 : t 0 = b) (hv0 : vectorAbsSum (v 0) ≤ M)
    (hh : 0 ≤ h) (heps : 0 ≤ eps)
    (ht : ∀ k, k ≤ m → 0 < t k ∧ t k ≤ b)
    (hnext : ∀ k, k < m → t (k+1) = t k-h)
    (hA : ∀ k, k < m → ∀ j, t k * matrixColumnAbsSum (A (t k)) j ≤ (N : Rat))
    (herr : ∀ k, k < m →
      vectorAbsSum (fun i => v (k+1) i-v k i+h*matrixApply (A (t k)) (v k) i)
        ≤ eps*h) :
    (t m)^N * vectorAbsSum (v m) ≤ b^N*M + eps*b^N*((m : Rat)*h) := by
  have hb : 0 < b := by have := (ht 0 (by omega)).1; rwa [h0] at this
  have hall : ∀ k, k ≤ m →
      (t k)^N * vectorAbsSum (v k) ≤ b^N*M + eps*b^N*((k : Rat)*h) := by
    intro k
    induction k with
    | zero =>
        intro _
        rw [h0]
        have := Rat.mul_le_mul_of_nonneg_left hv0 (Rat.pow_nonneg (n := N) (Rat.le_of_lt hb))
        change b^N * vectorAbsSum (v 0) ≤ b^N*M + eps*b^N*(0*h)
        grind
    | succ k ih =>
        intro hk
        have hik := ih (by omega)
        have hn := hnext k (by omega)
        have hs := weighted_norm_step (N := N) (A := A (t k)) (v := v k) (w := v (k+1))
          (ht (k+1) hk).1 (show t (k+1) ≤ t k by grind)
          (ht k (by omega)).2 heps (hA k (by omega))
          (by rw [hn, show t k - (t k-h) = h by grind]; exact herr k (by omega))
        have hd : t k-t (k+1) = h := by rw [hn]; grind
        rw [hd] at hs
        simp only [Rat.natCast_add]
        clear hA herr hnext ht ih hn h0 hv0
        grind
  exact hall m (by omega)

theorem le_of_positive_errors {x y C : Rat} (hC : 0 ≤ C)
    (h : ∀ eps : QPos, x ≤ y + C*eps.val) : x ≤ y := by
  apply Decidable.byContradiction
  intro hxy
  have hd : 0 < x-y := by grind
  have hc : 0 < 2*(C+1) := by grind
  let eps : QPos := ⟨(x-y)/(2*(C+1)), by
    rw [Rat.div_def]
    exact Rat.mul_pos hd (Rat.inv_pos.mpr hc)⟩
  have he := h eps
  have heq : eps.val * (2*(C+1)) = x-y := by
    dsimp [eps]
    rw [Rat.div_def]
    have := Rat.inv_mul_cancel (2*(C+1)) (Rat.ne_of_gt hc)
    grind
  have hp := eps.property
  grind

/-- Construct an equal rational subdivision finer than a given positive step. -/
theorem rational_mesh {L delta : Rat} (hL : 0 < L) (hd : 0 < delta) :
    ∃ m : Nat, 0 < m ∧ 0 < L/(m : Rat) ∧ L/(m : Rat) ≤ delta ∧
      (m : Rat)*(L/(m : Rat)) = L := by
  let m := (delta/L).den+1
  have hm : 0 < m := by dsimp [m]; omega
  have hmr : (0 : Rat) < (m : Rat) := Rat.natCast_pos.mpr hm
  have hprod : (m : Rat)*(L/(m : Rat)) = L :=
    FormalPowerSeries.mul_div_cancel_left (Rat.ne_of_gt hmr)
  have hq : 0 < delta/L := by
    rw [Rat.div_def]
    exact Rat.mul_pos hd (Rat.inv_pos.mpr hL)
  have hb : 1/(m : Rat) ≤ delta/L := one_div_den_succ_le_of_pos hq
  have hb' := Rat.mul_le_mul_of_nonneg_right hb (Rat.le_of_lt hL)
  have hc : (delta/L)*L = delta := by
    rw [Rat.div_def]
    have := Rat.inv_mul_cancel L (Rat.ne_of_gt hL)
    grind
  have hh : L/(m : Rat) = (1/(m : Rat))*L := by
    simp only [Rat.div_def]; grind
  refine ⟨m, hm, ?_, ?_, hprod⟩
  · rw [Rat.div_def]
    exact Rat.mul_pos hL (Rat.inv_pos.mpr hmr)
  · grind

/-- The forward Fuchs estimate for arbitrary interval-valued solutions.
The sole coefficient hypothesis is a simple-pole bound on each column.
All subdivisions and precision synchronizations are finite. -/
theorem LinearSolution.weighted_growth {d : Nat} {A : Rat → RatMatrix d} {R : Rat}
    (S : LinearSolution A R) (N : Nat)
    (hA : ∀ t, 0 < t → t ≤ R → ∀ j, t*matrixColumnAbsSum (A t) j ≤ (N : Rat))
    {a b M : Rat} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R)
    (hM : NormBound (S.value b) M) (n : Nat) :
    a^N * normFloor (S.value a) n ≤ b^N*M := by
  by_cases heq : a = b
  · subst b
    exact Rat.mul_le_mul_of_nonneg_left (hM n) (Rat.pow_nonneg (Rat.le_of_lt ha))
  have hab' : a < b := by grind
  have hbpos : 0 < b := by grind
  apply le_of_positive_errors (C := b^N*(b-a))
    (Rat.mul_nonneg (Rat.pow_nonneg (Rat.le_of_lt hbpos)) (by grind))
  intro eps
  obtain ⟨m, hm, hhpos, hhdelta, hmesh⟩ :=
    rational_mesh (show 0 < b-a by grind) (S.radius a b eps).property
  let h : Rat := (b-a)/(m : Rat)
  let t : Nat → Rat := fun k => b-(k : Rat)*h
  have ht (k : Nat) (hk : k ≤ m) : a ≤ t k ∧ t k ≤ b := by
    have hk0 : (0 : Rat) ≤ (k : Rat) := Rat.natCast_nonneg
    have hkm : (k : Rat) ≤ (m : Rat) := by exact_mod_cast hk
    have hp := Rat.mul_le_mul_of_nonneg_right hkm (Rat.le_of_lt hhpos)
    have hp0 := Rat.mul_nonneg hk0 (Rat.le_of_lt hhpos)
    dsimp [t, h] at *
    grind
  have ht0 : t 0 = b := by simp [t]; grind
  have htm : t m = a := by dsimp [t, h]; grind
  have hnext (k : Nat) : t (k+1) = t k-h := by
    simp only [t, Rat.natCast_add]
    grind
  let stages : Nat → Nat := fun k => S.stage a b eps (t k) (-h)
  let stage := max n (maxBelow stages m)
  let v : Nat → RatVector d := fun k => nearestVector (S.value (t k)) stage
  have hvalid (k : Nat) (hk : k ≤ m) : ∀ i, (S.value (t k) i).Valid :=
    S.valid (t k) (by have := (ht k hk).1; grind)
      (Rat.le_trans (ht k hk).2 hb)
  have hv (k : Nat) (hk : k ≤ m) : InBoxes (S.value (t k)) stage (v k) :=
    nearestVector_mem (hvalid k hk) stage
  have herr (k : Nat) (hk : k < m) :
      vectorAbsSum (fun i => v (k+1) i-v k i+h*matrixApply (A (t k)) (v k) i)
        ≤ eps.val*h := by
    have hstep : t k + -h = t (k+1) := by rw [hnext]; grind
    have hs : S.stage a b eps (t k) (-h) ≤ stage :=
      Nat.le_trans (le_maxBelow stages hk) (Nat.le_max_right _ _)
    have hg := S.residual a b eps (t k) (-h) stage (v k) (v (k+1)) ha
      (ht k (by omega)).1 (ht k (by omega)).2
      (by rw [hstep]; exact (ht (k+1) (by omega)).1)
      (by rw [hstep]; exact (ht (k+1) (by omega)).2) hb
      (by change -((b-a)/(m : Rat)) ≠ 0; grind)
      (by rw [qabs_neg, qabs_eq_self_of_nonneg (Rat.le_of_lt hhpos)]; exact hhdelta)
      hs (hv k (by omega)) (by rw [hstep]; exact hv (k+1) (by omega))
    rw [qabs_neg, qabs_eq_self_of_nonneg (Rat.le_of_lt hhpos)] at hg
    have he : (fun i => v (k+1) i-v k i- -h*matrixApply (A (t k)) (v k) i) =
        (fun i => v (k+1) i-v k i+h*matrixApply (A (t k)) (v k) i) := by
      funext i; grind
    rw [he] at hg
    exact hg
  have hg := finite_grid_growth t v b h eps.val M N m ht0
    (by change normFloor (S.value (t 0)) stage ≤ M; rw [ht0]; exact hM stage)
    (Rat.le_of_lt hhpos) (Rat.le_of_lt eps.property)
    (fun k hk => ⟨by have := (ht k hk).1; grind, (ht k hk).2⟩)
    (fun k _ => hnext k)
    (fun k hk => hA (t k) (by have := (ht k (by omega)).1; grind)
      (Rat.le_trans (ht k (by omega)).2 hb)) herr
  have hcoarse : normFloor (S.value a) n ≤ vectorAbsSum (v m) := by
    apply normFloor_le
    have hv' := inBoxes_of_later (hvalid m (by omega)) (Nat.le_max_left n _) (hv m (by omega))
    rwa [htm] at hv'
  have hc := Rat.mul_le_mul_of_nonneg_left hcoarse (Rat.pow_nonneg (n := N) (Rat.le_of_lt ha))
  rw [htm] at hg
  change (m : Rat)*h = b-a at hmesh
  rw [hmesh] at hg
  grind

theorem LinearSolution.fuchs_growth {d : Nat} {A : Rat → RatMatrix d} {R : Rat}
    (S : LinearSolution A R) (N : Nat)
    (hA : ∀ t, 0 < t → t ≤ R → ∀ j, t*matrixColumnAbsSum (A t) j ≤ (N : Rat))
    {a b M : Rat} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R)
    (hM : NormBound (S.value b) M) :
    NormBound (S.value a) (b^N*M/a^N) := by
  intro n
  have hg := S.weighted_growth N hA ha hab hb hM n
  have hp := Rat.pow_pos (n := N) ha
  have hc : (b^N*M/a^N)*a^N = b^N*M := by
    rw [Rat.div_def]
    have := Rat.inv_mul_cancel (a^N) (Rat.ne_of_gt hp)
    grind
  apply Rat.le_of_mul_le_mul_right (c := a^N)
  · grind
  · exact hp

/-- Every solution has an explicit moderate-growth bound, obtained by
computing its outer endpoint at stage zero. -/
theorem LinearSolution.moderate_growth {d : Nat} {A : Rat → RatMatrix d} {R : Rat}
    (S : LinearSolution A R) (N : Nat)
    (hA : ∀ t, 0 < t → t ≤ R → ∀ j, t*matrixColumnAbsSum (A t) j ≤ (N : Rat))
    {a b : Rat} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    NormBound (S.value a) (b^N * normCeiling (S.value b) 0 / a^N) :=
  S.fuchs_growth N hA ha hab hb
    (normBound_from_initial_boxes (S.valid b (by grind) hb))

end ComputableAnalysis.LinearODE
