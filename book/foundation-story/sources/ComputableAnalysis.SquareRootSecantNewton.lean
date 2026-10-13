import ComputableAnalysis.AlgebraicFunctions
import ComputableAnalysis.PowerSeries

/-! Inverting the convex square function by two explicit rational lines.
The algorithm uses neither a general derivative nor a real root as an oracle. -/
namespace ComputableAnalysis.SquareRootSecantNewton
set_option maxHeartbeats 3000000

def step (q : Rat) (I : QInterval) : QInterval :=
  { lo := (q+I.lo*I.hi)/(I.lo+I.hi)
    hi := (I.hi*I.hi+q)/(2*I.hi) }

theorem step_spec {q : Rat} {I : QInterval}
    (ha : 0<I.lo) (hs : SqrtIntervalSpec q I) :
    SqrtIntervalSpec q (step q I) ∧
      I.lo ≤ (step q I).lo ∧ (step q I).hi ≤ I.hi ∧
      (step q I).width ≤ I.width*I.width/(2*I.hi) ∧
      (step q I).width ≤ I.width/2 := by
  let a := I.lo
  let b := I.hi
  have hab : a≤b := hs.2.1
  have hb : 0<b := by dsimp [a,b] at *; grind
  have hd : 0<a+b := by dsimp [a,b] at *; grind
  have hd2 : 0<2*b := by grind
  have hc := Rat.mul_inv_cancel (a+b) (Rat.ne_of_gt hd)
  have hc2 := Rat.mul_inv_cancel (2*b) (Rat.ne_of_gt hd2)
  have hlo : a*a≤q := hs.2.2.1
  have hhi : q≤b*b := hs.2.2.2
  have hapos : 0<a := ha
  have habpos := Rat.mul_pos hapos hb
  have hn := rat_square_nonneg_basic (b*b-q)
  have hqn := Rat.mul_nonneg (by grind : 0≤q-a*a) (by grind : 0≤b*b-q)
  have hgap := Rat.mul_nonneg (by grind : 0≤b-a) (by grind : 0≤b*b-q)
  have hinv := Rat.inv_pos.mpr hd
  have hinv2 := Rat.inv_pos.mpr hd2
  have hnonneg : 0≤(q+a*b)/(a+b) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by have := rat_square_nonneg_basic a; grind) (Rat.le_of_lt hinv)
  have hlow : a≤(q+a*b)/(a+b) := by
    apply Rat.le_of_mul_le_mul_right (c:=a+b) _ hd
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)]; grind
  have hupp : (b*b+q)/(2*b)≤b := by
    apply Rat.le_of_mul_le_mul_right (c:=2*b) _ hd2
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hd2)]; grind
  have hslo : ((q+a*b)/(a+b))*((q+a*b)/(a+b))≤q := by
    apply Rat.le_of_mul_le_mul_right (c:=(a+b)*(a+b)) _ (Rat.mul_pos hd hd)
    have heq : (q+a*b)/(a+b)*((q+a*b)/(a+b))*((a+b)*(a+b)) = (q+a*b)*(q+a*b) := by
      simp only [Rat.div_def]; grind [Rat.mul_assoc,Rat.mul_comm]
    rw [heq]
    grind only
  have hshi : q≤((b*b+q)/(2*b))*((b*b+q)/(2*b)) := by
    apply Rat.le_of_mul_le_mul_right (c:=(2*b)*(2*b)) _ (Rat.mul_pos hd2 hd2)
    have heq : (b*b+q)/(2*b)*((b*b+q)/(2*b))*((2*b)*(2*b)) = (b*b+q)*(b*b+q) := by
      simp only [Rat.div_def]; grind [Rat.mul_assoc,Rat.mul_comm]
    rw [heq]
    grind only
  have horder : (q+a*b)/(a+b)≤(b*b+q)/(2*b) := by
    apply Rat.le_of_mul_le_mul_right (c:=(a+b)*(2*b)) _ (Rat.mul_pos hd hd2)
    simp only [Rat.div_def]
    grind [Rat.mul_assoc,Rat.mul_comm]
  have heq : (b*b+q)/(2*b)-(q+a*b)/(a+b) =
      (b-a)*(b*b-q)/((2*b)*(a+b)) := by
    apply Rat.le_antisymm <;> apply Rat.le_of_mul_le_mul_right (c:=((2*b)*(a+b))) _ (Rat.mul_pos hd2 hd)
    all_goals
      simp only [Rat.div_def]
      have hcc := Rat.mul_inv_cancel ((2*b)*(a+b)) (Rat.ne_of_gt (Rat.mul_pos hd2 hd))
      grind [Rat.mul_assoc,Rat.mul_comm]
  have hquad : (b*b+q)/(2*b)-(q+a*b)/(a+b)≤(b-a)*(b-a)/(2*b) := by
    rw [heq]
    apply Rat.le_of_mul_le_mul_right (c:=((2*b)*(a+b))) _ (Rat.mul_pos hd2 hd)
    rw [Rat.div_mul_cancel (Rat.ne_of_gt (Rat.mul_pos hd2 hd))]
    simp only [Rat.div_def]
    have hm := Rat.mul_le_mul_of_nonneg_left
      (show b*b-q≤(b-a)*(a+b) by grind) (show 0≤b-a by grind)
    grind [Rat.mul_assoc,Rat.mul_comm]
  have hhalf : (b-a)*(b-a)/(2*b)≤(b-a)/2 := by
    apply Rat.le_of_mul_le_mul_right (c:=2*b) _ hd2
    rw [Rat.div_mul_cancel (Rat.ne_of_gt hd2)]
    have hm := Rat.mul_le_mul_of_nonneg_left (show b-a≤b by grind) (show 0≤b-a by grind)
    grind [Rat.div_def]
  exact ⟨⟨hnonneg,horder,hslo,hshi⟩,hlow,hupp,hquad,Rat.le_trans hquad hhalf⟩

def bracket : Nat → QInterval
  | 0 => {lo:=1,hi:=2}
  | n+1 => step 2 (bracket n)

theorem bracket_spec (n : Nat) :
    SqrtIntervalSpec 2 (bracket n) ∧ 1≤(bracket n).lo := by
  induction n with
  | zero => exact ⟨by unfold SqrtIntervalSpec bracket sq; decide +kernel,by decide +kernel⟩
  | succ n ih =>
    have h := step_spec (by grind : 0<(bracket n).lo) ih.1
    exact ⟨h.1,Rat.le_trans ih.2 h.2.1⟩

theorem bracket_nested (n : Nat) :
    (bracket n).lo≤(bracket (n+1)).lo ∧
    (bracket (n+1)).hi≤(bracket n).hi := by
  have hs := bracket_spec n
  have h := step_spec (by grind : 0<(bracket n).lo) hs.1
  exact ⟨h.2.1,h.2.2.1⟩

theorem bracket_quadratic (n : Nat) :
    (bracket (n+1)).width ≤ (bracket n).width*(bracket n).width/2 := by
  have hs := bracket_spec n
  have h := step_spec (by grind : 0<(bracket n).lo) hs.1
  have hb : 1≤(bracket n).hi := Rat.le_trans hs.2 hs.1.2.1
  have hm := Rat.mul_le_mul_of_nonneg_left (show (2:Rat)≤2*(bracket n).hi by grind)
    (rat_square_nonneg_basic (bracket n).width)
  have hd : 0<2*(bracket n).hi := by grind
  have hc := Rat.mul_inv_cancel (2*(bracket n).hi) (Rat.ne_of_gt hd)
  apply Rat.le_trans h.2.2.2.1
  apply Rat.le_of_mul_le_mul_right (c:=2*(bracket n).hi) _ hd
  rw [Rat.div_mul_cancel (Rat.ne_of_gt hd)]
  grind [Rat.div_def]

theorem bracket_width (n : Nat) : (bracket n).width≤((1:Rat)/2)^n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    have hs := bracket_spec n
    have h := step_spec (by grind : 0<(bracket n).lo) hs.1
    have hm := Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel : (0:Rat)≤1/2)
    rw [Rat.pow_succ]
    exact Rat.le_trans h.2.2.2.2 (by simpa only [Rat.div_def,Rat.one_mul] using hm)

def sqrtTwo : RealRaw := { compute:=bracket }

theorem sqrtTwo_valid : sqrtTwo.Valid := by
  refine ⟨fun n => by have h := (bracket_spec n).1.2.1; change 0≤(bracket n).hi-(bracket n).lo; grind,?_,?_⟩
  · intro n m hnm
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
    induction k with
    | zero => exact ⟨Rat.le_refl,(bracket_spec n).1.2.1,Rat.le_refl⟩
    | succ k ih =>
      have ih := ih (by omega)
      have h := bracket_nested (n+k)
      exact ⟨Rat.le_trans ih.1 h.1,(bracket_spec (n+k+1)).1.2.1,Rat.le_trans h.2 ih.2.2⟩
  · intro eps
    refine ⟨RationalMajorant.halfDecayShift 1 eps,fun n hn => ?_⟩
    have h := RationalMajorant.halfDecayShift_spec_of_le (by decide +kernel : (0:Rat)≤1) eps hn
    exact Rat.le_trans (bracket_width n) (by simpa using h)

theorem sqrtTwo_equiv_bisection : sqrtTwo.Equiv (sqrtRaw 2 (by unfold sqrtDomain; decide +kernel)) := by
  apply RealRaw.equiv_symm
  exact sqrtRaw_equiv_of_spec (by unfold sqrtDomain; decide +kernel) ⟨sqrtTwo_valid,fun n => (bracket_spec n).1⟩

end ComputableAnalysis.SquareRootSecantNewton
