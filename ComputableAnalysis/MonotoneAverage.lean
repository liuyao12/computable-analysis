import ComputableAnalysis.ClosedArctanInverse
import ComputableAnalysis.IntervalSelections

/-! Finite dyadic endpoint sums. There is no integral or chosen limiting value
in this module. The evaluation stage remains separate from mesh depth. -/
namespace ComputableAnalysis.MonotoneAverage
open ClosedArctanInverse

/-- Normalized left and right rectangle sums on a dyadic partition. -/
def left (f : Rat → Rat) (a b : Rat) : Nat → Rat
  | 0 => f a
  | n+1 => (left f a ((a+b)/2) n + left f ((a+b)/2) b n)/2

def right (f : Rat → Rat) (a b : Rat) : Nat → Rat
  | 0 => f b
  | n+1 => (right f a ((a+b)/2) n + right f ((a+b)/2) b n)/2

abbrev Decreases (f : Rat → Rat) : Prop :=
  ∀ a b, Unit a → Unit b → a ≤ b → f b ≤ f a

theorem midpoint_unit {a b : Rat} (ha : Unit a) (hb : Unit b) : Unit ((a+b)/2) := by
  have a0:=ha.1; have a1:=ha.2; have b0:=hb.1; have b1:=hb.2
  simp only [Rat.div_def]
  constructor <;> grind

theorem midpoint_between {a b : Rat} (hab : a ≤ b) : a ≤ (a+b)/2 ∧ (a+b)/2 ≤ b := by
  simp only [Rat.div_def]; constructor <;> grind

theorem left_bounds (f : Rat → Rat) (lo hi : Rat)
    (hf : ∀ x, Unit x → lo ≤ f x ∧ f x ≤ hi)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (n : Nat) :
    lo ≤ left f a b n ∧ left f a b n ≤ hi := by
  induction n generalizing a b with
  | zero => exact hf a ha
  | succ n ih =>
    have h1:=ih ha (midpoint_unit ha hb)
    have h2:=ih (midpoint_unit ha hb) hb
    clear ih hf
    simp only [left,Rat.div_def] at h1 h2 ⊢; constructor <;> grind

theorem right_bounds (f : Rat → Rat) (lo hi : Rat)
    (hf : ∀ x, Unit x → lo ≤ f x ∧ f x ≤ hi)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (n : Nat) :
    lo ≤ right f a b n ∧ right f a b n ≤ hi := by
  induction n generalizing a b with
  | zero => exact hf b hb
  | succ n ih =>
    have h1:=ih ha (midpoint_unit ha hb)
    have h2:=ih (midpoint_unit ha hb) hb
    clear ih hf
    simp only [right,Rat.div_def] at h1 h2 ⊢; constructor <;> grind

theorem ordered (f : Rat → Rat) (hf : Decreases f)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a ≤ b) (n : Nat) :
    right f a b n ≤ left f a b n := by
  induction n generalizing a b with
  | zero => exact hf a b ha hb hab
  | succ n ih =>
    have hm:=midpoint_unit ha hb; have hh:=midpoint_between hab
    have h1:=ih ha hm hh.1; have h2:=ih hm hb hh.2
    clear ih
    simp only [left,right,Rat.div_def] at h1 h2 ⊢; grind

theorem gap (f : Rat → Rat) (a b : Rat) (n : Nat) :
    left f a b n-right f a b n=meshRadius n*(f a-f b) := by
  induction n generalizing a b with
  | zero =>
    simp only [left,right]
    rw [show meshRadius 0=(1 : Rat) by decide +kernel,Rat.one_mul]
  | succ n ih =>
    have h1:=ih a ((a+b)/2); have h2:=ih ((a+b)/2) b
    have he : meshRadius (n+1)=meshRadius n/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
      exact Rat.mul_comm _ _
    rw [he]
    clear ih
    simp only [left,right,Rat.div_def] at h1 h2 ⊢; grind

theorem one_refinement (f : Rat → Rat) (hf : Decreases f)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a ≤ b) (n : Nat) :
    right f a b n ≤ right f a b (n+1) ∧ left f a b (n+1) ≤ left f a b n := by
  induction n generalizing a b with
  | zero =>
    have hm:=midpoint_unit ha hb; have hh:=midpoint_between hab
    have h1:=hf a ((a+b)/2) ha hm hh.1
    have h2:=hf ((a+b)/2) b hm hb hh.2
    clear hf
    simp only [left,right,Rat.div_def] at h1 h2 ⊢
    constructor <;> grind
  | succ n ih =>
    have hm:=midpoint_unit ha hb; have hh:=midpoint_between hab
    have h1:=ih ha hm hh.1; have h2:=ih hm hb hh.2
    clear ih hf
    change (right f a ((a+b)/2) n+right f ((a+b)/2) b n)/2 ≤
        (right f a ((a+b)/2) (n+1)+right f ((a+b)/2) b (n+1))/2 ∧
      (left f a ((a+b)/2) (n+1)+left f ((a+b)/2) b (n+1))/2 ≤
        (left f a ((a+b)/2) n+left f ((a+b)/2) b n)/2
    simp only [Rat.div_def] at h1 h2 ⊢
    constructor <;> grind

theorem refinement (f : Rat → Rat) (hf : Decreases f)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a ≤ b)
    {n m : Nat} (hnm : n ≤ m) :
    right f a b n ≤ right f a b m ∧ left f a b m ≤ left f a b n := by
  induction m with
  | zero =>
    have he : n=0 := by omega
    subst n
    exact ⟨Rat.le_refl,Rat.le_refl⟩
  | succ m ih =>
    by_cases h : n≤m
    · have hh:=ih h
      have hstep:=one_refinement f hf ha hb hab m
      exact ⟨Rat.le_trans hh.1 hstep.1,Rat.le_trans hstep.2 hh.2⟩
    · have he : n=m+1 := by omega
      subst n
      exact ⟨Rat.le_refl,Rat.le_refl⟩

theorem mesh_error (f : Rat → Rat) (hf : Decreases f)
    (hf0 : 0 ≤ f 1) (hf1 : f 0 ≤ 1) {n m : Nat} (hnm : n ≤ m) :
    qabs (left f 0 1 n-left f 0 1 m) ≤ meshRadius n := by
  have h:=refinement f hf (a:=0) (b:=1) ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel) hnm
  have ho:=ordered f hf (a:=0) (b:=1) ⟨by decide +kernel,by decide +kernel⟩ ⟨by decide +kernel,by decide +kernel⟩ (by decide +kernel) m
  have hg:=gap f 0 1 n
  have hm:=Rat.mul_le_mul_of_nonneg_left (show f 0-f 1 ≤ 1 by grind) (Rat.le_of_lt (meshRadius_pos n))
  rw [qabs_eq_self_of_nonneg (by grind : 0 ≤ left f 0 1 n-left f 0 1 m)]
  grind

theorem perturbation (f g : Rat → Rat) (E : Rat)
    (h : ∀ x, Unit x → qabs (f x-g x) ≤ E)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (n : Nat) :
    qabs (left f a b n-left g a b n) ≤ E := by
  induction n generalizing a b with
  | zero => exact h a ha
  | succ n ih =>
    have h1:=ih ha (midpoint_unit ha hb)
    have h2:=ih (midpoint_unit ha hb) hb
    have hp1:=self_le_qabs (left f a ((a+b)/2) n-left g a ((a+b)/2) n)
    have hn1:=neg_qabs_le_self (left f a ((a+b)/2) n-left g a ((a+b)/2) n)
    have hp2:=self_le_qabs (left f ((a+b)/2) b n-left g ((a+b)/2) b n)
    have hn2:=neg_qabs_le_self (left f ((a+b)/2) b n-left g ((a+b)/2) b n)
    clear ih h
    simp only [Rat.div_def] at h1 h2 hp1 hn1 hp2 hn2
    apply qabs_le_of_neg_le_le <;> simp only [left,Rat.div_def] <;> grind

theorem left_add (f g : Rat → Rat) (a b : Rat) (n : Nat) :
    left (fun x => f x+g x) a b n=left f a b n+left g a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def]; clear ih; grind

theorem left_mul (c : Rat) (f : Rat → Rat) (a b : Rat) (n : Nat) :
    left (fun x => c*f x) a b n=c*left f a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def]; clear ih; grind

theorem left_sub (f g : Rat → Rat) (a b : Rat) (n : Nat) :
    left (fun x => f x-g x) a b n=left f a b n-left g a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.div_def]; clear ih; grind

/-- The last endpoint lies below every left sum for a decreasing function. -/
theorem endpoint_le_left (f : Rat → Rat) (hf : Decreases f)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a≤b) (d : Nat) : f b≤left f a b d := by
  have hr:=refinement f hf ha hb hab (n:=0) (m:=d) (Nat.zero_le d)
  have ho:=ordered f hf ha hb hab d
  exact Rat.le_trans hr.1 ho

/-- Positivity on a quarter of the interval supplies a quantitative lower
bound for all sufficiently refined dyadic averages. -/
theorem quarter_mass (f : Rat → Rat) (hf : Decreases f)
    (hf0 : ∀ x, Unit x → 0≤f x) (d : Nat) :
    f (1/4)/4 ≤ left f 0 1 (d+2) := by
  have hu0 : Unit (0:Rat) := ⟨by decide +kernel,by decide +kernel⟩
  have hu1 : Unit (1:Rat) := ⟨by decide +kernel,by decide +kernel⟩
  have hu2 : Unit ((0+1:Rat)/2) := midpoint_unit hu0 hu1
  have hu4 : Unit ((0+(0+1:Rat)/2)/2) := midpoint_unit hu0 hu2
  have hleft:=endpoint_le_left f hf hu0 hu4 (by decide +kernel) d
  have hbound (a b : Rat) (ha : Unit a) (hb : Unit b) (k : Nat) : 0≤left f a b k := by
    have hb0:=hf0 1 hu1
    have hB : ∀ x, Unit x → 0≤f x ∧ f x≤f 0 := by
      intro x hx
      exact ⟨hf0 x hx,hf 0 x hu0 hx hx.1⟩
    exact (left_bounds f 0 (f 0) hB ha hb k).1
  have hmid:=hbound _ _ hu4 hu2 d
  have hright:=hbound _ _ hu2 hu1 (d+1)
  have hval : ((0+(0+1:Rat)/2)/2)=1/4 := by decide +kernel
  rw [hval] at hleft
  change f (1/4)/4 ≤ ((left f 0 ((0+(0+1)/2)/2) d+
    left f ((0+(0+1)/2)/2) ((0+1)/2) d)/2+left f ((0+1)/2) 1 (d+1))/2
  simp only [Rat.div_def] at hleft hmid hright ⊢
  grind only


end ComputableAnalysis.MonotoneAverage
