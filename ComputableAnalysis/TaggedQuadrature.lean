import ComputableAnalysis.MonotoneAverage
import ComputableAnalysis.RationalSampleLimits

/-!
# Tagged finite quadrature

A tag is a rational point of a rational cell. The finite average permits any
such selection, not just the left endpoint. These operations do not introduce
an integral or select a limiting real number.
-/
namespace ComputableAnalysis.TaggedQuadrature
open ClosedArctanInverse MonotoneAverage RationalSampleLimits

structure Tag where
  point : Rat → Rat → Rat
  between : ∀ {a b}, a ≤ b → a ≤ point a b ∧ point a b ≤ b

def leftTag : Tag := ⟨fun a _ => a, fun h => ⟨Rat.le_refl,h⟩⟩
def rightTag : Tag := ⟨fun _ b => b, fun h => ⟨h,Rat.le_refl⟩⟩
def midpointTag : Tag := ⟨fun a b => (a+b)/2, midpoint_between⟩

def average (f : Rat → Rat) (tag : Tag) (a b : Rat) : Nat → Rat
  | 0 => f (tag.point a b)
  | n+1 => (average f tag a ((a+b)/2) n + average f tag ((a+b)/2) b n)/2

theorem average_left (f : Rat → Rat) (a b : Rat) (n : Nat) :
    average f leftTag a b n = left f a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,left,ih]

theorem average_right (f : Rat → Rat) (a b : Rat) (n : Nat) :
    average f rightTag a b n = right f a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,right,ih]

theorem average_const (c : Rat) (tag : Tag) (a b : Rat) (n : Nat) :
    average (fun _ => c) tag a b n = c := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,ih,Rat.div_def]; grind only

theorem average_add (f g : Rat → Rat) (tag : Tag) (a b : Rat) (n : Nat) :
    average (fun x => f x+g x) tag a b n =
      average f tag a b n + average g tag a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,ih,Rat.div_def]; grind only

theorem average_scale (c : Rat) (f : Rat → Rat) (tag : Tag) (a b : Rat) (n : Nat) :
    average (fun x => c*f x) tag a b n = c*average f tag a b n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,ih,Rat.div_def]; grind only

/-- Finite averaging preserves pointwise convergence on the finitely many
selected tags. The evaluation cutoff is allowed to depend on the fixed mesh. -/
theorem average_close (f g : Rat → Nat → Rat) (tag : Tag)
    {a b : Rat} (hab : a ≤ b)
    (h : ∀ x, a ≤ x → x ≤ b → Close (f x) (g x)) (n : Nat) :
    Close (fun q => average (fun x => f x q) tag a b n)
      (fun q => average (fun x => g x q) tag a b n) := by
  induction n generalizing a b with
  | zero => exact h _ (tag.between hab).1 (tag.between hab).2
  | succ n ih =>
    have hm := midpoint_between hab
    have hl := ih hm.1 (fun x hx hy => h x hx (Rat.le_trans hy hm.2))
    have hr := ih hm.2 (fun x hx hy => h x (Rat.le_trans hm.1 hx) hy)
    have hs := close_scale ((2:Rat)⁻¹) (close_add hl hr)
    simpa only [average,Rat.div_def,Rat.mul_comm] using hs

/-- For a monotone function, every tag lies between its endpoint sums. -/
theorem decreasing_bounds (f : Rat → Rat) (hf : Decreases f) (tag : Tag)
    {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a ≤ b) (n : Nat) :
    right f a b n ≤ average f tag a b n ∧ average f tag a b n ≤ left f a b n := by
  induction n generalizing a b with
  | zero =>
    have ht := tag.between hab
    have hu : Unit (tag.point a b) := ⟨Rat.le_trans ha.1 ht.1,Rat.le_trans ht.2 hb.2⟩
    exact ⟨hf _ _ hu hb ht.2,hf _ _ ha hu ht.1⟩
  | succ n ih =>
    have hm := midpoint_unit ha hb
    have hh := midpoint_between hab
    have hl := ih ha hm hh.1
    have hr := ih hm hb hh.2
    simp only [average,left,right,Rat.div_def]
    constructor <;> grind only

/-- A Lipschitz cell estimate controls arbitrary tags at every finite depth. -/
theorem lipschitz_tag_error (f : Rat → Rat) (L : Rat) (hL : 0 ≤ L)
    (hf : ∀ x y, Unit x → Unit y → qabs (f x-f y) ≤ L*qabs (x-y))
    (tag : Tag) {a b : Rat} (ha : Unit a) (hb : Unit b) (hab : a ≤ b) (n : Nat) :
    qabs (average f tag a b n-left f a b n) ≤ L*(b-a)*meshRadius n := by
  induction n generalizing a b with
  | zero =>
    have ht := tag.between hab
    have hu : Unit (tag.point a b) := ⟨Rat.le_trans ha.1 ht.1,Rat.le_trans ht.2 hb.2⟩
    have h1 := hf _ a hu ha
    rw [qabs_eq_self_of_nonneg (by have hh:=ht.1;grind : 0≤tag.point a b-a)] at h1
    have h2 := Rat.mul_le_mul_of_nonneg_left (show tag.point a b-a ≤ b-a by grind) hL
    simpa only [average,left,show meshRadius 0=1 by decide +kernel,Rat.mul_one] using Rat.le_trans h1 h2
  | succ n ih =>
    have hm := midpoint_unit ha hb
    have hh := midpoint_between hab
    have hl := ih ha hm hh.1
    have hr := ih hm hb hh.2
    have ht := qabs_add_le
      (average f tag a ((a+b)/2) n-left f a ((a+b)/2) n)
      (average f tag ((a+b)/2) b n-left f ((a+b)/2) b n)
    have he : average f tag a b (n+1)-left f a b (n+1) =
      ((average f tag a ((a+b)/2) n-left f a ((a+b)/2) n)+
       (average f tag ((a+b)/2) b n-left f ((a+b)/2) b n))/2 := by
      simp only [average,left,Rat.div_def]; grind only
    have hmsh : meshRadius (n+1)=meshRadius n/2 := by
      simp only [meshRadius,Rat.pow_succ,Rat.div_def,Rat.one_mul,Rat.inv_mul_rev]
      exact Rat.mul_comm _ _
    rw [he,hmsh]
    simp only [Rat.div_def,qabs_mul,show qabs ((2:Rat)⁻¹)=(2:Rat)⁻¹ by decide +kernel]
    simp only [Rat.div_def] at hl hr
    grind only

/-- Every midpoint rule is exact on affine functions. This is a reusable
finite quadrature fact, not a special evaluated integral. -/
theorem midpoint_affine (s c a b : Rat) (n : Nat) :
    average (fun x => s*x+c) midpointTag a b n = s*((a+b)/2)+c := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [average,ih,Rat.div_def]; grind only

end ComputableAnalysis.TaggedQuadrature
