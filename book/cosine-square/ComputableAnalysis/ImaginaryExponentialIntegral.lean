import ComputableAnalysis.FiniteSampleCalculus

/-! Integration of a supplied imaginary exponential from its differential law.
No integral identity is a hypothesis. The frequency and its inverse can be
inexact represented-constant samples, with a proved uniform inverse bound. -/
namespace ComputableAnalysis.ImaginaryExponentialIntegral
open ClosedArctanInverse FiniteSampleCalculus RationalSampleLimits MonotoneAverage

variable {R I : SampleFunction} {w inv : Nat → Rat}

/-- The real coordinate of E/(i*w). -/
def realEndpointModel (hI : Model I (fun t q=>w q*R t q))
    (K : Rat) (hK : 0≤K) (hb : Bounded inv K) (hi : ∀ q, inv q*w q=1) :
    Model (fun t q=>inv q*I t q) R := by
  apply ((Model.constant inv K hK hb).mul hI).congr
  · intros; rfl
  · intro t q
    change 0*I t q+inv q*(w q*R t q)=R t q
    rw [Rat.zero_mul,Rat.zero_add,←Rat.mul_assoc,hi,Rat.one_mul]

/-- The imaginary coordinate of E/(i*w). -/
def imagEndpointModel (hR : Model R (fun t q=> -w q*I t q))
    (K : Rat) (hK : 0≤K) (hb : Bounded inv K) (hi : ∀ q, inv q*w q=1) :
    Model (fun t q=> -(inv q*R t q)) I := by
  apply ((Model.const (-1)).mul ((Model.constant inv K hK hb).mul hR)).congr
  · intro t q; grind only
  · intro t q
    change 0*(inv q*R t q)+(-1)*(0*R t q+inv q*(-w q*I t q))=I t q
    have h:=hi q
    grind only

/-- The definite-integral law for the real part of an imaginary exponential.
The final premise compares a chosen quadrature with finite mesh sums. -/
theorem integrate_real (hI : Model I (fun t q=>w q*R t q))
    (K : Rat) (hK : 0≤K) (hb : Bounded inv K) (hi : ∀ q, inv q*w q=1)
    (sums : Nat → Rat) (B : Rat) (hB : 0≤B)
    (hm : ∀ d q, d≤q → qabs (sums q-left (fun t=>R t q) 0 1 d)≤B*meshRadius d) :
    Close sums (fun q=>inv q*I 1 q-inv q*I 0 q) :=
  chosen_samples_FTC (realEndpointModel hI K hK hb hi) sums B hB hm

theorem integrate_imag (hR : Model R (fun t q=> -w q*I t q))
    (K : Rat) (hK : 0≤K) (hb : Bounded inv K) (hi : ∀ q, inv q*w q=1)
    (sums : Nat → Rat) (B : Rat) (hB : 0≤B)
    (hm : ∀ d q, d≤q → qabs (sums q-left (fun t=>I t q) 0 1 d)≤B*meshRadius d) :
    Close sums (fun q=> -(inv q*R 1 q)- -(inv q*R 0 q)) :=
  chosen_samples_FTC (imagEndpointModel hR K hK hb hi) sums B hB hm

/-- Exact represented-value version of exponential integration for a supplied,
justified quadrature. Membership links the raw objects to the finite samples;
no desired endpoint equality is assumed. -/
theorem real_integral_equiv (hI : Model I (fun t q=>w q*R t q))
    (K : Rat) (hK : 0≤K) (hb : Bounded inv K) (hi : ∀ q, inv q*w q=1)
    (sums : Nat → Rat) (B : Rat) (hB : 0≤B)
    (hm : ∀ d q, d≤q → qabs (sums q-left (fun t=>R t q) 0 1 d)≤B*meshRadius d)
    (integral endpoint : RealRaw) (hv : integral.Valid) (he : endpoint.Valid)
    (hs : ∀ q, IntervalSelections.InBox (sums q) (integral.compute q))
    (hf : ∀ q, IntervalSelections.InBox (inv q*I 1 q-inv q*I 0 q) (endpoint.compute q)) :
    integral.Equiv endpoint :=
  equiv_of_close hv he sums _ hs hf (integrate_real hI K hK hb hi sums B hB hm)

private theorem left_zero (a b : Rat) (n : Nat) : left (fun _=>0) a b n=0 := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp only [left,ih,Rat.zero_add,Rat.div_def,Rat.zero_mul]

/-- Zero derivative implies constant value, proved by finite telescoping. -/
theorem zero_derivative_close {F : SampleFunction} (M : Model F (fun _ _=>0))
    {t : Rat} (ht : Unit t) : Close (F t) (F 0) := by
  by_cases he : t=0
  · subst t; exact close_refl _
  have hp : 0<t := by have h:=ht.1;grind only
  have hC : 0≤M.errorBound*t*t :=
    Rat.mul_nonneg (Rat.mul_nonneg M.errorBound_nonneg ht.1) ht.1
  have hs : Small (fun d=>M.errorBound*t*t*meshRadius d) :=
    small_of_geometric_bound _ hC (fun d=>by
      rw [qabs_eq_self_of_nonneg (Rat.mul_nonneg hC (Rat.le_of_lt (meshRadius_pos d)))];exact Rat.le_refl)
  intro eps
  obtain ⟨d,hd⟩:=hs eps
  obtain ⟨N,hN⟩:=finite_telescope M d ⟨by decide +kernel,by decide +kernel⟩ ht hp
  refine ⟨N,fun q hq=>?_⟩
  have h:=hN q hq
  rw [left_zero,Rat.mul_zero,show ∀ a:Rat, a-0=a by intros;grind] at h
  simp only [show ∀ a:Rat, a-0=a by intros;grind] at h
  exact Rat.le_trans h (Rat.le_trans (self_le_qabs _) (hd d (Nat.le_refl d)))

private theorem square_le_norm (a b : Rat) : a*a≤a*a+b*b := by
  have hb : 0≤b*b := by
    by_cases h : 0≤b
    · exact Rat.mul_nonneg h h
    · have hn : 0≤ -b := by grind
      have hh:=Rat.mul_nonneg hn hn
      grind only
  grind only

private theorem small_of_norm {a b : Nat → Rat} (h : Small (fun q=>a q*a q+b q*b q)) : Small a := by
  intro eps
  let eta : QPos := ⟨eps.val*eps.val, Rat.mul_pos eps.property eps.property⟩
  obtain ⟨N,hN⟩:=h eta
  refine ⟨N,fun q hq=>?_⟩
  have hn:=Rat.le_trans (square_le_norm (a q) (b q))
    (Rat.le_trans (self_le_qabs _) (hN q hq))
  have he : qabs (a q)*qabs (a q)=a q*a q := by
    unfold qabs; split <;> grind only
  change a q*a q≤eps.val*eps.val at hn
  by_cases hl : qabs (a q)≤eps.val
  · exact hl
  · have hh : eps.val<qabs (a q) := by grind
    have h1:=Rat.mul_lt_mul_of_pos_left hh eps.property
    have h2:=Rat.mul_lt_mul_of_pos_right hh (by grind : 0<qabs (a q))
    rw [he] at h2
    grind only

/-- Uniqueness for the imaginary-exponential differential equation. The energy
of the difference has zero derivative; no exponential or integral equality is
assumed. This makes the geometric Euler construction a characterized solution. -/
theorem solution_unique {R I U V : SampleFunction} (w : Nat → Rat)
    (r : Model R (fun t q=> -w q*I t q)) (i : Model I (fun t q=>w q*R t q))
    (u : Model U (fun t q=> -w q*V t q)) (v : Model V (fun t q=>w q*U t q))
    (hr : Close (R 0) (U 0)) (hi : Close (I 0) (V 0))
    {t : Rat} (ht : Unit t) : Close (R t) (U t) ∧ Close (I t) (V t) := by
  let A := fun t q=>R t q-U t q
  let B := fun t q=>I t q-V t q
  let a : Model A (fun t q=> -w q*B t q) :=
    (r.add ((Model.const (-1)).mul u)).congr (by intros;dsimp [A];grind only)
      (by intros;dsimp [B];grind only)
  let b : Model B (fun t q=>w q*A t q) :=
    (i.add ((Model.const (-1)).mul v)).congr (by intros;dsimp [B];grind only)
      (by intros;dsimp [A];grind only)
  let energy : Model (fun t q=>A t q*A t q+B t q*B t q) (fun _ _=>0) :=
    ((a.mul a).add (b.mul b)).congr (by intros;rfl) (by intros;grind only)
  have h0 : Small (fun q=>A 0 q*A 0 q+B 0 q*B 0 q) :=
    small_add (small_mul_bounded hr a.valueBound_nonneg (fun q=>a.value 0 q ⟨by decide,by decide⟩))
      (small_mul_bounded hi b.valueBound_nonneg (fun q=>b.value 0 q ⟨by decide,by decide⟩))
  have hnorm := small_of_close_zero (close_trans (zero_derivative_close energy ht) (close_zero_of_small h0))
  exact ⟨small_of_norm hnorm,small_of_norm (by simpa only [Rat.add_comm] using hnorm)⟩

end ComputableAnalysis.ImaginaryExponentialIntegral
