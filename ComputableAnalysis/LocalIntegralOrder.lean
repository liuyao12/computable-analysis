import ComputableAnalysis.IntegralRectangleSpecification
import ComputableAnalysis.GeometricSequence

/-! Integral order on a supplied segment from a local quadratic finite-error
bound. The law requires no global extension across poles. -/
namespace ComputableAnalysis.Integral

private theorem local_lower_dyadic {F f : Rat → Rat} {a b E : Rat}
    (hE : 0 ≤ E)
    (herr : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      qabs (F v-F u-(v-u)*f u) ≤ (v-u)*(v-u)*E)
    (n : Nat) {u v c : Rat} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hc : ∀ x, u ≤ x → x ≤ v → c ≤ f x) :
    (v-u)*c-(v-u)*(v-u)*E*((1 : Rat)/2)^n ≤ F v-F u := by
  induction n generalizing u v with
  | zero =>
    have he := herr u v hau huv hvb
    have hlo := neg_qabs_le_self (F v-F u-(v-u)*f u)
    have hf := Rat.mul_le_mul_of_nonneg_left (hc u (Rat.le_refl) huv) (show 0 ≤ v-u by grind)
    simp only [Rat.pow_zero,Rat.mul_one]
    grind only
  | succ n ih =>
    have ham : a ≤ (u+v)/2 := by grind
    have hum : u ≤ (u+v)/2 := by grind
    have hmv : (u+v)/2 ≤ v := by grind
    have hmb : (u+v)/2 ≤ b := by grind
    have hl := ih hau hum hmb (fun x hx hy => hc x hx (Rat.le_trans hy hmv))
    have hr := ih ham hmv hvb (fun x hx hy => hc x (Rat.le_trans hum hx) hy)
    rw [Rat.pow_succ]
    grind only

theorem integral_lower_of_local_error {F f : Rat → Rat} {a b E : Rat}
    (hE : 0 ≤ E)
    (herr : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      qabs (F v-F u-(v-u)*f u) ≤ (v-u)*(v-u)*E)
    {u v c : Rat} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hc : ∀ x, u ≤ x → x ≤ v → c ≤ f x) : (v-u)*c ≤ F v-F u := by
  by_cases h : (v-u)*c ≤ F v-F u
  · exact h
  exfalso
  let eps : QPos := ⟨((v-u)*c-(F v-F u))/2,by grind⟩
  have hnon := Rat.mul_nonneg (Rat.mul_nonneg (show 0 ≤ v-u by grind) (show 0 ≤ v-u by grind)) hE
  obtain ⟨N,hN⟩ := GeometricSequence.shrinks hnon eps
  have he := hN N (Nat.le_refl _)
  have hl := local_lower_dyadic hE herr N hau huv hvb hc
  change (v-u)*(v-u)*E*((1 : Rat)/2)^N ≤ ((v-u)*c-(F v-F u))/2 at he
  grind only

/-- A proved law converting local finite secant errors into exact cell order. -/
theorem exactCellOrder_of_local_error {F f : Rat → Rat} {a b E : Rat}
    (hE : 0 ≤ E)
    (herr : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      qabs (F v-F u-(v-u)*f u) ≤ (v-u)*(v-u)*E) :
    ExactCellOrderPreservation f (fun u v => F v-F u) a b := by
  constructor
  · intro u v c hau huv hvb hc
    exact integral_lower_of_local_error hE herr hau huv hvb (fun x hx hy => hc hx hy)
  · intro u v c hau huv hvb hc
    have hn : ∀ x y, a ≤ x → x ≤ y → y ≤ b →
        qabs ((-F y)-(-F x)-(y-x)*(-f x)) ≤ (y-x)*(y-x)*E := by
      intro x y hx hxy hy
      rw [show (-F y)-(-F x)-(y-x)*(-f x)= -(F y-F x-(y-x)*f x) by grind only,qabs_neg]
      exact herr x y hx hxy hy
    have h := integral_lower_of_local_error hE hn (c := -c) hau huv hvb (by
      intro x hx hy
      have := hc hx hy
      grind only)
    grind only

end ComputableAnalysis.Integral
