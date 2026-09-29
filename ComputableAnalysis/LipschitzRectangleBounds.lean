import ComputableAnalysis.IntegralRectangleSpecification

/-! Explicit rectangles for a supplied rational function with a proved
Lipschitz bound. This supplies tightness; no integral value is assumed. -/
namespace ComputableAnalysis.Integral

def lipschitzBounds (f : Rat → Rat) (a b L : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → qabs (f y-f x) ≤ L*(y-x))
    (N : Nat) (hN : 0 < N) : Bounds (FunctionOnInterval.exactRat f a b) where
  partition := RationalPartition.uniform a b N hN hab
  lower k := f (leftPoint a b N k)-L*mesh a b N
  upper k := f (leftPoint a b N k)+L*mesh a b N
  lower_le := by
    intro k hk x hx j
    let P := RationalPartition.uniform a b N hN hab
    have hc0 := (P.cell k hk).lower_mem
    have hc1 := (P.cell k hk).upper_mem
    have he := hf (leftPoint a b N k) x hc0 hx.1 (Rat.le_trans hx.2 hc1)
    have hfcell := hf (leftPoint a b N k) (leftPoint a b N (k+1)) hc0
      (P.cell k hk).ordered hc1
    have hm : L*(x-leftPoint a b N k) ≤ L*mesh a b N := by
      by_cases hL : 0 ≤ L
      · apply Rat.mul_le_mul_of_nonneg_left ?_ hL
        have hstep := leftPoint_step a b N k
        have hu : x ≤ leftPoint a b N (k+1) := hx.2
        grind only
      · have hwidth := (P.cell k hk).ordered
        have hstep := leftPoint_step a b N k
        have hnon := qabs_nonneg (f (leftPoint a b N (k+1))-f (leftPoint a b N k))
        have hg := Rat.mul_nonneg (show 0 ≤ -L by grind) (show 0 ≤ x-leftPoint a b N k by have hh : leftPoint a b N k ≤ x := hx.1; grind)
        have hgap : 0 ≤ mesh a b N := mesh_nonneg_of_le hN hab
        rw [hstep] at hfcell
        grind only
    have hl := neg_qabs_le_self (f x-f (leftPoint a b N k))
    change _ ≤ f x
    grind only
  upper_ge := by
    intro k hk x hx j
    let P := RationalPartition.uniform a b N hN hab
    have hc0 := (P.cell k hk).lower_mem
    have hc1 := (P.cell k hk).upper_mem
    have he := hf (leftPoint a b N k) x hc0 hx.1 (Rat.le_trans hx.2 hc1)
    have hfcell := hf (leftPoint a b N k) (leftPoint a b N (k+1)) hc0
      (P.cell k hk).ordered hc1
    have hm : L*(x-leftPoint a b N k) ≤ L*mesh a b N := by
      by_cases hL : 0 ≤ L
      · apply Rat.mul_le_mul_of_nonneg_left ?_ hL
        have hstep := leftPoint_step a b N k
        have hu : x ≤ leftPoint a b N (k+1) := hx.2
        grind only
      · have hstep := leftPoint_step a b N k
        have hnon := qabs_nonneg (f (leftPoint a b N (k+1))-f (leftPoint a b N k))
        have hg := Rat.mul_nonneg (show 0 ≤ -L by grind) (show 0 ≤ x-leftPoint a b N k by have hh : leftPoint a b N k ≤ x := hx.1; grind)
        have hgap : 0 ≤ mesh a b N := mesh_nonneg_of_le hN hab
        rw [hstep] at hfcell
        grind only
    have hl := self_le_qabs (f x-f (leftPoint a b N k))
    change f x ≤ _
    grind only

theorem lipschitzBounds_gap (f : Rat → Rat) (a b L : Rat) (hab : a ≤ b)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → qabs (f y-f x) ≤ L*(y-x))
    (N : Nat) (hN : 0 < N) :
    (lipschitzBounds f a b L hab hf N hN).upperSum-
      (lipschitzBounds f a b L hab hf N hN).lowerSum = 2*L*(b-a)*mesh a b N := by
  have h (n : Nat) :
      rectangleSum (fun k => mesh a b N*(f (leftPoint a b N k)+L*mesh a b N)) n-
      rectangleSum (fun k => mesh a b N*(f (leftPoint a b N k)-L*mesh a b N)) n =
      (n : Rat)*2*L*mesh a b N*mesh a b N := by
    induction n with
    | zero => simp only [rectangleSum]; grind
    | succ n ih => simp only [rectangleSum,Rat.natCast_add]; grind only
  unfold Bounds.upperSum Bounds.lowerSum lipschitzBounds
  simp only [RationalPartition.uniform,leftPoint_step]
  rw [h]
  have hNmesh := natCast_mul_mesh_eq_sub (a := a) (b := b) hN
  grind only

theorem lipschitz_tight (f : Rat → Rat) (a b L : Rat) (hab : a ≤ b) (hL : 0 ≤ L)
    (hf : ∀ x y, a ≤ x → x ≤ y → y ≤ b → qabs (f y-f x) ≤ L*(y-x)) :
    HasTightBounds (FunctionOnInterval.exactRat f a b) := by
  intro eps
  let C := 2*L*(b-a)*(b-a)
  have hC : 0 ≤ C := Rat.mul_nonneg (Rat.mul_nonneg (by grind) (by grind)) (by grind)
  have ht : 0 < eps.val/(C+1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by grind))
  obtain ⟨N,hN⟩ := shrinksToZero_of_natOverSuccBound (C := 1)
    (width := fun n => 1/((n+1 : Nat) : Rat)) (fun _ => Rat.le_refl) ⟨_,ht⟩
  refine ⟨lipschitzBounds f a b L hab hf (N+1) (by omega), ?_⟩
  rw [lipschitzBounds_gap]
  have h := hN N (Nat.le_refl _)
  have hm := Rat.mul_le_mul_of_nonneg_right h (show 0 ≤ C+1 by grind)
  have hc := Rat.mul_inv_cancel (C+1) (by grind)
  have hi : 0 ≤ (((N+1 : Nat) : Rat)⁻¹) := Rat.le_of_lt (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega)))
  simp only [Rat.div_def,Rat.one_mul] at hm
  have he : eps.val*(C+1)⁻¹*(C+1)=eps.val := by grind only
  rw [he] at hm
  unfold mesh
  rw [if_neg (show N+1 ≠ 0 by omega)]
  have he' : 2*L*(b-a)*((b-a)/((N+1 : Nat) : Rat))=C*(((N+1 : Nat) : Rat)⁻¹) := by
    dsimp [C]
    rw [Rat.div_def]
    grind only
  rw [he']
  grind only

end ComputableAnalysis.Integral
