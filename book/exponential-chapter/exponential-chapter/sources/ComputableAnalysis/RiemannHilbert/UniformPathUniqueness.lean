import ComputableAnalysis.RiemannHilbert.LocalCoefficientFunction

/-! Uniqueness from explicit uniform first-order errors on a rationally
parameterized represented path. The endpoint values need not be rational.
No integration, completed norm, compactness, or uniqueness field is used. -/
namespace ComputableAnalysis.RiemannHilbert.UniformPath
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

abbrev unitInterval (t : Rat) : Prop := 0 ≤ t ∧ t ≤ 1

def meshStage (delta : QPos) : Nat :=
  PrecisionSearch.firstFrom (fun N => decide ((RepresentedCauchySum.error N).val ≤ delta.val))
    (by
      obtain ⟨N,hN⟩ := RepresentedCauchySum.error_shrinks delta
      exact ⟨N, fun k hk => by simp only [decide_eq_true_eq]; exact hN k hk⟩) 0

theorem meshStage_spec (delta : QPos) :
    (RepresentedCauchySum.error (meshStage delta)).val ≤ delta.val := by
  have h := (PrecisionSearch.firstFrom_spec
    (fun N => decide ((RepresentedCauchySum.error N).val ≤ delta.val))
    (by
      obtain ⟨N,hN⟩ := RepresentedCauchySum.error_shrinks delta
      exact ⟨N, fun k hk => by simp only [decide_eq_true_eq]; exact hN k hk⟩) 0).2
  simpa only [meshStage, decide_eq_true_eq] using h

theorem finite_increment_bound (y : Nat → Fiber n) (C E : Rat) (N : Nat)
    (h0 : CoordinateBound (y 0) C)
    (hstep : ∀ i, i<N → CoordinateBound (Fiber.sub (y (i+1)) (y i)) E) :
    CoordinateBound (y N) (C+(N : Rat)*E) := by
  induction N with
  | zero =>
    change CoordinateBound (y 0) (C+0*E)
    simpa only [Rat.zero_mul, Rat.add_zero] using h0
  | succ N ih =>
    have hs := bound_add (ih (fun i hi => hstep i (by omega))) (hstep N (by omega))
    have he : (C+(N : Rat)*E)+E=C+((N+1 : Nat) : Rat)*E := by
      rw [Rat.natCast_add]; grind
    rw [he] at hs
    intro d
    exact Small.congr
      ((Fiber.add (y N) (Fiber.sub (y (N+1)) (y N))).property d) ((y (N+1)).property d)
      (SeriesLimitLaws.add_difference _ _ ((y (N+1)).property d) ((y N).property d)) (hs d)

/-- A finite mesh converts first-order defects into a bound on the path,
with the previous bound used only in the justified operator estimate. -/
theorem bound_with_error (y : Rat → Fiber n) (A : Rat → ValueMap (Fiber n) (Fiber n))
    (L B : Rat) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hy0 : y 0 ≈ Fiber.zero n) (hyB : ∀ t, unitInterval t → CoordinateBound (y t) B)
    (hA : ∀ t, unitInterval t → ∀ C, 0 ≤ C → ∀ x, CoordinateBound x C →
      CoordinateBound ((A t).eval x) (L*C))
    (delta : QPos → QPos)
    (hdefect : ∀ (eps : QPos) s t, unitInterval s → unitInterval t →
      0 ≤ t-s → t-s ≤ (delta eps).val →
      CoordinateBound
        (Fiber.sub (Fiber.sub (y t) (y s)) (ratScale (t-s) ((A s).eval (y s))))
        (eps.val*(t-s)))
    (eps : QPos) (t : Rat) (ht : unitInterval t) :
    CoordinateBound (y t) (L*B+eps.val) := by
  let N := meshStage (delta eps)+1
  have hN : 0 < N := by dsimp [N]; omega
  let H : Rat := t/(N : Rat)
  have hn : 0 < (N : Rat) := (Rat.natCast_pos).2 hN
  have hne : (N : Rat) ≠ 0 := Rat.ne_of_gt hn
  have hH : 0 ≤ H := Rat.mul_nonneg ht.1 (Rat.le_of_lt ((Rat.inv_pos).2 hn))
  have hHt : (N : Rat)*H=t := by
    dsimp [H]; rw [Rat.mul_comm]; exact Rat.div_mul_cancel hne
  have hHdelta : H ≤ (delta eps).val := by
    have he := meshStage_spec (delta eps)
    have hunit := Rat.mul_le_mul_of_nonneg_right ht.2 (Rat.le_of_lt ((Rat.inv_pos).2 hn))
    change t*(N : Rat)⁻¹ ≤ 1*(N : Rat)⁻¹ at hunit
    have he' : 1/(N : Rat) ≤ (delta eps).val := he
    exact Rat.le_trans hunit he'
  have hpoint : ∀ i, i ≤ N → unitInterval ((i : Rat)*H) := by
    intro i hi
    have hic : (i : Rat) ≤ (N : Rat) := by exact_mod_cast hi
    exact ⟨Rat.mul_nonneg Rat.natCast_nonneg hH,
      Rat.le_trans (Rat.mul_le_mul_of_nonneg_right hic hH) (hHt ▸ ht.2)⟩
  have hs := finite_increment_bound (fun i => y ((i : Rat)*H)) 0 ((L*B+eps.val)*H) N
    (by
      change CoordinateBound (y (0*H)) 0
      rw [Rat.zero_mul]
      exact bound_congr (Setoid.symm hy0) (bound_zero 0 (by decide))) (by
      intro i hi
      have hiN : i ≤ N := by omega
      have hisN : i+1 ≤ N := by omega
      have hd : ((i+1 : Nat) : Rat)*H-(i : Rat)*H=H := by rw [Rat.natCast_add]; grind
      have hf := hdefect eps ((i : Rat)*H) (((i+1 : Nat) : Rat)*H)
        (hpoint i hiN) (hpoint (i+1) hisN) (by rw [hd]; exact hH) (by rw [hd]; exact hHdelta)
      have ha := bound_ratScale hH (hA _ (hpoint i hiN) B hB _ (hyB _ (hpoint i hiN)))
      rw [hd] at hf
      have hb := bound_add ha hf
      have he : H*(L*B)+eps.val*H=(L*B+eps.val)*H := by grind
      rw [he] at hb
      intro d
      exact Small.congr
        ((Fiber.add (ratScale H ((A ((i : Rat)*H)).eval (y ((i : Rat)*H))))
          (Fiber.sub (Fiber.sub (y (((i+1 : Nat) : Rat)*H)) (y ((i : Rat)*H)))
            (ratScale H ((A ((i : Rat)*H)).eval (y ((i : Rat)*H)))))).property d)
        ((Fiber.sub (y (((i+1 : Nat) : Rat)*H)) (y ((i : Rat)*H))).property d)
        (SeriesLimitLaws.add_difference _ _
          ((Fiber.sub (y (((i+1 : Nat) : Rat)*H)) (y ((i : Rat)*H))).property d)
          ((ratScale H ((A ((i : Rat)*H)).eval (y ((i : Rat)*H)))).property d)) (hb d))
  rw [hHt] at hs
  intro d
  apply (hs d).mono
  rw [Rat.zero_add]
  have he : (N : Rat)*((L*B+eps.val)*H)=t*(L*B+eps.val) := by
    calc
      _ = ((N : Rat)*H)*(L*B+eps.val) := by grind
      _ = _ := by rw [hHt]
  rw [he]
  have hc : 0 ≤ L*B+eps.val := Rat.add_nonneg (Rat.mul_nonneg hL hB) (Rat.le_of_lt eps.property)
  have hh := Rat.mul_le_mul_of_nonneg_right ht.2 hc
  simpa only [Rat.one_mul] using hh

/-- A proved contraction of any supplied uniform path bound. -/
theorem improve_bound (y : Rat → Fiber n) (A : Rat → ValueMap (Fiber n) (Fiber n))
    (L B : Rat) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hy0 : y 0 ≈ Fiber.zero n) (hyB : ∀ t, unitInterval t → CoordinateBound (y t) B)
    (hA : ∀ t, unitInterval t → ∀ C, 0 ≤ C → ∀ x, CoordinateBound x C →
      CoordinateBound ((A t).eval x) (L*C))
    (delta : QPos → QPos)
    (hdefect : ∀ (eps : QPos) s t, unitInterval s → unitInterval t →
      0 ≤ t-s → t-s ≤ (delta eps).val →
      CoordinateBound
        (Fiber.sub (Fiber.sub (y t) (y s)) (ratScale (t-s) ((A s).eval (y s))))
        (eps.val*(t-s)))
    (t : Rat) (ht : unitInterval t) :
    CoordinateBound (y t) (L*B) := by
  intro d
  apply SeriesLimitLaws.small_closed _ (L*B) (fun k => (RepresentedCauchySum.error k).val)
    RepresentedCauchySum.error_shrinks
  intro k
  exact bound_with_error y A L B hL hB hy0 hyB hA delta hdefect (RepresentedCauchySum.error k) t ht d

/-- Exact uniqueness on the whole path from first-order defects, an initial
zero, one justified value bound, and a sufficiently small operator bound. -/
theorem zero (y : Rat → Fiber n) (A : Rat → ValueMap (Fiber n) (Fiber n))
    (L B : Rat) (hL : 0 ≤ L) (hLsmall : L ≤ (1 : Rat)/2) (hB : 0 ≤ B)
    (hy0 : y 0 ≈ Fiber.zero n) (hyB : ∀ t, unitInterval t → CoordinateBound (y t) B)
    (hA : ∀ t, unitInterval t → ∀ C, 0 ≤ C → ∀ x, CoordinateBound x C →
      CoordinateBound ((A t).eval x) (L*C))
    (delta : QPos → QPos)
    (hdefect : ∀ (eps : QPos) s t, unitInterval s → unitInterval t →
      0 ≤ t-s → t-s ≤ (delta eps).val →
      CoordinateBound
        (Fiber.sub (Fiber.sub (y t) (y s)) (ratScale (t-s) ((A s).eval (y s))))
        (eps.val*(t-s)))
    (t : Rat) (ht : unitInterval t) : y t ≈ Fiber.zero n := by
  have hb : ∀ (k : Nat) (t : Rat), unitInterval t → CoordinateBound (y t) (B*L^k) := by
    intro k
    induction k with
    | zero => simpa only [Rat.pow_zero, Rat.mul_one] using hyB
    | succ k ih =>
      intro t ht
      have hs := improve_bound y A L (B*L^k) hL (Rat.mul_nonneg hB (Rat.pow_nonneg hL))
        hy0 ih hA delta hdefect t ht
      have he : L*(B*L^k)=B*L^(k+1) := by rw [Rat.pow_succ]; grind
      rw [he] at hs; exact hs
  intro d
  have hs : Small ((y t).val d) 0 := by
    apply SeriesLimitLaws.small_closed _ 0 (fun k => 4*B*L^k)
      (LocalODE.tail_bound_shrinks B L hB hL hLsmall)
    intro k
    apply (hb k t ht d).mono
    rw [Rat.zero_add]
    have hp : 0 ≤ B*L^k := Rat.mul_nonneg hB (Rat.pow_nonneg hL)
    grind
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ ComplexRaw.zero
    (by simpa only [Rat.add_zero] using SeriesLimitLaws.small_sub hs (Small.zero (by decide : (0 : Rat) ≤ 0)))

end ComputableAnalysis.RiemannHilbert.UniformPath
