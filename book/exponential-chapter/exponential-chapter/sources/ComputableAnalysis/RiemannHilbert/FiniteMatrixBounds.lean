import ComputableAnalysis.RiemannHilbert.FiniteFiberBasis

/-! A justified bound on finitely many basis images gives a bound on
every represented input vector, without computing an operator norm. -/
namespace ComputableAnalysis.RiemannHilbert.ValueMap
open ComplexRaw FunctionTheory LocalSystem
variable {n m : Nat}

theorem imageBasisPrefix_bound_of_basis (f : ValueMap (Fiber n) (Fiber m))
    (B : Rat) (hB : 0 ≤ B) (hb : ∀ i : Fin n, CoordinateBound (f.eval (Fiber.basis i)) B)
    (x : Fiber n) (E : Rat) (hE : 0 ≤ E) (hx : CoordinateBound x E)
    (k : Nat) (hk : k ≤ n) :
    CoordinateBound (imageBasisPrefix f x k) ((k : Rat)*(2*E*B)) := by
  induction k with
  | zero =>
    change CoordinateBound (Fiber.zero m) (0*(2*E*B))
    simpa only [Rat.zero_mul] using (bound_zero (n := m) 0 Rat.le_refl)
  | succ k ih =>
    have hkn : k < n := by omega
    rw [imageBasisPrefix,dif_pos hkn]
    have hs := bound_add (ih (by omega))
      (bound_scale (c := Fiber.coordinate x ⟨k,hkn⟩) (x := f.eval (Fiber.basis ⟨k,hkn⟩))
        hE hB (hx ⟨k,hkn⟩) (hb ⟨k,hkn⟩))
    have he : (k : Rat)*(2*E*B)+2*E*B=((k+1 : Nat) : Rat)*(2*E*B) := by
      rw [Rat.natCast_add]
      grind only
    rw [he] at hs
    exact hs

theorem linear_bound_of_basis (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f)
    (B : Rat) (hB : 0 ≤ B) (hb : ∀ i : Fin n, CoordinateBound (f.eval (Fiber.basis i)) B)
    (x : Fiber n) (E : Rat) (hE : 0 ≤ E) (hx : CoordinateBound x E) :
    CoordinateBound (f.eval x) ((2*(n : Rat)*B)*E) := by
  have hs := bound_congr (Setoid.symm (matrix_action f hf x))
    (imageBasisPrefix_bound_of_basis f B hB hb x E hE hx n (Nat.le_refl n))
  have he : (n : Rat)*(2*E*B)=(2*(n : Rat)*B)*E := by grind only
  rw [he] at hs
  exact hs

end ComputableAnalysis.RiemannHilbert.ValueMap
