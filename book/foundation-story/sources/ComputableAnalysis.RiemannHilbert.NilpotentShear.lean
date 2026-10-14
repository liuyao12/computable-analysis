import ComputableAnalysis.RiemannHilbert.ConnectionFrameChange

/-! Constructed nonconstant invertible frames I+sN for a supplied linear
operator with proved N²=0. Both inverse laws and quantitative bounds are
derived over arbitrary valid represented complex parameters. -/
namespace ComputableAnalysis.RiemannHilbert.NilpotentShear
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def forward (N : ValueMap (Fiber n) (Fiber n)) (s : Scalar) : ValueMap (Fiber n) (Fiber n) :=
  ValueMap.sum ValueMap.identity (N.followedBy (Fiber.scaleMap s))

def backward (N : ValueMap (Fiber n) (Fiber n)) (s : Scalar) : ValueMap (Fiber n) (Fiber n) :=
  ValueMap.difference ValueMap.identity (N.followedBy (Fiber.scaleMap s))

theorem forward_linear (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N) (s : Scalar) :
    IsLinear (forward N s) :=
  ValueMap.sum_linear _ _ (IsLinear.identity n) (IsLinear.followedBy hN (Fiber.scaleMap_linear s))

theorem backward_linear (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N) (s : Scalar) :
    IsLinear (backward N s) :=
  ValueMap.difference_linear _ _ (IsLinear.identity n) (IsLinear.followedBy hN (Fiber.scaleMap_linear s))

theorem scaled_square_zero (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N)
    (hNil : ∀ x, N.eval (N.eval x) ≈ Fiber.zero n) (s : Scalar) (x : Fiber n) :
    N.eval (Fiber.scale s (N.eval x)) ≈ Fiber.zero n :=
  Setoid.trans (hN.2 s (N.eval x))
    (Setoid.trans (Fiber.scale_congr (equiv_refl _ s.property) (hNil x)) (Fiber.scale_zero s))

theorem operator_forward (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N)
    (hNil : ∀ x, N.eval (N.eval x) ≈ Fiber.zero n) (s : Scalar) (x : Fiber n) :
    N.eval ((forward N s).eval x) ≈ N.eval x :=
  Setoid.trans (hN.1 x (Fiber.scale s (N.eval x)))
    (Setoid.trans (Fiber.add_congr (Setoid.refl _) (scaled_square_zero N hN hNil s x)) (Fiber.add_zero _))

theorem operator_backward (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N)
    (hNil : ∀ x, N.eval (N.eval x) ≈ Fiber.zero n) (s : Scalar) (x : Fiber n) :
    N.eval ((backward N s).eval x) ≈ N.eval x :=
  Setoid.trans (hN.sub x (Fiber.scale s (N.eval x)))
    (Setoid.trans (Fiber.sub_congr (Setoid.refl _) (scaled_square_zero N hN hNil s x)) (Fiber.sub_zero _))

private theorem sub_add_cancel (x y : Fiber n) : Fiber.add (Fiber.sub x y) y ≈ x :=
  Setoid.trans (Fiber.add_comm _ _) (fun i => SeriesLimitLaws.add_difference (x.val i) (y.val i) (x.property i) (y.property i))

private theorem add_sub_cancel (x y : Fiber n) : Fiber.sub (Fiber.add x y) y ≈ x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub (Fiber.add x y) y).property i) (hright := x.property i)
  change (ComplexRawQuotient.ofRaw (x.val i) (x.property i)+ComplexRawQuotient.ofRaw (y.val i) (y.property i))-
    ComplexRawQuotient.ofRaw (y.val i) (y.property i)=ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  grind

def frame (N : ValueMap (Fiber n) (Fiber n)) (hN : IsLinear N)
    (hNil : ∀ x, N.eval (N.eval x) ≈ Fiber.zero n) (s : Scalar) : LinearIso n n where
  toValueIso := {
    forward := forward N s
    backward := backward N s
    forward_backward := fun x => Setoid.trans
      (Fiber.add_congr (Setoid.refl _) (Fiber.scale_congr (equiv_refl _ s.property) (operator_backward N hN hNil s x)))
      (sub_add_cancel x (Fiber.scale s (N.eval x)))
    backward_forward := fun x => Setoid.trans
      (Fiber.sub_congr (Setoid.refl _) (Fiber.scale_congr (equiv_refl _ s.property) (operator_forward N hN hNil s x)))
      (add_sub_cancel x (Fiber.scale s (N.eval x))) }
  linear := forward_linear N hN s

theorem forward_congr (N : ValueMap (Fiber n) (Fiber n)) (s t : Scalar) (hst : s.val.Equiv t.val) :
    (forward N s).Equiv (forward N t) :=
  fun x => Fiber.add_congr (Setoid.refl _) (Fiber.scale_congr hst (Setoid.refl (N.eval x)))

theorem forward_bound (N : ValueMap (Fiber n) (Fiber n)) (L R : Rat) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hN : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (N.eval x) (L*B))
    (s : Scalar) (hs : Small s.val R) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((forward N s).eval x) ((1+2*R*L)*B) := by
  have hsN := bound_scale (c := s) (x := N.eval x) (B := R) (C := L*B) hR (Rat.mul_nonneg hL hB) hs (hN B hB x hx)
  have hh := bound_add hx hsN
  have he : B+2*R*(L*B)=(1+2*R*L)*B := by grind
  rw [he] at hh
  exact hh

theorem backward_bound (N : ValueMap (Fiber n) (Fiber n)) (L R : Rat) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hN : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (N.eval x) (L*B))
    (s : Scalar) (hs : Small s.val R) (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((backward N s).eval x) ((1+2*R*L)*B) := by
  have hsN := bound_scale (c := s) (x := N.eval x) (B := R) (C := L*B) hR (Rat.mul_nonneg hL hB) hs (hN B hB x hx)
  have hh := bound_sub hx hsN
  have he : B+2*R*(L*B)=(1+2*R*L)*B := by grind
  rw [he] at hh
  exact hh

end ComputableAnalysis.RiemannHilbert.NilpotentShear
