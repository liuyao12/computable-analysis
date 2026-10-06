import ComputableAnalysis.RiemannHilbert.OperatorBounds

/-! Linearity derived from justified finite linear approximations and their errors. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory LocalSystem

namespace Fiber
theorem sub_zero_bound {x y : Fiber n} (hxy : x ≈ y) : CoordinateBound (sub x y) 0 := by
  intro i
  have he := FunctionTheory.sub_congr (equiv_refl _ (x.property i)) (equiv_symm (hxy i))
  have hz := equiv_trans ((sub x y).property i) (sub_valid (x.property i) (x.property i)) (ofQComplex_valid _)
    he (add_neg_equiv _ (x.property i))
  exact Small.congr (ofQComplex_valid _) ((sub x y).property i) (equiv_symm hz) (Small.zero (by decide))

theorem scale_sub (c : Scalar) (x y : Fiber n) : scale c (sub x y) ≈ sub (scale c x) (scale c y) := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (scale c (sub x y)).property i) (hright := (sub (scale c x) (scale c y)).property i)
  change ComplexRawQuotient.ofRaw c.val c.property*
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i)-ComplexRawQuotient.ofRaw (y.val i) (y.property i)) =
    ComplexRawQuotient.ofRaw c.val c.property*ComplexRawQuotient.ofRaw (x.val i) (x.property i)-
      ComplexRawQuotient.ofRaw c.val c.property*ComplexRawQuotient.ofRaw (y.val i) (y.property i)
  grind

end Fiber

/-- Pointwise represented errors and finite linearity suffice for exact
linearity of the supplied map. No limit or linearity conclusion is assumed. -/
theorem linear_of_prefixes {n m : Nat} (f : ValueMap (Fiber n) (Fiber m))
    (p : Nat → ValueMap (Fiber n) (Fiber m)) (hp : ∀ N, IsLinear (p N))
    (e : Fiber n → Nat → Rat) (he : ∀ x, ShrinksToZero (e x))
    (he0 : ∀ x N, 0 ≤ e x N)
    (hclose : ∀ x N, CoordinateBound (Fiber.sub (f.eval x) ((p N).eval x)) (e x N)) : IsLinear f := by
  constructor
  · intro x y i
    let E := fun N => e (Fiber.add x y) N+(e x N+e y N)
    have hE := RepresentedCauchySum.sum_shrinks _ _ (he (Fiber.add x y))
      (RepresentedCauchySum.sum_shrinks _ _ (he x) (he y))
    apply SeriesLimitLaws.equiv_of_small_sub_zero
    apply SeriesLimitLaws.small_of_prefix_bound _ ((Fiber.sub (f.eval (Fiber.add x y)) (Fiber.add (f.eval x) (f.eval y))).property i)
      (fun N => (Fiber.sub ((p N).eval (Fiber.add x y)) (Fiber.add ((p N).eval x) ((p N).eval y))).val i)
      (fun N => (Fiber.sub ((p N).eval (Fiber.add x y)) (Fiber.add ((p N).eval x) ((p N).eval y))).property i)
      0 E hE
    · intro N
      have hs := LocalODE.small_add (hclose x N i) (hclose y N i)
      have hg := Small.congr
        ((Fiber.add (Fiber.sub (f.eval x) ((p N).eval x)) (Fiber.sub (f.eval y) ((p N).eval y))).property i)
        ((Fiber.sub (Fiber.add (f.eval x) (f.eval y)) (Fiber.add ((p N).eval x) ((p N).eval y))).property i)
        (equiv_symm (SeriesLimitLaws.addition_difference _ _ _ _ (f.eval x |>.property i) ((p N).eval x |>.property i)
          (f.eval y |>.property i) ((p N).eval y |>.property i))) hs
      exact SeriesLimitLaws.difference_close _ _ _ _
        (f.eval (Fiber.add x y) |>.property i) ((Fiber.add (f.eval x) (f.eval y)).property i)
        ((p N).eval (Fiber.add x y) |>.property i) ((Fiber.add ((p N).eval x) ((p N).eval y)).property i)
        _ _ (hclose (Fiber.add x y) N i) hg
    · intro N
      exact Fiber.sub_zero_bound ((hp N).1 x y) i
  · intro c x i
    let B := LocalODE.initialBound c.val
    have hB := LocalODE.initialBound_nonneg c.val
    let E := fun N => e (Fiber.scale c x) N+(2*B)*e x N
    have hE := RepresentedCauchySum.sum_shrinks _ _ (he (Fiber.scale c x))
      (SeriesLimitLaws.shrinks_scale _ (he x) (2*B) (Rat.mul_nonneg (by decide) hB))
    apply SeriesLimitLaws.equiv_of_small_sub_zero
    apply SeriesLimitLaws.small_of_prefix_bound _ ((Fiber.sub (f.eval (Fiber.scale c x)) (Fiber.scale c (f.eval x))).property i)
      (fun N => (Fiber.sub ((p N).eval (Fiber.scale c x)) (Fiber.scale c ((p N).eval x))).val i)
      (fun N => (Fiber.sub ((p N).eval (Fiber.scale c x)) (Fiber.scale c ((p N).eval x))).property i)
      0 E hE
    · intro N
      have hs := bound_scale (x := Fiber.sub (f.eval x) ((p N).eval x)) (c := c)
        (B := B) (C := e x N) hB (he0 x N) (LocalODE.initialBound_valid c.val c.property) (hclose x N)
      have hg := bound_congr (Fiber.scale_sub c (f.eval x) ((p N).eval x)) hs
      exact SeriesLimitLaws.difference_close _ _ _ _
        (f.eval (Fiber.scale c x) |>.property i) ((Fiber.scale c (f.eval x)).property i)
        ((p N).eval (Fiber.scale c x) |>.property i) ((Fiber.scale c ((p N).eval x)).property i)
        _ _ (hclose (Fiber.scale c x) N i) (hg i)
    · intro N
      exact Fiber.sub_zero_bound ((hp N).2 c x) i

end ComputableAnalysis.RiemannHilbert
