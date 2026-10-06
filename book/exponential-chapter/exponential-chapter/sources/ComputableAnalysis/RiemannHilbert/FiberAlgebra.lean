import ComputableAnalysis.RiemannHilbert.RepresentedFiber
import ComputableAnalysis.ComplexRawQuotientAlgebra

/-! Exact finite-vector algebra over valid complex-box representations. -/
namespace ComputableAnalysis.RiemannHilbert.Fiber

variable {n : Nat}

theorem add_assoc (x y z : Fiber n) : add (add x y) z ≈ add x (add y z) :=
  fun i => ComplexRaw.add_assoc_equiv _ _ _ (x.property i) (y.property i) (z.property i)

theorem add_comm (x y : Fiber n) : add x y ≈ add y x :=
  fun i => ComplexRaw.add_comm_equiv _ _ (x.property i) (y.property i)

theorem zero_add (x : Fiber n) : add (zero n) x ≈ x :=
  fun i => ComplexRaw.zero_add_equiv _ (x.property i)

theorem add_zero (x : Fiber n) : add x (zero n) ≈ x :=
  fun i => ComplexRaw.add_zero_equiv _ (x.property i)

/-- The middle two summands can be interchanged as represented values. -/
theorem add_four (a b c d : Fiber n) :
    add (add a b) (add c d) ≈ add (add a c) (add b d) :=
  Setoid.trans (Setoid.symm (add_assoc (add a b) c d))
    (Setoid.trans (add_congr (add_assoc a b c) (Setoid.refl d))
      (Setoid.trans (add_congr (add_congr (Setoid.refl a) (add_comm b c)) (Setoid.refl d))
        (Setoid.trans (add_congr (Setoid.symm (add_assoc a c b)) (Setoid.refl d))
          (add_assoc (add a c) b d))))

theorem scale_add (a : Scalar) (x y : Fiber n) :
    scale a (add x y) ≈ add (scale a x) (scale a y) :=
  fun i => ComplexRaw.mul_add_equiv _ _ _ a.property (x.property i) (y.property i)

theorem scale_zero (a : Scalar) : scale a (zero n) ≈ zero n :=
  fun _ => ComplexRaw.mul_zero_equiv a.val a.property

end ComputableAnalysis.RiemannHilbert.Fiber
