import ComputableAnalysis.RiemannHilbert.TransitionAtlas
import ComputableAnalysis.RiemannHilbert.VectorFiniteSums

/-! Vector operations on glued fiber names. Operands may use different
charts. Every coordinate formula and every representation-invariance law
is proved from linearity of the transitions and their cocycle. -/
namespace ComputableAnalysis.RiemannHilbert.AtlasFiber
universe u v
variable {X : Type u} {I : Type v} {n : Nat} {a : TransitionAtlas X I n} {p : X}

def add (x y : AtlasFiber a p) : AtlasFiber a p :=
  inChart x.chart x.mem (Fiber.add x.coordinates (coordinatesIn x.chart x.mem y))

def scale (s : Scalar) (x : AtlasFiber a p) : AtlasFiber a p :=
  inChart x.chart x.mem (Fiber.scale s x.coordinates)

def zeroIn (i : I) (hi : a.domain i p) : AtlasFiber a p := inChart i hi (Fiber.zero n)

def neg (x : AtlasFiber a p) : AtlasFiber a p :=
  inChart x.chart x.mem (Fiber.neg x.coordinates)

theorem coordinatesIn_add (i : I) (hi : a.domain i p) (x y : AtlasFiber a p) :
    coordinatesIn i hi (add x y) ≈ Fiber.add (coordinatesIn i hi x) (coordinatesIn i hi y) :=
  Setoid.trans ((a.transition p x.chart i x.mem hi).linear.1 _ _)
    (Fiber.add_congr (Setoid.refl _)
      (a.cocycle p y.chart x.chart i y.mem x.mem hi y.coordinates))

theorem coordinatesIn_scale (i : I) (hi : a.domain i p) (s : Scalar) (x : AtlasFiber a p) :
    coordinatesIn i hi (scale s x) ≈ Fiber.scale s (coordinatesIn i hi x) :=
  (a.transition p x.chart i x.mem hi).linear.2 s x.coordinates

theorem coordinatesIn_zero (i j : I) (hi : a.domain i p) (hj : a.domain j p) :
    coordinatesIn i hi (zeroIn j hj) ≈ Fiber.zero n :=
  (a.transition p j i hj hi).linear.zero

theorem coordinatesIn_neg (i : I) (hi : a.domain i p) (x : AtlasFiber a p) :
    coordinatesIn i hi (neg x) ≈ Fiber.neg (coordinatesIn i hi x) :=
  (a.transition p x.chart i x.mem hi).linear.neg x.coordinates

theorem add_congr {x x' y y' : AtlasFiber a p} (hx : x ≈ x') (hy : y ≈ y') :
    add x y ≈ add x' y' := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_add x.chart x.mem x y)
    (Setoid.trans (Fiber.add_congr (coordinatesIn_congr x.chart x.mem hx)
      (coordinatesIn_congr x.chart x.mem hy))
      (Setoid.symm (coordinatesIn_add x.chart x.mem x' y')))

theorem scale_congr {s t : Scalar} {x y : AtlasFiber a p}
    (hst : s.val.Equiv t.val) (hxy : x ≈ y) : scale s x ≈ scale t y := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_scale x.chart x.mem s x)
    (Setoid.trans (Fiber.scale_congr hst (coordinatesIn_congr x.chart x.mem hxy))
      (Setoid.symm (coordinatesIn_scale x.chart x.mem t y)))

theorem zeroIn_independent (i j : I) (hi : a.domain i p) (hj : a.domain j p) :
    zeroIn i hi ≈ zeroIn j hj := by
  change (a.transition p i j hi hj).toValueIso.forward.eval (Fiber.zero n) ≈ Fiber.zero n
  exact (a.transition p i j hi hj).linear.zero

theorem neg_congr {x y : AtlasFiber a p} (hxy : x ≈ y) : neg x ≈ neg y := by
  apply coordinatesIn_reflects x.chart x.mem
  have he : Fiber.neg (coordinatesIn x.chart x.mem x) ≈ Fiber.neg (coordinatesIn x.chart x.mem y) :=
    fun i => ComplexRaw.neg_equiv (coordinatesIn_congr x.chart x.mem hxy i)
  exact Setoid.trans (coordinatesIn_neg x.chart x.mem x)
    (Setoid.trans he
      (Setoid.symm (coordinatesIn_neg x.chart x.mem y)))

theorem add_comm (x y : AtlasFiber a p) : add x y ≈ add y x := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_add x.chart x.mem x y)
    (Setoid.trans (Fiber.add_comm _ _) (Setoid.symm (coordinatesIn_add x.chart x.mem y x)))

theorem add_assoc (x y z : AtlasFiber a p) : add (add x y) z ≈ add x (add y z) := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_add x.chart x.mem (add x y) z)
    (Setoid.trans (Fiber.add_congr (coordinatesIn_add x.chart x.mem x y) (Setoid.refl _))
      (Setoid.trans (Fiber.add_assoc _ _ _)
        (Setoid.trans (Fiber.add_congr (Setoid.refl _) (Setoid.symm (coordinatesIn_add x.chart x.mem y z)))
          (Setoid.symm (coordinatesIn_add x.chart x.mem x (add y z))))))

theorem zero_add (i : I) (hi : a.domain i p) (x : AtlasFiber a p) :
    add (zeroIn i hi) x ≈ x := by
  apply coordinatesIn_reflects i hi
  exact Setoid.trans (coordinatesIn_add i hi (zeroIn i hi) x)
    (Setoid.trans (Fiber.add_congr (coordinatesIn_zero i i hi hi) (Setoid.refl _)) (Fiber.zero_add _))

theorem add_neg (i : I) (hi : a.domain i p) (x : AtlasFiber a p) :
    add x (neg x) ≈ zeroIn i hi := by
  apply coordinatesIn_reflects i hi
  have he : Fiber.add (coordinatesIn i hi x) (Fiber.neg (coordinatesIn i hi x)) ≈ Fiber.zero n :=
    fun j => ComplexRaw.add_neg_equiv _ ((coordinatesIn i hi x).property j)
  exact Setoid.trans (coordinatesIn_add i hi x (neg x))
    (Setoid.trans (Fiber.add_congr (Setoid.refl _) (coordinatesIn_neg i hi x))
      (Setoid.trans he
        (Setoid.symm (coordinatesIn_zero i i hi hi))))

theorem scale_one (x : AtlasFiber a p) :
    scale ⟨ComplexRaw.one, ComplexRaw.ofQComplex_valid _⟩ x ≈ x := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_scale x.chart x.mem _ x)
    (fun i => ComplexRaw.one_mul_equiv _ ((coordinatesIn x.chart x.mem x).property i))

theorem scale_zeroScalar (i : I) (hi : a.domain i p) (x : AtlasFiber a p) :
    scale ⟨ComplexRaw.zero, ComplexRaw.ofQComplex_valid _⟩ x ≈ zeroIn i hi := by
  apply coordinatesIn_reflects i hi
  exact Setoid.trans (coordinatesIn_scale i hi _ x)
    (Setoid.trans (Fiber.zero_scale _) (Setoid.symm (coordinatesIn_zero i i hi hi)))

theorem scale_scalar_add (s t : Scalar) (x : AtlasFiber a p) :
    scale ⟨ComplexRaw.add s.val t.val, ComplexRaw.add_valid s.property t.property⟩ x ≈
      add (scale s x) (scale t x) := by
  apply coordinatesIn_reflects x.chart x.mem
  have he : Fiber.scale ⟨ComplexRaw.add s.val t.val, ComplexRaw.add_valid s.property t.property⟩
      (coordinatesIn x.chart x.mem x) ≈
      Fiber.add (Fiber.scale s (coordinatesIn x.chart x.mem x)) (Fiber.scale t (coordinatesIn x.chart x.mem x)) :=
    fun i => ComplexRaw.add_mul_equiv _ _ _ s.property t.property
      ((coordinatesIn x.chart x.mem x).property i)
  exact Setoid.trans (coordinatesIn_scale x.chart x.mem _ x)
    (Setoid.trans he
      (Setoid.trans (Fiber.add_congr (Setoid.symm (coordinatesIn_scale x.chart x.mem s x))
        (Setoid.symm (coordinatesIn_scale x.chart x.mem t x)))
        (Setoid.symm (coordinatesIn_add x.chart x.mem (scale s x) (scale t x)))))

theorem scale_add (s : Scalar) (x y : AtlasFiber a p) :
    scale s (add x y) ≈ add (scale s x) (scale s y) := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_scale x.chart x.mem s (add x y))
    (Setoid.trans (Fiber.scale_congr (ComplexRaw.equiv_refl _ s.property) (coordinatesIn_add x.chart x.mem x y))
      (Setoid.trans (Fiber.scale_add s _ _)
        (Setoid.trans (Fiber.add_congr (Setoid.symm (coordinatesIn_scale x.chart x.mem s x))
          (Setoid.symm (coordinatesIn_scale x.chart x.mem s y)))
          (Setoid.symm (coordinatesIn_add x.chart x.mem (scale s x) (scale s y))))))

theorem scale_scale (s t : Scalar) (x : AtlasFiber a p) :
    scale s (scale t x) ≈ scale ⟨ComplexRaw.mul s.val t.val, ComplexRaw.mul_valid s.property t.property⟩ x := by
  apply coordinatesIn_reflects x.chart x.mem
  exact Setoid.trans (coordinatesIn_scale x.chart x.mem s (scale t x))
    (Setoid.trans (Fiber.scale_congr (ComplexRaw.equiv_refl _ s.property) (coordinatesIn_scale x.chart x.mem t x))
      (Setoid.trans (Fiber.scale_scale s t _) (Setoid.symm (coordinatesIn_scale x.chart x.mem _ x))))

end ComputableAnalysis.RiemannHilbert.AtlasFiber
