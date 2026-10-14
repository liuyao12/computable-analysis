import ComputableAnalysis.RiemannHilbert.VectorSeries

/-! Constructing the coefficient operator function and its finite-prefix bounds. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory

namespace Fiber
def scaleMap (c : Scalar) : ValueMap (Fiber n) (Fiber n) :=
  ⟨scale c, fun h => scale_congr (equiv_refl _ c.property) h⟩

theorem scaleMap_linear (c : Scalar) : IsLinear (scaleMap (n := n) c) := by
  constructor
  · exact scale_add c
  · intro d x i
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (scale c (scale d x)).property i)
      (hright := (scale d (scale c x)).property i)
    change ComplexRawQuotient.ofRaw c.val c.property*
      (ComplexRawQuotient.ofRaw d.val d.property*ComplexRawQuotient.ofRaw (x.val i) (x.property i)) =
      ComplexRawQuotient.ofRaw d.val d.property*
      (ComplexRawQuotient.ofRaw c.val c.property*ComplexRawQuotient.ofRaw (x.val i) (x.property i))
    grind
end Fiber

namespace LocalSystem
variable {n : Nat}

def blockMap (a : Nat → ValueMap (Fiber n) (Fiber n)) (N k : Nat) : ValueMap (Fiber n) (Fiber n) :=
  ⟨fun x => vectorBlock (fun j => (a j).eval x) N k,
    fun h => vectorBlock_congr _ _ (fun j => (a j).congr h) N k⟩

theorem blockMap_linear (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ j, IsLinear (a j))
    (N k : Nat) : IsLinear (blockMap a N k) := by
  induction k with
  | zero => exact ⟨fun _ _ => Setoid.symm (Fiber.zero_add (Fiber.zero n)),
      fun c _ => Setoid.symm (Fiber.scale_zero c)⟩
  | succ k ih =>
    constructor
    · intro x y
      exact Setoid.trans (Fiber.add_congr (ih.1 x y) ((ha (N+k)).1 x y)) (Fiber.add_four _ _ _ _)
    · intro c x
      exact Setoid.trans (Fiber.add_congr (ih.2 c x) ((ha (N+k)).2 c x))
        (Setoid.symm (Fiber.scale_add c _ _))

def operatorPrefixMap (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (N : Nat) :
    ValueMap (Fiber n) (Fiber n) :=
  blockMap (fun k => (a k).followedBy (Fiber.scaleMap ⟨LocalODE.power z.val k,
    LocalODE.power_valid z.val z.property k⟩)) 0 N

theorem operatorPrefixMap_linear (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (z : Scalar) (N : Nat) : IsLinear (operatorPrefixMap a z N) :=
  blockMap_linear _ (fun k => IsLinear.followedBy (ha k) (Fiber.scaleMap_linear _)) 0 N

theorem operatorPrefix_value (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (N : Nat) (x : Fiber n) :
    (operatorPrefixMap a z N).eval x = VectorSeries.block (fun k => (a k).eval x) z 0 N := rfl

theorem operatorCoefficient_bound (a : Nat → ValueMap (Fiber n) (Fiber n)) (M K B : Rat)
    (hB : 0 ≤ B) (haB : OperatorMajorant a M K) (x : Fiber n) (hx : CoordinateBound x B) (k : Nat) :
    CoordinateBound ((a k).eval x) ((2*M*B)*K^k) := by
  have hs := haB k B hB x hx
  have he : 2*M*K^k*B=(2*M*B)*K^k := by grind
  rw [he] at hs; exact hs

def operatorValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (M K R : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) : ValueMap (Fiber n) (Fiber n) where
  eval x := VectorSeries.value (fun k => (a k).eval x) z (2*M*initialBound x) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK hR
    (operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x) haB x (initialBound_valid x)) hz hlocal
  congr {x y} hxy := VectorSeries.value_congr _ _ z z (fun k => (a k).congr hxy) (equiv_refl _ z.property)
    (2*M*initialBound x) K R (2*M*initialBound y) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK hR
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg y)) hK hR
    (operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x) haB x (initialBound_valid x))
    (operatorCoefficient_bound a M K (initialBound y) (initialBound_nonneg y) haB y (initialBound_valid y))
    hz hz hlocal hlocal

/-- A separately justified input bound may be used without changing the
operator value computed from its internal first-box bound. -/
theorem operatorValue_agreement (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (M K R B : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hB : 0 ≤ B) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (x : Fiber n) (hx : CoordinateBound x B) :
    (operatorValue a z M K R hM hK hR haB hz hlocal).eval x ≈
      VectorSeries.value (fun k => (a k).eval x) z (2*M*B) K R
        (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
        (operatorCoefficient_bound a M K B hB haB x hx) hz hlocal :=
  VectorSeries.value_congr _ _ z z (fun _ => Setoid.refl _) (equiv_refl _ z.property)
    (2*M*initialBound x) K R (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) (initialBound_nonneg x)) hK hR
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound a M K (initialBound x) (initialBound_nonneg x) haB x (initialBound_valid x))
    (operatorCoefficient_bound a M K B hB haB x hx) hz hz hlocal hlocal

theorem operatorValue_bound (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (M K R B : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hB : 0 ≤ B) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((operatorValue a z M K R hM hK hR haB hz hlocal).eval x) (8*M*B) := by
  have hs := VectorSeries.value_bound (fun k => (a k).eval x) z (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound a M K B hB haB x hx) hz hlocal
  have he : 4*(2*M*B)=8*M*B := by grind
  rw [he] at hs
  exact bound_congr (Setoid.symm (operatorValue_agreement a z M K R B hM hK hR hB haB hz hlocal x hx)) hs

theorem operatorValue_close (a : Nat → ValueMap (Fiber n) (Fiber n)) (z : Scalar) (M K R B : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hR : 0 ≤ R) (hB : 0 ≤ B) (haB : OperatorMajorant a M K)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound (Fiber.sub ((operatorValue a z M K R hM hK hR haB hz hlocal).eval x)
      ((operatorPrefixMap a z N).eval x)) (8*M*B*(2*K*R)^N) := by
  have hs := VectorSeries.value_close (fun k => (a k).eval x) z (2*M*B) K R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hB) hK hR
    (operatorCoefficient_bound a M K B hB haB x hx) hz hlocal N
  have he : 4*(2*M*B)*(2*K*R)^N=8*M*B*(2*K*R)^N := by grind
  rw [he] at hs
  exact bound_congr (Fiber.sub_congr
    (Setoid.symm (operatorValue_agreement a z M K R B hM hK hR hB haB hz hlocal x hx)) (Setoid.refl _)) hs

end LocalSystem
end ComputableAnalysis.RiemannHilbert
