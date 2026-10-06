import ComputableAnalysis.RiemannHilbert.LocalSystemSum
import ComputableAnalysis.RiemannHilbert.CoefficientSuperposition

/-! Initial-data superposition for the actual finite-rank represented sums. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory
variable {n : Nat}

theorem coordinateSum_add (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (x y : Fiber n) (z : Scalar)
    (M C D E K R : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (hx : CoordinateBound x C) (hy : CoordinateBound y D) (hxy : CoordinateBound (Fiber.add x y) E)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (i : Fin n) :
    (coordinateSum a (Fiber.add x y) z E K R i).Equiv
      (add (coordinateSum a x z C K R i) (coordinateSum a y z D K R i)) := by
  have hcx := fun k => coefficient_majorant a x M C K hM hC hK hMK haB hx k i
  have hcy := fun k => coefficient_majorant a y M D K hM hD hK hMK haB hy k i
  have hcd : ∀ k, Small (add (coordinateSeries a x i k) (coordinateSeries a y i k)) ((C+D)*K^k) := by
    intro k
    have hs := LocalODE.small_add (hcx k) (hcy k)
    have he : C*K^k+D*K^k=(C+D)*K^k := by grind
    rw [he] at hs; exact hs
  have hcxy := fun k => coefficient_majorant a (Fiber.add x y) M E K hM hE hK hMK haB hxy k i
  have hm := LocalODE.coefficientSum_valid _ z.val
    (fun k => add_valid (coordinateSeries_valid a x i k) (coordinateSeries_valid a y i k))
    z.property (C+D) K R (Rat.add_nonneg hC hD) hK hR hcd hz hlocal
  have he := LocalODE.coefficientSum_congr_of_bounds _ _ z.val z.val
    (coordinateSeries_valid a (Fiber.add x y) i)
    (fun k => add_valid (coordinateSeries_valid a x i k) (coordinateSeries_valid a y i k))
    z.property z.property (fun k => coefficient_add a ha x y k i)
    (equiv_refl _ z.property) E K R (C+D) K R hE hK hR (Rat.add_nonneg hC hD) hK hR
    hcxy hcd hz hz hlocal hlocal
  exact equiv_trans
    (coordinateSum_valid a (Fiber.add x y) z M E K R hM hE hK hR hMK haB hxy hz hlocal i)
    hm
    (add_valid (coordinateSum_valid a x z M C K R hM hC hK hR hMK haB hx hz hlocal i)
      (coordinateSum_valid a y z M D K R hM hD hK hR hMK haB hy hz hlocal i)) he
    (LocalODE.coefficientSum_add _ _ z.val (coordinateSeries_valid a x i) (coordinateSeries_valid a y i)
      z.property C D K R hC hD hK hR hcx hcy hz hlocal)

theorem coordinateSum_scale (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (c : Scalar) (x : Fiber n) (z : Scalar)
    (M B C E K R : Rat) (hM : 0 ≤ M) (hB : 0 ≤ B) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (hc : Small c.val B) (hx : CoordinateBound x C) (hcx : CoordinateBound (Fiber.scale c x) E)
    (hz : Small z.val R) (hlocal : 2*K*R ≤ (1 : Rat)/2) (i : Fin n) :
    (coordinateSum a (Fiber.scale c x) z E K R i).Equiv
      (mul c.val (coordinateSum a x z C K R i)) := by
  have hcs := fun k => coefficient_majorant a x M C K hM hC hK hMK haB hx k i
  have hBC : 0 ≤ 2*B*C := Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) hC
  have hcd : ∀ k, Small (mul c.val (coordinateSeries a x i k)) ((2*B*C)*K^k) := by
    intro k
    have hs := Small.mul c.property (coordinateSeries_valid a x i k) hB
      (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) hc (hcs k)
    have he : 2*B*(C*K^k)=(2*B*C)*K^k := by grind
    rw [he] at hs; exact hs
  have hscaled := fun k => coefficient_majorant a (Fiber.scale c x) M E K hM hE hK hMK haB hcx k i
  have hm := LocalODE.coefficientSum_valid _ z.val
    (fun k => mul_valid c.property (coordinateSeries_valid a x i k)) z.property
    (2*B*C) K R hBC hK hR hcd hz hlocal
  have he := LocalODE.coefficientSum_congr_of_bounds _ _ z.val z.val
    (coordinateSeries_valid a (Fiber.scale c x) i)
    (fun k => mul_valid c.property (coordinateSeries_valid a x i k)) z.property z.property
    (fun k => coefficient_scale a ha c x k i) (equiv_refl _ z.property)
    E K R (2*B*C) K R hE hK hR hBC hK hR hscaled hcd hz hz hlocal hlocal
  exact equiv_trans
    (coordinateSum_valid a (Fiber.scale c x) z M E K R hM hE hK hR hMK haB hcx hz hlocal i)
    hm (mul_valid c.property (coordinateSum_valid a x z M C K R hM hC hK hR hMK haB hx hz hlocal i)) he
    (LocalODE.coefficientSum_scale _ z.val c.val (coordinateSeries_valid a x i) z.property c.property
      B C K R hB hC hK hR hc hcs hz hlocal)

/-- The summed evaluation is a represented map of the initial vector. -/
def localValueMap (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z) : ValueMap (Fiber n) (Fiber n) :=
  ⟨fun x => localValue a x M K hM hK hMK haB z hz,
    fun hxy => localValue_congr a a _ _ (fun k => ValueMap.equiv_refl (a k)) hxy
      M K M K hM hK hM hK hMK hMK haB haB z z (equiv_refl _ z.property) hz hz⟩

theorem localValueMap_linear (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K) (z : Scalar)
    (hz : LocalODE.interior (LocalODE.solutionRadius K hK).val z) :
    IsLinear (localValueMap a M K hM hK hMK haB z hz) := by
  have hR := Rat.le_of_lt (LocalODE.solutionRadius K hK).property
  have hzB := LocalODE.interior_bound _ z hz
  have hlocal : 2*K*(LocalODE.solutionRadius K hK).val ≤ (1 : Rat)/2 := by
    have := LocalODE.solutionRadius_small K hK
    have := Rat.mul_nonneg hK hR
    grind
  constructor
  · intro x y i
    exact coordinateSum_add a ha x y z M (initialBound x) (initialBound y)
      (initialBound (Fiber.add x y)) K (LocalODE.solutionRadius K hK).val
      hM (initialBound_nonneg x) (initialBound_nonneg y) (initialBound_nonneg _) hK hR hMK haB
      (initialBound_valid x) (initialBound_valid y) (initialBound_valid _) hzB hlocal i
  · intro c x i
    exact coordinateSum_scale a ha c x z M (LocalODE.initialBound c.val) (initialBound x)
      (initialBound (Fiber.scale c x)) K (LocalODE.solutionRadius K hK).val
      hM (LocalODE.initialBound_nonneg _) (initialBound_nonneg x) (initialBound_nonneg _) hK hR hMK haB
      (LocalODE.initialBound_valid c.val c.property) (initialBound_valid x) (initialBound_valid _) hzB hlocal i

theorem localValueMap_initial (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K) :
    (localValueMap a M K hM hK hMK haB ⟨zero, ofQComplex_valid _⟩
      (LocalODE.interior_zero _ (LocalODE.solutionRadius K hK).property)).Equiv ValueMap.identity :=
  fun x => localValue_initial a x M K hM hK hMK haB

end ComputableAnalysis.RiemannHilbert.LocalSystem
