import ComputableAnalysis.RiemannHilbert.UniformLocalUniqueness

/-! The actual local series supplies the uniform derivative data used by
finite-mesh uniqueness, rather than assuming these data in its constructor. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

theorem localValue_bound (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    CoordinateBound (localValue a initial M K hM hK hMK haB z hz) (4*initialBound initial) :=
  VectorSeries.value_bound (coefficient a initial) z (initialBound initial) K (solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    (coefficient_majorant a initial M (initialBound initial) K hM (initialBound_nonneg initial) hK hMK haB
      (initialBound_valid initial))
    (interior_bound _ z hz) (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)

theorem localValue_uniform_derivative (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (eps H : QPos) (w z : Scalar) (hw : interior (solutionRadius K hK).val w)
    (hz : interior (solutionRadius K hK).val z)
    (hH : H.val ≤ (derivativeDelta (initialBound initial) K (initialBound_nonneg initial) hK eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound
      (Fiber.sub
        (Fiber.sub (localValue a initial M K hM hK hMK haB z hz)
          (localValue a initial M K hM hK hMK haB w hw))
        (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩
          (localDerivative a initial M K hM hK hMK haB w hw)))
      (eps.val*H.val) := by
  intro d
  let F := localValue a initial M K hM hK hMK haB z hz
  let G := localValue a initial M K hM hK hMK haB w hw
  let D := localDerivative a initial M K hM hK hMK haB w hw
  let c : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  have hs := BoundedSeries.sum_derivative_error (coordinateSeries a initial d) w.val z.val
    (coordinateSeries_valid a initial d) w.property z.property
    (initialBound initial) K (solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    (fun k => coefficient_majorant a initial M (initialBound initial) K hM
      (initialBound_nonneg initial) hK hMK haB (initialBound_valid initial) k d)
    (interior_bound _ w hw) (interior_bound _ z hz) (solutionRadius_small K hK) eps H hH hzw
  exact Small.congr
    (SeriesLimitLaws.remainder_valid (F.val d) (G.val d) (D.val d) c.val
      (F.property d) (G.property d) (D.property d) c.property)
    ((Fiber.sub (Fiber.sub F G) (Fiber.scale c D)).property d)
    (FunctionTheory.sub_congr (equiv_refl _ (sub_valid (F.property d) (G.property d)))
      (mul_comm_equiv (D.val d) c.val (D.property d) c.property)) hs

theorem localValue_uniform_remainder (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (initial : Fiber n) (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K)
    (eps H : QPos) (w z : Scalar) (hw : interior (solutionRadius K hK).val w)
    (hz : interior (solutionRadius K hK).val z)
    (hH : H.val ≤ (derivativeDelta (initialBound initial) K (initialBound_nonneg initial) hK eps).val)
    (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound
      (UniformLocal.remainder (coefficientValueMap a M K hM hK haB)
        (localValue a initial M K hM hK hMK haB) w z hw hz) (eps.val*H.val) := by
  have hs := localValue_uniform_derivative a initial M K hM hK hMK haB eps H w z hw hz hH hzw
  let c : Scalar := ⟨sub z.val w.val, sub_valid z.property w.property⟩
  exact bound_congr
    (Fiber.sub_congr (Setoid.refl _) (Fiber.scale_congr (a := c) (b := c) (equiv_refl _ c.property)
      (localValue_ode a ha initial M K hM hK hMK haB w hw))) hs

theorem local_operator_small (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) :
    2*(solutionRadius K hK).val*(8*M) ≤ (1 : Rat)/2 := by
  have hr := Rat.le_of_lt (solutionRadius K hK).property
  have h := Rat.mul_le_mul_of_nonneg_right hMK hr
  have hs := solutionRadius_small K hK
  grind

/-- The constructed local solution agrees with every supplied horizontal field
having justified uniform first-order errors and a value bound on this disk.
The other field need not be supplied as a power series. -/
theorem localValue_unique_uniform
    (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (initial : Fiber n) (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : OperatorMajorant a M K)
    (g : UniformLocal.Field (n := n) (solutionRadius K hK).val)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hg0 : g ⟨zero, ofQComplex_valid _⟩ (interior_zero _ (solutionRadius K hK).property) ≈ initial)
    (B : Rat) (hB : 0 ≤ B) (hgB : ∀ z hz, CoordinateBound (g z hz) B)
    (delta : QPos → QPos)
    (hgrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (delta eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformLocal.remainder (coefficientValueMap a M K hM hK haB) g w z hw hz)
        (eps.val*H.val))
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    localValue a initial M K hM hK hMK haB z hz ≈ g z hz :=
  UniformLocal.equal (solutionRadius K hK) (coefficientValueMap a M K hM hK haB)
    (localValue a initial M K hM hK hMK haB) g (8*M) (4*initialBound initial) B
    (Rat.mul_nonneg (by decide) hM) (local_operator_small M K hM hK hMK)
    (Rat.mul_nonneg (by decide) (initialBound_nonneg initial)) hB
    (fun z w hz hw hzw => localValue_congr a a initial initial
      (fun _ => ValueMap.equiv_refl _) (Setoid.refl _) M K M K hM hK hM hK hMK hMK haB haB
      z w hzw hz hw)
    hgcongr (Setoid.trans (localValue_initial a initial M K hM hK hMK haB) (Setoid.symm hg0))
    (localValue_bound a initial M K hM hK hMK haB) hgB
    (coefficientValueMap_linear a ha M K hM hK haB)
    (fun z hz C hC x hx => operatorValue_bound a z M K (solutionRadius K hK).val C hM hK
      (Rat.le_of_lt (solutionRadius K hK).property) hC haB (interior_bound _ z hz)
      (by
        have := solutionRadius_small K hK
        have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
        grind) x hx)
    (derivativeDelta (initialBound initial) K (initialBound_nonneg initial) hK) delta
    (localValue_uniform_remainder a ha initial M K hM hK hMK haB) hgrem z hz

end ComputableAnalysis.RiemannHilbert.LocalSystem
