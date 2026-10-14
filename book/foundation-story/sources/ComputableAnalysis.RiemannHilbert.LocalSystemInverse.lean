import ComputableAnalysis.RiemannHilbert.NeumannSeries

/-! The actual local solution evaluator is a constructed linear isomorphism
at every represented point of its certified domain. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

theorem localValue_agreement (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (B : Rat) (hB : 0 ≤ B) (hinitial : CoordinateBound initial B)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    localValue a initial M K hM hK hMK haB z hz ≈
      VectorSeries.value (coefficient a initial) z B K (solutionRadius K hK).val
        hB hK (Rat.le_of_lt (solutionRadius K hK).property)
        (coefficient_majorant a initial M B K hM hB hK hMK haB hinitial)
        (interior_bound _ z hz) (by
          have := solutionRadius_small K hK
          have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
          grind) :=
  VectorSeries.value_congr _ _ z z (fun _ => Setoid.refl _) (equiv_refl _ z.property)
    (initialBound initial) K (solutionRadius K hK).val B K (solutionRadius K hK).val
    (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    hB hK (Rat.le_of_lt (solutionRadius K hK).property)
    (coefficient_majorant a initial M (initialBound initial) K hM (initialBound_nonneg initial) hK hMK haB
      (initialBound_valid initial))
    (coefficient_majorant a initial M B K hM hB hK hMK haB hinitial)
    (interior_bound _ z hz) (interior_bound _ z hz)
    (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)
    (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind)

theorem localValue_deviation (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (B : Rat) (hB : 0 ≤ B) (hinitial : CoordinateBound initial B)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    CoordinateBound (Fiber.sub (localValue a initial M K hM hK hMK haB z hz) initial)
      ((8*K*(solutionRadius K hK).val)*B) := by
  have hs := VectorSeries.value_close (coefficient a initial) z B K (solutionRadius K hK).val
    hB hK (Rat.le_of_lt (solutionRadius K hK).property)
    (coefficient_majorant a initial M B K hM hB hK hMK haB hinitial) (interior_bound _ z hz)
    (by
      have := solutionRadius_small K hK
      have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
      grind) 1
  have hp : VectorSeries.block (coefficient a initial) z 0 1 ≈ initial := by
    simp only [VectorSeries.block, vectorBlock, VectorSeries.term, Nat.zero_add, LocalODE.power, coefficient_zero]
    change Fiber.add (Fiber.zero n) (Fiber.scale ⟨one, ofQComplex_valid _⟩ initial) ≈ initial
    exact Setoid.trans (Fiber.zero_add _) (fun i => one_mul_equiv _ (initial.property i))
  have he : 4*B*(2*K*(solutionRadius K hK).val)^1=(8*K*(solutionRadius K hK).val)*B := by
    rw [Rat.pow_one]; grind
  rw [he] at hs
  exact bound_congr (Fiber.sub_congr
    (Setoid.symm (localValue_agreement a initial M K hM hK hMK haB B hB hinitial z hz)) hp) hs

theorem localValueMap_deviation (a : Nat → ValueMap (Fiber n) (Fiber n))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z)
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound
      ((ValueMap.difference ValueMap.identity (localValueMap a M K hM hK hMK haB z hz)).eval x)
      ((8*K*(solutionRadius K hK).val)*B) :=
  fun i => RepresentedCauchySum.small_sub_symm _ _ _
    (localValue_deviation a x M K hM hK hMK haB B hB hx z hz i)

/-- No inverse is supplied: it is the represented Neumann sum of the
deviation of the actual local solution map from identity. -/
def localValueIso (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) : LinearIso n n :=
  Neumann.linearIso (localValueMap a M K hM hK hMK haB z hz)
    (localValueMap_linear a ha M K hM hK hMK haB z hz)
    (8*K*(solutionRadius K hK).val)
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) (Rat.le_of_lt (solutionRadius K hK).property))
    (solutionRadius_small K hK) (localValueMap_deviation a M K hM hK hMK haB z hz)

def initialFromValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (v : Fiber n) : Fiber n :=
  (localValueIso a ha M K hM hK hMK haB z hz).toValueIso.backward.eval v

theorem localValue_initialFromValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (v : Fiber n) :
    localValue a (initialFromValue a ha M K hM hK hMK haB z hz v) M K hM hK hMK haB z hz ≈ v :=
  (localValueIso a ha M K hM hK hMK haB z hz).toValueIso.forward_backward v

theorem initialFromValue_localValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (initial : Fiber n) :
    initialFromValue a ha M K hM hK hMK haB z hz
      (localValue a initial M K hM hK hMK haB z hz) ≈ initial :=
  (localValueIso a ha M K hM hK hMK haB z hz).toValueIso.backward_forward initial

theorem localValue_reflects (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) (x y : Fiber n)
    (hxy : localValue a x M K hM hK hMK haB z hz ≈ localValue a y M K hM hK hMK haB z hz) :
    x ≈ y := (localValueIso a ha M K hM hK hMK haB z hz).toValueIso.forward_reflects hxy

theorem initialFromValue_congr (a b : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (hb : ∀ k, IsLinear (b k)) (hab : ∀ k, (a k).Equiv (b k))
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L) (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : interior (solutionRadius K hK).val z) (hw : interior (solutionRadius L hL).val w)
    (x y : Fiber n) (hxy : x ≈ y) :
    initialFromValue a ha M K hM hK hMK haB z hz x ≈ initialFromValue b hb P L hP hL hPL hbB w hw y := by
  let F := (localValueIso a ha M K hM hK hMK haB z hz).toValueIso
  let G := (localValueIso b hb P L hP hL hPL hbB w hw).toValueIso
  have hforward : F.forward.Equiv G.forward :=
    fun v => localValue_congr a b v v hab (Setoid.refl _) M K P L hM hK hP hL hMK hPL haB hbB z w hzw hz hw
  exact Setoid.trans (F.backward.congr hxy) (ValueIso.inverse_congr F G hforward y)

end ComputableAnalysis.RiemannHilbert.LocalSystem
