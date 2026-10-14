import ComputableAnalysis.RiemannHilbert.CenteredUniqueness

/-! Agreement of the constructed local horizontal solution with a supplied
local solution on an automatically computed common neighborhood. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

def smallerRadius (r s : QPos) : QPos := if r.val ≤ s.val then r else s

theorem smallerRadius_le_left (r s : QPos) : (smallerRadius r s).val ≤ r.val := by
  unfold smallerRadius; split <;> grind

theorem smallerRadius_le_right (r s : QPos) : (smallerRadius r s).val ≤ s.val := by
  unfold smallerRadius; split <;> grind

theorem interior_mono (R S : Rat) (z : Scalar) (hRS : R ≤ S) (hz : interior R z) : interior S z := by
  obtain ⟨r,hr,hrR,hzr⟩ := hz
  exact ⟨r,hr,by grind,hzr⟩

def germRadius (K : Rat) (hK : 0 ≤ K) (p : Scalar) (hp : interior (solutionRadius K hK).val p) : QPos :=
  smallerRadius (interiorRadius (solutionRadius K hK).val p hp) (solutionRadius K hK)

theorem germRadius_inside (K : Rat) (hK : 0 ≤ K) (p : Scalar) (hp : interior (solutionRadius K hK).val p)
    (z : Scalar) (hz : Centered.domain p (germRadius K hK p hp).val z) :
    interior (solutionRadius K hK).val z :=
  interiorRadius_inside _ p hp z
    ((interior_bound _ (Centered.offset p z) hz).mono (smallerRadius_le_left _ _))

def comparisonRadius (K : Rat) (hK : 0 ≤ K) (p : Scalar) (hp : interior (solutionRadius K hK).val p)
    (r : QPos) : QPos := smallerRadius r (germRadius K hK p hp)

theorem comparisonRadius_original (K : Rat) (hK : 0 ≤ K) (p : Scalar)
    (hp : interior (solutionRadius K hK).val p) (r : QPos)
    (z : Scalar) (hz : Centered.domain p (comparisonRadius K hK p hp r).val z) :
    Centered.domain p r.val z :=
  interior_mono _ _ (Centered.offset p z) (smallerRadius_le_left _ _) hz

theorem comparisonRadius_chart (K : Rat) (hK : 0 ≤ K) (p : Scalar)
    (hp : interior (solutionRadius K hK).val p) (r : QPos)
    (z : Scalar) (hz : Centered.domain p (comparisonRadius K hK p hp r).val z) :
    interior (solutionRadius K hK).val z :=
  germRadius_inside K hK p hp z
    (interior_mono _ _ (Centered.offset p z) (smallerRadius_le_right _ _) hz)

theorem comparisonRadius_small (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (r : QPos) :
    2*(comparisonRadius K hK p hp r).val*(8*M) ≤ (1 : Rat)/2 := by
  have hR := smallerRadius_le_right r (germRadius K hK p hp)
  have hG := smallerRadius_le_right (interiorRadius (solutionRadius K hK).val p hp) (solutionRadius K hK)
  have hs := local_operator_small M K hM hK hMK
  have hle : (comparisonRadius K hK p hp r).val ≤ (solutionRadius K hK).val :=
    Rat.le_trans hR hG
  have hm : 0 ≤ 16*M := Rat.mul_nonneg (by decide) hM
  have hh := Rat.mul_le_mul_of_nonneg_left hle hm
  grind

/-- The supplied field may live on its own arbitrarily small centered domain.
The constructor computes the common neighborhood and proves containment.
Uniform derivative errors are required only where both functions are defined. -/
theorem throughValue_unique_local
    (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n)
    (r : QPos) (g : Centered.Field (n := n) p r.val)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (hgp : g p (Centered.center_mem p r) ≈ v)
    (B : Rat) (hB : 0 ≤ B) (hgB : ∀ z hz, CoordinateBound (g z hz) B)
    (delta : QPos → QPos)
    (hgrem : ∀ (eps H : QPos) w z
      (hw : Centered.domain p r.val w) (hz : Centered.domain p r.val z)
      (hwChart : interior (solutionRadius K hK).val w) (hzChart : interior (solutionRadius K hK).val z),
      H.val ≤ (delta eps).val → Small (sub z.val w.val) H.val →
      CoordinateBound
        (Fiber.sub (Fiber.sub (g z hz) (g w hw))
          (Fiber.scale ⟨sub z.val w.val, sub_valid z.property w.property⟩
            ((coefficientValueMap a M K hM hK haB w hwChart).eval (g w hw)))) (eps.val*H.val))
    (z : Scalar) (hz : Centered.domain p (comparisonRadius K hK p hp r).val z) :
    throughValue a ha M K hM hK hMK haB p hp v z (comparisonRadius_chart K hK p hp r z hz) ≈
      g z (comparisonRadius_original K hK p hp r z hz) := by
  let R := comparisonRadius K hK p hp r
  let chart := fun z hz => comparisonRadius_chart K hK p hp r z hz
  let original := fun z hz => comparisonRadius_original K hK p hp r z hz
  let initial := initialFromValue a ha M K hM hK hMK haB p hp v
  let f : Centered.Field (n := n) p R.val := fun z hz => localValue a initial M K hM hK hMK haB z (chart z hz)
  let h : Centered.Field (n := n) p R.val := fun z hz => g z (original z hz)
  let A : Centered.OperatorField (n := n) p R.val := fun z hz => coefficientValueMap a M K hM hK haB z (chart z hz)
  refine Centered.equal p R A f h (8*M) (4*initialBound initial) B
    (Rat.mul_nonneg (by decide) hM) (comparisonRadius_small M K hM hK hMK p hp r)
    (Rat.mul_nonneg (by decide) (initialBound_nonneg initial)) hB
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (derivativeDelta (initialBound initial) K (initialBound_nonneg initial) hK) delta ?_ ?_ z hz
  · intro z w hz hw hzw
    exact localValue_congr a a initial initial (fun _ => ValueMap.equiv_refl _) (Setoid.refl _)
      M K M K hM hK hM hK hMK hMK haB haB z w hzw (chart z hz) (chart w hw)
  · intro z w hz hw hzw
    exact hgcongr z w (original z hz) (original w hw) hzw
  · exact Setoid.trans (throughValue_normalized a ha M K hM hK hMK haB p hp v) (Setoid.symm hgp)
  · intro z hz
    exact localValue_bound a initial M K hM hK hMK haB z (chart z hz)
  · intro z hz
    exact hgB z (original z hz)
  · intro z hz
    exact coefficientValueMap_linear a ha M K hM hK haB z (chart z hz)
  · intro z hz C hC x hx
    exact operatorValue_bound a z M K (solutionRadius K hK).val C hM hK
      (Rat.le_of_lt (solutionRadius K hK).property) hC haB (interior_bound _ z (chart z hz))
      (by
        have := solutionRadius_small K hK
        have := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
        grind) x hx
  · intro eps H w z hw hz hH hzw
    exact localValue_uniform_remainder a ha initial M K hM hK hMK haB eps H w z (chart w hw) (chart z hz) hH hzw
  · intro eps H w z hw hz hH hzw
    exact hgrem eps H w z (original w hw) (original z hz) (chart w hw) (chart z hz) hH hzw

end ComputableAnalysis.RiemannHilbert.LocalSystem
