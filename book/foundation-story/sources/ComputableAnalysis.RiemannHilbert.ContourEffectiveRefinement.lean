import ComputableAnalysis.RiemannHilbert.ContourDerivativeEdges

/-! An explicit Lipschitz bound yields a dyadic Cauchy tail independent of
the refinement factor. Degenerate intervals are included. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem intervalGridStep_dyadic (I : QInterval) (n : Nat) :
    intervalGridStep I (2^n)=I.width*((1:Rat)/2)^n := by
  rw [RationalMajorant.half_pow_eq_one_div_nat_two_pow]
  simp only [intervalGridStep,Rat.div_def,Rat.one_mul]

theorem intervalGridCell_difference_bound (I : QInterval) (n j : Nat) (hI : I.lo≤I.hi)
    (p q : Rat)
    (hp : (intervalGridCell I (2^n) j).lo≤p ∧ p≤(intervalGridCell I (2^n) j).hi)
    (hq : (intervalGridCell I (2^n) j).lo≤q ∧ q≤(intervalGridCell I (2^n) j).hi) :
    -(I.width+1)*((1:Rat)/2)^n≤q-p ∧ q-p≤(I.width+1)*((1:Rat)/2)^n := by
  have hpow : 0<((1:Rat)/2)^n := Rat.pow_pos (by decide +kernel : (0:Rat)<1/2)
  have hw : 0≤I.width := by unfold QInterval.width; grind only
  have hs := intervalGridStep_dyadic I n
  dsimp [intervalGridCell] at hp hq
  simp only [Rat.natCast_add] at hp hq
  change I.lo+(j:Rat)*intervalGridStep I (2^n)≤p ∧
    p≤I.lo+((j:Rat)+1)*intervalGridStep I (2^n) at hp
  change I.lo+(j:Rat)*intervalGridStep I (2^n)≤q ∧
    q≤I.lo+((j:Rat)+1)*intervalGridStep I (2^n) at hq
  constructor <;> grind only

theorem intervalGridPrefix_lipschitz_refinement_bound (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (L : Rat) (hL : 0≤L)
    (hlip : ∀ p q : Rat, I.lo≤p ∧ p≤I.hi → I.lo≤q ∧ q≤I.hi → ∀ H : QPos,
      -H.val≤q-p → q-p≤H.val → Small (sub (sample q).val (sample p).val) (L*H.val))
    (n F : Nat) (hF : 0<F) :
    Small (sub (intervalGridPrefix sample I ((2^n)*F)).val
      (intervalGridPrefix sample I (2^n)).val)
      (L*I.width*(I.width+1)*((1:Rat)/2)^n) := by
  have hw : 0≤I.width := by unfold QInterval.width; grind only
  let H : QPos := ⟨(I.width+1)*((1:Rat)/2)^n,
    Rat.mul_pos (by grind only) (Rat.pow_pos (by decide +kernel : (0:Rat)<1/2))⟩
  have he : I.width*(L*H.val)=L*I.width*(I.width+1)*((1:Rat)/2)^n := by
    dsimp [H]; grind only
  rw [←he]
  apply intervalGridPrefix_refinement_bound sample I (2^n) F hI (Nat.two_pow_pos n) hF
    (L*H.val) (Rat.mul_nonneg hL (Rat.le_of_lt H.property))
  intro j t hj ht
  have hp := intervalGridTag_mem_cell I (2^n) j hI (Nat.two_pow_pos n)
  have hq := intervalGridRefinedTag_mem_cell I (2^n) F j t hI (Nat.two_pow_pos n) hF ht
  have hd := intervalGridCell_difference_bound I n j hI _ _ hp hq
  exact hlip _ _
    (intervalGridCell_contains_initial I (2^n) j hI (Nat.two_pow_pos n) hj _ hp)
    (intervalGridCell_contains_initial I (2^n) j hI (Nat.two_pow_pos n) hj _ hq) H (by dsimp [H]; grind only) hd.2

theorem intervalGridPrefix_lipschitz_dyadic_bound (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (L : Rat) (hL : 0≤L)
    (hlip : ∀ p q : Rat, I.lo≤p ∧ p≤I.hi → I.lo≤q ∧ q≤I.hi → ∀ H : QPos,
      -H.val≤q-p → q-p≤H.val → Small (sub (sample q).val (sample p).val) (L*H.val))
    (k n : Nat) (hkn : k≤n) :
    Small (sub (intervalGridPrefix sample I (2^n)).val
      (intervalGridPrefix sample I (2^k)).val)
      (L*I.width*(I.width+1)*((1:Rat)/2)^k) := by
  obtain ⟨r,hr⟩ := Nat.exists_eq_add_of_le hkn
  rw [hr,Nat.pow_add]
  exact intervalGridPrefix_lipschitz_refinement_bound sample I hI L hL hlip k (2^r) (Nat.two_pow_pos r)

theorem horizontalContinuousPrefix_effective_cauchy (f : DomainFunctions.Map) (hf : Holomorphic f)
    (I : QInterval) (y : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (horizontalIntervalRectangle I y) z → f.domain z)
    (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains (horizontalIntervalRectangle I y) z),
      Small (hf.derivative z (hdom z hz)).val B.val) (k n : Nat) (hkn : k≤n) :
    Small (sub (horizontalContinuousPrefix f I y hdom n).val
      (horizontalContinuousPrefix f I y hdom k).val)
      (4*B.val*I.width*(I.width+1)*((1:Rat)/2)^k) :=
  intervalGridPrefix_lipschitz_dyadic_bound _ I hI (4*B.val)
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) B.property))
    (horizontalIntervalSample_derivative_bound f hf I y hdom B hder) k n hkn

theorem verticalContinuousPrefix_effective_cauchy (f : DomainFunctions.Map) (hf : Holomorphic f)
    (I : QInterval) (x : Rat) (hI : I.lo≤I.hi)
    (hdom : ∀ z : Scalar, representedRectangleContains (verticalIntervalRectangle I x) z → f.domain z)
    (B : QPos)
    (hder : ∀ z (hz : representedRectangleContains (verticalIntervalRectangle I x) z),
      Small (hf.derivative z (hdom z hz)).val B.val) (k n : Nat) (hkn : k≤n) :
    Small (sub (verticalContinuousPrefix f I x hdom n).val
      (verticalContinuousPrefix f I x hdom k).val)
      (8*B.val*I.width*(I.width+1)*((1:Rat)/2)^k) := by
  let a := rationalRectangleScalar (⟨0,1⟩ : QComplex)
  let p := intervalGridPrefix (verticalIntervalSample f I x hdom) I (2^n)
  let q := intervalGridPrefix (verticalIntervalSample f I x hdom) I (2^k)
  have hb := intervalGridPrefix_lipschitz_dyadic_bound _ I hI (4*B.val)
    (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) B.property))
    (verticalIntervalSample_derivative_bound f hf I x hdom B hder) k n hkn
  have hw : 0≤I.width := by unfold QInterval.width; grind only
  have hC : 0≤4*B.val*I.width*(I.width+1)*((1:Rat)/2)^k := by
    apply Rat.mul_nonneg
    · exact Rat.mul_nonneg (Rat.mul_nonneg (Rat.le_of_lt (Rat.mul_pos (by decide +kernel) B.property)) hw)
        (by grind only)
    · exact Rat.le_of_lt (Rat.pow_pos (by decide +kernel : (0:Rat)<1/2))
  have ha : Small a.val 1 := by
    refine ⟨?_,?_,?_,?_⟩ <;> intro i j
    · change (-1:Rat)≤0; decide +kernel
    · change (0:Rat)≤1; decide +kernel
    · change (-1:Rat)≤1; decide +kernel
    · change (1:Rat)≤1; decide +kernel
  have hs := Small.mul a.property (sub_valid p.property q.property)
    (show (0:Rat)≤1 by decide +kernel) hC ha hb
  have he : 2*1*(4*B.val*I.width*(I.width+1)*((1:Rat)/2)^k)=
      8*B.val*I.width*(I.width+1)*((1:Rat)/2)^k := by grind only
  rw [he] at hs
  exact Small.congr (mul_valid a.property (sub_valid p.property q.property))
    (sub_valid (scalarProduct a p).property (scalarProduct a q).property)
    (equiv_symm (product_difference_left a p q)) hs

end ComputableAnalysis.RiemannHilbert.RectangularContour
