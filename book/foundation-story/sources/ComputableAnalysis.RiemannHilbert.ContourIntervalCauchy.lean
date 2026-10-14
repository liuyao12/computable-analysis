import ComputableAnalysis.RiemannHilbert.ContourIntervalPrefix
import ComputableAnalysis.RiemannHilbert.ContourLimitComparison

/-! Arbitrarily deep refinement and tag agreement for actual interval
quadratures. Cauchy estimates are proved without constructing a completion. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def intervalCellOscillation (sample : Rat → Scalar) (I : QInterval) : Prop :=
  ∀ eps : QPos, ∃ N, ∀ n, N≤n → ∀ j, j<2^n → ∀ p q : Rat,
    ((intervalGridCell I (2^n) j).lo≤p ∧ p≤(intervalGridCell I (2^n) j).hi) →
    ((intervalGridCell I (2^n) j).lo≤q ∧ q≤(intervalGridCell I (2^n) j).hi) →
    Small (sub (sample q).val (sample p).val) eps.val

def intervalOscillationBudget (I : QInterval) (eps : QPos) : QPos :=
  divideRadius eps ⟨1+qabs I.width,by have h := qabs_nonneg I.width; grind only⟩

theorem intervalOscillationBudget_bound (I : QInterval) (eps : QPos) :
    I.width*(intervalOscillationBudget I eps).val≤eps.val := by
  have h := divideRadius_identity eps
    (⟨1+qabs I.width,by have h := qabs_nonneg I.width; grind only⟩ : QPos)
  have hb : I.width≤1+qabs I.width := by have he := self_le_qabs I.width; grind only
  have hs := Rat.mul_le_mul_of_nonneg_right hb (Rat.le_of_lt (intervalOscillationBudget I eps).property)
  change (1+qabs I.width)*(intervalOscillationBudget I eps).val=eps.val at h
  rw [h] at hs
  exact hs

theorem intervalGridPrefix_eventual_refinement (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ r,
      Small (sub (intervalGridPrefix sample I (2^(n+r))).val
        (intervalGridPrefix sample I (2^n)).val) eps.val := by
  let eta := intervalOscillationBudget I eps
  obtain ⟨N,hN⟩ := hosc eta
  refine ⟨N, ?_⟩
  intro n hn r
  have hs := intervalGridPrefix_refinement_bound sample I (2^n) (2^r) hI
    (Nat.two_pow_pos n) (Nat.two_pow_pos r) eta.val (Rat.le_of_lt eta.property)
    (fun j t hj ht => hN n hn j hj _ _
      (intervalGridTag_mem_cell I (2^n) j hI (Nat.two_pow_pos n))
      (intervalGridRefinedTag_mem_cell I (2^n) (2^r) j t hI
        (Nat.two_pow_pos n) (Nat.two_pow_pos r) ht))
  rw [←Nat.pow_add] at hs
  exact hs.mono (intervalOscillationBudget_bound I eps)

theorem intervalGridPrefix_dyadic_cauchy (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (eps : QPos) :
    ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (intervalGridPrefix sample I (2^n)).val
        (intervalGridPrefix sample I (2^m)).val) eps.val := by
  obtain ⟨N,hN⟩ := intervalGridPrefix_eventual_refinement sample I hI hosc eps
  refine ⟨N, ?_⟩
  intro n m hn hm
  by_cases he : n≤m
  · obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le he
    exact RepresentedCauchySum.small_sub_symm _ _ _ (hN n hn r)
  · have hmn : m≤n := by omega
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hN m hm r

theorem intervalGridTaggedPrefix_eventual_agreement (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ tag other : Nat → Rat,
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤tag j ∧ tag j≤(intervalGridCell I (2^n) j).hi) →
      (∀ j, j<2^n → (intervalGridCell I (2^n) j).lo≤other j ∧ other j≤(intervalGridCell I (2^n) j).hi) →
      Small (sub (intervalGridTaggedPrefix sample I (2^n) tag).val
        (intervalGridTaggedPrefix sample I (2^n) other).val) eps.val := by
  let eta := intervalOscillationBudget I eps
  obtain ⟨N,hN⟩ := hosc eta
  refine ⟨N, ?_⟩
  intro n hn tag other htag hother
  exact (intervalGridTaggedPrefix_difference_bound sample I (2^n) hI (Nat.two_pow_pos n)
    tag other eta.val (Rat.le_of_lt eta.property)
    (fun j hj => hN n hn j hj _ _ (hother j hj) (htag j hj))).mono
      (intervalOscillationBudget_bound I eps)

theorem intervalGridTaggedPrefix_limits_agree (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (tag other : Nat → Nat → Rat)
    (htag : ∀ n j, j<2^n → (intervalGridCell I (2^n) j).lo≤tag n j ∧ tag n j≤(intervalGridCell I (2^n) j).hi)
    (hother : ∀ n j, j<2^n → (intervalGridCell I (2^n) j).lo≤other n j ∧ other n j≤(intervalGridCell I (2^n) j).hi)
    (u v : Scalar) (hu : Converges (fun n => intervalGridTaggedPrefix sample I (2^n) (tag n)) u)
    (hv : Converges (fun n => intervalGridTaggedPrefix sample I (2^n) (other n)) v) : u≈v := by
  apply converge_unique _ _ _ hu
  apply converge_perturbation _ _ _ hv
  intro eps
  obtain ⟨N,hN⟩ := intervalGridTaggedPrefix_eventual_agreement sample I hI hosc eps
  exact ⟨N,fun n hn => hN n hn (tag n) (other n) (htag n) (hother n)⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
