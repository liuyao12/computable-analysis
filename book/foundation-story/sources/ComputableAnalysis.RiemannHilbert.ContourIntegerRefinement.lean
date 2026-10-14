import ComputableAnalysis.RiemannHilbert.ContourIntervalCauchy

/-! One continuity depth controls every positive integer refinement factor.
The factor may vary arbitrarily with the quadrature stage. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem intervalGridPrefix_eventual_integer_refinement (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (eps : QPos) :
    ∃ N, ∀ n, N≤n → ∀ F, 0<F →
      Small (sub (intervalGridPrefix sample I ((2^n)*F)).val
        (intervalGridPrefix sample I (2^n)).val) eps.val := by
  let eta := intervalOscillationBudget I eps
  obtain ⟨N,hN⟩ := hosc eta
  refine ⟨N, ?_⟩
  intro n hn F hF
  exact (intervalGridPrefix_refinement_bound sample I (2^n) F hI (Nat.two_pow_pos n) hF
    eta.val (Rat.le_of_lt eta.property) (fun j t hj ht => hN n hn j hj _ _
      (intervalGridTag_mem_cell I (2^n) j hI (Nat.two_pow_pos n))
      (intervalGridRefinedTag_mem_cell I (2^n) F j t hI (Nat.two_pow_pos n) hF ht))).mono
        (intervalOscillationBudget_bound I eps)

theorem intervalGridPrefix_integer_refinement_converges (sample : Rat → Scalar) (I : QInterval)
    (hI : I.lo≤I.hi) (hosc : intervalCellOscillation sample I) (F : Nat → Nat)
    (hF : ∀ n, 0<F n) (u : Scalar) (hu : Converges (fun n => intervalGridPrefix sample I (2^n)) u) :
    Converges (fun n => intervalGridPrefix sample I ((2^n)*F n)) u := by
  apply converge_perturbation _ _ _ hu
  intro eps
  obtain ⟨N,hN⟩ := intervalGridPrefix_eventual_integer_refinement sample I hI hosc eps
  exact ⟨N,fun n hn => hN n hn (F n) (hF n)⟩

end ComputableAnalysis.RiemannHilbert.RectangularContour
