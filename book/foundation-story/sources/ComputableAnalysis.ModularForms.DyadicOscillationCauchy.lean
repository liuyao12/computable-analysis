import ComputableAnalysis.ModularForms.DyadicRefinementError

/-! Cauchy midpoint averages derived from arbitrary-error cell oscillation. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem dyadicAverage_cauchy_of_cell_oscillation (f : Rat → Scalar)
    (osc : ∀ eps : QPos, ∃ N, ∀ choice : Nat → Bool, ∀ n, N≤n → ∀ u v : Rat,
      (bisectionInterval ⟨0,1⟩ choice n).lo≤u →
      u≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      (bisectionInterval ⟨0,1⟩ choice n).lo≤v →
      v≤(bisectionInterval ⟨0,1⟩ choice n).hi →
      Small (sub (f u).val (f v).val) eps.val)
    (eps : QPos) :
    ∃ N, ∀ n m, N≤n → N≤m →
      Small (sub (dyadicSampleAverage f ⟨0,1⟩ n).val
        (dyadicSampleAverage f ⟨0,1⟩ m).val) eps.val := by
  obtain ⟨N,hcells⟩ := osc eps
  have hN : ∀ n, N≤n → ∀ k,
      Small (sub (dyadicSampleAverage f ⟨0,1⟩ (n+k)).val
        (dyadicSampleAverage f ⟨0,1⟩ n).val) eps.val := by
    intro n hn k
    apply dyadicSampleAverage_refinement_error f ⟨0,1⟩ n k eps.val
    intro choice
    let J := bisectionInterval ⟨0,1⟩ choice n
    have ho := bisectionInterval_ordered (⟨0,1⟩ : QInterval) (by decide +kernel) choice n
    have hm := midpoint_mem J ho
    apply dyadicSampleAverage_error f (f J.midpoint) J ho eps.val
    intro u hu0 hu1
    exact hcells choice n hn u J.midpoint hu0 hu1 hm.1 hm.2
  refine ⟨N, ?_⟩
  intro n m hn hm
  by_cases hmn : m≤n
  · have ha : m+(n-m)=n := by omega
    have hb := hN m hm (n-m)
    rw [ha] at hb
    exact hb
  · have ha : n+(m-n)=m := by omega
    have hb := hN n hn (m-n)
    rw [ha] at hb
    have hneg := SeriesLimitLaws.small_neg hb
    let A := dyadicSampleAverage f ⟨0,1⟩ n
    let B := dyadicSampleAverage f ⟨0,1⟩ m
    have hev : (neg (sub B.val A.val)).Equiv (sub A.val B.val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (sub_valid B.property A.property))
        (hright := sub_valid A.property B.property)
      let X := ComplexRawQuotient.ofRaw A.val A.property
      let Y := ComplexRawQuotient.ofRaw B.val B.property
      change -(Y-X)=X-Y
      grind only
    exact Small.congr (neg_valid (sub_valid B.property A.property))
      (sub_valid A.property B.property) hev hneg

end ComputableAnalysis.ModularForms
