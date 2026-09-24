import ComputableAnalysis.ArctanTaylorBoundary
import ComputableAnalysis.PiProofs

namespace ComputableAnalysis.ArctanTaylor
open PiProofs

theorem term_numerator (x : Rat) (n : Nat) :
    (-x*x)^n*x = (-1:Rat)^n*x^(2*n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1=2*n+1+1+1 by omega]
    rw [Rat.pow_succ (-x*x), Rat.pow_succ (-1), Rat.pow_succ x, Rat.pow_succ x]
    grind only

theorem term_neg (x : Rat) (n : Nat) : term (-x) n = -term x n := by
  have he : -(-x)*(-x) = -x*x := by grind
  simp only [term,he,Rat.div_def]
  grind only

theorem partialSum_neg (x : Rat) (n : Nat) : partialSum (-x) n = -partialSum x n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih => rw [partialSum,partialSum,ih,term_neg]; grind only

theorem partialSum_kernel (x : Rat) (n : Nat) :
    partialSum x (n+1) = Taylor.ArctanKernel.kernelPartialIntegralBetween 0 x n := by
  induction n with
  | zero => simp [partialSum,term,Taylor.ArctanKernel.kernelPartialIntegralBetween]; grind
  | succ n ih =>
    rw [partialSum,ih,Taylor.ArctanKernel.kernelPartialIntegralBetween]
    simp only [term,term_numerator,Taylor.ArctanKernel.kernelTermIntegralBetween]
    have hz : (0:Rat)^(2*(n+1)+1)=0 := by rw [Rat.pow_succ]; simp
    rw [hz]
    grind only

theorem endpoints (x : Rat) (n : Nat) :
    partialSum x (2*n) = ArctanValidity.lo x n ∧
      partialSum x (2*n+1) = ArctanValidity.hi x n := by
  constructor
  · cases n with
    | zero => simp [partialSum,ArctanValidity.lo,ArctanValidity.state_zero]
    | succ n =>
      rw [show 2*(n+1)=2*n+1+1 by omega,partialSum_kernel]
      exact (ArctanValidity.endpoints_eq_kernelPartialIntegralBetween x n).2.symm
  · rw [partialSum_kernel]
    exact (ArctanValidity.endpoints_eq_kernelPartialIntegralBetween x n).1.symm

theorem sample_in_box {x : Rat} (hx : arctanDomain x) (n : Nat) :
    ((arctan x).compute (n/2)).lo ≤ partialSum x n ∧
      partialSum x n ≤ ((arctan x).compute (n/2)).hi := by
  have hnonneg (x : Rat) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
      ((arctan x).compute (n/2)).lo ≤ partialSum x n ∧
        partialSum x n ≤ ((arctan x).compute (n/2)).hi := by
    rw [ArctanValidity.arctan_compute_nonneg x hx0,
      qabs_eq_self_of_nonneg hx0]
    have he := endpoints x (n/2)
    have ho := ArctanValidity.interval_ordered hx0 (n/2)
    change ArctanValidity.lo x (n/2) ≤ _ ∧ _ ≤ ArctanValidity.hi x (n/2)
    have hn : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
    rcases hn with hn|hn
    · have hs : partialSum x n = ArctanValidity.lo x (n/2) := (congrArg (partialSum x) hn).trans he.1
      rw [hs]; exact ⟨Rat.le_refl,ho⟩
    · have hs : partialSum x n = ArctanValidity.hi x (n/2) := (congrArg (partialSum x) hn).trans he.2
      rw [hs]; exact ⟨ho,Rat.le_refl⟩
  by_cases hx0 : 0 ≤ x
  · exact hnonneg x hx0 hx.2
  · have hneg : x < 0 := by grind
    have hnx0 : 0 ≤ -x := by grind
    have hh := hnonneg (-x) hnx0 (show -x ≤ 1 by have := hx.1; grind)
    rw [ArctanValidity.arctan_compute_neg x hx0,qabs_eq_neg_of_nonpos (Rat.le_of_lt hneg)]
    rw [ArctanValidity.arctan_compute_nonneg (-x) hnx0,qabs_eq_self_of_nonneg hnx0] at hh
    rw [partialSum_neg] at hh
    change -ArctanValidity.hi (-x) (n/2) ≤ _ ∧ _ ≤ -ArctanValidity.lo (-x) (n/2)
    change ArctanValidity.lo (-x) (n/2) ≤ _ ∧ _ ≤ ArctanValidity.hi (-x) (n/2) at hh
    constructor <;> grind only

theorem series_converges {x : Rat} (hx : arctanDomain x) :
    ConvergesTo (partialSum x) (arctan x) := by
  have hv := ArctanValidity.validAt x hx
  refine ⟨hv,?_⟩
  intro eps
  obtain ⟨N,hN⟩ := hv.2.2 eps
  refine ⟨2*N,?_⟩
  intro n hn k
  have hs := sample_in_box hx n
  have hw := hN (n/2) (by omega)
  have hleft := hv.2.1 k (max k (n/2)) (Nat.le_max_left _ _)
  have hright := hv.2.1 (n/2) (max k (n/2)) (Nat.le_max_right _ _)
  simp only [QInterval.width] at *
  constructor <;> grind only

/-- Changing the algorithm representing the target does not change convergence. -/
theorem ConvergesTo.equiv {s : Nat → Rat} {v w : RealRaw}
    (h : ConvergesTo s v) (hw : w.Valid) (he : v.Equiv w) : ConvergesTo s w := by
  refine ⟨hw,?_⟩
  intro eps
  let e : QPos := ⟨eps.val/2, by have := eps.property; grind⟩
  obtain ⟨N,hN⟩ := h.2 e
  obtain ⟨K,hK⟩ := h.1.2.2 e
  refine ⟨N,?_⟩
  intro n hn j
  let k := max j K
  have hs := hN n hn k
  have hvw := (RealRaw.compareAt_overlap_iff v w k k).1 (he k)
  have hb := hw.2.1 j k (Nat.le_max_left _ _)
  have hv := hK k (Nat.le_max_right _ _)
  simp only [QInterval.width, QInterval.Overlaps,e] at *
  constructor <;> grind only

theorem geometric_converges {x : Rat} (hx : qabs x ≤ 1) :
    ConvergesTo (partialSum x) (ArctanGeometry.arctanGeom x) := by
  have hd : arctanDomain x := by
    have := neg_qabs_le_self x
    have := self_le_qabs x
    constructor <;> grind
  exact (series_converges hd).equiv
    (ArctanGeometry.arctanGeom_valid_on_powerSeriesDomain hx)
    (arctanEqualsGeom_finiteRiemannBridge_on_unit hx)

theorem convergence_iff (x : Rat) :
    (∃ v : RealRaw, ConvergesTo (partialSum x) v) ↔ qabs x ≤ 1 := by
  constructor
  · rintro ⟨v,hv⟩
    by_cases h : qabs x ≤ 1
    · exact h
    · exact False.elim (not_converges (by grind) v hv)
  · intro h
    exact ⟨_,geometric_converges h⟩

end ComputableAnalysis.ArctanTaylor
