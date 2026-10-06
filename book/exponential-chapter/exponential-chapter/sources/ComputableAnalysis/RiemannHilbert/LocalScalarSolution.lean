import ComputableAnalysis.RiemannHilbert.LocalODEIdentity

/-! Packaging internal radius and initial-value bounds for the scalar solution. -/
namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw FunctionTheory

def initialBound (initial : ComplexRaw) : Rat := boxCoordinateBound (initial.compute 0)

theorem initialBound_nonneg (initial : ComplexRaw) : 0 ≤ initialBound initial :=
  boxCoordinateBound_nonneg _

theorem initialBound_valid (initial : ComplexRaw) (h0 : initial.Valid) :
    Small initial (initialBound initial) := small_from_box initial h0 0

def solutionRadius (K : Rat) (hK : 0 ≤ K) : QPos :=
  ⟨1/(32*(K+1)), by
    have hd : 0 < 32*(K+1) := Rat.mul_pos (by decide) (by grind)
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 hd⟩

theorem solutionRadius_small (K : Rat) (hK : 0 ≤ K) :
    8*K*(solutionRadius K hK).val ≤ (1 : Rat)/2 := by
  have hd : 0 < 32*(K+1) := Rat.mul_pos (by decide) (by grind)
  have he : (solutionRadius K hK).val*(32*(K+1)) = 1 :=
    Rat.div_mul_cancel (Rat.ne_of_gt hd)
  have hpos := (solutionRadius K hK).property
  have hh : 8*K ≤ 16*(K+1) := by grind
  have hmul := Rat.mul_le_mul_of_nonneg_right hh (Rat.le_of_lt hpos)
  have he2 : 16*(K+1)*(solutionRadius K hK).val = (1 : Rat)/2 := by
    rw [Rat.div_def, Rat.one_mul]
    have ht : (2 : Rat)*(16*(K+1)*(solutionRadius K hK).val) = 1 := by grind
    have htwo : (2 : Rat)*(2 : Rat)⁻¹ = 1 :=
      Rat.mul_inv_cancel _ (by decide)
    grind
  rw [he2] at hmul
  exact hmul

def localSolution (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (M K : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : ∀ i, Small (a i) (M*K^i)) : CertifiedFunctions.Map :=
  seriesMap a initial ha h0 M (initialBound initial) K (solutionRadius K hK).val
    hM (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    hMK haB (initialBound_valid initial h0) (solutionRadius_small K hK)

def localSolution_holomorphic (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (M K : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : ∀ i, Small (a i) (M*K^i)) :
    CertifiedFunctions.Holomorphic (localSolution a initial ha h0 M K hM hK hMK haB) :=
  seriesMap_holomorphic a initial ha h0 M (initialBound initial) K (solutionRadius K hK).val
    hM (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    hMK haB (initialBound_valid initial h0) (solutionRadius_small K hK)

theorem localSolution_initial (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (M K : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : ∀ i, Small (a i) (M*K^i)) :
    ((localSolution a initial ha h0 M K hM hK hMK haB).eval ⟨zero, ofQComplex_valid _⟩).Equiv initial :=
  seriesMap_initial a initial ha h0 M (initialBound initial) K (solutionRadius K hK).val
    hM (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    hMK haB (initialBound_valid initial h0) (solutionRadius_small K hK)

theorem localSolution_center_mem (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (M K : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : ∀ i, Small (a i) (M*K^i)) :
    (localSolution a initial ha h0 M K hM hK hMK haB).domain ⟨zero, ofQComplex_valid _⟩ :=
  interior_zero _ (solutionRadius K hK).property

theorem localSolution_ode (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (M K : Rat)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K)
    (haB : ∀ i, Small (a i) (M*K^i)) (z : Scalar)
    (hz : (localSolution a initial ha h0 M K hM hK hMK haB).domain z) :
    ((localSolution_holomorphic a initial ha h0 M K hM hK hMK haB).derivative z).Equiv
      (mul (coefficientSum a z.val ha z.property M K (solutionRadius K hK).val)
        ((localSolution a initial ha h0 M K hM hK hMK haB).eval z)) :=
  seriesMap_ode a initial ha h0 M (initialBound initial) K (solutionRadius K hK).val
    hM (initialBound_nonneg initial) hK (Rat.le_of_lt (solutionRadius K hK).property)
    hMK haB (initialBound_valid initial h0) (solutionRadius_small K hK) z hz

/-- Neither representations nor the certified coefficient majorants affect
the constructed solution on the intersection of the two local domains. -/
theorem localSolution_congr (a b : Nat → ComplexRaw) (x y : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid) (hx : x.Valid) (hy : y.Valid)
    (hab : ∀ i, (a i).Equiv (b i)) (hxy : x.Equiv y)
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L)
    (haB : ∀ i, Small (a i) (M*K^i)) (hbB : ∀ i, Small (b i) (P*L^i))
    (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : (localSolution a x ha hx M K hM hK hMK haB).domain z)
    (hw : (localSolution b y hb hy P L hP hL hPL hbB).domain w) :
    ((localSolution a x ha hx M K hM hK hMK haB).eval z).Equiv
      ((localSolution b y hb hy P L hP hL hPL hbB).eval w) := by
  have hR := Rat.le_of_lt (solutionRadius K hK).property
  have hS := Rat.le_of_lt (solutionRadius L hL).property
  have hq : 2*K*(solutionRadius K hK).val ≤ (1 : Rat)/2 := by
    have := solutionRadius_small K hK
    have := Rat.mul_nonneg hK hR
    grind
  have hr : 2*L*(solutionRadius L hL).val ≤ (1 : Rat)/2 := by
    have := solutionRadius_small L hL
    have := Rat.mul_nonneg hL hS
    grind
  exact sumValue_congr_of_bounds a b x y z.val w.val ha hb hx hy z.property w.property
    hab hxy hzw M (initialBound x) K (solutionRadius K hK).val
    P (initialBound y) L (solutionRadius L hL).val
    hM (initialBound_nonneg x) hK hR hP (initialBound_nonneg y) hL hS hMK hPL haB hbB
    (initialBound_valid x hx) (initialBound_valid y hy)
    (interior_bound _ z hz) (interior_bound _ w hw) hq hr

end ComputableAnalysis.RiemannHilbert.LocalODE
