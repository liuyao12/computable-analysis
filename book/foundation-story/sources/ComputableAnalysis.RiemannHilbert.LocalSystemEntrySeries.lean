import ComputableAnalysis.RiemannHilbert.LocalCoefficientFunction
import ComputableAnalysis.RiemannHilbert.SeriesMatrixFields

/-! Actual operator-series entries agree with scalar series formed from
their finite coefficient matrices. Both convergence bounds and radii may
differ. This connects the system solver to scalar Cauchy reconstruction. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE DomainFunctions
set_option autoImplicit false
variable {n : Nat}

theorem coefficientValueMap_entry_series
    (a : Nat → ValueMap (Fiber n) (Fiber n)) (M K : Rat) (hM : 0≤M) (hK : 0≤K)
    (haB : OperatorMajorant a M K) (p : Scalar) (c : Nat → ComplexRaw) (hc : ∀ k, (c k).Valid)
    (C L R : Rat) (hC : 0≤C) (hL : 0≤L) (hR : 0≤R)
    (hb : ∀ k, Small (c k) (C*L^k)) (hl : 8*L*R≤(1:Rat)/2) (i j : Fin n)
    (he : ∀ k, (((a k).eval (Fiber.basis i)).val j).Equiv (c k))
    (z : Scalar) (hz : Centered.domain p (solutionRadius K hK).val z) (hw : Centered.domain p R z) :
    (((coefficientValueMap a M K hM hK haB (Centered.offset p z) hz).eval (Fiber.basis i)).val j).Equiv
      ((CenteredSeries.function p c hc C L R hC hL hR hb hl).eval z hw).val := by
  have hleft : 2*K*(solutionRadius K hK).val≤(1:Rat)/2 := by
    have hs := solutionRadius_small K hK
    have hp := Rat.mul_nonneg hK (Rat.le_of_lt (solutionRadius K hK).property)
    grind only
  have hright : 2*L*R≤(1:Rat)/2 := by have hp := Rat.mul_nonneg hL hR; grind only
  exact coefficientSum_congr_of_bounds (fun k => ((a k).eval (Fiber.basis i)).val j) c
    (Centered.offset p z).val (Centered.offset p z).val (fun k => ((a k).eval (Fiber.basis i)).property j) hc
    (Centered.offset p z).property (Centered.offset p z).property he (equiv_refl _ (Centered.offset p z).property)
    (2*M*initialBound (Fiber.basis i)) K (solutionRadius K hK).val C L R
    (Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) hM) (initialBound_nonneg (Fiber.basis i))) hK
    (Rat.le_of_lt (solutionRadius K hK).property) hC hL hR
    (fun k => operatorCoefficient_bound a M K (initialBound (Fiber.basis i)) (initialBound_nonneg (Fiber.basis i))
      haB (Fiber.basis i) (initialBound_valid (Fiber.basis i)) k j)
    hb (interior_bound _ _ hz) (interior_bound _ _ hw) hleft hright

end ComputableAnalysis.RiemannHilbert.LocalSystem
