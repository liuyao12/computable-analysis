import ComputableAnalysis.ModularForms.TauPowerDerivative
import ComputableAnalysis.ModularForms.LambertHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicComposition

/-! Actual Lambert monomial values are holomorphic on the nome disk. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

private theorem power_inside (q : Scalar) (hq : tauEulerNomeDomain q) (N : Nat) :
    LocalODE.interior (1/4) (nomePowerScalar q N) := by
  refine ⟨nomePowerRadius (1/1024) N, nomePowerRadius_nonneg _ (by decide +kernel) N, ?_,
    nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N⟩
  have h := tauEulerGeometricPower_le_first (2*(1/1024:Rat))
    (by decide +kernel) (by decide +kernel) N
  have hh : (2*(1/1024:Rat)) < 1/4 := by decide +kernel
  change (2*(1/1024:Rat))^(N+1) < 1/4
  grind only

def tauLambertPowerMap (N : Nat) : DomainFunctions.Map where
  domain := tauEulerNomeDomain
  eval q hq := ⟨nomeLambertPower q (1/1024) N,
    nomeLambertPower_valid q _ (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ q hq) N⟩
  domain_congr := tauEulerNomeDomain_openData.invariant
  eval_congr q w hq hw he := nomeLambertPower_congr q w (1/1024) (1/1024)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalODE.interior_bound _ q hq) (LocalODE.interior_bound _ w hw) he N

def tauLambertPowerMap_holomorphic (N : Nat) : Holomorphic (tauLambertPowerMap N) := by
  let f := lambertOpenMap (1/4) (by decide +kernel) (by decide +kernel)
  let g := tauMapPower tauCoordinateMap (N+1)
  let hf := lambertOpenMap_holomorphic (1/4) (by decide +kernel) (by decide +kernel)
  let hg := tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)
  exact (hf.compose hg).transfer (tauLambertPowerMap N)
    (fun q hq => ⟨trivial, power_inside q hq N⟩)
    ⟨tauEulerNomeDomain_openData.radius,tauEulerNomeDomain_openData.inside⟩
    (fun q hq => lambertFactor_congr (nomePowerScalar q N) (nomePowerScalar q N)
      (1/4) (nomePowerRadius (1/1024) N) (by decide +kernel)
      (nomePowerRadius_nonneg _ (by decide +kernel) N) (by decide +kernel)
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
      (LocalODE.interior_bound _ _ (power_inside q hq N))
      (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)
      (equiv_refl _ (nomePowerScalar q N).property))

/-- The chain-rule derivative uses the actual Lambert derivative at its own power radius. -/
theorem tauLambertPowerMap_derivative (N : Nat) (q : Scalar) (hq : tauEulerNomeDomain q) :
    ((tauLambertPowerMap_holomorphic N).derivative q hq).val.Equiv
      (mul (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius (1/1024) N)
        (nomePowerRadius_nonneg _ (by decide +kernel) N)
        (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
        (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)).val
        ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).val) := by
  have hd := lambertDiskDerivative_congr (nomePowerScalar q N) (nomePowerScalar q N)
    (1/4) (nomePowerRadius (1/1024) N) (by decide +kernel)
    (nomePowerRadius_nonneg _ (by decide +kernel) N) (by decide +kernel)
    (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
    (LocalODE.interior_bound _ _ (power_inside q hq N))
    (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)
    (equiv_refl _ (nomePowerScalar q N).property)
  exact mul_equiv
    (lambertDiskDerivative (nomePowerScalar q N) (1/4) (by decide +kernel) (by decide +kernel)
      (LocalODE.interior_bound _ _ (power_inside q hq N))).property
    (lambertDiskDerivative (nomePowerScalar q N) (nomePowerRadius (1/1024) N)
      (nomePowerRadius_nonneg _ (by decide +kernel) N)
      (nomePowerRadius_local _ (by decide +kernel) (by decide +kernel) N)
      (nomePowerScalar_small q _ (by decide +kernel) (LocalODE.interior_bound _ q hq) N)).property
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property
    ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property
    hd (equiv_refl _ ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).derivative q trivial).property)

end ComputableAnalysis.ModularForms
