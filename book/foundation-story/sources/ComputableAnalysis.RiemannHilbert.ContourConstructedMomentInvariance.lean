import ComputableAnalysis.RiemannHilbert.ContourPowerDeformation

/-! Every certified enclosing rectangle converges to the constructed local
moment. Different local holomorphy witnesses and equivalent pole names give
the same exact represented value at every order. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem fixedRectanglePowerContour_transfer_limit (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J K : QInterval × QInterval)
    (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (hK : ∀ z, representedRectangleContains K z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (hc : RectanglePoleInterior K b) (m : Nat)
    (u : Scalar) (hu : Converges (fixedRectanglePowerContour f K hK b hc m) u) :
    Converges (fixedRectanglePowerContour f J hJ b hb m) u := by
  let H := commonRectangle K J
  let hH := commonRectangle_domain f K J hK
  let hp := commonRectangle_pole_inside K J b hc hb
  let G := commonRectangleRibbon K J b hc hb
  let G' : RectangleRibbon := {
    outer := J
    inner := H
    xLo := by dsimp [H,commonRectangle]; grind
    xOrder := (rectanglePoleInterior_ordered H b hp).1
    xHi := by dsimp [H,commonRectangle]; grind
    yLo := by dsimp [H,commonRectangle]; grind
    yOrder := (rectanglePoleInterior_ordered H b hp).2
    yHi := by dsimp [H,commonRectangle]; grind }
  have hcommon : Converges (fixedRectanglePowerContour f H hH b hp m) u := by
    apply converge_perturbation _ _ u hu
    intro eps
    obtain ⟨N,hN⟩ := fixedRectanglePowerContour_nested_difference f hf G hK hH b hc hp m eps
    exact ⟨N,fun n hn => RepresentedCauchySum.small_sub_symm _ _ _ (hN n hn)⟩
  exact converge_perturbation _ _ u hcommon
    (fixedRectanglePowerContour_nested_difference f hf G' hJ hH b hb hp m)

theorem fixedRectanglePowerContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (m : Nat) :
    Converges (fixedRectanglePowerContour f J hJ b hb m) (effectiveLocalPowerValue f hf b ha m) :=
  fixedRectanglePowerContour_transfer_limit f hf J (effectiveLocalRectangle f hf b ha) hJ
    (effectiveLocalRectangle_domain f hf b ha) b hb (effectiveLocalRectangle_pole_inside f hf b ha) m _
    (effectiveLocalPowerValue_converges f hf b ha m)

theorem effectiveLocalPowerValue_congr (f : DomainFunctions.Map) (hf hg : Holomorphic f) (b c : Scalar)
    (hb : f.domain b) (hc : f.domain c) (he : b≈c) (m : Nat) :
    effectiveLocalPowerValue f hf b hb m≈effectiveLocalPowerValue f hg c hc m := by
  let J := effectiveLocalRectangle f hf b hb
  let hJ := effectiveLocalRectangle_domain f hf b hb
  let hp := effectiveLocalRectangle_pole_inside f hf b hb
  let hpc := rectanglePoleInterior_congr J b c he hp
  have hu : Converges (fixedRectanglePowerContour f J hJ c hpc m) (effectiveLocalPowerValue f hf b hb m) :=
    converge_congr _ _ _ (effectiveLocalPowerValue_converges f hf b hb m)
      (fun n => fixedRectanglePowerContour_pole_congr f J hJ b c hp hpc he m n)
  exact fixedRectanglePowerContour_rectangles_agree f hf J (effectiveLocalRectangle f hg c hc) hJ
    (effectiveLocalRectangle_domain f hg c hc) c hpc (effectiveLocalRectangle_pole_inside f hg c hc) m _ _ hu
    (effectiveLocalPowerValue_converges f hg c hc m)

theorem localCauchyMoment_congr (f : DomainFunctions.Map) (hf hg : Holomorphic f) (b c : Scalar)
    (hb : f.domain b) (hc : f.domain c) (he : b≈c) (k : Nat) :
    localCauchyMoment f hf b hb k≈localCauchyMoment f hg c hc k :=
  mul_equiv inverseGeometricPeriod.property inverseGeometricPeriod.property
    (effectiveLocalPowerValue f hf b hb (k+1)).property (effectiveLocalPowerValue f hg c hc (k+1)).property
    (equiv_refl _ inverseGeometricPeriod.property) (effectiveLocalPowerValue_congr f hf hg b c hb hc he (k+1))

def normalizedFixedRectangleMomentContour (f : DomainFunctions.Map) (J : QInterval × QInterval)
    (hJ : ∀ z, representedRectangleContains J z → f.domain z) (b : Scalar)
    (hb : RectanglePoleInterior J b) (k n : Nat) : Scalar :=
  scalarProduct inverseGeometricPeriod (fixedRectanglePowerContour f J hJ b hb (k+1) n)

theorem normalizedFixedRectangleMomentContour_converges (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (k : Nat) :
    Converges (normalizedFixedRectangleMomentContour f J hJ b hb k) (localCauchyMoment f hf b ha k) :=
  converge_product_left inverseGeometricPeriod _ _ (fixedRectanglePowerContour_converges f hf J hJ b hb ha (k+1))

theorem normalizedFixedRectangleMomentContour_limit_identity (f : DomainFunctions.Map) (hf : Holomorphic f)
    (J : QInterval × QInterval) (hJ : ∀ z, representedRectangleContains J z → f.domain z)
    (b : Scalar) (hb : RectanglePoleInterior J b) (ha : f.domain b) (k : Nat) (u : Scalar)
    (hu : Converges (normalizedFixedRectangleMomentContour f J hJ b hb k) u) : u≈localCauchyMoment f hf b ha k :=
  converge_unique _ _ _ hu (normalizedFixedRectangleMomentContour_converges f hf J hJ b hb ha k)

end ComputableAnalysis.RiemannHilbert.RectangularContour
