import ComputableAnalysis.ModularForms.UpperFiniteRemainder
import ComputableAnalysis.ModularForms.UpperPowerRegionalRemainder

/-! Regional quadratic bounds for the actual finite-map point remainders. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem upperPointRemainder_nonzero (a : Scalar) (ha : InUpperHalfPlane a.val)
    (z : Scalar) (hz : InUpperHalfPlane z.val) (k : Nat)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    upperPointRemainder a ha z hz k u=latticePowerRemainder u hu a z ha hz k := by
  simp only [upperPointRemainder,latticePowerRemainder,DomainFunctions.remainder,
    upperPointMap,upperPointPower,dif_pos hu,upperPointMap_holomorphic,Holomorphic.transfer]
  rfl

theorem upperPointRemainder_region_bound
    (a z : Scalar) (ha : InUpperHalfPlane a.val) (hz : InUpperHalfPlane z.val)
    (R U eta : Rat) (A Z : Nat) (hR : 0≤R) (hU : 0≤U) (heta : 0<eta)
    (hregionA : LatticeRegionBox a R eta A) (hheightA : (a.val.compute A).hi.im≤U)
    (hregionZ : LatticeRegionBox z R eta Z) (hheightZ : (z.val.compute Z).hi.im≤U)
    (H : Rat) (hH : 0≤H) (hza : Small (sub z.val a.val) H)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) (k : Nat) :
    Small (upperPointRemainder a ha z hz k u)
      (powerRemainderCoefficient (latticeRegionReciprocalConstant R U eta) k*
        ((QuadraticOrder163.shellRadius u:Rat)⁻¹)^k*H*H) := by
  rw [upperPointRemainder_nonzero a ha z hz k u hu]
  exact latticePower_remainder_region_decay_bound a z ha hz R U eta A Z hR hU heta
    hregionA hheightA hregionZ hheightZ H hH hza u hu k

end ComputableAnalysis.ModularForms
