import ComputableAnalysis.ModularForms.CotangentNomeKernel
import ComputableAnalysis.ModularForms.LambertHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.DomainDerivativeInvariance

/-! Holomorphicity and an exact differential identity for the actual nome quotient kernel. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private def nomeKernelOpenData (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    ScalarTopology.OpenData (lambertOpenMap r hr hlocal).domain where
  invariant := (lambertOpenMap r hr hlocal).domain_congr
  radius := (lambertOpenMap_holomorphic r hr hlocal).openDomain.radius
  inside := (lambertOpenMap_holomorphic r hr hlocal).openDomain.inside

def cotangentNomeOpenMap (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) : DomainFunctions.Map :=
  sumOn (constantOn (lambertOpenMap r hr hlocal).domain
    (nomeKernelOpenData r hr hlocal).invariant ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩)
    (sumOn (lambertOpenMap r hr hlocal) (lambertOpenMap r hr hlocal) (fun _ h => h))
    (fun _ h => h)

theorem cotangentNomeOpenMap_eval (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (z : Scalar) (hz : (cotangentNomeOpenMap r hr hlocal).domain z) :
    ((cotangentNomeOpenMap r hr hlocal).eval z hz).val = cotangentNomeKernel z r := rfl

def cotangentNomeOpenMap_holomorphic (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2) :
    Holomorphic (cotangentNomeOpenMap r hr hlocal) :=
  (constantOn_holomorphic (nomeKernelOpenData r hr hlocal)
    ⟨ofQComplex QComplex.one,ofQComplex_valid _⟩).sumOn
    ((lambertOpenMap_holomorphic r hr hlocal).sumOn
      (lambertOpenMap_holomorphic r hr hlocal) (fun _ h => h)) (fun _ h => h)

def cotangentNomeDerivative (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) : Scalar :=
  scalarSum (lambertDiskDerivative z r hr hlocal hz) (lambertDiskDerivative z r hr hlocal hz)

theorem cotangentNomeOpenMap_derivative (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (z : Scalar) (hz : (cotangentNomeOpenMap r hr hlocal).domain z) :
    ((cotangentNomeOpenMap_holomorphic r hr hlocal).derivative z hz).val.Equiv
      (cotangentNomeDerivative z r hr hlocal (LocalODE.interior_bound r z hz)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ((cotangentNomeOpenMap_holomorphic r hr hlocal).derivative z hz).property)
    (hright := (cotangentNomeDerivative z r hr hlocal (LocalODE.interior_bound r z hz)).property)
  let D := ComplexRawQuotient.ofRaw (lambertDiskDerivative z r hr hlocal
    (LocalODE.interior_bound r z hz)).val
    (lambertDiskDerivative z r hr hlocal (LocalODE.interior_bound r z hz)).property
  change 0+(D+D)=D+D
  grind only

def cotangentNomeOpenMap_hasDerivativeAt (r : Rat) (hr : 0≤r) (hlocal : 2*r≤(1:Rat)/2)
    (z : Scalar) (hz : (cotangentNomeOpenMap r hr hlocal).domain z) :
    HasDerivativeAt (cotangentNomeOpenMap r hr hlocal) z hz
      (cotangentNomeDerivative z r hr hlocal (LocalODE.interior_bound r z hz)) :=
  ((cotangentNomeOpenMap_holomorphic r hr hlocal).atPoint z hz).congrDerivative
    (cotangentNomeOpenMap_derivative r hr hlocal z hz)

theorem cotangentNomeKernel_differential_identity (z : Scalar) (r : Rat) (hr : 0≤r)
    (hlocal : 2*r≤(1:Rat)/2) (hz : Small z.val r) :
    (add (mul z.val (cotangentNomeDerivative z r hr hlocal hz).val)
      (mul z.val (cotangentNomeDerivative z r hr hlocal hz).val)).Equiv
      (sub (mul (cotangentNomeKernel z r) (cotangentNomeKernel z r))
        (ofQComplex QComplex.one)) := by
  have vs := nomeGeometricSum_valid z r hr hlocal hz
  have vl := lambertFactor_valid z r hr hlocal hz
  have vk := cotangentNomeKernel_valid z r hr hlocal hz
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) vs)
    (hright := ofQComplex_valid _) (nomeGeometricSum_inverse z r hr hlocal hz)
  have hl := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (sub_valid (ofQComplex_valid _) z.property) vl)
    (hright := z.property) (lambertFactor_multiplication z r hr hlocal hz)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (mul_valid z.property (cotangentNomeDerivative z r hr hlocal hz).property)
      (mul_valid z.property (cotangentNomeDerivative z r hr hlocal hz).property))
    (hright := sub_valid (mul_valid vk vk) (ofQComplex_valid _))
  let Z := ComplexRawQuotient.ofRaw z.val z.property
  let S := ComplexRawQuotient.ofRaw (nomeGeometricSum z r) vs
  let L := ComplexRawQuotient.ofRaw (lambertFactor z r) vl
  change (1-Z)*S=1 at hi
  change (1-Z)*L=Z at hl
  change Z*(S*S+S*S)+Z*(S*S+S*S)=(1+(L+L))*(1+(L+L))-1
  grind only

end ComputableAnalysis.ModularForms
