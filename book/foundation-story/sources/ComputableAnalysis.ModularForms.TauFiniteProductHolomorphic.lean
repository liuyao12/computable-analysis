import ComputableAnalysis.ModularForms.TauEulerNomeMap
import ComputableAnalysis.RiemannHilbert.DomainAffineFunction
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums
import ComputableAnalysis.RiemannHilbert.DomainUniformLimitContinuity

/-! Actual holomorphic witnesses for the literal finite Euler products. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def tauMapPower (f : DomainFunctions.Map) (n : Nat) : DomainFunctions.Map where
  domain := f.domain
  eval q hq := ⟨LocalODE.power (f.eval q hq).val n,
    LocalODE.power_valid _ (f.eval q hq).property n⟩
  domain_congr := f.domain_congr
  eval_congr q w hq hw he := LocalODE.power_congr _ _ (f.eval q hq).property
    (f.eval w hw).property (f.eval_congr q w hq hw he) n

def tauMapPower_holomorphic (f : DomainFunctions.Map) (hf : Holomorphic f) (n : Nat) :
    Holomorphic (tauMapPower f n) := by
  induction n with
  | zero =>
    let E : ScalarTopology.OpenData f.domain := {
      invariant := f.domain_congr, radius := hf.openDomain.radius, inside := hf.openDomain.inside }
    exact (constantOn_holomorphic E oneScalar).transfer (tauMapPower f 0)
      (fun _ h => h) { radius := hf.openDomain.radius, inside := hf.openDomain.inside } (fun q hq => equiv_refl _ (ofQComplex_valid _))
  | succ n ih =>
    exact (ih.productOn hf (fun _ h => h)).transfer (tauMapPower f (n+1))
      (fun _ h => h) { radius := hf.openDomain.radius, inside := hf.openDomain.inside } (fun q hq =>
        equiv_refl _ (mul_valid (LocalODE.power_valid _ (f.eval q hq).property n) (f.eval q hq).property))

def tauCoordinateMap : DomainFunctions.Map where
  domain _ := True
  eval q _ := q
  domain_congr _ _ _ := Iff.rfl
  eval_congr _ _ _ _ he := he

def tauCoordinateMap_holomorphic : Holomorphic tauCoordinateMap := by
  let Z : Scalar := ⟨zero,ofQComplex_valid _⟩
  let O := oneScalar
  let h := DomainFunctions.affine_holomorphic Z O
  exact h.transfer tauCoordinateMap (fun _ _ => trivial) { radius := h.openDomain.radius, inside := h.openDomain.inside } (fun q hq => by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ((DomainFunctions.affine Z O).eval q trivial).property) (hright := q.property)
    let Q := ComplexRawQuotient.ofRaw q.val q.property
    change 0+1*Q=Q
    grind only)

private def constantOne : DomainFunctions.Map :=
  constantOn (fun _ => True) (fun _ _ _ => Iff.rfl) oneScalar

private def constantOne_holomorphic : Holomorphic constantOne :=
  constantOn_holomorphic {
    invariant := fun _ _ _ => Iff.rfl
    radius := fun _ _ => unitError
    inside := fun _ _ _ _ => trivial } oneScalar

def tauEulerFactorMap (N : Nat) : DomainFunctions.Map :=
  sumOn constantOne (negate (tauMapPower tauCoordinateMap (N+1))) (fun _ _ => trivial)

def tauEulerFactorMap_holomorphic (N : Nat) : Holomorphic (tauEulerFactorMap N) :=
  constantOne_holomorphic.sumOn ((tauMapPower_holomorphic tauCoordinateMap tauCoordinateMap_holomorphic (N+1)).negate)
    (fun _ _ => trivial)

/-- The actual finite-product evaluator, on the entire represented complex plane. -/
def finiteDiscriminantEulerMap (N : Nat) : DomainFunctions.Map where
  domain _ := True
  eval q _ := finiteDiscriminantEulerProduct q N
  domain_congr _ _ _ := Iff.rfl
  eval_congr q w _ _ he := finiteDiscriminantEulerProduct_congr q w he N

/-- Genuine derivative and derivative-continuity data for every finite product. -/
def finiteDiscriminantEulerMap_holomorphic (N : Nat) : Holomorphic (finiteDiscriminantEulerMap N) := by
  induction N with
  | zero =>
    exact constantOne_holomorphic.transfer (finiteDiscriminantEulerMap 0)
      (fun _ _ => trivial) constantOne_holomorphic.openDomain
      (fun q hq => equiv_refl _ (ofQComplex_valid _))
  | succ N ih =>
    let hF := tauMapPower_holomorphic (tauEulerFactorMap N) (tauEulerFactorMap_holomorphic N) 24
    let hP := ih.productOn hF (fun _ _ => trivial)
    exact hP.transfer (finiteDiscriminantEulerMap (N+1)) (fun _ _ => trivial)
      { radius := ih.openDomain.radius, inside := ih.openDomain.inside }
      (fun q hq => equiv_refl _ (finiteDiscriminantEulerProduct q (N+1)).property)

/-- Actual continuity follows from the uniform shrinking errors and finite
holomorphic prefixes. Selection of a prefix in this witness is proof-only. -/
theorem tauEulerNomeMap_continuous : Nonempty (ContinuousOn tauEulerNomeDomain tauEulerNomeMap.eval) := by
  let p := fun N q (_ : tauEulerNomeDomain q) => finiteDiscriminantEulerProduct q N
  have hp : ∀ N, ContinuousOn tauEulerNomeDomain (p N) := fun N =>
    restrictContinuous (finiteDiscriminantEulerMap N).eval
      (finiteDiscriminantEulerMap_holomorphic N).continuous (fun _ _ => trivial)
  exact ⟨continuousOn_of_uniform_prefixes tauEulerNomeMap.eval p hp
    (tauEulerProductTail (1/1024))
    (tauEulerProductTail_shrinks (1/1024) (by decide +kernel) Rat.le_refl)
    (fun N q hq => tauEulerProduct_close_prefix q (1/1024) (by decide +kernel)
      Rat.le_refl (LocalODE.interior_bound _ q hq) N)⟩

end ComputableAnalysis.ModularForms
