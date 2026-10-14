import ComputableAnalysis.ModularForms.DiskLambertPolynomialBridge
import ComputableAnalysis.RiemannHilbert.BoundedHolomorphicSequenceLimit

/-! Holomorphicity of the full-disk extension of the primary rational Lambert
function. Finite polynomial laws, uniform rational errors and the checked
represented-input bridge construct local Cauchy derivative witnesses. -/
namespace ComputableAnalysis.ModularForms.DiskLambert
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions RationalLambert CauchyTaylor EisensteinDiskPatches
set_option maxHeartbeats 1000000

def map (k : Nat) : DomainFunctions.Map where
  domain := EisensteinUnitDisk.domain
  eval q hq := ⟨value q hq k,value_valid q hq k⟩
  domain_congr := EisensteinUnitDisk.invariant
  eval_congr q z hq hz he := value_congr q z hq hz he k

def patchMap (P : Patch) (k : Nat) : DomainFunctions.Map :=
  onDomain (map k) (openData P).invariant (included P)
def patchPolynomial (P : Patch) (k N : Nat) : DomainFunctions.Map :=
  onDomain (polynomialMap k N (cutoff (EisensteinDiskPatches.radius P) k+N)) (openData P).invariant (fun _ _ => trivial)
def patchPolynomial_holomorphic (P : Patch) (k N : Nat) : Holomorphic (patchPolynomial P k N) :=
  (polynomialMap_holomorphic k N (cutoff (EisensteinDiskPatches.radius P) k+N)).onDomain (openData P) (fun _ _ => trivial)

theorem patch_holomorphic_exists (P : Patch) (k : Nat) : Nonempty (Holomorphic (patchMap P k)) := by
  let r := EisensteinDiskPatches.radius P
  have hr : 0≤r := Rat.le_of_lt (radius_pos P)
  have hr1 : r<1 := radius_lt_one P
  let e := polynomialError r k
  let B : QPos := ⟨2*budget r k+1,by have := budget_nonneg r hr hr1 k; grind only⟩
  apply BoundedHolomorphicSequenceLimit.exists_holomorphic (patchMap P k) (patchPolynomial P k)
    (fun _ => rfl) (patchPolynomial_holomorphic P k) B
    (fun N q hq => (polynomial_patch_bound P q hq k N (cutoff r k+N)).mono (by dsimp [B]; grind only))
    (fun N => 2*e N) e
    (RepresentedCauchySum.twice_shrinks e (polynomialError_shrinks r hr hr1 k))
    (polynomialError_shrinks r hr hr1 k)
    (fun N => Rat.mul_nonneg (by decide +kernel) (polynomialError_nonneg r hr hr1 k N))
  · intro N L hNL q hL hN
    have hleft := RepresentedCauchySum.small_sub_symm _ _ _ (value_polynomial_close P q hL k L)
    have hright := value_polynomial_close P q hN k N
    have hb := triangle _ _ _ ((patchPolynomial P k L).eval q hL).property
      ((patchMap P k).eval q hN).property ((patchPolynomial P k N).eval q hN).property _ _ hleft hright
    have he := polynomialError_antitone r hr hr1 k N L hNL
    exact hb.mono (by change e L+e N≤2*e N; dsimp [e] at *; grind only)
  · exact fun N q hf _ => value_polynomial_close P q hf k N

noncomputable def patch_holomorphic (P : Patch) (k : Nat) : Holomorphic (patchMap P k) :=
  Classical.choice (patch_holomorphic_exists P k)

/-- Actual holomorphicity on the entire open Euclidean unit disk. No
holomorphicity, derivative or Cauchy identity is assumed for the limit. -/
noncomputable def holomorphic (k : Nat) : Holomorphic (map k) := by
  let P := fun q hq => Classical.choose (covers q hq)
  have mem := fun q hq => Classical.choose_spec (covers q hq)
  exact holomorphic_of_local (map k) (fun q hq => patchMap (P q hq) k)
    (fun q hq => patch_holomorphic (P q hq) k) mem
    (fun q hq => included (P q hq)) (fun q hq z hz => equiv_refl _ (value_valid z (included (P q hq) z hz) k))
end ComputableAnalysis.ModularForms.DiskLambert
