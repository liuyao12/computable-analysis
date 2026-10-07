import ComputableAnalysis.ModularForms.RepresentedSumFactor

/-! Exact finite-sum transformation for the actual CM-orbit reciprocal evaluator. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

abbrev NonzeroOrder163 := {u : QuadraticOrder163 // u≠zero}

def cmOrbitPowerTerm163 (g : SL2Z) (k : Nat) (u : NonzeroOrder163) : ComplexRaw :=
  LocalODE.power (cmOrbitLatticeInverse163 g u.val u.property).val k

def cmReindexedPowerTerm163 (g : SL2Z) (k : Nat) (u : NonzeroOrder163) : ComplexRaw :=
  LocalODE.power (complexInverse (basisIndex (latticeIndexMatrix g) u.val)
    (basisIndex_nonzero _ u.val u.property)).val k

/-- Every finite list of nonzero CM lattice indices satisfies the actual
weight transformation identity, with the denominator power outside the sum. -/
theorem cmOrbitFiniteSum163_transform (g : SL2Z) (k : Nat) (us : List NonzeroOrder163) :
    (LocalODE.sum (us.map (cmOrbitPowerTerm163 g k))).Equiv
      (ComplexRaw.mul (LocalODE.power (cmOrbitDenominator163 g).val k)
        (LocalODE.sum (us.map (cmReindexedPowerTerm163 g k)))) := by
  let c := LocalODE.power (cmOrbitDenominator163 g).val k
  have hc : c.Valid := LocalODE.power_valid _ (cmOrbitDenominator163 g).property k
  have hf (u : NonzeroOrder163) : (cmReindexedPowerTerm163 g k u).Valid :=
    LocalODE.power_valid _ (complexInverse _ _).property k
  have hv (f : NonzeroOrder163 → ComplexRaw) (h : ∀ u, (f u).Valid) :
      (LocalODE.sum (us.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact h u
  exact ComplexRaw.equiv_trans
    (hv _ (fun u => LocalODE.power_valid _ (cmOrbitLatticeInverse163 g u.val u.property).property k))
    (hv _ (fun u => ComplexRaw.mul_valid hc (hf u)))
    (ComplexRaw.mul_valid hc (hv _ hf))
    (representedSum_map_equiv us (cmOrbitPowerTerm163 g k)
      (fun u => ComplexRaw.mul c (cmReindexedPowerTerm163 g k u))
      (fun u => cmOrbitLatticeInverse163_power_transform g u.val u.property k))
    (representedSum_factor c hc (cmReindexedPowerTerm163 g k) hf us)

end ComputableAnalysis.ModularForms
