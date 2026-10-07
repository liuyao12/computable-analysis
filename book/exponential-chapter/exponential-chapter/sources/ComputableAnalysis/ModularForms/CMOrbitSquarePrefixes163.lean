import ComputableAnalysis.ModularForms.CMOrbitFiniteSum163
import ComputableAnalysis.ModularForms.LatticeBasisSum163

/-! Actual transformed reciprocal prefixes and their exact finite weight law. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

def cmOrbitPointPower163 (g : SL2Z) (k : Nat) (u : QuadraticOrder163) : ComplexRaw :=
  if hu : u≠zero then LocalODE.power (cmOrbitLatticeInverse163 g u hu).val k else ComplexRaw.zero

theorem cmOrbitPointPower163_valid (g : SL2Z) (k : Nat) (u : QuadraticOrder163) :
    (cmOrbitPointPower163 g k u).Valid := by
  unfold cmOrbitPointPower163
  split
  · exact LocalODE.power_valid _ (cmOrbitLatticeInverse163 _ _ _).property k
  · exact ComplexRaw.ofQComplex_valid _

theorem cmOrbitPointPower163_transform (g : SL2Z) (k : Nat) (u : QuadraticOrder163) :
    (cmOrbitPointPower163 g k u).Equiv
      (ComplexRaw.mul (LocalODE.power (cmOrbitDenominator163 g).val k)
        (pointPower k (basisIndex (latticeIndexMatrix g) u))) := by
  by_cases hu : u≠zero
  · simp only [cmOrbitPointPower163,pointPower,dif_pos hu,dif_pos (basisIndex_nonzero _ u hu)]
    exact cmOrbitLatticeInverse163_power_transform g u hu k
  · have hz : u=zero := by by_cases hz : u=zero; exact hz; exact False.elim (hu hz)
    subst u
    have hb : basisIndex (latticeIndexMatrix g) zero=zero := by
      apply QuadraticOrder163.ext <;> simp [basisIndex,zero]
    simp only [hb,cmOrbitPointPower163,pointPower,dif_neg (show ¬zero≠zero by simp)]
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ComplexRaw.ofQComplex_valid _)
      (hright := ComplexRaw.mul_valid
        (LocalODE.power_valid _ (cmOrbitDenominator163 g).property k) (ComplexRaw.ofQComplex_valid _))
    change (0:ScalarAlgebra.Value)=
      ComplexRawQuotient.ofRaw (LocalODE.power (cmOrbitDenominator163 g).val k)
        (LocalODE.power_valid _ (cmOrbitDenominator163 g).property k)*0
    grind

def cmOrbitSquarePrefix163 (g : SL2Z) (k n : Nat) : ComplexRaw :=
  LocalODE.sum ((squarePoints (basisComparisonFactor (latticeIndexMatrix g)*(n+1))).map
    (cmOrbitPointPower163 g k))

theorem cmOrbitSquarePrefix163_valid (g : SL2Z) (k n : Nat) : (cmOrbitSquarePrefix163 g k n).Valid := by
  apply LocalODE.sum_valid
  intro z hz
  obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
  exact cmOrbitPointPower163_valid g k u

theorem cmOrbitSquarePrefix163_transform (g : SL2Z) (k n : Nat) :
    (cmOrbitSquarePrefix163 g k n).Equiv
      (ComplexRaw.mul (LocalODE.power (cmOrbitDenominator163 g).val k)
        (basisReindexedPrefix (latticeIndexMatrix g) k n)) := by
  let us := squarePoints (basisComparisonFactor (latticeIndexMatrix g)*(n+1))
  let c := LocalODE.power (cmOrbitDenominator163 g).val k
  let f := fun u => pointPower k (basisIndex (latticeIndexMatrix g) u)
  have hc : c.Valid := LocalODE.power_valid _ (cmOrbitDenominator163 g).property k
  have hf (u : QuadraticOrder163) : (f u).Valid := pointPower_valid k _
  have hv (f : QuadraticOrder163 → ComplexRaw) (h : ∀ u, (f u).Valid) :
      (LocalODE.sum (us.map f)).Valid := by
    apply LocalODE.sum_valid
    intro z hz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hz
    exact h u
  have he := ComplexRaw.equiv_trans (cmOrbitSquarePrefix163_valid g k n)
    (hv _ (fun u => ComplexRaw.mul_valid hc (hf u)))
    (ComplexRaw.mul_valid hc (hv f hf))
    (representedSum_map_equiv us (cmOrbitPointPower163 g k)
      (fun u => ComplexRaw.mul c (f u)) (cmOrbitPointPower163_transform g k))
    (representedSum_factor c hc f hf us)
  simpa only [basisReindexedPrefix,List.map_map,Function.comp_def] using he

end ComputableAnalysis.ModularForms
