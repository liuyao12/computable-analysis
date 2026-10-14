import ComputableAnalysis.ModularForms.PairedDivisionQuadraticPiNormalization
import ComputableAnalysis.ModularForms.UpperHorizontalRowSums
import ComputableAnalysis.ModularForms.UpperEvenLatticeRows

/-! Exact rational values of actual horizontal lattice-point powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

/-- Actual powers of rational real names agree with their rational powers. -/
theorem rationalReal_power (r : Rat) (k : Nat) :
    (LocalODE.power (ofQComplex ⟨r,0⟩) k).Equiv (ofQComplex ⟨r^k,0⟩) := by
  induction k with
  | zero =>
    rw [Rat.pow_zero]
    exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih =>
    have h1 := mul_equiv (LocalODE.power_valid _ (ofQComplex_valid _) k) (ofQComplex_valid _)
      (ofQComplex_valid ⟨r,0⟩) (ofQComplex_valid ⟨r,0⟩) ih (equiv_refl (ofQComplex ⟨r,0⟩) (ofQComplex_valid _))
    have h2 := rationalRealProduct_equiv (r^k) r
    rw [Rat.pow_succ]
    exact equiv_trans (LocalODE.power_valid _ (ofQComplex_valid _) (k+1))
      (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _) h1 h2

/-- The actual inverse at every nonzero horizontal lattice point is rational. -/
theorem latticeInverse_horizontal (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Int) (hn : n≠0) :
    (latticeInverse z hz ⟨n,0⟩ (by intro h; exact hn (congrArg QuadraticOrder163.x h))).val.Equiv
      (ofQComplex ⟨(n:Rat)⁻¹,0⟩) := by
  have hu : (⟨n,0⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
    intro h
    exact hn (congrArg QuadraticOrder163.x h)
  have hv : (latticeVector z ⟨n,0⟩).val.Equiv (ofQComplex ⟨(n:Rat),0⟩) := integerAffine_zero n z
  have hnon : (n:Rat)≠0 := by exact_mod_cast hn
  have hp := rationalRealProduct_equiv (n:Rat) ((n:Rat)⁻¹)
  rw [Rat.mul_inv_cancel (n:Rat) hnon] at hp
  apply RepresentedReciprocal.inverse_unique (latticeVector z ⟨n,0⟩)
    (latticeVector_nonzero z hz ⟨n,0⟩ hu) ⟨ofQComplex ⟨(n:Rat)⁻¹,0⟩,ofQComplex_valid _⟩
  exact equiv_trans (mul_valid (latticeVector z ⟨n,0⟩).property (ofQComplex_valid _))
    (mul_valid (ofQComplex_valid _) (ofQComplex_valid _)) (ofQComplex_valid _)
    (mul_equiv (latticeVector z ⟨n,0⟩).property (ofQComplex_valid _)
      (ofQComplex_valid _) (ofQComplex_valid _) hv (equiv_refl _ (ofQComplex_valid _))) hp

/-- Actual horizontal lattice-point powers have their exact rational values. -/
theorem upperPointPower_horizontal (z : Scalar) (hz : InUpperHalfPlane z.val)
    (n : Int) (hn : n≠0) (k : Nat) :
    (upperPointPower z hz k ⟨n,0⟩).Equiv (ofQComplex ⟨((n:Rat)⁻¹)^k,0⟩) := by
  have hu : (⟨n,0⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
    intro h
    exact hn (congrArg QuadraticOrder163.x h)
  have he := latticeInverse_horizontal z hz n hn
  have hpow := LocalODE.power_congr _ _ (latticeInverse z hz ⟨n,0⟩ hu).property (ofQComplex_valid _) he k
  simp only [upperPointPower,dif_pos hu]
  exact equiv_trans (LocalODE.power_valid _ (latticeInverse z hz ⟨n,0⟩ hu).property k)
    (LocalODE.power_valid _ (ofQComplex_valid _) k) (ofQComplex_valid _) hpow (rationalReal_power _ k)

end ComputableAnalysis.ModularForms
