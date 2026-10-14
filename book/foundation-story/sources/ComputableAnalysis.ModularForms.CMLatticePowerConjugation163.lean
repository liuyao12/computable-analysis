import ComputableAnalysis.ModularForms.CMLatticeInverseConjugation163
import ComputableAnalysis.RiemannHilbert.LocalODESum
import ComputableAnalysis.FTA.Algebra

/-! Conjugation of the actual inverse-power terms of the CM lattice sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert

/-- Natural powers commute with conjugation for every valid represented value. -/
theorem representedPower_conjugate (z : ComplexRaw) (hz : z.Valid) (k : Nat) :
    (ComplexRaw.conj (LocalODE.power z k)).Equiv
      (LocalODE.power (ComplexRaw.conj z) k) := by
  induction k with
  | zero =>
    change (ComplexRaw.conj ComplexRaw.one).Equiv ComplexRaw.one
    intro n
    apply (ComplexRaw.compareAt_overlap_iff _ _ n n).mpr
    change (⟨(1:Rat),0⟩ : QComplex) ≤ ⟨1,0⟩ ∧ (⟨(1:Rat),0⟩ : QComplex) ≤ ⟨1,0⟩
    decide +kernel
  | succ k ih =>
    have hmul := RepresentedPolynomial.conj_mul
      (⟨LocalODE.power z k,LocalODE.power_valid z hz k⟩ : ComplexCert)
      (⟨z,hz⟩ : ComplexCert)
    exact ComplexRaw.equiv_trans
      (ComplexRaw.conj_valid _ (LocalODE.power_valid z hz (k+1)))
      (ComplexRaw.mul_valid (ComplexRaw.conj_valid _ (LocalODE.power_valid z hz k))
        (ComplexRaw.conj_valid _ hz))
      (LocalODE.power_valid _ (ComplexRaw.conj_valid _ hz) (k+1)) hmul
      (ComplexRaw.mul_equiv (ComplexRaw.conj_valid _ (LocalODE.power_valid z hz k))
        (LocalODE.power_valid _ (ComplexRaw.conj_valid _ hz) k)
        (ComplexRaw.conj_valid _ hz) (ComplexRaw.conj_valid _ hz) ih
        (ComplexRaw.equiv_refl _ (ComplexRaw.conj_valid _ hz)))

namespace QuadraticOrder163

/-- Conjugation of every lattice term is the term at the conjugate lattice point. -/
theorem complexInverse_power_conjugate (u : QuadraticOrder163) (hu : u≠zero) (k : Nat) :
    (ComplexRaw.conj (LocalODE.power (complexInverse u hu).val k)).Equiv
      (LocalODE.power (complexInverse (conjugate u) (conjugate_nonzero u hu)).val k) := by
  exact ComplexRaw.equiv_trans
    (ComplexRaw.conj_valid _ (LocalODE.power_valid _ (complexInverse u hu).property k))
    (LocalODE.power_valid _ (ComplexRaw.conj_valid _ (complexInverse u hu).property) k)
    (LocalODE.power_valid _ (complexInverse (conjugate u) (conjugate_nonzero u hu)).property k)
    (representedPower_conjugate _ (complexInverse u hu).property k)
    (LocalODE.power_congr _ _ (ComplexRaw.conj_valid _ (complexInverse u hu).property)
      (complexInverse (conjugate u) (conjugate_nonzero u hu)).property
      (complexInverse_conjugate u hu) k)

end QuadraticOrder163
end ComputableAnalysis.ModularForms
