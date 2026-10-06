import ComputableAnalysis.ModularForms.CMWeightFourTailRate163
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Constructed represented weight-four lattice sum at the discriminant -163 CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory
set_option maxRecDepth 8192

private def blockValue (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (weightFourTailBlock N k) (weightFourTailBlock_valid N k)

private theorem blockValue_succ (N k : Nat) : blockValue N (k+1)=
    blockValue N k+ComplexRawQuotient.ofRaw
      (QuadraticOrder163.shellSum (N+k+1) (by omega) 4)
      (QuadraticOrder163.shellSum_valid _ _ _) := rfl

private theorem blockValue_split (N k : Nat) : blockValue 0 (N+k)=blockValue 0 N+blockValue N k := by
  induction k with
  | zero => change blockValue 0 N=blockValue 0 N+0; grind
  | succ k ih =>
    have he : N+(k+1)=(N+k)+1 := by omega
    rw [he,blockValue_succ,blockValue_succ,ih]
    have hidx : 0+(N+k)+1=N+k+1 := by omega
    simp only [hidx]
    grind

theorem weightFourPrefix_difference (N k : Nat) :
    (ComplexRaw.sub (weightFourTailBlock 0 (N+k)) (weightFourTailBlock 0 N)).Equiv
      (weightFourTailBlock N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (weightFourTailBlock_valid _ _) (weightFourTailBlock_valid _ _))
    (hright := weightFourTailBlock_valid _ _)
  change blockValue 0 (N+k)+ -blockValue 0 N=blockValue N k
  have h := blockValue_split N k
  grind

def weightFourPrefix (n : Nat) : ComplexRaw := weightFourTailBlock 0 (n+1)

theorem weightFourPrefix_valid (n : Nat) : (weightFourPrefix n).Valid := weightFourTailBlock_valid _ _

theorem weightFourPrefix_cauchy (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (weightFourPrefix n) (weightFourPrefix k)) (weightFourTailRate k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have h := weightFourPrefix_difference (k+1) (n-k)
  rw [he] at h
  exact Small.congr (weightFourTailBlock_valid _ _)
    (ComplexRaw.sub_valid (weightFourPrefix_valid n) (weightFourPrefix_valid k))
    (ComplexRaw.equiv_symm h) (weightFourTailBlock_uniform_small (k+1) (n-k) (by omega))

def weightFourLatticeSum163 : ComplexRaw :=
  RepresentedCauchySum.value weightFourPrefix weightFourPrefix_valid weightFourTailRate

theorem weightFourLatticeSum163_valid : weightFourLatticeSum163.Valid :=
  RepresentedCauchySum.value_valid _ _ _ weightFourTailRate_shrinks weightFourPrefix_cauchy

theorem weightFourLatticeSum163_close_prefix (N : Nat) :
    Small (ComplexRaw.sub weightFourLatticeSum163 (weightFourPrefix N)) (weightFourTailRate N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ weightFourPrefix_cauchy N

end ComputableAnalysis.ModularForms
