import ComputableAnalysis.ModularForms.CMWeightSixTailRate163
import ComputableAnalysis.RiemannHilbert.RepresentedCauchySum

/-! Constructed represented weight-six lattice sum at the discriminant -163 CM point. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory
set_option maxRecDepth 8192

-- Keep lattice sums symbolic during the finite additive proofs below.
@[irreducible] private def blockValue (N k : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw (weightSixTailBlock N k) (weightSixTailBlock_valid N k)

private theorem blockValue_succ (N k : Nat) : blockValue N (k+1)=
    blockValue N k+ComplexRawQuotient.ofRaw
      (QuadraticOrder163.shellSum (N+k+1) (by omega) 6)
      (QuadraticOrder163.shellSum_valid _ _ _) := by
  unfold blockValue
  rfl

private theorem blockValue_split (N k : Nat) : blockValue 0 (N+k)=blockValue 0 N+blockValue N k := by
  induction k with
  | zero =>
    have hzero : blockValue N 0=0 := by unfold blockValue; rfl
    simp only [Nat.add_zero,hzero]
    exact (ComplexRawQuotient.add_zero _).symm
  | succ k ih =>
    have he : N+(k+1)=(N+k)+1 := by omega
    rw [he,blockValue_succ,blockValue_succ,ih]
    have hidx : 0+(N+k)+1=N+k+1 := by omega
    simp only [hidx]
    exact ComplexRawQuotient.add_assoc _ _ _

theorem weightSixPrefix_difference (N k : Nat) :
    (ComplexRaw.sub (weightSixTailBlock 0 (N+k)) (weightSixTailBlock 0 N)).Equiv
      (weightSixTailBlock N k) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := ComplexRaw.sub_valid (weightSixTailBlock_valid _ _) (weightSixTailBlock_valid _ _))
    (hright := weightSixTailBlock_valid _ _)
  have he : blockValue 0 (N+k)+ -blockValue 0 N=blockValue N k := by
    rw [blockValue_split N k,ComplexRawQuotient.add_comm (blockValue 0 N) (blockValue N k)]
    exact ScalarAlgebra.sub_add_cancel (blockValue N k) (blockValue 0 N)
  change ComplexRawQuotient.ofRaw (weightSixTailBlock 0 (N+k)) (weightSixTailBlock_valid _ _) +
    -ComplexRawQuotient.ofRaw (weightSixTailBlock 0 N) (weightSixTailBlock_valid _ _) =
      ComplexRawQuotient.ofRaw (weightSixTailBlock N k) (weightSixTailBlock_valid _ _)
  simpa only [blockValue] using he

def weightSixPrefix (n : Nat) : ComplexRaw := weightSixTailBlock 0 (n+1)

theorem weightSixPrefix_valid (n : Nat) : (weightSixPrefix n).Valid := weightSixTailBlock_valid _ _

theorem weightSixPrefix_cauchy (k n : Nat) (hkn : k≤n) :
    Small (ComplexRaw.sub (weightSixPrefix n) (weightSixPrefix k)) (weightSixTailRate k) := by
  have he : (k+1)+(n-k)=n+1 := by omega
  have h := weightSixPrefix_difference (k+1) (n-k)
  rw [he] at h
  exact Small.congr (weightSixTailBlock_valid _ _)
    (ComplexRaw.sub_valid (weightSixPrefix_valid n) (weightSixPrefix_valid k))
    (ComplexRaw.equiv_symm h) (weightSixTailBlock_uniform_small (k+1) (n-k) (by omega))

def weightSixLatticeSum163 : ComplexRaw :=
  RepresentedCauchySum.value weightSixPrefix weightSixPrefix_valid weightSixTailRate

theorem weightSixLatticeSum163_valid : weightSixLatticeSum163.Valid :=
  RepresentedCauchySum.value_valid _ _ _ weightSixTailRate_shrinks weightSixPrefix_cauchy

theorem weightSixLatticeSum163_close_prefix (N : Nat) :
    Small (ComplexRaw.sub weightSixLatticeSum163 (weightSixPrefix N)) (weightSixTailRate N) :=
  RepresentedCauchySum.value_close_prefix _ _ _ weightSixPrefix_cauchy N

end ComputableAnalysis.ModularForms
