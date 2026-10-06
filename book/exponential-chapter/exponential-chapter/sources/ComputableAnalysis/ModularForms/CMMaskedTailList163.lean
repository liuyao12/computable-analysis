import ComputableAnalysis.ModularForms.CMMaskedShellList163
import ComputableAnalysis.ModularForms.CMMaskedTail163
import ComputableAnalysis.ModularForms.RepresentedSumAppend

/-! Uniform bounds for actual concatenated lists of selected tail terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def maskedTailTerms (keep : Nat → Nat → Bool) (w N : Nat) : Nat → List ComplexRaw
  | 0 => []
  | k+1 => maskedTailTerms keep w N k ++
      (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
        (shellTerm (N+k+1) (by omega) w))

theorem maskedTailTerms_valid (keep : Nat → Nat → Bool) (w N k : Nat) :
    ∀ z ∈ maskedTailTerms keep w N k, z.Valid := by
  induction k with
  | zero => simp [maskedTailTerms]
  | succ k ih =>
    intro z hz
    rcases List.mem_append.mp hz with h|h
    · exact ih z h
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      exact shellTerm_valid _ _ _ _

theorem maskedWeightFourTail_list_equiv (keep : Nat → Nat → Bool) (N k : Nat) :
    (LocalODE.sum (maskedTailTerms keep 4 N k)).Equiv (maskedWeightFourTailBlock keep N k) := by
  induction k with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ k ih =>
    let terms := (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
      (shellTerm (N+k+1) (by omega) 4))
    have ht : ∀ z ∈ terms, z.Valid := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact shellTerm_valid _ _ _ _
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (maskedTailTerms_valid keep 4 N (k+1)))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (maskedTailTerms_valid keep 4 N k))
        (LocalODE.sum_valid _ ht))
      (maskedWeightFourTailBlock_valid keep N (k+1))
      (representedSum_append _ terms (maskedTailTerms_valid keep 4 N k) ht)
      (ComplexRaw.add_equiv ih (ComplexRaw.equiv_symm
        (maskedShellSum_list_equiv (N+k+1) (by omega) 4 (keep (N+k+1)))))

theorem maskedWeightFourTail_list_uniform_small (keep : Nat → Nat → Bool) (N k : Nat)
    (hN : 0<N) : Small (LocalODE.sum (maskedTailTerms keep 4 N k))
      (weightFourTailConstant*reciprocalSquare N) :=
  Small.congr (maskedWeightFourTailBlock_valid keep N k)
    (LocalODE.sum_valid _ (maskedTailTerms_valid keep 4 N k))
    (ComplexRaw.equiv_symm (maskedWeightFourTail_list_equiv keep N k))
    (maskedWeightFourTailBlock_uniform_small keep N k hN)

theorem maskedWeightSixTail_list_equiv (keep : Nat → Nat → Bool) (N k : Nat) :
    (LocalODE.sum (maskedTailTerms keep 6 N k)).Equiv (maskedWeightSixTailBlock keep N k) := by
  induction k with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ k ih =>
    let terms := (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
      (shellTerm (N+k+1) (by omega) 6))
    have ht : ∀ z ∈ terms, z.Valid := by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact shellTerm_valid _ _ _ _
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (maskedTailTerms_valid keep 6 N (k+1)))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (maskedTailTerms_valid keep 6 N k))
        (LocalODE.sum_valid _ ht))
      (maskedWeightSixTailBlock_valid keep N (k+1))
      (representedSum_append _ terms (maskedTailTerms_valid keep 6 N k) ht)
      (ComplexRaw.add_equiv ih (ComplexRaw.equiv_symm
        (maskedShellSum_list_equiv (N+k+1) (by omega) 6 (keep (N+k+1)))))

theorem maskedWeightSixTail_list_uniform_small (keep : Nat → Nat → Bool) (N k : Nat)
    (hN : 0<N) : Small (LocalODE.sum (maskedTailTerms keep 6 N k))
      (weightSixTailConstant*reciprocalSquare N) :=
  Small.congr (maskedWeightSixTailBlock_valid keep N k)
    (LocalODE.sum_valid _ (maskedTailTerms_valid keep 6 N k))
    (ComplexRaw.equiv_symm (maskedWeightSixTail_list_equiv keep N k))
    (maskedWeightSixTailBlock_uniform_small keep N k hN)

end ComputableAnalysis.ModularForms
