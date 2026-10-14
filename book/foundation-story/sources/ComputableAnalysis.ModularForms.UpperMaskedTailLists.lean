import ComputableAnalysis.ModularForms.UpperMaskedShellLists
import ComputableAnalysis.ModularForms.UpperMaskedTails
import ComputableAnalysis.ModularForms.RepresentedSumAppend

/-! Uniform bounds for actual concatenated lists of selected tail terms. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory QuadraticOrder163

def upperMaskedTailTerms (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (w N : Nat) : Nat → List ComplexRaw
  | 0 => []
  | k+1 => upperMaskedTailTerms z hz keep w N k ++
      (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
        (upperShellTerm z hz (N+k+1) (by omega) w))

theorem upperMaskedTailTerms_valid (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (w N k : Nat) :
    ∀ zz ∈ upperMaskedTailTerms z hz keep w N k, zz.Valid := by
  induction k with
  | zero => simp [upperMaskedTailTerms]
  | succ k ih =>
    intro zz hzz
    rcases List.mem_append.mp hzz with h|h
    · exact ih zz h
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
      exact upperShellTerm_valid z hz _ _ _ _

theorem upperMaskedWeightFourTail_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) :
    (LocalODE.sum (upperMaskedTailTerms z hz keep 4 N k)).Equiv (upperMaskedWeightFourTailBlock z hz keep N k) := by
  induction k with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ k ih =>
    let terms := (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
      (upperShellTerm z hz (N+k+1) (by omega) 4))
    have ht : ∀ zz ∈ terms, zz.Valid := by
      intro zz hzz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
      exact upperShellTerm_valid z hz _ _ _ _
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 4 N (k+1)))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 4 N k))
        (LocalODE.sum_valid _ ht))
      (upperMaskedWeightFourTailBlock_valid z hz keep N (k+1))
      (representedSum_append _ terms (upperMaskedTailTerms_valid z hz keep 4 N k) ht)
      (ComplexRaw.add_equiv ih (ComplexRaw.equiv_symm
        (upperMaskedShellSum_list_equiv z hz (N+k+1) (by omega) 4 (keep (N+k+1)))))

theorem upperMaskedWeightFourTail_list_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat)
    (hN : 0<N) : Small (LocalODE.sum (upperMaskedTailTerms z hz keep 4 N k))
      (upperWeightFourTailConstant z hz*reciprocalSquare N) :=
  Small.congr (upperMaskedWeightFourTailBlock_valid z hz keep N k)
    (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 4 N k))
    (ComplexRaw.equiv_symm (upperMaskedWeightFourTail_list_equiv z hz keep N k))
    (upperMaskedWeightFourTailBlock_uniform_small z hz keep N k hN)

theorem upperMaskedWeightSixTail_list_equiv (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat) :
    (LocalODE.sum (upperMaskedTailTerms z hz keep 6 N k)).Equiv (upperMaskedWeightSixTailBlock z hz keep N k) := by
  induction k with
  | zero => exact ComplexRaw.equiv_refl _ (ComplexRaw.ofQComplex_valid _)
  | succ k ih =>
    let terms := (((List.range (8*(N+k+1))).filter (keep (N+k+1))).map
      (upperShellTerm z hz (N+k+1) (by omega) 6))
    have ht : ∀ zz ∈ terms, zz.Valid := by
      intro zz hzz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hzz
      exact upperShellTerm_valid z hz _ _ _ _
    exact ComplexRaw.equiv_trans
      (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 6 N (k+1)))
      (ComplexRaw.add_valid (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 6 N k))
        (LocalODE.sum_valid _ ht))
      (upperMaskedWeightSixTailBlock_valid z hz keep N (k+1))
      (representedSum_append _ terms (upperMaskedTailTerms_valid z hz keep 6 N k) ht)
      (ComplexRaw.add_equiv ih (ComplexRaw.equiv_symm
        (upperMaskedShellSum_list_equiv z hz (N+k+1) (by omega) 6 (keep (N+k+1)))))

theorem upperMaskedWeightSixTail_list_uniform_small (z : Scalar) (hz : InUpperHalfPlane z.val) (keep : Nat → Nat → Bool) (N k : Nat)
    (hN : 0<N) : Small (LocalODE.sum (upperMaskedTailTerms z hz keep 6 N k))
      (upperWeightSixTailConstant z hz*reciprocalSquare N) :=
  Small.congr (upperMaskedWeightSixTailBlock_valid z hz keep N k)
    (LocalODE.sum_valid _ (upperMaskedTailTerms_valid z hz keep 6 N k))
    (ComplexRaw.equiv_symm (upperMaskedWeightSixTail_list_equiv z hz keep N k))
    (upperMaskedWeightSixTailBlock_uniform_small z hz keep N k hN)

end ComputableAnalysis.ModularForms
