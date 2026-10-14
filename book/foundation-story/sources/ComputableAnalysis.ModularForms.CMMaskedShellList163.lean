import ComputableAnalysis.ModularForms.CMMaskedShell163
import ComputableAnalysis.ModularForms.FiniteSumSplit

/-! Exact list interpretation of selected CM shell sums. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert QuadraticOrder163

private def indexValue (f : Nat → ScalarAlgebra.Value) : List Nat → ScalarAlgebra.Value
  | [] => 0
  | i::is => f i+indexValue f is

private theorem indexValue_append (f : Nat → ScalarAlgebra.Value) (as bs : List Nat) :
    indexValue f (as++bs)=indexValue f as+indexValue f bs := by
  induction as with
  | nil => change _=0+_; grind
  | cons a as ih => simp only [List.cons_append,indexValue,ih]; grind

private theorem indexValue_raw (f : Nat → ComplexRaw) (hf : ∀ i, (f i).Valid) (is : List Nat) :
    ComplexRawQuotient.ofRaw (LocalODE.sum (is.map f))
      (LocalODE.sum_valid _ (by intro z hz; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz; exact hf i))=
    indexValue (fun i => ComplexRawQuotient.ofRaw (f i) (hf i)) is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change ComplexRawQuotient.ofRaw (f i) (hf i)+
      ComplexRawQuotient.ofRaw (LocalODE.sum (is.map f))
        (LocalODE.sum_valid _ (by intro z hz; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz; exact hf j))=_
    rw [ih]
    rfl

private theorem maskedPrefix_value (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) (n : Nat) :
    ComplexRawQuotient.ofRaw (maskedShellPrefix r hr k keep n)
      (maskedShellPrefix_valid r hr k keep n)=
    indexValue (fun i => ComplexRawQuotient.ofRaw (shellTerm r hr k i) (shellTerm_valid r hr k i))
      ((List.range n).filter keep) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ,List.filter_append,indexValue_append]
    cases hk : keep n
    · have he : (if keep n then shellTerm r hr k n else ComplexRaw.zero)=ComplexRaw.zero := by simp [hk]
      change ComplexRawQuotient.ofRaw (maskedShellPrefix r hr k keep n)
        (maskedShellPrefix_valid r hr k keep n)+
        ComplexRawQuotient.ofRaw (if keep n then shellTerm r hr k n else ComplexRaw.zero)
          (by rw [he]; exact ComplexRaw.ofQComplex_valid _) = _
      simp only [hk,List.filter_cons,List.filter_nil,Bool.false_eq_true,if_false,indexValue]
      rw [ih]
      rfl
    · change ComplexRawQuotient.ofRaw (maskedShellPrefix r hr k keep n)
        (maskedShellPrefix_valid r hr k keep n)+
        ComplexRawQuotient.ofRaw (if keep n then shellTerm r hr k n else ComplexRaw.zero)
          (by simp only [hk,if_true]; exact shellTerm_valid r hr k n) = _
      simp only [hk,if_true,List.filter_cons,List.filter_nil,indexValue]
      rw [ih]
      grind

/-- The selected recursive shell is exactly the filtered finite term sum. -/
theorem maskedShellSum_list_equiv (r : Nat) (hr : 0<r) (k : Nat) (keep : Nat → Bool) :
    (maskedShellSum r hr k keep).Equiv
      (LocalODE.sum (((List.range (8*r)).filter keep).map (shellTerm r hr k))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := maskedShellSum_valid r hr k keep)
    (hright := LocalODE.sum_valid _ (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact shellTerm_valid r hr k i))
  rw [indexValue_raw _ (shellTerm_valid r hr k)]
  exact maskedPrefix_value r hr k keep (8*r)


/-- The quantitative bound applies directly to an arbitrary filtered shell list. -/
theorem filteredWeightFourShell_small (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    FunctionTheory.Small
      (LocalODE.sum (((List.range (8*r)).filter keep).map (shellTerm r hr 4)))
      (weightFourTailConstant*reciprocalCube r) := by
  apply FunctionTheory.Small.congr (maskedShellSum_valid r hr 4 keep)
    (LocalODE.sum_valid _ (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact shellTerm_valid r hr 4 i))
    (maskedShellSum_list_equiv r hr 4 keep)
  exact maskedWeightFourShell_small r hr keep

/-- The quantitative bound applies directly to an arbitrary filtered shell list. -/
theorem filteredWeightSixShell_small (r : Nat) (hr : 0<r) (keep : Nat → Bool) :
    FunctionTheory.Small
      (LocalODE.sum (((List.range (8*r)).filter keep).map (shellTerm r hr 6)))
      (weightSixTailConstant*reciprocalCube r) := by
  apply FunctionTheory.Small.congr (maskedShellSum_valid r hr 6 keep)
    (LocalODE.sum_valid _ (by
      intro z hz
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
      exact shellTerm_valid r hr 6 i))
    (maskedShellSum_list_equiv r hr 6 keep)
  exact maskedWeightSixShell_small r hr keep

end ComputableAnalysis.ModularForms
