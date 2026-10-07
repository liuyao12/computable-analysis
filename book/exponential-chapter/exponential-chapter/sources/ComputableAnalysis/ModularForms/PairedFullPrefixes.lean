import ComputableAnalysis.ModularForms.PairedFullSeries

/-! Literal full-prefix comparisons for the actual joined paired series. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem pairedFullTerm_tail (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) (n : Nat) :
    (pairedFullTerm z hd (4*B+n)).val=(pairedTailTerm z B hz n).val := by
  rfl

theorem pairedFullBlock_tail (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) (N : Nat) :
    ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) (4*B) N=
      ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 N := by
  induction N with
  | zero => simp only [ScalarSeries.block.eq_1]
  | succ N ih =>
    simp only [ScalarSeries.block.eq_2,Nat.zero_add]
    change add (ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) (4*B) N)
      (pairedFullTerm z hd (4*B+N)).val =
      add (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 N)
        (pairedTailTerm z B hz N).val
    exact (congrArg (fun x => add x (pairedFullTerm z hd (4*B+N)).val) ih).trans
      (congrArg (fun x => add (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 N) x)
        (pairedFullTerm_tail z hd B hz N))

theorem pairedFullValue_close (z : Scalar) (hd : PairedSeriesDomain z) (B : Nat)
    (hz : Small z.val (B:Rat)) (N : Nat) :
    Small (sub (pairedFullValue z hd B hz)
      (ScalarSeries.block (fun n => (pairedFullTerm z hd n).val) 0 (4*B+(N+1))))
      (((16*B:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  let t := fun n => (pairedFullTerm z hd n).val
  have ht : ∀ n, (t n).Valid := fun n => (pairedFullTerm z hd n).property
  have hp := pairedTailValue_close z B hz N
  have he : (sub (pairedFullValue z hd B hz) (ScalarSeries.block t 0 (4*B+(N+1)))).Equiv
      (sub (pairedTailValue z B hz) (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 (N+1))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedFullValue_valid z hd B hz) (ScalarSeries.block_valid t ht 0 _))
      (hright := sub_valid (pairedTailValue_valid z B hz)
        (ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hz n).property) 0 _))
    change (ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 (4*B)) (ScalarSeries.block_valid t ht 0 _)+
      ComplexRawQuotient.ofRaw (pairedTailValue z B hz) (pairedTailValue_valid z B hz))-
      ComplexRawQuotient.ofRaw (ScalarSeries.block t 0 (4*B+(N+1))) (ScalarSeries.block_valid t ht 0 _) = _
    rw [ScalarSeries.prefix_image,ScalarSeries.prefix_image,FiniteProducts.prefix_append]
    rw [← ScalarSeries.block_image t ht (4*B) (N+1)]
    have heq := pairedFullBlock_tail z hd B hz (N+1)
    change ScalarSeries.block t (4*B) (N+1)=_ at heq
    have hclass : ComplexRawQuotient.ofRaw (ScalarSeries.block t (4*B) (N+1))
        (ScalarSeries.block_valid t ht (4*B) (N+1)) =
        ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 (N+1))
          (ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hz n).property) 0 (N+1)) := by
      congr 1
    rw [hclass]
    let A := FiniteProducts.partialSum (fun n => ComplexRawQuotient.ofRaw (t n) (ht n)) (4*B)
    let T := ComplexRawQuotient.ofRaw (pairedTailValue z B hz) (pairedTailValue_valid z B hz)
    let P := ComplexRawQuotient.ofRaw (ScalarSeries.block (fun n => (pairedTailTerm z B hz n).val) 0 (N+1))
      (ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hz n).property) 0 (N+1))
    change (A+T)-(A+P)=T-P
    grind only
  exact Small.congr
    (sub_valid (pairedTailValue_valid z B hz)
      (ScalarSeries.block_valid _ (fun n => (pairedTailTerm z B hz n).property) 0 _))
    (sub_valid (pairedFullValue_valid z hd B hz) (ScalarSeries.block_valid t ht 0 _))
    (equiv_symm he) hp

end ComputableAnalysis.ModularForms
