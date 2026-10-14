import ComputableAnalysis.ModularForms.DyadicSampleAverage

/-! Uniform cell errors combine into a whole-average refinement error. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

theorem halfAverage_pair_difference (a b c d : Scalar) :
    (sub (scaleRat (1/2) (add a.val b.val))
      (scaleRat (1/2) (add c.val d.val))).Equiv
      (scaleRat (1/2) (add (sub a.val c.val) (sub b.val d.val))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (scaleRat_valid (add_valid a.property b.property))
      (scaleRat_valid (add_valid c.property d.property)))
    (hright := scaleRat_valid (add_valid (sub_valid a.property c.property)
      (sub_valid b.property d.property)))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  let C := ComplexRawQuotient.ofRaw c.val c.property
  let D := ComplexRawQuotient.ofRaw d.val d.property
  change ComplexRawQuotient.scaleRat (1/2) (A+B)-
    ComplexRawQuotient.scaleRat (1/2) (C+D)=
    ComplexRawQuotient.scaleRat (1/2) ((A-C)+(B-D))
  have hn (X : ScalarAlgebra.Value) :
      ComplexRawQuotient.scaleRat (1/2) (-X)= -ComplexRawQuotient.scaleRat (1/2) X := by
    rw [ComplexRawQuotient.neg_eq_scaleRat_neg_one, ComplexRawQuotient.scaleRat_scaleRat,
      ComplexRawQuotient.neg_scaleRat]
    congr 1
    grind only
  change _=ComplexRawQuotient.scaleRat (1/2) ((A+ -C)+(B+ -D))
  rw [ComplexRawQuotient.scaleRat_add, ComplexRawQuotient.scaleRat_add,
    ComplexRawQuotient.scaleRat_add, ComplexRawQuotient.scaleRat_add,
    ComplexRawQuotient.scaleRat_add, hn, hn]
  grind only

theorem dyadicSampleAverage_refinement_error (f : Rat → Scalar) (I : QInterval)
    (n k : Nat) (E : Rat)
    (cells : ∀ choice : Nat → Bool,
      let J := bisectionInterval I choice n
      Small (sub (dyadicSampleAverage f J k).val (f J.midpoint).val) E) :
    Small (sub (dyadicSampleAverage f I (n+k)).val
      (dyadicSampleAverage f I n).val) E := by
  induction n generalizing I with
  | zero => simpa only [Nat.zero_add, bisectionInterval, dyadicSampleAverage] using cells (fun _ => false)
  | succ n ih =>
    have child (r : Bool) : ∀ choice : Nat → Bool,
        let J := bisectionInterval (bisectInterval I r) choice n
        Small (sub (dyadicSampleAverage f J k).val (f J.midpoint).val) E := by
      intro choice
      let extended : Nat → Bool := fun j => match j with
        | 0 => r
        | j+1 => choice j
      have hb := cells extended
      rw [bisectionInterval_shift] at hb
      exact hb
    have hl := ih (bisectInterval I false) (child false)
    have hr := ih (bisectInterval I true) (child true)
    have hb := LocalODE.small_scale (by decide +kernel : (0:Rat)≤1/2)
      (LocalODE.small_add hl hr)
    have he : (1:Rat)/2*(E+E)=E := by grind only
    rw [he] at hb
    have hnk : n+1+k=(n+k)+1 := by omega
    rw [hnk]
    exact Small.congr
      (scaleRat_valid (add_valid
        (sub_valid (dyadicSampleAverage f (bisectInterval I false) (n+k)).property
          (dyadicSampleAverage f (bisectInterval I false) n).property)
        (sub_valid (dyadicSampleAverage f (bisectInterval I true) (n+k)).property
          (dyadicSampleAverage f (bisectInterval I true) n).property)))
      (sub_valid (dyadicSampleAverage f I ((n+k)+1)).property
        (dyadicSampleAverage f I (n+1)).property)
      (equiv_symm (halfAverage_pair_difference
        (dyadicSampleAverage f (bisectInterval I false) (n+k))
        (dyadicSampleAverage f (bisectInterval I true) (n+k))
        (dyadicSampleAverage f (bisectInterval I false) n)
        (dyadicSampleAverage f (bisectInterval I true) n))) hb

end ComputableAnalysis.ModularForms
