import ComputableAnalysis.ModularForms.DyadicSampleReversal

/-! Exact finite-list flattening of the executable bisection sampler. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

def dyadicMidpoints (I : QInterval) : Nat → List Rat
  | 0 => [I.midpoint]
  | n+1 => dyadicMidpoints (bisectInterval I false) n ++
      dyadicMidpoints (bisectInterval I true) n

def sampleListSum (f : Rat → Scalar) : List Rat → Scalar
  | [] => ⟨zero,ofQComplex_valid _⟩
  | u::us =>
    let t := sampleListSum f us
    ⟨add (f u).val t.val,add_valid (f u).property t.property⟩

theorem dyadicMidpoints_length (I : QInterval) (n : Nat) :
    (dyadicMidpoints I n).length=2^n := by
  induction n generalizing I with
  | zero => rfl
  | succ n ih =>
    rw [dyadicMidpoints,List.length_append,ih,ih,Nat.pow_succ]
    omega

theorem sampleListSum_append (f : Rat → Scalar) (xs ys : List Rat) :
    (sampleListSum f (xs++ys)).val.Equiv
      (add (sampleListSum f xs).val (sampleListSum f ys).val) := by
  induction xs with
  | nil =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (sampleListSum f ys).property)
      (hright := add_valid (ofQComplex_valid _) (sampleListSum f ys).property)
    let Y := ComplexRawQuotient.ofRaw (sampleListSum f ys).val (sampleListSum f ys).property
    change Y=0+Y
    grind only
  | cons x xs ih =>
    have hb := add_equiv (equiv_refl _ (f x).property) ih
    have ha : (add (f x).val (add (sampleListSum f xs).val (sampleListSum f ys).val)).Equiv
        (add (sampleListSum f (x::xs)).val (sampleListSum f ys).val) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := add_valid (f x).property (add_valid (sampleListSum f xs).property (sampleListSum f ys).property))
        (hright := add_valid (sampleListSum f (x::xs)).property (sampleListSum f ys).property)
      let X := ComplexRawQuotient.ofRaw (f x).val (f x).property
      let S := ComplexRawQuotient.ofRaw (sampleListSum f xs).val (sampleListSum f xs).property
      let Y := ComplexRawQuotient.ofRaw (sampleListSum f ys).val (sampleListSum f ys).property
      change X+(S+Y)=(X+S)+Y
      grind only
    exact equiv_trans (sampleListSum f ((x::xs)++ys)).property
      (add_valid (f x).property (add_valid (sampleListSum f xs).property (sampleListSum f ys).property))
      (add_valid (sampleListSum f (x::xs)).property (sampleListSum f ys).property) hb ha

theorem dyadicSampleAverage_flatten (f : Rat → Scalar) (I : QInterval) (n : Nat) :
    (dyadicSampleAverage f I n).val.Equiv
      (scaleRat (((1:Rat)/2)^n) (sampleListSum f (dyadicMidpoints I n)).val) := by
  induction n generalizing I with
  | zero =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (f I.midpoint).property)
      (hright := scaleRat_valid (sampleListSum f (dyadicMidpoints I 0)).property)
    let X := ComplexRawQuotient.ofRaw (f I.midpoint).val (f I.midpoint).property
    change X=ComplexRawQuotient.scaleRat (((1:Rat)/2)^0) (X+0)
    rw [Rat.pow_zero,ComplexRawQuotient.scaleRat_one]
    grind only
  | succ n ih =>
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := (dyadicSampleAverage f I (n+1)).property)
      (hright := scaleRat_valid (sampleListSum f (dyadicMidpoints I (n+1))).property)
    have hl := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (dyadicSampleAverage f (bisectInterval I false) n).property)
      (hright := scaleRat_valid (sampleListSum f (dyadicMidpoints (bisectInterval I false) n)).property)
      (ih (bisectInterval I false))
    have hr := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (dyadicSampleAverage f (bisectInterval I true) n).property)
      (hright := scaleRat_valid (sampleListSum f (dyadicMidpoints (bisectInterval I true) n)).property)
      (ih (bisectInterval I true))
    have hs := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (sampleListSum f (dyadicMidpoints I (n+1))).property)
      (hright := add_valid (sampleListSum f (dyadicMidpoints (bisectInterval I false) n)).property
        (sampleListSum f (dyadicMidpoints (bisectInterval I true) n)).property)
      (sampleListSum_append f _ _)
    let A := ComplexRawQuotient.ofRaw (dyadicSampleAverage f (bisectInterval I false) n).val (dyadicSampleAverage f (bisectInterval I false) n).property
    let B := ComplexRawQuotient.ofRaw (dyadicSampleAverage f (bisectInterval I true) n).val (dyadicSampleAverage f (bisectInterval I true) n).property
    let L := ComplexRawQuotient.ofRaw (sampleListSum f (dyadicMidpoints (bisectInterval I false) n)).val (sampleListSum f (dyadicMidpoints (bisectInterval I false) n)).property
    let T := ComplexRawQuotient.ofRaw (sampleListSum f (dyadicMidpoints (bisectInterval I true) n)).val (sampleListSum f (dyadicMidpoints (bisectInterval I true) n)).property
    let S := ComplexRawQuotient.ofRaw (sampleListSum f (dyadicMidpoints I (n+1))).val (sampleListSum f (dyadicMidpoints I (n+1))).property
    change A=ComplexRawQuotient.scaleRat (((1:Rat)/2)^n) L at hl
    change B=ComplexRawQuotient.scaleRat (((1:Rat)/2)^n) T at hr
    change S=L+T at hs
    change ComplexRawQuotient.scaleRat (1/2) (A+B)=ComplexRawQuotient.scaleRat (((1:Rat)/2)^(n+1)) S
    rw [hl,hr,hs,← ComplexRawQuotient.scaleRat_add,ComplexRawQuotient.scaleRat_scaleRat,Rat.pow_succ]
    rw [Rat.mul_comm ((1:Rat)/2) (((1:Rat)/2)^n)]

end ComputableAnalysis.ModularForms
