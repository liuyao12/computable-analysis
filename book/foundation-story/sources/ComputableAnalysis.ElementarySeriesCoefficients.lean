import ComputableAnalysis.ElementaryPowerSeries

/-! Exact finite coefficient identities for the certified odd/even samplers. -/
namespace ComputableAnalysis.ElementaryPowerSeries
open ComplexExponentialApproximation

theorem sinSign_succ (n : Nat) : ComplexSeries.sinSign (n+1) = -ComplexSeries.sinSign n := by
  unfold ComplexSeries.sinSign
  by_cases h : n%2=0
  · have hs : (n+1)%2 ≠ 0 := by omega
    simp [h,hs]
  · have hs : (n+1)%2=0 := by omega
    simp [h,hs]

theorem pow_eq_natPow (z : QComplex) (n : Nat) : QComplex.pow z n = QComplex.natPow z n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [QComplex.pow,ih,QComplex.natPow_succ,QComplex.mul_comm_cert]

theorem pow_mul (z w : QComplex) (n : Nat) :
    QComplex.pow (QComplex.mul z w) n = QComplex.mul (QComplex.pow z n) (QComplex.pow w n) := by
  simp only [pow_eq_natPow,QComplex.natPow_mul]

theorem pow_neg (z : QComplex) (n : Nat) :
    QComplex.pow (QComplex.neg z) n = QComplex.scaleRat (ComplexSeries.sinSign n) (QComplex.pow z n) := by
  induction n with
  | zero => simp [QComplex.pow,ComplexSeries.sinSign,QComplex.scaleRat,QComplex.one]
  | succ n ih =>
    rw [QComplex.pow,QComplex.pow,ih,sinSign_succ]
    simp only [QComplex.mul,QComplex.neg,QComplex.scaleRat]
    congr 1 <;> grind only

theorem pow_i_even (n : Nat) :
    QComplex.pow ElementaryRational.imaginaryUnit (2*n) = ⟨ComplexSeries.sinSign n,0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,QComplex.pow,QComplex.pow,ih,sinSign_succ]
    simp only [ElementaryRational.imaginaryUnit,QComplex.mul]
    congr 1 <;> grind only

theorem pow_i_odd (n : Nat) :
    QComplex.pow ElementaryRational.imaginaryUnit (2*n+1) = ⟨0,ComplexSeries.sinSign n⟩ := by
  rw [QComplex.pow,pow_i_even]
  simp only [ElementaryRational.imaginaryUnit,QComplex.mul]
  congr 1 <;> grind only

theorem expTerm_neg_even (z : QComplex) (n : Nat) :
    term (QComplex.neg z) (2*n) = term z (2*n) := by
  have hs : ComplexSeries.sinSign (2*n)=1 := by
    unfold ComplexSeries.sinSign; rw [if_pos (by omega)]
  unfold term ComplexSeries.expTerm
  rw [pow_neg,hs,QComplex.scaleRat_one_cert]

theorem expTerm_neg_odd (z : QComplex) (n : Nat) :
    term (QComplex.neg z) (2*n+1) = QComplex.neg (term z (2*n+1)) := by
  have hs : ComplexSeries.sinSign (2*n+1)= -1 := by
    unfold ComplexSeries.sinSign; rw [if_neg (by omega)]
  unfold term ComplexSeries.expTerm
  rw [pow_neg,hs,QComplex.scaleRat_neg_one_cert]
  simp only [QComplex.divRat,QComplex.neg]
  congr 1 <;> grind only [Rat.div_def]

theorem expTerm_i_even (z : QComplex) (n : Nat) :
    term (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n) = ComplexSeries.cosTerm z n := by
  unfold term ComplexSeries.expTerm ComplexSeries.cosTerm
  rw [pow_mul,pow_i_even]
  simp only [QComplex.mul,QComplex.divRat,QComplex.scaleRat,Rat.zero_mul,Rat.mul_zero,Rat.add_zero,Rat.sub_eq_add_neg,Rat.neg_zero]
  congr 1 <;> grind only [Rat.div_def]

theorem expTerm_i_odd (z : QComplex) (n : Nat) :
    term (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n+1) =
      QComplex.mul ElementaryRational.imaginaryUnit (ComplexSeries.sinTerm z n) := by
  unfold term ComplexSeries.expTerm ComplexSeries.sinTerm
  rw [pow_mul,pow_i_odd]
  simp only [ElementaryRational.imaginaryUnit,QComplex.mul,QComplex.divRat,QComplex.scaleRat,
    Rat.zero_mul,Rat.mul_zero,Rat.add_zero,Rat.zero_add]
  congr 1 <;> grind only [Rat.div_def]

theorem pair_add (odd : Bool) (a b c d : QComplex) :
    pair odd (QComplex.add a c) (QComplex.add b d) =
      QComplex.add (pair odd a b) (pair odd c d) := by
  cases odd <;> simp only [pair,if_true,if_false,Bool.false_eq_true,QComplex.scaleRat,
    QComplex.sub,QComplex.add,QComplex.neg]
  all_goals congr 1 <;> grind only

theorem pair_same (z : QComplex) : pair false z z = z := by
  simp only [pair,Bool.false_eq_true,if_false,QComplex.scaleRat,QComplex.add]
  congr 1 <;> grind only
theorem pair_difference_same (z : QComplex) : pair true z z = QComplex.zero := by
  simp only [pair,if_true,QComplex.scaleRat,QComplex.sub,QComplex.add,QComplex.neg,QComplex.zero]
  congr 1 <;> grind only
theorem pair_opposite (z : QComplex) : pair false z (QComplex.neg z) = QComplex.zero := by
  simp only [pair,Bool.false_eq_true,if_false,QComplex.scaleRat,QComplex.add,QComplex.neg,QComplex.zero]
  congr 1 <;> grind only
theorem pair_difference_opposite (z : QComplex) : pair true z (QComplex.neg z) = z := by
  simp only [pair,if_true,QComplex.scaleRat,QComplex.sub,QComplex.add,QComplex.neg]
  congr 1 <;> grind only

theorem pairPrefix_even_succ (odd : Bool) (z : QComplex) (n : Nat) :
    pairPrefix odd z (2*(n+1)) = QComplex.add (pairPrefix odd z (2*n))
      (term z (if odd then 2*n+1 else 2*n)) := by
  unfold pairPrefix
  rw [show 2*(n+1)=2*n+1+1 by omega,expPrefix_succ,expPrefix_succ,expPrefix_succ,expPrefix_succ]
  rw [pair_add,pair_add,expTerm_neg_even,expTerm_neg_odd]
  cases odd
  · rw [pair_same,pair_opposite,QComplex.add_zero_cert]; rfl
  · rw [pair_difference_same,pair_difference_opposite,QComplex.add_zero_cert]; rfl

theorem sine_partial_succ (z : QComplex) (n : Nat) : ComplexSeries.sinPartial z (n+1) =
    QComplex.add (ComplexSeries.sinPartial z n) (ComplexSeries.sinTerm z n) := by
  unfold ComplexSeries.sinPartial; rw [List.range_succ,List.foldl_append]; rfl
theorem cosine_partial_succ (z : QComplex) (n : Nat) : ComplexSeries.cosPartial z (n+1) =
    QComplex.add (ComplexSeries.cosPartial z n) (ComplexSeries.cosTerm z n) := by
  unfold ComplexSeries.cosPartial; rw [List.range_succ,List.foldl_append]; rfl

theorem pairPrefix_i_cosine (z : QComplex) (n : Nat) :
    pairPrefix false (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n) = ComplexSeries.cosPartial z n := by
  induction n with
  | zero => exact pair_same QComplex.zero
  | succ n ih =>
    rw [pairPrefix_even_succ]
    simp only [Bool.false_eq_true,if_false]
    rw [ih,expTerm_i_even,cosine_partial_succ]

theorem pairPrefix_i_sine (z : QComplex) (n : Nat) :
    pairPrefix true (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n) =
      QComplex.mul ElementaryRational.imaginaryUnit (ComplexSeries.sinPartial z n) := by
  induction n with
  | zero =>
    change pair true QComplex.zero QComplex.zero = QComplex.mul ElementaryRational.imaginaryUnit QComplex.zero
    rw [pair_difference_same,QComplex.mul_zero_cert]
  | succ n ih =>
    rw [pairPrefix_even_succ]
    simp only [if_true]
    rw [ih,expTerm_i_odd,←QComplex.mul_add_cert,sine_partial_succ]


theorem pairPrefix_odd_succ (odd : Bool) (z : QComplex) (n : Nat) :
    pairPrefix odd z (2*n+1) = QComplex.add (pairPrefix odd z (2*n))
      (if odd then QComplex.zero else term z (2*n)) := by
  unfold pairPrefix
  rw [expPrefix_succ,expPrefix_succ,pair_add,expTerm_neg_even]
  cases odd
  · rw [pair_same]; rfl
  · rw [pair_difference_same]; rfl

theorem pairPrefix_i_cosine_odd (z : QComplex) (n : Nat) :
    pairPrefix false (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n+1) =
      ComplexSeries.cosPartial z (n+1) := by
  rw [pairPrefix_odd_succ,pairPrefix_i_cosine]
  simp only [Bool.false_eq_true,if_false]
  rw [expTerm_i_even,cosine_partial_succ]

theorem pairPrefix_i_sine_odd (z : QComplex) (n : Nat) :
    pairPrefix true (QComplex.mul ElementaryRational.imaginaryUnit z) (2*n+1) =
      QComplex.mul ElementaryRational.imaginaryUnit (ComplexSeries.sinPartial z n) := by
  rw [pairPrefix_odd_succ,pairPrefix_i_sine]
  simp only [if_true,QComplex.add_zero_cert]

def hyperbolicSinePartial (z : QComplex) (n : Nat) : QComplex :=
  (List.range n).foldl (fun p k => QComplex.add p (term z (2*k+1))) QComplex.zero
def hyperbolicCosinePartial (z : QComplex) (n : Nat) : QComplex :=
  (List.range n).foldl (fun p k => QComplex.add p (term z (2*k))) QComplex.zero

theorem hyperbolicSinePartial_succ (z : QComplex) (n : Nat) :
    hyperbolicSinePartial z (n+1) = QComplex.add (hyperbolicSinePartial z n) (term z (2*n+1)) := by
  unfold hyperbolicSinePartial; rw [List.range_succ,List.foldl_append]; rfl
theorem hyperbolicCosinePartial_succ (z : QComplex) (n : Nat) :
    hyperbolicCosinePartial z (n+1) = QComplex.add (hyperbolicCosinePartial z n) (term z (2*n)) := by
  unfold hyperbolicCosinePartial; rw [List.range_succ,List.foldl_append]; rfl

theorem pairPrefix_hyperbolicSine (z : QComplex) (n : Nat) :
    pairPrefix true z (2*n) = hyperbolicSinePartial z n := by
  induction n with
  | zero => exact pair_difference_same QComplex.zero
  | succ n ih =>
    rw [pairPrefix_even_succ,ih,hyperbolicSinePartial_succ]
    simp only [if_true]

theorem pairPrefix_hyperbolicCosine (z : QComplex) (n : Nat) :
    pairPrefix false z (2*n) = hyperbolicCosinePartial z n := by
  induction n with
  | zero => exact pair_same QComplex.zero
  | succ n ih =>
    rw [pairPrefix_even_succ,ih,hyperbolicCosinePartial_succ]
    simp only [Bool.false_eq_true,if_false]

end ComputableAnalysis.ElementaryPowerSeries
