import ComputableAnalysis.ModularForms.SymmetricReciprocalPrefixes

/-! Quantitative translation errors for the actual symmetric reciprocal prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

theorem upperSymmetricReciprocalPrefix_shift (z : Scalar)
    (hz : InUpperHalfPlane z.val) (N : Nat) :
    (sub (upperSymmetricReciprocalPrefix (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1) N) (upperSymmetricReciprocalPrefix z hz N)).Equiv
    (sub (upperIntegerReciprocal z hz ((N:Int)+1)).val
      (upperIntegerReciprocal z hz (-(N:Int))).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := sub_valid (upperSymmetricReciprocalPrefix_valid _ _ N)
      (upperSymmetricReciprocalPrefix_valid z hz N))
    (hright := sub_valid (upperIntegerReciprocal z hz _).property
      (upperIntegerReciprocal z hz _).property)
  change ComplexRawQuotient.ofRaw (upperSymmetricReciprocalPrefix (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1) N) (upperSymmetricReciprocalPrefix_valid _ _ N) -
    ComplexRawQuotient.ofRaw (upperSymmetricReciprocalPrefix z hz N)
      (upperSymmetricReciprocalPrefix_valid z hz N) =
    upperIntegerReciprocalClass z hz ((N:Int)+1) - upperIntegerReciprocalClass z hz (-(N:Int))
  rw [upperSymmetricReciprocalPrefix_class,upperSymmetricReciprocalPrefix_class,
    upperIntegerReciprocal_symmetric_shift]

theorem upperSymmetricReciprocalPrefix_shift_bound (z : Scalar)
    (hz : InUpperHalfPlane z.val) (R : Rat) (hR : 0≤R) (hsmall : Small z.val R)
    (N : Nat) (hN : 0<N) (hRN : R≤(N:Rat))
    (hlarge : 16*R*R≤pairedIntegerSquare N)
    (hlargeSucc : 16*R*R≤pairedIntegerSquare (N+1)) :
    Small (sub (upperSymmetricReciprocalPrefix (integerShiftScalar z 1)
      (integerShiftScalar_upper z hz 1) N) (upperSymmetricReciprocalPrefix z hz N))
      (16*(1/((N+1:Nat):Rat))+16*(1/(N:Rat))) := by
  have hsucc : 0<N+1 := by omega
  have hRs : R≤((N+1:Nat):Rat) := by
    have hn : (N:Rat)≤((N+1:Nat):Rat) := by exact_mod_cast (show N≤N+1 by omega)
    grind only
  have hp := upperIntegerReciprocal_plus_bound z hz R hR hsmall (N+1) hsucc hlargeSucc hRs
  have hm := upperIntegerReciprocal_minus_bound z hz R hR hsmall N hN hlarge hRN
  have he : ((N+1:Nat):Int)=(N:Int)+1 := by omega
  rw [he] at hp
  have h := LocalODE.small_add hp (SeriesLimitLaws.small_neg hm)
  exact Small.congr (sub_valid (upperIntegerReciprocal z hz _).property
      (upperIntegerReciprocal z hz _).property)
    (sub_valid (upperSymmetricReciprocalPrefix_valid _ _ N)
      (upperSymmetricReciprocalPrefix_valid z hz N))
    (equiv_symm (upperSymmetricReciprocalPrefix_shift z hz N)) h

end ComputableAnalysis.ModularForms
