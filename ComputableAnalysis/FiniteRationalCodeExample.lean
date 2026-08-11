import ComputableAnalysis.Basic

/-!
# A finite rational-coding witness

The canonical rational-name enumeration assigns an explicit natural index to
`3/5`.  This is a concrete instance of the coding interface behind item 3;
it does not use an infinite set or an attained real.
-/

namespace ComputableAnalysis

theorem rationalNatIndex_three_fifths :
    rationalNatIndex (3 / 5 : Rat) = 61 := by
  native_decide

theorem rationalNatCode_index_three_fifths :
    rationalNatCode (rationalNatIndex (3 / 5 : Rat)) =
      RationalCode.encode (3 / 5 : Rat) := by
  exact rationalNatCode_index (3 / 5 : Rat)

theorem rationalNatCode_decode_three_fifths :
    RationalCode.decode (rationalNatCode 61) = (3 / 5 : Rat) := by
  rw [show (61 : Nat) = rationalNatIndex (3 / 5 : Rat) by
    native_decide]
  rw [rationalNatCode_index_three_fifths]
  exact RationalCode.decode_encode (3 / 5 : Rat)

end ComputableAnalysis
