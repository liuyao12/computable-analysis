import ComputableAnalysis.FiniteExponentialTaylor

/-!
# A concrete finite Taylor checkpoint

This is a worked instance of the item-35 remainder machinery.  The values are
literal rationals: the example records the first exponential prefixes at
`x = 1` and then invokes the potential-infinity enclosure for all later finite
prefixes on the unit box.
-/

namespace ComputableAnalysis

namespace FiniteExponentialTaylor

def exampleEps : QPos := ⟨1 / 100, by native_decide⟩

theorem expTaylorPrefix_stage5_one :
    FinitePolynomial.expTaylorPrefix 5 1 = (163 : Rat) / 60 := by
  native_decide

theorem expTaylorPrefix_stage6_one :
    FinitePolynomial.expTaylorPrefix 6 1 = (1957 : Rat) / 720 := by
  native_decide

theorem expTaylorPrefix_stage8_one :
    FinitePolynomial.expTaylorPrefix 8 1 = (109601 : Rat) / 40320 := by
  native_decide

theorem expTaylorPrefix_stage10_one :
    FinitePolynomial.expTaylorPrefix 10 1 = (9864101 : Rat) / 3628800 := by
  native_decide

theorem expTaylorPrefix_stage12_one :
    FinitePolynomial.expTaylorPrefix 12 1 =
      (260412269 : Rat) / 95800320 := by
  native_decide

theorem expTaylorPrefix_stage14_one :
    FinitePolynomial.expTaylorPrefix 14 1 =
      (47395032961 : Rat) / 17435658240 := by
  native_decide

theorem expTaylorPrefix_stage16_one :
    FinitePolynomial.expTaylorPrefix 16 1 =
      (56874039553217 : Rat) / 20922789888000 := by
  native_decide

theorem scheduled_expTaylorPrefix_one_remainder_le :
    qabs
        (FinitePolynomial.expTaylorPrefix
            (scheduledPrefixDegree 1 exampleEps + 7) 1 -
          FinitePolynomial.expTaylorPrefix
            (scheduledPrefixDegree 1 exampleEps) 1) <=
      exampleEps.val := by
  apply scheduled_expTaylorPrefix_remainder_le
  · native_decide
  · native_decide

theorem scheduled_expTaylorPrefix_one_enclosure :
    let center := FinitePolynomial.expTaylorPrefix
      (scheduledPrefixDegree 1 exampleEps) 1
    let later := FinitePolynomial.expTaylorPrefix
      (scheduledPrefixDegree 1 exampleEps + 7) 1
    center - exampleEps.val <= later /\ later <= center + exampleEps.val := by
  apply scheduled_expTaylorPrefix_enclosure
  · native_decide
  · native_decide

end FiniteExponentialTaylor

end ComputableAnalysis
