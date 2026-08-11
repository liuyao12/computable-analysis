import ComputableAnalysis.GeometricPiRotation

/-!
# Finite certificate for the geometric half-pi rotation input

This packages the geometric half-angle data consumed by the rotation lift:
valid nested rational boxes, the elementary `[1,2]` enclosure, the explicit
width modulus, and equivalence with the rational-circle quarter turn.  The
certificate is entirely representation-level; it does not invoke completed
real or complex numbers.
-/

namespace ComputableAnalysis

namespace GeometricPiRotation

theorem halfPiInput_certificate :
    halfPiInput.raw.Valid /\
      (forall n : Nat,
        (1 : Rat) <= (halfPiInput.raw.compute n).lo /\
          (halfPiInput.raw.compute n).hi <= 2) /\
      (forall n : Nat,
        (halfPiInput.raw.compute n).width <=
          2 / (((n + 1 : Nat) : Rat))) /\
      halfPiInput.raw.Equiv
        (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) := by
  refine ⟨halfPiInput.valid, halfPiInput.bounds,
    halfPiInput.width_le_two_div_succ, ?_⟩
  simpa [halfPiInput] using halfPi_equiv_geometricQuarterTurnOne

end GeometricPiRotation

end ComputableAnalysis
