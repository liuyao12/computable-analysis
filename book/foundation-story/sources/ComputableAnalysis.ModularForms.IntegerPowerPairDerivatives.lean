import ComputableAnalysis.ModularForms.IntegerPowerFiniteHolomorphic
import ComputableAnalysis.ModularForms.NomeMomentPrefixLinearity

/-! Exact derivatives of actual paired reciprocal powers. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

theorem integerReciprocalPower_pair_derivative_values (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k n : Nat) :
    (add ((integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).derivative z hz).val
      ((integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k).derivative z hz).val).Equiv
      (neg (scaleRat (k:Rat) (upperPairedIntegerPower z hz (k+1) (n+1)).val)) := by
  let a := ((integerReciprocalPowerMap (-((n+1:Nat):Int)) (k+1)).eval z hz)
  let b := ((integerReciprocalPowerMap ((n+1:Nat):Int) (k+1)).eval z hz)
  have h : (add ((integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).derivative z hz).val
      ((integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k).derivative z hz).val).Equiv
      (add (neg (scaleRat (k:Rat) a.val)) (neg (scaleRat (k:Rat) b.val))) :=
    add_equiv (integerReciprocalPowerMap_derivative (-((n+1:Nat):Int)) k z hz)
      (integerReciprocalPowerMap_derivative ((n+1:Nat):Int) k z hz)
  apply equiv_trans
    (add_valid ((integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).derivative z hz).property
      ((integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k).derivative z hz).property)
    (add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) a.property)) (neg_valid (scaleRat_valid (r := (k:Rat)) b.property)))
    (neg_valid (scaleRat_valid (r := (k:Rat)) (upperPairedIntegerPower z hz (k+1) (n+1)).property)) h
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (neg_valid (scaleRat_valid (r := (k:Rat)) a.property)) (neg_valid (scaleRat_valid (r := (k:Rat)) b.property)))
    (hright := neg_valid (scaleRat_valid (r := (k:Rat)) (upperPairedIntegerPower z hz (k+1) (n+1)).property))
  let A := ComplexRawQuotient.ofRaw a.val a.property
  let B := ComplexRawQuotient.ofRaw b.val b.property
  change -ComplexRawQuotient.scaleRat (k:Rat) A+ -ComplexRawQuotient.scaleRat (k:Rat) B=
    -ComplexRawQuotient.scaleRat (k:Rat) (A+B)
  rw [ComplexRawQuotient.scaleRat_add]
  generalize ComplexRawQuotient.scaleRat (k:Rat) A=u,
    ComplexRawQuotient.scaleRat (k:Rat) B=v
  grind only

theorem pairedIntegerPowerMap_derivative (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k n : Nat) :
    ((pairedIntegerPowerMap_holomorphic k n).derivative z hz).val.Equiv
      (neg (scaleRat (k:Rat) (upperPairedIntegerPower z hz (k+1) (n+1)).val)) :=
  integerReciprocalPower_pair_derivative_values z hz k n

theorem pairedIntegerPowerFiniteMap_derivative_values (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k N : Nat) :
    ((pairedIntegerPowerFiniteMap_holomorphic k N).derivative z hz).val.Equiv
      (ScalarSeries.block (fun n => ((pairedIntegerPowerMap_holomorphic k n).derivative z hz).val) 0 N) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    change (add ((pairedIntegerPowerFiniteMap_holomorphic k N).derivative z hz).val
      ((pairedIntegerPowerMap_holomorphic k N).derivative z hz).val).Equiv _
    rw [ScalarSeries.block.eq_2]
    rw [Nat.zero_add]
    exact add_equiv ih (equiv_refl _ ((pairedIntegerPowerMap_holomorphic k N).derivative z hz).property)

theorem pairedIntegerPowerFiniteMap_derivative (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k N : Nat) :
    ((pairedIntegerPowerFiniteMap_holomorphic k N).derivative z hz).val.Equiv
      (neg (scaleRat (k:Rat)
        ((pairedIntegerPowerFiniteMap (k+1) N).eval z hz).val)) := by
  let t := fun n => (upperPairedIntegerPower z hz (k+1) (n+1)).val
  have vt n : (t n).Valid := (upperPairedIntegerPower z hz (k+1) (n+1)).property
  have h1 := ScalarSeries.block_congr _ _ (fun n => pairedIntegerPowerMap_derivative z hz k n) 0 N
  have h2 := reciprocalSquare_block_neg (fun n => scaleRat (k:Rat) (t n))
    (fun n => scaleRat_valid (r := (k:Rat)) (vt n)) N
  have h3 := neg_equiv (representedBlock_scale t vt (k:Rat) 0 N)
  exact equiv_trans ((pairedIntegerPowerFiniteMap_holomorphic k N).derivative z hz).property
    (ScalarSeries.block_valid _ (fun n => ((pairedIntegerPowerMap_holomorphic k n).derivative z hz).property) 0 N)
    (neg_valid (scaleRat_valid (r := (k:Rat)) (ScalarSeries.block_valid t vt 0 N)))
    (pairedIntegerPowerFiniteMap_derivative_values z hz k N)
    (equiv_trans (ScalarSeries.block_valid _ (fun n => ((pairedIntegerPowerMap_holomorphic k n).derivative z hz).property) 0 N)
      (ScalarSeries.block_valid _ (fun n => neg_valid (scaleRat_valid (r := (k:Rat)) (vt n))) 0 N)
      (neg_valid (scaleRat_valid (r := (k:Rat)) (ScalarSeries.block_valid t vt 0 N))) h1
      (equiv_trans (ScalarSeries.block_valid _ (fun n => neg_valid (scaleRat_valid (r := (k:Rat)) (vt n))) 0 N)
        (neg_valid (ScalarSeries.block_valid _ (fun n => scaleRat_valid (r := (k:Rat)) (vt n)) 0 N))
        (neg_valid (scaleRat_valid (r := (k:Rat)) (ScalarSeries.block_valid t vt 0 N))) h2 h3))

end ComputableAnalysis.ModularForms
