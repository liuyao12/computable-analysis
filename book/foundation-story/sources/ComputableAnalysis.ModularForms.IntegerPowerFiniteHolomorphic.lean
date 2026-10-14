import ComputableAnalysis.ModularForms.IntegerPowerRowIntegerPeriods

/-! Actual finite reciprocal-power row maps and their holomorphic constructions. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def pairedIntegerPowerMap (k n : Nat) : DomainFunctions.Map :=
  sumOn (integerReciprocalPowerMap (-((n+1:Nat):Int)) k)
    (integerReciprocalPowerMap ((n+1:Nat):Int) k)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedIntegerPowerMap_holomorphic (k n : Nat) : Holomorphic (pairedIntegerPowerMap k n) :=
  (integerReciprocalPowerMap_holomorphic (-((n+1:Nat):Int)) k).sumOn
    (integerReciprocalPowerMap_holomorphic ((n+1:Nat):Int) k)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def pairedIntegerPowerFiniteMap (k N : Nat) : DomainFunctions.Map where
  domain z := InUpperHalfPlane z.val
  eval z hz := ⟨ScalarSeries.block (fun n => (upperPairedIntegerPower z hz k (n+1)).val) 0 N,
    ScalarSeries.block_valid _ (fun n => (upperPairedIntegerPower z hz k (n+1)).property) 0 N⟩
  domain_congr := upperOpenData.invariant
  eval_congr z w hz hw he := ScalarSeries.block_congr _ _
    (fun n => upperPairedIntegerPower_congr z w hz hw he k (n+1)) 0 N

def pairedIntegerPowerFiniteMap_holomorphic (k N : Nat) : Holomorphic (pairedIntegerPowerFiniteMap k N) := by
  induction N with
  | zero =>
    apply (constantOn_holomorphic upperOpenData ⟨zero,ofQComplex_valid _⟩).transfer
      (pairedIntegerPowerFiniteMap k 0) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    apply (ih.sumOn (pairedIntegerPowerMap_holomorphic k N) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)).transfer
      (pairedIntegerPowerFiniteMap k (N+1)) (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz) ⟨upperRadius,upperRadius_inside⟩
    intro z hz
    simp only [sumOn,pairedIntegerPowerFiniteMap,pairedIntegerPowerMap,scalarSum,
      ScalarSeries.block.eq_2,Nat.zero_add]
    exact equiv_refl _ (add_valid
      (ScalarSeries.block_valid _ (fun n => (upperPairedIntegerPower z hz k (n+1)).property) 0 N)
      (upperPairedIntegerPower z hz k (N+1)).property)

def integerPowerFiniteRowMap (k N : Nat) : DomainFunctions.Map :=
  sumOn (integerReciprocalPowerMap 0 k) (pairedIntegerPowerFiniteMap k N)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

def integerPowerFiniteRowMap_holomorphic (k N : Nat) : Holomorphic (integerPowerFiniteRowMap k N) :=
  (integerReciprocalPowerMap_holomorphic 0 k).sumOn (pairedIntegerPowerFiniteMap_holomorphic k N)
    (fun (z : Scalar) (hz : InUpperHalfPlane z.val) => hz)

theorem integerPowerFiniteRowMap_eval (z : Scalar) (hz : InUpperHalfPlane z.val) (k N : Nat) :
    ((integerPowerFiniteRowMap k N).eval z hz).val=integerPowerRowPrefix z hz k N := rfl

end ComputableAnalysis.ModularForms
