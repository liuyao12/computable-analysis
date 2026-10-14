import ComputableAnalysis.ModularForms.IntegerPowerGlobalDerivative

/-! Holomorphic canonical reciprocal-power rows on the full upper half-plane. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

private theorem positive_successor (c : Rat) (hc : 0≤c) : 0<c+1 := by grind only
private theorem scaled_error_le (c e eps : Rat) (he : 0≤e) (h : (c+1)*e=eps) : c*e≤eps := by grind only

private def scaleContinuousNonnegative {D : Scalar → Prop} (f : ∀ z, D z → Scalar)
    (hf : ContinuousOn D f) (c : Rat) (hc : 0≤c) :
    ContinuousOn D (fun z hz => ⟨scaleRat c (f z hz).val,scaleRat_valid (f z hz).property⟩) where
  delta a ha eps := hf.delta a ha (divideRadius eps ⟨c+1,positive_successor c hc⟩)
  estimate a ha eps z hz hd := by
    have h := represented_prefix_scale_close (f z hz) (f a ha) c _ hc (hf.estimate a ha _ z hz hd)
    exact h.mono (scaled_error_le c _ _
      (Rat.le_of_lt (divideRadius eps ⟨c+1,positive_successor c hc⟩).property)
      (divideRadius_identity eps ⟨c+1,positive_successor c hc⟩))

def integerPowerRowSlope (k : Nat) (hk : 2≤k) (z : Scalar)
    (hz : InUpperHalfPlane z.val) : Scalar :=
  ⟨neg (scaleRat (k:Rat) (integerReciprocalPowerRowSum z hz (k+1) (by omega)).val),
    neg_valid (scaleRat_valid (r := (k:Rat)) (integerReciprocalPowerRowSum z hz (k+1) (by omega)).property)⟩

def integerPowerRowSlope_continuous (k : Nat) (hk : 2≤k) :
    ContinuousOn (integerPowerRowMap k hk).domain (integerPowerRowSlope k hk) :=
  negateContinuous _ (scaleContinuousNonnegative (integerPowerRowMap (k+1) (by omega)).eval
    (integerPowerRowMap_continuous (k+1) (by omega)) (k:Rat) Rat.natCast_nonneg)

theorem integerPowerRowDerivative_congr (k : Nat) (hk : 2≤k) (z w : Scalar)
    (hz : InUpperHalfPlane z.val) (hw : InUpperHalfPlane w.val) (he : z.val.Equiv w.val) :
    (integerPowerRowDerivative k hk z hz).val.Equiv (integerPowerRowDerivative k hk w hw).val :=
  equiv_trans (integerPowerRowDerivative k hk z hz).property (integerPowerRowSlope k hk z hz).property
    (integerPowerRowDerivative k hk w hw).property (integerPowerRowDerivative_next_power k hk z hz)
    (equiv_trans (integerPowerRowSlope k hk z hz).property (integerPowerRowSlope k hk w hw).property
      (integerPowerRowDerivative k hk w hw).property
      (neg_equiv (scaleRat_equiv (r := (k:Rat))
        (integerReciprocalPowerRowSum_congr z w hz hw he (k+1) (by omega))))
      (equiv_symm (integerPowerRowDerivative_next_power k hk w hw)))

def integerPowerRowDerivative_continuous (k : Nat) (hk : 2≤k) :
    ContinuousOn (integerPowerRowMap k hk).domain (integerPowerRowDerivative k hk) where
  delta := (integerPowerRowSlope_continuous k hk).delta
  estimate a ha eps z hz hd :=
    Small.congr (sub_valid (integerPowerRowSlope k hk z hz).property (integerPowerRowSlope k hk a ha).property)
      (sub_valid (integerPowerRowDerivative k hk z hz).property (integerPowerRowDerivative k hk a ha).property)
      (FunctionTheory.sub_congr (equiv_symm (integerPowerRowDerivative_next_power k hk z hz))
        (equiv_symm (integerPowerRowDerivative_next_power k hk a ha)))
      ((integerPowerRowSlope_continuous k hk).estimate a ha eps z hz hd)

def integerPowerRowMap_holomorphic (k : Nat) (hk : 2≤k) : Holomorphic (integerPowerRowMap k hk) where
  openDomain := ⟨upperRadius,upperRadius_inside⟩
  derivative := integerPowerRowDerivative k hk
  atPoint := integerPowerRowMap_hasDerivativeAt k hk
  derivative_congr := integerPowerRowDerivative_congr k hk
  continuousDerivative := integerPowerRowDerivative_continuous k hk

theorem integerPowerRowMap_holomorphic_derivative (k : Nat) (hk : 2≤k) (z : Scalar)
    (hz : InUpperHalfPlane z.val) :
    ((integerPowerRowMap_holomorphic k hk).derivative z hz).val.Equiv
      (integerPowerRowSlope k hk z hz).val := integerPowerRowDerivative_next_power k hk z hz

end ComputableAnalysis.ModularForms
