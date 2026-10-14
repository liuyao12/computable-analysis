import ComputableAnalysis.ModularForms.TauCoefficientGeometricBound
import ComputableAnalysis.ModularForms.TauNormalizedCoefficientEvaluation

/-! Transfer of integer absolute majorants to represented complex monomials. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- Signed integer scaling is bounded by the integer's absolute value. -/
theorem small_scale_integer (z : ComplexRaw) (hz : z.Valid) (r : Rat)
    (hr : Small z r) (a : Int) : Small (scaleRat (a:Rat) z) ((a.natAbs:Rat)*r) := by
  cases a with
  | ofNat n => exact LocalODE.small_scale (Rat.natCast_nonneg : 0≤(n:Rat)) hr
  | negSucc n =>
    have hs := SeriesLimitLaws.small_neg
      (LocalODE.small_scale (Rat.natCast_nonneg : 0≤((n+1:Nat):Rat)) hr)
    have hc : ((Int.negSucc n):Rat) = -((n+1:Nat):Rat) := by
      rw [Int.negSucc_eq,Rat.intCast_neg,Rat.intCast_add,Rat.intCast_natCast,Rat.natCast_add]
      rfl
    have he : (neg (scaleRat ((n+1:Nat):Rat) z)).Equiv (scaleRat ((Int.negSucc n):Rat) z) := by
      apply ComplexRawQuotient.equiv_of_ofRaw_eq
        (hleft := neg_valid (scaleRat_valid hz)) (hright := scaleRat_valid hz)
      rw [ComplexRawQuotient.ofRaw_neg _ (scaleRat_valid hz),
        ComplexRawQuotient.ofRaw_scaleRat _ _ hz,ComplexRawQuotient.ofRaw_scaleRat _ _ hz,hc]
      exact ComplexRawQuotient.neg_scaleRat _ _
    exact Small.congr (neg_valid (scaleRat_valid hz)) (scaleRat_valid hz) he hs

/-- Actual finite Euler polynomial terms have a uniform geometric bound. -/
theorem discriminantProduct_complex_term_bound (q : Scalar) (hq : Small q.val (1/1024)) (N n : Nat) :
    Small (scaleRat (discriminantProduct N n:Rat) (LocalODE.power q.val n)) (2*(1/2:Rat)^n) := by
  have hp := LocalODE.power_small q.val q.property (1/1024) (by decide +kernel) hq n
  have he : (2:Rat)*(1/1024)=1/512 := by decide +kernel
  rw [he] at hp
  exact (small_scale_integer _ (LocalODE.power_valid _ q.property n) _ hp _).mono
    (discriminantProduct_geometric_coefficient_bound N n)

/-- The unnormalized tau-series monomials inherit the same geometric estimate. -/
theorem tau_complex_term_bound (q : Scalar) (hq : Small q.val (1/1024)) (n : Nat) :
    Small (scaleRat (tau (n+1):Rat) (LocalODE.power q.val n)) (2*(1/2:Rat)^n) :=
  discriminantProduct_complex_term_bound q hq n n

end ComputableAnalysis.ModularForms
