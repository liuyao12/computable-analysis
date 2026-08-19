import ComputableAnalysis.FinitePolynomialCalculus
import ComputableAnalysis.FiniteFTCIntervalRegular

/-!
# First finite trigonometric-prefix integral

The first nonzero sine Taylor prefix is exactly `x`.  This module deliberately
integrates that finite prefix before any tail or completed trigonometric value
is introduced.
-/

namespace ComputableAnalysis

namespace FiniteSinePrefix

open FormalPowerSeries
open FinitePolynomial
open ExactFunction

def sineTaylorPrefixOne : FunctionOnInterval :=
  FunctionOnInterval.exactRat
    (fun x : Rat => 1 * x + 0) 0 ((1 : Rat) / 2)

theorem sineTaylorPrefixOne_eq_identity (x : Rat) :
    taylorPrefix sinCoeff 2 x = x := by
  have hone : (1 : Rat)⁻¹ = 1 := by native_decide
  simp [taylorPrefix, integratedTaylorPrefix, taylorDerivativePrefix,
    FormalPowerSeries.coefficientShift, sinCoeff, cosCoeff, Rat.div_def, hone]
  grind

def sineTaylorPrefixOneIntegralCertificate :
    Integral.IntervalRegularIntegralCertificate sineTaylorPrefixOne := by
  have hfunction : sineTaylorPrefixOne =
      FunctionOnInterval.exactRat (fun x : Rat => 1 * x + 0) 0 ((1 : Rat) / 2) := by
    funext
    rfl
  rw [hfunction]
  exact Integral.exactRat_affine_unitSlope 1 0 0 ((1 : Rat) / 2)
    (by native_decide) (by native_decide)

def sineTaylorPrefixOneIntegralRaw : RealRaw :=
  Integral.raw sineTaylorPrefixOne sineTaylorPrefixOneIntegralCertificate

theorem sineTaylorPrefixOneIntegralRaw_valid :
    sineTaylorPrefixOneIntegralRaw.Valid := by
  exact Integral.raw_valid _ sineTaylorPrefixOneIntegralCertificate

theorem sineTaylorPrefixOneIntegralRaw_equiv_one_eighth :
    sineTaylorPrefixOneIntegralRaw.Equiv (RealRaw.ofRat (1 / 8)) := by
  unfold sineTaylorPrefixOneIntegralRaw
  have hraw :
      Integral.raw sineTaylorPrefixOne sineTaylorPrefixOneIntegralCertificate =
        RealRaw.ofRat ((1 / 2 - 0) * (1 * (0 + 1 / 2) / 2 + 0)) := by
    exact Integral.exactRat_affine_unitSlope_raw_eq_ofRat
      1 0 0 ((1 : Rat) / 2) (by native_decide) (by native_decide)
  rw [hraw]
  have hval : ((1 / 2 - 0) * (1 * (0 + 1 / 2) / 2 + 0) : Rat) = 1 / 8 := by
    native_decide
  rw [hval]
  apply RealRaw.equiv_refl
  exact RealRaw.ofRat_valid _

/-! The next finite sine prefix is the first non-affine target. -/

def sineTaylorPrefixThreeRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x - x ^ 3 / 6)

def sineTaylorPrefixThreePrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 2 / 2 - x ^ 4 / 24)

theorem sineTaylorPrefixThree_eq_cubic (x : Rat) :
    taylorPrefix sinCoeff 4 x = x - x ^ 3 / 6 := by
  have hone : (1 : Rat)⁻¹ = 1 := by native_decide
  simp [taylorPrefix, integratedTaylorPrefix, taylorDerivativePrefix,
    FormalPowerSeries.coefficientShift, sinCoeff, cosCoeff, Rat.div_def, hone]
  grind

theorem sineTaylorPrefixThree_primitive_endpoint_factor
    {a b : Rat} (ha : 0 <= a) (hab : a <= b) :
    (b ^ 2 / 2 - b ^ 4 / 24) - (a ^ 2 / 2 - a ^ 4 / 24) =
      (b - a) *
        ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) := by
  grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def sineTaylorPrefixThree_derivative_certificate
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hbound : b <= (1 : Rat) / 2) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (taylorPrefix sinCoeff 4) a b)
      (FunctionOnInterval.exactRat
        (taylorPrefix cosCoeff 3) a b) := by
  exact sineTaylorPrefix_hasDerivativeOnInterval 3 a b 1
      (by grind : -1 <= a) (by grind : b <= 1) (by native_decide)

/-! The first genuinely non-affine effective-FTC data. -/

def sineTaylorPrefixThreePartitionOf (eps : QPos) : RationalPartition 0 ((1 : Rat) / 2) :=
  RationalPartition.uniform 0 ((1 : Rat) / 2) (eps.val.den + 1)
    (by omega) (by native_decide)

def sineTaylorPrefixThreeBound
    {a b : Rat} (C : RationalSubinterval a b) (_n : Nat) : QInterval :=
  { lo := C.lower - C.lower ^ 3 / 6,
    hi := C.upper - C.upper ^ 3 / 6 }

theorem sineTaylorPrefixThree_value_mono
    {a b x : Rat} (ha : 0 <= a) (hab : a <= b)
    (hbx : x <= b) (hax : a <= x) (hb : b <= (1 : Rat) / 2) :
    a - a ^ 3 / 6 <= x - x ^ 3 / 6 /\
      x - x ^ 3 / 6 <= b - b ^ 3 / 6 := by
  have hx0 : 0 <= x := Rat.le_trans ha hax
  have hsumax : x ^ 2 + x * a + a ^ 2 <= 3 / 4 := by
    have hxa : x <= (1 : Rat) / 2 := Rat.le_trans hbx hb
    have hsqx : x ^ 2 <= (1 : Rat) / 4 := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hxa hx0
      have h2 := Rat.mul_le_mul_of_nonneg_left hxa
        (by native_decide : (0 : Rat) <= 1 / 2)
      have hhalf : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by native_decide
      rw [hhalf] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hsqa : a ^ 2 <= (1 : Rat) / 4 := by
      have haHalf : a <= (1 : Rat) / 2 := Rat.le_trans hax hxa
      have h1 := Rat.mul_le_mul_of_nonneg_right haHalf ha
      have h2 := Rat.mul_le_mul_of_nonneg_left haHalf
        (by native_decide : (0 : Rat) <= 1 / 2)
      have hhalf : (1 / 2 : Rat) * (1 / 2) = 1 / 4 := by native_decide
      rw [hhalf] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hprod : x * a <= (1 : Rat) / 4 := by
      have haHalf : a <= (1 : Rat) / 2 := Rat.le_trans hax hxa
      have h1 := Rat.mul_le_mul_of_nonneg_right hxa ha
      have h2 := Rat.mul_le_mul_of_nonneg_left haHalf
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.mul_comm]
    grind
  have hsumxb : x ^ 2 + x * b + b ^ 2 <= 3 / 4 := by
    have hxb0 : 0 <= b := Rat.le_trans hx0 hbx
    have hsqx : x ^ 2 <= (1 : Rat) / 4 := by
      have hxh : x <= (1 : Rat) / 2 := Rat.le_trans hbx hb
      have h1 := Rat.mul_le_mul_of_nonneg_right hxh hx0
      have h2 := Rat.mul_le_mul_of_nonneg_left hxh
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hsqb : b ^ 2 <= (1 : Rat) / 4 := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hb hxb0
      have h2 := Rat.mul_le_mul_of_nonneg_left hb
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hprod : x * b <= (1 : Rat) / 4 := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hbx
        (by exact Rat.le_trans hx0 hbx)
      have hbb := Rat.mul_le_mul_of_nonneg_left hb
        (by exact Rat.le_trans hx0 hbx)
      have h2 := Rat.mul_le_mul_of_nonneg_left hb
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.mul_comm]
    grind
  have hleft : (x - a) *
      (1 - (x ^ 2 + x * a + a ^ 2) / 6) =
      (x - x ^ 3 / 6) - (a - a ^ 3 / 6) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hright : (b - x) *
      (1 - (b ^ 2 + b * x + x ^ 2) / 6) =
      (b - b ^ 3 / 6) - (x - x ^ 3 / 6) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  constructor
  · have hfactor : 0 <= 1 - (x ^ 2 + x * a + a ^ 2) / 6 := by grind
    have hprod : 0 <= (x - a) *
        (1 - (x ^ 2 + x * a + a ^ 2) / 6) := by
      exact Rat.mul_nonneg (by grind) hfactor
    have hineq : 0 <= (x - x ^ 3 / 6) - (a - a ^ 3 / 6) := by
      rw [← hleft]
      exact hprod
    grind
  · have hfactor : 0 <= 1 - (x ^ 2 + x * b + b ^ 2) / 6 := by grind
    have hfactor' : 0 <= 1 - (b ^ 2 + b * x + x ^ 2) / 6 := by
      simpa [Rat.mul_comm, Rat.add_comm, Rat.add_left_comm, Rat.add_assoc]
        using hfactor
    have hdiff : 0 <= b - x := by grind
    have hprod : 0 <= (b - x) *
        (1 - (b ^ 2 + b * x + x ^ 2) / 6) := by
      exact Rat.mul_nonneg hdiff hfactor'
    have hineq : 0 <= (b - b ^ 3 / 6) - (x - x ^ 3 / 6) := by
      rw [← hright]
      exact hprod
    grind

def sineTaylorPrefixThreeDerivativeBound (eps : QPos) (k : Nat)
    (hk : k < (sineTaylorPrefixThreePartitionOf eps).pieces) :
    DerivativeBoundOnSubinterval sineTaylorPrefixThreeRaw
      ((sineTaylorPrefixThreePartitionOf eps).cell k hk) := by
  let C := (sineTaylorPrefixThreePartitionOf eps).cell k hk
  exact {
    bound := fun n => sineTaylorPrefixThreeBound C n
    evalPrecision := fun n => n
    domain_on := fun x hx => trivial
    bound_ordered := fun n => by
      unfold sineTaylorPrefixThreeBound QInterval.width
      have hmono := sineTaylorPrefixThree_value_mono C.lower_mem
        C.ordered (Rat.le_refl : C.upper <= C.upper) C.ordered C.upper_mem
      grind
    contains_values := fun n x hx => by
      unfold sineTaylorPrefixThreeBound sineTaylorPrefixThreeRaw
        RealFunRaw.exact QInterval.ContainsInterval
      exact sineTaylorPrefixThree_value_mono C.lower_mem C.ordered
        hx.2 hx.1 C.upper_mem }

theorem sineTaylorPrefixThree_average_range
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hb : b <= (1 : Rat) / 2) :
    a - a ^ 3 / 6 <=
        ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) /\
      ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) <=
        b - b ^ 3 / 6 := by
  have hleft :
      ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) -
        (a - a ^ 3 / 6) =
      (b - a) *
        (1 / 2 - (b ^ 2 + 2 * a * b + 3 * a ^ 2) / 24) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hright :
      (b - b ^ 3 / 6) -
        ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) =
      (b - a) *
        (1 / 2 - (3 * b ^ 2 + 2 * a * b + a ^ 2) / 24) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have haHalf : a <= (1 : Rat) / 2 := Rat.le_trans hab hb
  have ha2 : a ^ 2 <= (1 : Rat) / 4 := by
    have h1 := Rat.mul_le_mul_of_nonneg_right haHalf ha
    have h2 := Rat.mul_le_mul_of_nonneg_left haHalf
      (by native_decide : (0 : Rat) <= 1 / 2)
    rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
    grind [Rat.pow_succ, Rat.mul_comm]
  have hb2 : b ^ 2 <= (1 : Rat) / 4 := by
    have hb0 : 0 <= b := Rat.le_trans ha hab
    have h1 := Rat.mul_le_mul_of_nonneg_right hb hb0
    have h2 := Rat.mul_le_mul_of_nonneg_left hb
      (by native_decide : (0 : Rat) <= 1 / 2)
    rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
    grind [Rat.pow_succ, Rat.mul_comm]
  have hab2 : a * b <= (1 : Rat) / 4 := by
    have hb0 : 0 <= b := Rat.le_trans ha hab
    have h1 := Rat.mul_le_mul_of_nonneg_right hab hb0
    have h2 := Rat.mul_le_mul_of_nonneg_left hb
      (by native_decide : (0 : Rat) <= 1 / 2)
    rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
    grind [Rat.mul_comm]
  have hw : 0 <= b - a := by grind
  constructor
  · have hdiff : 0 <=
        ((a + b) / 2 -
          (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) -
          (a - a ^ 3 / 6) := by
      rw [hleft]
      have hcoef : 0 <=
          1 / 2 - (b ^ 2 + 2 * a * b + 3 * a ^ 2) / 24 := by grind
      exact Rat.mul_nonneg hw hcoef
    grind
  · have hdiff : 0 <=
        (b - b ^ 3 / 6) -
          ((a + b) / 2 -
            (b ^ 3 + b ^ 2 * a + b * a ^ 2 + a ^ 3) / 24) := by
      rw [hright]
      have hcoef : 0 <=
          1 / 2 - (3 * b ^ 2 + 2 * a * b + a ^ 2) / 24 := by grind
      exact Rat.mul_nonneg hw hcoef
    grind

theorem sineTaylorPrefixThree_bound_width_le
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hb : b <= (1 : Rat) / 2) :
    (b - b ^ 3 / 6) - (a - a ^ 3 / 6) <= b - a := by
  have hright := sineTaylorPrefixThree_average_range ha hab hb
  have hfactor := sineTaylorPrefixThree_value_mono ha hab
    (by exact Rat.le_refl) hab hb
  have hcoef : 0 <=
      1 - ((b ^ 2 + b * a + a ^ 2) / 6) := by
    have ha2 : a ^ 2 <= (1 : Rat) / 4 := by
      have haHalf : a <= (1 : Rat) / 2 := Rat.le_trans hab hb
      have ha0 : 0 <= a := ha
      have h1 := Rat.mul_le_mul_of_nonneg_right haHalf ha0
      have h2 := Rat.mul_le_mul_of_nonneg_left haHalf
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hb0 : 0 <= b := Rat.le_trans ha hab
    have hb2 : b ^ 2 <= (1 : Rat) / 4 := by
      have h1 := Rat.mul_le_mul_of_nonneg_right hb hb0
      have h2 := Rat.mul_le_mul_of_nonneg_left hb
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.pow_succ, Rat.mul_comm]
    have hab2 : a * b <= (1 : Rat) / 4 := by
      have h1 := Rat.mul_le_mul_of_nonneg_left hab hb0
      have h2 := Rat.mul_le_mul_of_nonneg_left hb
        (by native_decide : (0 : Rat) <= 1 / 2)
      rw [show (1 / 2 : Rat) * (1 / 2) = 1 / 4 by native_decide] at h2
      grind [Rat.mul_comm]
    grind
  have hid :
      (b - b ^ 3 / 6) - (a - a ^ 3 / 6) =
        (b - a) * (1 - (b ^ 2 + b * a + a ^ 2) / 6) := by
    grind [Rat.sub_eq_add_neg, Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hid]
  have hcoef_le :
      1 - ((b ^ 2 + b * a + a ^ 2) / 6) <= 1 := by
    have hb0 : 0 <= b := Rat.le_trans ha hab
    have hba0 : 0 <= b * a := Rat.mul_nonneg hb0 ha
    have hbsq : 0 <= b ^ 2 := by
      simpa [Rat.pow_succ] using RationalCircle.Stage.ratSquare_nonneg b
    have hasq : 0 <= a ^ 2 := by
      simpa [Rat.pow_succ] using RationalCircle.Stage.ratSquare_nonneg a
    have hsum : 0 <= b ^ 2 + b * a + a ^ 2 := by grind
    grind
  simpa using Rat.mul_le_mul_of_nonneg_left hcoef_le (by grind : 0 <= b - a)

theorem sineTaylorPrefixThree_local_endpoint_contained
    {a b : Rat} (C : RationalSubinterval a b) (n : Nat)
    (ha : 0 <= C.lower) (hb : C.upper <= (1 : Rat) / 2) :
    (C.scaleBound (sineTaylorPrefixThreeBound C n)).ContainsInterval
      (endpointDifferenceInterval sineTaylorPrefixThreePrimitiveRaw
        C.lower C.upper 0) := by
  have hw : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  have hfactor := sineTaylorPrefixThree_primitive_endpoint_factor
    (a := C.lower) (b := C.upper) ha C.ordered
  have havg := sineTaylorPrefixThree_average_range
    (a := C.lower) (b := C.upper) ha C.ordered hb
  unfold RationalSubinterval.scaleBound sineTaylorPrefixThreeBound
    endpointDifferenceInterval sineTaylorPrefixThreePrimitiveRaw RealFunRaw.exact
  simp only [QInterval.scaleByRat, if_pos hw]
  rw [hfactor]
  constructor
  · exact Rat.mul_le_mul_of_nonneg_left havg.1 hw
  · exact Rat.mul_le_mul_of_nonneg_left havg.2 hw

def sineTaylorPrefixThreeEffectiveFTCData :
    EffectiveDerivativeBoundFTC sineTaylorPrefixThreePrimitiveRaw
      sineTaylorPrefixThreeRaw 0 ((1 : Rat) / 2) where
  primitive_valid := RealFunRaw.exact_valid _
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := fun eps => sineTaylorPrefixThreePartitionOf eps
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  derivativeBound := sineTaylorPrefixThreeDerivativeBound
  domain_at_partition := by intro eps i hi; trivial
  localControl := by
    intro eps k hk
    let C := (sineTaylorPrefixThreePartitionOf eps).cell k hk
    let B := sineTaylorPrefixThreeDerivativeBound eps k hk
    exact {
      primitive_domain_lower := trivial
      primitive_domain_upper := trivial
      endpointPrecision := fun _ => 0
      endpoint_contained := by
        intro n
        exact sineTaylorPrefixThree_local_endpoint_contained C n
          C.lower_mem C.upper_mem }
  endpointPrecision_agreement := by intro eps k hk n; rfl
  riemann_width := by
    intro eps
    let N := eps.val.den + 1
    have hN : 0 < N := by omega
    have hbound : forall k (hk : k < N),
        (sineTaylorPrefixThreeBound
          ((RationalPartition.uniform 0 ((1 : Rat) / 2) N hN
            (by native_decide)).cell k hk) 0).width <=
          mesh 0 ((1 : Rat) / 2) N := by
      intro k hk
      let C := (RationalPartition.uniform 0 ((1 : Rat) / 2) N hN
        (by native_decide : (0 : Rat) <= 1 / 2)).cell k hk
      have hcell := sineTaylorPrefixThree_bound_width_le
        (a := C.lower) (b := C.upper) C.lower_mem C.ordered C.upper_mem
      have hmesh := RationalPartition.uniform_cell_width 0 ((1 : Rat) / 2)
        N hN (by native_decide) k hk
      change (sineTaylorPrefixThreeBound C 0).width <=
        mesh 0 ((1 : Rat) / 2) N
      calc
        (sineTaylorPrefixThreeBound C 0).width <= C.width := hcell
        _ = mesh 0 ((1 : Rat) / 2) N := hmesh
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      N hN (by native_decide : (0 : Rat) <= 1 / 2)
      (fun k hk =>
        (sineTaylorPrefixThreeDerivativeBound eps k hk).bound 0)
      (mesh 0 ((1 : Rat) / 2) N) hbound
    have hsum_bound :
        ((sineTaylorPrefixThreePartitionOf eps).boundIntegralSum
          (fun k hk =>
            (sineTaylorPrefixThreeDerivativeBound eps k hk).bound 0)).width <=
          ((1 : Rat) / 2) * mesh 0 ((1 : Rat) / 2) N := by
      change ((RationalPartition.uniform 0 ((1 : Rat) / 2) N hN
          (by native_decide)).boundIntegralSum
        (fun k hk =>
          (sineTaylorPrefixThreeDerivativeBound eps k hk).bound 0)).width <=
        ((1 : Rat) / 2) * mesh 0 ((1 : Rat) / 2) N
      have hpart : sineTaylorPrefixThreePartitionOf eps =
          RationalPartition.uniform 0 ((1 : Rat) / 2) N hN
            (by native_decide) := by
        unfold sineTaylorPrefixThreePartitionOf
        congr
      cases hpart
      calc
        ((RationalPartition.uniform 0 ((1 : Rat) / 2) N hN
            (by native_decide)).boundIntegralSum
          (fun k hk =>
            (sineTaylorPrefixThreeDerivativeBound eps k hk).bound 0)).width <=
            ((1 : Rat) / 2 - 0) * mesh 0 ((1 : Rat) / 2) N := hsum
        _ = ((1 : Rat) / 2) * mesh 0 ((1 : Rat) / 2) N := by
          congr 1 <;> grind
    have hmesh : mesh 0 ((1 : Rat) / 2) N = 1 / (2 * (N : Rat)) := by
      unfold mesh
      rw [if_neg (Nat.ne_of_gt hN), Rat.div_def]
      grind
    have hden := FTC.one_div_den_succ_le_of_pos eps.property
    have hfinal : ((1 : Rat) / 2) * mesh 0 ((1 : Rat) / 2) N <= eps.val := by
      rw [hmesh]
      dsimp [N]
      rw [Rat.natCast_add]
      have hsmall : 1 / ((eps.val.den : Rat) + 1) <= eps.val := by
        simpa [Rat.natCast_add] using hden
      have hpos : 0 < (eps.val.den : Rat) + 1 := by
        exact_mod_cast (Nat.succ_pos eps.val.den)
      have hinv : 0 <= ((eps.val.den : Rat) + 1)⁻¹ :=
        Rat.le_of_lt ((Rat.inv_pos).2 hpos)
      rw [Rat.div_def] at hsmall ⊢
      calc
        (1 / 2) * (1 / (2 * ((eps.val.den : Rat) + 1))) <=
            1 / ((eps.val.den : Rat) + 1) := by
              rw [Rat.div_def, Rat.div_def]
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= eps.val := hsmall
    exact Rat.le_trans hsum_bound hfinal
  endpoint_width := by
    intro eps
    simpa [endpointDifferenceInterval, sineTaylorPrefixThreePrimitiveRaw,
      RealFunRaw.exact, QInterval.width, Rat.sub_self] using
      (Rat.le_of_lt eps.property)

theorem sineTaylorPrefixThreeEffectiveFTC_equiv_endpoint :
    sineTaylorPrefixThreeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      sineTaylorPrefixThreeEffectiveFTCData.toDerivativeBoundFTC.endpointRaw := by
  exact effectiveDerivativeBoundFTC sineTaylorPrefixThreeEffectiveFTCData

theorem sineTaylorPrefixThreeEffectiveFTC_equiv_fortySeven_over_threeEightFour :
    sineTaylorPrefixThreeEffectiveFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      (RealRaw.ofRat (47 / 384)) := by
  let H := sineTaylorPrefixThreeEffectiveFTCData.toDerivativeBoundFTC
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  have hover := H.overlap (precisionAtStage n)
  change QInterval.Overlaps
    (H.boundedIntegralCompute n) { lo := 47 / 384, hi := 47 / 384 }
  have hzero : (1 / 2 : Rat) ^ 2 / 2 - (1 / 2 : Rat) ^ 4 / 24 =
      47 / 384 := by native_decide
  have hzero0 : (0 : Rat) ^ 2 / 2 - (0 : Rat) ^ 4 / 24 = 0 := by
    native_decide
  have hsub : (47 / 384 : Rat) - 0 = 47 / 384 := by native_decide
  simpa [H, DerivativeBoundFTC.boundedIntegralCompute,
    DerivativeBoundFTC.boundedIntegralInterval,
    DerivativeBoundFTC.endpointInterval, endpointDifferenceInterval,
    sineTaylorPrefixThreePrimitiveRaw, RealFunRaw.exact, hzero, hzero0, hsub] using hover

/-! A second concrete rung: square the same finite sine prefix.  This is the
first product-valued test for the later `sin (pi*x)^2` application. -/

def sineTaylorPrefixThreeSquareRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => (x - x ^ 3 / 6) ^ 2)

def sineTaylorPrefixThreeSquarePrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact (fun x : Rat => x ^ 3 / 3 - x ^ 5 / 15 + x ^ 7 / 252)

def sineTaylorPrefixThreeSquareDerivativeValue (x : Rat) : Rat :=
  (x - x ^ 3 / 6) ^ 2

def sineTaylorPrefixThreeSquarePrimitiveValue (x : Rat) : Rat :=
  x ^ 3 / 3 - x ^ 5 / 15 + x ^ 7 / 252

theorem sineTaylorPrefixThreeSquare_nondecreasing
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hb : b <= (1 : Rat) / 2) :
    sineTaylorPrefixThreeSquareDerivativeValue a <=
      sineTaylorPrefixThreeSquareDerivativeValue b := by
  have hpa := sineTaylorPrefixThree_value_mono
    (a := 0) (b := a) (x := a)
    (by native_decide) (by exact ha) (by exact Rat.le_refl)
    (by exact ha) (by exact Rat.le_trans hab hb)
  have hpb := sineTaylorPrefixThree_value_mono
    (a := 0) (b := b) (x := b)
    (by native_decide) (by exact Rat.le_trans ha hab) (by exact Rat.le_refl)
    (by exact Rat.le_trans ha hab) hb
  unfold sineTaylorPrefixThreeSquareDerivativeValue
  have hmul :
      (a - a ^ 3 / 6) * (a - a ^ 3 / 6) <=
        (b - b ^ 3 / 6) * (b - b ^ 3 / 6) := by
    apply rat_mul_le_mul_of_nonneg
    · have hzero : (0 : Rat) - 0 ^ 3 / 6 = 0 := by native_decide
      simpa [hzero] using hpa.1
    · exact (sineTaylorPrefixThree_value_mono
        (a := a) (b := b) (x := b) ha hab
        (by exact Rat.le_refl) (by exact hab) hb).1
    · have hzero : (0 : Rat) - 0 ^ 3 / 6 = 0 := by native_decide
      simpa [hzero] using hpa.1
    · exact (sineTaylorPrefixThree_value_mono
        (a := a) (b := b) (x := b) ha hab
        (by exact Rat.le_refl) (by exact hab) hb).1
  simpa [Rat.pow_succ] using hmul

theorem sineTaylorPrefixThreeSquare_derivative_width_le
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hb : b <= (1 : Rat) / 2) :
    sineTaylorPrefixThreeSquareDerivativeValue b -
        sineTaylorPrefixThreeSquareDerivativeValue a <= b - a := by
  have hpa := sineTaylorPrefixThree_value_mono
    (a := 0) (b := a) (x := a)
    (by native_decide) ha (by exact Rat.le_refl) ha
    (by exact Rat.le_trans hab hb)
  have hpb := sineTaylorPrefixThree_value_mono
    (a := 0) (b := b) (x := b)
    (by native_decide) (by exact Rat.le_trans ha hab) (by exact Rat.le_refl)
    (by exact Rat.le_trans ha hab) hb
  have hmono := sineTaylorPrefixThree_value_mono
    (a := a) (b := b) (x := b) ha hab (by exact Rat.le_refl) hab hb
  have hpa0 : 0 <= a - a ^ 3 / 6 := by
    have hzero : (0 : Rat) - 0 ^ 3 / 6 = 0 := by native_decide
    simpa [hzero] using hpa.1
  have hpb0 : 0 <= b - b ^ 3 / 6 := by
    have hzero : (0 : Rat) - 0 ^ 3 / 6 = 0 := by native_decide
    simpa [hzero] using hpb.1
  have hpa_upper : a - a ^ 3 / 6 <= 1 / 2 := by
    have hterm : 0 <= a ^ 3 / 6 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.pow_nonneg ha)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
    have ha_half : a <= 1 / 2 := Rat.le_trans hab hb
    grind
  have hpb_upper : b - b ^ 3 / 6 <= 1 / 2 := by
    have hterm : 0 <= b ^ 3 / 6 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.pow_nonneg (Rat.le_trans ha hab))
        (Rat.le_of_lt ((Rat.inv_pos).2 (by native_decide)))
    grind
  have hsum :
      (b - b ^ 3 / 6) + (a - a ^ 3 / 6) <= 1 := by grind
  have hcube : 0 <= b ^ 3 - a ^ 3 := by
    have hfactor : b ^ 3 - a ^ 3 =
        (b - a) * (b ^ 2 + b * a + a ^ 2) := by
      grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
        Rat.mul_assoc, Rat.mul_comm]
    rw [hfactor]
    exact Rat.mul_nonneg (by grind)
      (Rat.add_nonneg (Rat.add_nonneg
        (Rat.pow_nonneg (Rat.le_trans ha hab))
        (Rat.mul_nonneg (Rat.le_trans ha hab) ha))
        (Rat.pow_nonneg ha))
  have hdiff :
      (b - b ^ 3 / 6) - (a - a ^ 3 / 6) <= b - a := by
    grind
  have hfactor :
      (b - b ^ 3 / 6) ^ 2 - (a - a ^ 3 / 6) ^ 2 =
        ((b - b ^ 3 / 6) - (a - a ^ 3 / 6)) *
          ((b - b ^ 3 / 6) + (a - a ^ 3 / 6)) := by
    grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  unfold sineTaylorPrefixThreeSquareDerivativeValue
  rw [hfactor]
  have hprod := rat_mul_le_mul_of_nonneg
    (a := (b - b ^ 3 / 6) - (a - a ^ 3 / 6))
    (b := b - a)
    (c := (b - b ^ 3 / 6) + (a - a ^ 3 / 6))
    (d := 1)
    (by grind) hdiff (by grind) (by grind)
  grind

theorem sineTaylorPrefixThreeSquarePrimitive_secant_formula
    {a b : Rat} (hne : b - a ≠ 0) :
    differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue a (b - a) =
      (b ^ 2 + b * a + a ^ 2) / 3 -
        (b ^ 4 + b ^ 3 * a + b ^ 2 * a ^ 2 + b * a ^ 3 + a ^ 4) / 15 +
        (b ^ 6 + b ^ 5 * a + b ^ 4 * a ^ 2 + b ^ 3 * a ^ 3 +
          b ^ 2 * a ^ 4 + b * a ^ 5 + a ^ 6) / 252 := by
  unfold differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue
  rw [Rat.div_def]
  have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
    Rat.mul_inv_cancel (b - a) hne
  grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

theorem sineTaylorPrefixThreeSquarePrimitive_secant_bracket
    {a b : Rat} (ha : 0 <= a) (hab : a <= b)
    (hb : b <= (1 : Rat) / 2) (hne : b - a ≠ 0) :
    a ^ 2 - b ^ 4 / 3 + a ^ 6 / 36 <=
        differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue a (b - a) /\
      differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue a (b - a) <=
        b ^ 2 - a ^ 4 / 3 + b ^ 6 / 36 := by
  have h2 := monomial_succ_secant_derivative_bracket 2 ha hab hne
  have h4 := monomial_succ_secant_derivative_bracket 4 ha hab hne
  have h6 := monomial_succ_secant_derivative_bracket 6 ha hab hne
  have h2q : differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) =
      differenceQuotient (fun z : Rat => (1 / 3 : Rat) * z ^ 3) a (b - a) := by
    congr 1
    funext z
    rw [Rat.div_def]
    grind
  have h4q : differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) =
      differenceQuotient (fun z : Rat => (1 / 15 : Rat) * z ^ 5) a (b - a) := by
    congr 1
    funext z
    rw [Rat.div_def]
    grind
  have h6q : differenceQuotient (fun z : Rat => z ^ 7 / 252) a (b - a) =
      differenceQuotient (fun z : Rat => (1 / 252 : Rat) * z ^ 7) a (b - a) := by
    congr 1
    funext z
    rw [Rat.div_def]
    grind
  have h2s : a ^ 2 <= differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) /\
      differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) <= b ^ 2 := by
    rw [h2q, differenceQuotient_scale]
    · constructor <;> grind
    · exact hne
  have h4s : -b ^ 4 / 3 <= -differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) /\
      -differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) <= -a ^ 4 / 3 := by
    rw [h4q, differenceQuotient_scale]
    · have hlo := rat_mul_le_mul_of_nonpos_left h4.2 (by native_decide : (-1 / 15 : Rat) <= 0)
      have hhi := rat_mul_le_mul_of_nonpos_left h4.1 (by native_decide : (-1 / 15 : Rat) <= 0)
      constructor <;> grind
    · exact hne
  have h6s : a ^ 6 / 36 <= differenceQuotient (fun z : Rat => z ^ 7 / 252) a (b - a) /\
      differenceQuotient (fun z : Rat => z ^ 7 / 252) a (b - a) <= b ^ 6 / 36 := by
    rw [h6q, differenceQuotient_scale]
    · constructor <;> grind
    · exact hne
  have hsumq : differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue a (b - a) =
      differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) -
        differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) +
        differenceQuotient (fun z : Rat => z ^ 7 / 252) a (b - a) := by
    unfold differenceQuotient sineTaylorPrefixThreeSquarePrimitiveValue
    have hcancel : (b - a) * (b - a)⁻¹ = 1 :=
      Rat.mul_inv_cancel (b - a) hne
    grind [Rat.pow_succ, Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  rw [hsumq]
  constructor
  · have h := rat_add_le_add (rat_add_le_add h2s.1 h4s.1) h6s.1
    rw [show a ^ 2 - b ^ 4 / 3 + a ^ 6 / 36 =
      a ^ 2 + -b ^ 4 / 3 + a ^ 6 / 36 by grind [Rat.div_def]]
    rw [show differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) -
        differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) =
        differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) +
          -differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) by grind]
    exact h
  · have h := rat_add_le_add (rat_add_le_add h2s.2 h4s.2) h6s.2
    rw [show differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) -
        differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) =
        differenceQuotient (fun z : Rat => z ^ 3 / 3) a (b - a) +
          -differenceQuotient (fun z : Rat => z ^ 5 / 15) a (b - a) by grind]
    rw [show b ^ 2 - a ^ 4 / 3 + b ^ 6 / 36 =
      b ^ 2 + -a ^ 4 / 3 + b ^ 6 / 36 by grind [Rat.div_def]]
    exact h

theorem sineTaylorPrefixThreeSquare_eq_square (x : Rat) :
    (taylorPrefix sinCoeff 4 x) ^ 2 = (x - x ^ 3 / 6) ^ 2 := by
  rw [sineTaylorPrefixThree_eq_cubic]

theorem sineTaylorPrefixThreeSquarePrimitive_endpoint :
    ((1 / 2 : Rat) ^ 3 / 3 - (1 / 2 : Rat) ^ 5 / 15 +
      (1 / 2 : Rat) ^ 7 / 252) -
      ((0 : Rat) ^ 3 / 3 - (0 : Rat) ^ 5 / 15 + (0 : Rat) ^ 7 / 252) =
      6389 / 161280 := by
  native_decide

/-! The square prefix also has a checked coefficient-shift derivative
certificate.  This is the finite algebra that the later effective-FTC cell
bounds will consume. -/

def sineSquarePrefixDerivativeCoeffs : Nat -> Rat :=
  fun n => if n = 2 then 1 else if n = 4 then -1 / 3 else
    if n = 6 then 1 / 36 else 0

theorem sineSquarePrefixDerivativeCoeffs_primitive (x : Rat) :
    integratedTaylorPrefix sineSquarePrefixDerivativeCoeffs 7 x =
      x ^ 3 / 3 - x ^ 5 / 15 + x ^ 7 / 252 := by
  simp [integratedTaylorPrefix, sineSquarePrefixDerivativeCoeffs]
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem sineSquarePrefixDerivativeCoeffs_integrand (x : Rat) :
    taylorDerivativePrefix sineSquarePrefixDerivativeCoeffs 7 x =
      (x - x ^ 3 / 6) ^ 2 := by
  simp [taylorDerivativePrefix, sineSquarePrefixDerivativeCoeffs]
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

def sineTaylorPrefixThreeSquare_derivative_certificate
    {a b : Rat} (ha : -1 <= a) (hb : b <= 1) :
    HasDerivativeOnInterval
      (FunctionOnInterval.exactRat
        (fun x : Rat => x ^ 3 / 3 - x ^ 5 / 15 + x ^ 7 / 252) a b)
      (FunctionOnInterval.exactRat
        (fun x : Rat => (x - x ^ 3 / 6) ^ 2) a b) := by
  have h := integratedTaylorPrefix_hasDerivativeOnInterval
    sineSquarePrefixDerivativeCoeffs 7 a b 1 ha hb (by native_decide)
  have hp : integratedTaylorPrefix sineSquarePrefixDerivativeCoeffs 7 =
      (fun x : Rat => x ^ 3 / 3 - x ^ 5 / 15 + x ^ 7 / 252) := by
    funext x
    exact sineSquarePrefixDerivativeCoeffs_primitive x
  have hd : taylorDerivativePrefix sineSquarePrefixDerivativeCoeffs 7 =
      (fun x : Rat => (x - x ^ 3 / 6) ^ 2) := by
    funext x
    exact sineSquarePrefixDerivativeCoeffs_integrand x
  rw [← hp, ← hd]
  exact h

end FiniteSinePrefix

end ComputableAnalysis
