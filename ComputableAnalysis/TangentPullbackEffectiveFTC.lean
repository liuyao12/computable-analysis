import ComputableAnalysis.SinPiIntegral
import ComputableAnalysis.Calculus

namespace ComputableAnalysis

namespace SinPiIntegral

def tangentPullbackPrimitiveRaw : RealFunRaw :=
  RealFunRaw.exact tangentPullbackPrimitive

def tangentPullbackDensityRaw : RealFunRaw :=
  RealFunRaw.exact tangentPullbackDensity

theorem tangentPullbackPrimitiveRaw_valid :
    tangentPullbackPrimitiveRaw.Valid :=
  RealFunRaw.exact_valid _

theorem tangentPullbackDensityRaw_valid :
    tangentPullbackDensityRaw.Valid :=
  RealFunRaw.exact_valid _

def tangentPullbackCellBound (C : RationalSubinterval 0 1) : QInterval :=
  { lo := tangentPullbackDensity C.lower - 24 * C.width,
    hi := tangentPullbackDensity C.lower + 24 * C.width }

theorem tangentPullbackCellBound_ordered
    (C : RationalSubinterval 0 1) :
    0 <= (tangentPullbackCellBound C).width := by
  unfold tangentPullbackCellBound QInterval.width
  have hw : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  grind

theorem tangentPullbackCellBound_contains_density
    (C : RationalSubinterval 0 1) {x : Rat}
    (hx : C.contains x) :
    (tangentPullbackCellBound C).ContainsInterval
      (tangentPullbackDensityRaw.compute x 0) := by
  have hC0 : 0 <= C.lower := C.lower_mem
  have hC1 : C.upper <= 1 := C.upper_mem
  have hxa : 0 <= x := Rat.le_trans hC0 hx.1
  have hxb : x <= 1 := Rat.le_trans hx.2 hC1
  have hLip := tangentPullbackDensity_lipschitz_on_unit.2
    C.lower x hC0 (Rat.le_trans C.ordered hC1) hxa hxb
  have hdist : qabs (x - C.lower) <= C.width := by
    rw [qabs_eq_self_of_nonneg (by grind [hx.1])]
    calc
      x - C.lower <= C.upper - C.lower := by grind [hx.2]
      _ = C.width := by rfl
  have hdiff : qabs (tangentPullbackDensity x -
      tangentPullbackDensity C.lower) <= 20 * C.width := by
    have hLip' : qabs (tangentPullbackDensity x -
        tangentPullbackDensity C.lower) <= 20 * qabs (x - C.lower) := by
      have hneg : tangentPullbackDensity C.lower - tangentPullbackDensity x =
          -(tangentPullbackDensity x - tangentPullbackDensity C.lower) := by
        grind
      rw [hneg, qabs_neg] at hLip
      exact hLip
    exact Rat.le_trans hLip'
      (Rat.mul_le_mul_of_nonneg_left hdist (by native_decide))
  unfold tangentPullbackCellBound QInterval.ContainsInterval
  change tangentPullbackDensity C.lower - 24 * C.width <=
      tangentPullbackDensity x /\
    tangentPullbackDensity x <= tangentPullbackDensity C.lower + 24 * C.width
  have hlow := neg_qabs_le_self
    (tangentPullbackDensity x - tangentPullbackDensity C.lower)
  have hhigh := self_le_qabs
    (tangentPullbackDensity x - tangentPullbackDensity C.lower)
  constructor <;> grind [Rat.sub_eq_add_neg]

theorem tangentPullbackCellBound_contains_endpoint
    (C : RationalSubinterval 0 1) (n : Nat)
    (hstrict : C.lower < C.upper) :
    (C.scaleBound (tangentPullbackCellBound C)).ContainsInterval
      (endpointDifferenceInterval tangentPullbackPrimitiveRaw
        C.lower C.upper n) := by
  have hC0 : 0 <= C.lower := C.lower_mem
  have hC1 : C.upper <= 1 := C.upper_mem
  have hwidth : 0 <= C.width := by
    unfold RationalSubinterval.width
    grind [C.ordered]
  have hrect := tangentPullback_rectangle_contains_primitive_increment
    hC0 hstrict hC1
  have hprimitive :
      endpointDifferenceInterval tangentPullbackPrimitiveRaw
        C.lower C.upper n =
        { lo := tangentPullbackPrimitive C.upper -
            tangentPullbackPrimitive C.lower,
          hi := tangentPullbackPrimitive C.upper -
            tangentPullbackPrimitive C.lower } := by
    unfold endpointDifferenceInterval tangentPullbackPrimitiveRaw
      RealFunRaw.exact
    rfl
  rw [hprimitive]
  change (C.scaleBound (tangentPullbackCellBound C)).ContainsInterval _
  unfold RationalSubinterval.scaleBound
  unfold tangentPullbackCellBound
  unfold QInterval.scaleByRat
  simp only [if_pos hwidth]
  unfold QInterval.ContainsInterval at hrect ⊢
  have hwEq : C.width = C.upper - C.lower := by rfl
  have hsq : 0 <= C.width * C.width :=
    rat_square_nonneg_basic C.width
  have hlow :
      C.width * (tangentPullbackDensity C.lower - 24 * C.width) <=
        (C.upper - C.lower) * tangentPullbackDensity C.lower -
          4 * ((C.upper - C.lower) * (C.upper - C.lower)) := by
    rw [hwEq]
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  have hhigh :
        (C.upper - C.lower) * tangentPullbackDensity C.lower +
          4 * ((C.upper - C.lower) * (C.upper - C.lower)) <=
        C.width * (tangentPullbackDensity C.lower + 24 * C.width) := by
    rw [hwEq]
    grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
  constructor
  · exact Rat.le_trans hlow hrect.1
  · exact Rat.le_trans hrect.2 hhigh

def tangentPullbackCandidateCellControl
    (C : RationalSubinterval 0 1) (hstrict : C.lower < C.upper) :
    CandidateDerivativeCellControl tangentPullbackPrimitiveRaw
      tangentPullbackDensityRaw C := by
  exact {
    bound := fun _ => tangentPullbackCellBound C
    derivativeEvalPrecision := fun _ => 0
    endpointPrecision := fun _ => 0
    primitive_domain_lower := trivial
    primitive_domain_upper := trivial
    candidate_domain_on := fun _ _ => trivial
    bound_ordered := fun _ => tangentPullbackCellBound_ordered C
    candidate_contained := fun _ x hx =>
      tangentPullbackCellBound_contains_density C hx
    endpoint_difference_contained := fun _ =>
      tangentPullbackCellBound_contains_endpoint C 0 hstrict }

def tangentPullbackPartition (eps : QPos) : RationalPartition 0 1 :=
  RationalPartition.uniform 0 1 (48 * (eps.val.den + 1))
    (by omega) (by native_decide)

theorem tangentPullbackPartition_cell_strict
    (eps : QPos) {k : Nat} (hk : k < (tangentPullbackPartition eps).pieces) :
    ((tangentPullbackPartition eps).cell k hk).lower <
      ((tangentPullbackPartition eps).cell k hk).upper := by
  have hpos : 0 < mesh 0 1 (48 * (eps.val.den + 1)) := by
    change 0 < mesh 0 1 (48 * (eps.val.den + 1))
    unfold mesh
    rw [if_neg (by omega : 48 * (eps.val.den + 1) ≠ 0)]
    rw [Rat.div_def]
    exact Rat.mul_pos (by native_decide)
      ((Rat.inv_pos).2 (Rat.natCast_pos.mpr (by omega)))
  have hw : 0 < ((tangentPullbackPartition eps).cell k hk).width := by
    change 0 < ((RationalPartition.uniform 0 1
      (48 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width
    rw [RationalPartition.uniform_cell_width 0 1
      (48 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
    exact hpos
  unfold RationalSubinterval.width at hw
  exact by grind

def tangentPullbackCandidateFTCData :
    CandidateDerivativeFTC tangentPullbackPrimitiveRaw
      tangentPullbackDensityRaw 0 1 where
  primitive_domain_lower := trivial
  primitive_domain_upper := trivial
  choosePartition := tangentPullbackPartition
  chooseEndpointPrecision := fun _ => 0
  chooseBoundStage := fun _ => 0
  cellControl := by
    intro eps k hk
    exact tangentPullbackCandidateCellControl
      ((tangentPullbackPartition eps).cell k hk)
      (tangentPullbackPartition_cell_strict eps hk)
  riemann_width := by
    intro eps
    let P := tangentPullbackPartition eps
    have hbound :
        forall k (hk : k < P.pieces),
          (tangentPullbackCellBound (P.cell k hk)).width <=
            48 * mesh 0 1 P.pieces := by
      intro k hk
      have hcell : (P.cell k hk).width = mesh 0 1 P.pieces := by
        change ((RationalPartition.uniform 0 1
          (48 * (eps.val.den + 1)) (by omega) (by native_decide)).cell k hk).width =
          mesh 0 1 (48 * (eps.val.den + 1))
        rw [RationalPartition.uniform_cell_width 0 1
          (48 * (eps.val.den + 1)) (by omega) (by native_decide) k hk]
      unfold tangentPullbackCellBound QInterval.width
      rw [hcell]
      grind
    have hsum := RationalPartition.uniform_boundIntegralSum_width_le
      P.pieces P.positive (show (0 : Rat) <= 1 by native_decide)
      (fun k hk => tangentPullbackCellBound (P.cell k hk))
      (48 * mesh 0 1 P.pieces) hbound
    change ((P.boundIntegralSum
      (fun k hk => tangentPullbackCellBound (P.cell k hk))).width <=
      (1 - 0) * (48 * mesh 0 1 P.pieces)) at hsum
    change ((P.boundIntegralSum
      (fun k hk => tangentPullbackCellBound (P.cell k hk))).width <= eps.val)
    have hmesh : mesh 0 1 P.pieces =
        1 / (((48 * (eps.val.den + 1) : Nat) : Rat)) := by
      change mesh 0 1 (48 * (eps.val.den + 1)) = _
      unfold mesh
      rw [if_neg (by omega : 48 * (eps.val.den + 1) ≠ 0)]
      rw [Rat.div_def, Rat.natCast_mul, Rat.natCast_add]
      grind [Rat.mul_assoc, Rat.mul_comm]
    have hone : 1 / (((eps.val.den + 1 : Nat) : Rat)) <= eps.val :=
      FTC.one_div_den_succ_le_of_pos eps.property
    rw [hmesh] at hsum
    have hsum' :
        (P.boundIntegralSum
          (fun k hk => tangentPullbackCellBound (P.cell k hk))).width <=
          1 / (((eps.val.den + 1 : Nat) : Rat)) := by
      calc
        (P.boundIntegralSum
            (fun k hk => tangentPullbackCellBound (P.cell k hk))).width <=
            (1 - 0) * (48 * (1 / (((48 * (eps.val.den + 1) : Nat) : Rat)))) := by
              simpa using hsum
        _ = 1 / (((eps.val.den + 1 : Nat) : Rat)) := by
          rw [Rat.natCast_mul, Rat.natCast_add, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm]
    exact Rat.le_trans hsum' hone
  endpoint_width := by
    intro eps
    change (endpointDifferenceInterval tangentPullbackPrimitiveRaw 0 1 0).width <= eps.val
    have hz :
        (endpointDifferenceInterval tangentPullbackPrimitiveRaw 0 1 0).width = 0 := by
      native_decide
    rw [hz]
    exact Rat.le_of_lt eps.property
  overlap := by
    intro eps
    let P := tangentPullbackPartition eps
    apply RationalPartition.boundIntegralSum_overlaps_endpointDifference
      P tangentPullbackPrimitiveRaw 0 tangentPullbackPrimitiveRaw_valid
    · intro i hi
      trivial
    · intro k hk
      exact (tangentPullbackCandidateCellControl (P.cell k hk)
        (tangentPullbackPartition_cell_strict eps hk)).endpoint_difference_contained 0

theorem tangentPullbackEffectiveFTC_equiv_endpoint :
    tangentPullbackCandidateFTCData.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      tangentPullbackCandidateFTCData.toDerivativeBoundFTC.endpointRaw :=
  candidateDerivativeFTC tangentPullbackCandidateFTCData

theorem tangentPullbackEndpoint_equiv_one :
    tangentPullbackCandidateFTCData.toDerivativeBoundFTC.endpointRaw.Equiv
      (RealRaw.ofRat 1) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff
    tangentPullbackCandidateFTCData.toDerivativeBoundFTC.endpointRaw
    (RealRaw.ofRat 1) n n).2
  change QInterval.Overlaps
    (endpointDifferenceInterval tangentPullbackPrimitiveRaw 0 1 0)
    { lo := 1, hi := 1 }
  unfold QInterval.Overlaps endpointDifferenceInterval
  native_decide

end SinPiIntegral

end ComputableAnalysis
