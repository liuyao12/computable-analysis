import ComputableAnalysis.Differential
import ComputableAnalysis.PowerSeries

/-!
# Direct scalar ODE uniqueness by finite mesh contraction

This module is deliberately separate from `PeanoBaker`.  For the scalar
initial-value problem `f' = f`, a direct rational mesh proof is shorter than
a general Volterra or Peano--Baker argument.  On a sufficiently short time
block, a finite subdivision turns the zero-initial difference estimate into a
strict contraction.  Refining the subdivision gives a sequence of rational
error envelopes, each at most half its predecessor.

The analytic work is to build the one-step mesh estimate from the two
derivative certificates.  The closure below is completely finite: the
explicit dyadic schedule converts repeated halving into equality of raw
interval representatives, with no complete function space and no Picard
iteration.
-/

namespace ComputableAnalysis

namespace ScalarODE

/-- A direct mesh-contraction certificate for one nonnegative rational error.

`bound round` is the rational envelope produced after `round` refinement
sweeps of a finite mesh.  The only analytic input is the checked local mesh
step `halve`; all later reasoning is rational arithmetic. -/
structure DirectMeshHalvingCertificate (error : Rat) where
  bound : Nat -> Rat
  error_nonneg : 0 <= error
  error_le_bound : forall round, error <= bound round
  halve : forall round,
    bound (round + 1) <= bound round * ((1 : Rat) / 2)

namespace DirectMeshHalvingCertificate

/-- Every finite refinement envelope is bounded by the explicit dyadic
envelope determined by the initial sweep. -/
theorem bound_le_geometric {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    forall round,
      certificate.bound round <=
        certificate.bound 0 * ((1 : Rat) / 2) ^ round
  | 0 => by
      simp
  | round + 1 => by
      have ih := bound_le_geometric certificate round
      calc
        certificate.bound (round + 1) <=
            certificate.bound round * ((1 : Rat) / 2) :=
          certificate.halve round
        _ <= (certificate.bound 0 * ((1 : Rat) / 2) ^ round) *
              ((1 : Rat) / 2) :=
          Rat.mul_le_mul_of_nonneg_right ih (by native_decide)
        _ = certificate.bound 0 * ((1 : Rat) / 2) ^ (round + 1) := by
          rw [Rat.pow_succ]
          grind [Rat.mul_assoc]

/-- The initial finite-mesh envelope is nonnegative, because it bounds a
nonnegative error. -/
theorem initial_bound_nonneg {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    0 <= certificate.bound 0 :=
  Rat.le_trans certificate.error_nonneg (certificate.error_le_bound 0)

/-- Repeated direct mesh contraction forces its error to be literally zero.

The proof chooses the executable refinement count supplied by
`RationalMajorant.halfDecayShift` for the tolerance `error / 2`; therefore it
does not invoke a real-number limit or an Archimedean axiom. -/
theorem error_eq_zero {error : Rat}
    (certificate : DirectMeshHalvingCertificate error) :
    error = 0 := by
  by_cases hzero : error = 0
  · exact hzero
  · have herrorPos : 0 < error :=
      Rat.lt_of_le_of_ne certificate.error_nonneg (Ne.symm hzero)
    let eps : QPos :=
      { val := error / 2
        property := by
          rw [Rat.div_def]
          exact Rat.mul_pos herrorPos
            ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2)) }
    have hround := certificate.error_le_bound
      (RationalMajorant.halfDecayShift (certificate.bound 0) eps)
    have hgeometric := bound_le_geometric certificate
      (RationalMajorant.halfDecayShift (certificate.bound 0) eps)
    have hsmall := RationalMajorant.halfDecayShift_spec
      (initial_bound_nonneg certificate) eps
    have hhalf : error <= error / 2 := by
      exact Rat.le_trans hround (Rat.le_trans hgeometric hsmall)
    have hstrict : error / 2 < error := by
      rw [Rat.div_def]
      have hinv : (2 : Rat)⁻¹ < 1 := by native_decide
      calc
        error * (2 : Rat)⁻¹ < error * 1 :=
          Rat.mul_lt_mul_of_pos_left hinv herrorPos
        _ = error := Rat.mul_one _
    have hnot : ¬ error <= error / 2 := by
      simpa [Rat.not_le] using hstrict
    exact False.elim (hnot hhalf)

end DirectMeshHalvingCertificate

/-- A direct finite-mesh comparison for two scalar self-derivative solutions.

For each rational input, the analytic layer supplies the error envelope from
finite subdivisions of the interval between the common initial coordinate and
that input.  The fields intentionally do not mention Peano--Baker, Volterra,
or Picard iteration. -/
structure SelfDerivativeDirectMeshComparison
    (f g : FunctionOnInterval)
    (_hf : SolvesSelfDerivativeOnInterval f)
    (_hg : SolvesSelfDerivativeOnInterval g) where
  same_lower : f.lower = g.lower
  same_upper : f.upper = g.upper
  error : Rat -> Rat
  mesh_halving :
    forall x, DirectMeshHalvingCertificate (error x)
  equivalent_of_error_zero :
    forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
      error x = 0 ->
        (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
          (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

namespace SelfDerivativeDirectMeshComparison

/-- A direct mesh comparison closes to function equivalence pointwise. -/
theorem equivalent
    {f g : FunctionOnInterval}
    {hf : SolvesSelfDerivativeOnInterval f}
    {hg : SolvesSelfDerivativeOnInterval g}
    (comparison : SelfDerivativeDirectMeshComparison f g hf hg) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨comparison.same_lower, comparison.same_upper, ?_⟩
  intro x hxF hxG
  apply comparison.equivalent_of_error_zero x hxF hxG
  exact (comparison.mesh_halving x).error_eq_zero

end SelfDerivativeDirectMeshComparison

/-- The analytic provider for direct scalar initial-value uniqueness.

To construct it by hand, subtract the two candidate finite-difference
certificates, cover a short rational time block by a finite mesh, and verify
that one full sweep halves its rational error envelope.  Longer intervals are
handled by a finite chain of such blocks. -/
def SelfDerivativeDirectMeshUniqueness : Prop :=
  forall f g,
    (hf : SolvesSelfDerivativeOnInterval f) ->
    (hg : SolvesSelfDerivativeOnInterval g) ->
    hf.initial = hg.initial ->
    hf.initial_value.Equiv hg.initial_value ->
    Nonempty (SelfDerivativeDirectMeshComparison f g hf hg)

/-- Direct finite mesh contraction supplies uniqueness for `f' = f` with a
common certified initial value. -/
theorem selfDerivativeInitialValueUnique_of_directMesh
    (hdirect : SelfDerivativeDirectMeshUniqueness) :
    SelfDerivativeInitialValueUnique := by
  intro f g hf hg hinitial hvalue
  rcases hdirect f g hf hg hinitial hvalue with ⟨comparison⟩
  exact comparison.equivalent

end ScalarODE

end ComputableAnalysis
