import ComputableAnalysis.FiniteBisectionIteration

/-!
# Reusable finite inverse-search interface

An inverse is represented by a finite target bracket.  A monotone rational
map, an input interval, and endpoint inequalities determine a bisection
computation whose output interval contains the requested target preimage.
-/

namespace ComputableAnalysis

structure FiniteInverseSearchCertificate where
  map : Rat → Rat
  target : Rat
  initialInterval : QInterval
  stage : Nat
  ordered : initialInterval.lo ≤ initialInterval.hi
  lower_bracket : map initialInterval.lo ≤ target
  upper_bracket : target ≤ map initialInterval.hi

def FiniteInverseSearchCertificate.output
    (certificate : FiniteInverseSearchCertificate) : QInterval :=
  monotoneTargetBisectionIterate certificate.map certificate.target
    certificate.stage certificate.initialInterval

theorem FiniteInverseSearchCertificate.output_bracket
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi := by
  exact monotoneBisectionIterate_preserves_target_bracket
    certificate.target certificate.ordered certificate.lower_bracket
    certificate.upper_bracket certificate.stage

theorem FiniteInverseSearchCertificate.output_width
    (certificate : FiniteInverseSearchCertificate) :
    certificate.output.width =
      certificate.initialInterval.width /
        (2 ^ certificate.stage : Rat) := by
  exact monotoneTargetBisectionIterate_width certificate.target certificate.stage

theorem FiniteInverseSearchCertificate.output_midpoint_witness
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi /\
      certificate.output.lo ≤ certificate.output.midpoint /\
      certificate.output.midpoint ≤ certificate.output.hi := by
  have hbracket := certificate.output_bracket
  have hordered := monotoneTargetBisectionIterate_ordered
    (f := certificate.map) (I := certificate.initialInterval)
    certificate.target certificate.ordered certificate.stage
  have hmid := QInterval.midpoint_mem hordered
  exact ⟨hbracket.1, hbracket.2, hmid.1, hmid.2⟩

theorem FiniteInverseSearchCertificate.stage_bracket
    (certificate : FiniteInverseSearchCertificate) (n : Nat) :
    certificate.map
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).lo <= certificate.target /\
      certificate.target <= certificate.map
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).hi := by
  exact monotoneBisectionIterate_preserves_target_bracket
    certificate.target certificate.ordered certificate.lower_bracket
    certificate.upper_bracket n

theorem FiniteInverseSearchCertificate.stage_width
    (certificate : FiniteInverseSearchCertificate) (n : Nat) :
    (monotoneTargetBisectionIterate certificate.map certificate.target n
      certificate.initialInterval).width =
        certificate.initialInterval.width / (2 ^ n : Rat) := by
  exact monotoneTargetBisectionIterate_width certificate.target n

/-! The classical intermediate-value step becomes an explicit error budget when
the map is monotone and Lipschitz on the initial interval.  The bisection
midpoint is then a rational representative whose target residual is bounded
by the Lipschitz constant times the current interval width. -/
theorem FiniteInverseSearchCertificate.midpoint_residual_le_lipschitz_width
    (certificate : FiniteInverseSearchCertificate) (L : Rat)
    (hL : 0 <= L)
    (hmono : ∀ ⦃x y : Rat⦄, x <= y -> certificate.map x <= certificate.map y)
    (hlip : ∀ x y : Rat,
      certificate.initialInterval.lo <= x ->
      x <= certificate.initialInterval.hi ->
      certificate.initialInterval.lo <= y ->
      y <= certificate.initialInterval.hi ->
      qabs (certificate.map x - certificate.map y) <=
        L * qabs (x - y)) :
    qabs (certificate.map certificate.output.midpoint - certificate.target) <=
      L * certificate.output.width := by
  let I := certificate.output
  have hI : I.lo <= I.hi := by
    dsimp [I]
    exact monotoneTargetBisectionIterate_ordered
      certificate.target certificate.ordered certificate.stage
  have hsub := monotoneTargetBisectionIterate_subinterval
    (f := certificate.map) certificate.target certificate.ordered certificate.stage
  have hmid := QInterval.midpoint_mem hI
  have hbracket := certificate.output_bracket
  have hmap_lo_mid : certificate.map I.lo <= certificate.map I.midpoint := by
    apply hmono
    exact hmid.1
  have hmap_mid_hi : certificate.map I.midpoint <= certificate.map I.hi := by
    apply hmono
    exact hmid.2
  have hcommon := qabs_sub_le_of_common_bounds
    hmap_lo_mid hmap_mid_hi hbracket.1 hbracket.2
  have hIlo_initial : certificate.initialInterval.lo <= I.lo := hsub.1
  have hIhi_initial : I.hi <= certificate.initialInterval.hi := hsub.2
  have hIhi_lower : certificate.initialInterval.lo <= I.hi :=
    Rat.le_trans hIlo_initial hI
  have hIlo_upper : I.lo <= certificate.initialInterval.hi :=
    Rat.le_trans hI hIhi_initial
  have himage_lip := hlip I.hi I.lo
    hIhi_lower hIhi_initial hIlo_initial hIlo_upper
  have hhi_lo : 0 <= I.hi - I.lo := by grind
  have hqabs_width : qabs (I.hi - I.lo) = I.width := by
    rw [qabs_eq_self_of_nonneg hhi_lo]
    rfl
  have himage : certificate.map I.hi - certificate.map I.lo <=
      L * I.width := by
    have hmap_order : certificate.map I.lo <= certificate.map I.hi :=
      hmono (hI)
    have himage_abs := himage_lip
    rw [qabs_eq_self_of_nonneg (by grind :
      0 <= certificate.map I.hi - certificate.map I.lo),
      hqabs_width] at himage_abs
    exact himage_abs
  dsimp [I] at hcommon himage ⊢
  exact Rat.le_trans hcommon himage

/-! The finite inverse search can also be run at every stage, producing the
nested interval algorithm used by `RealRaw`.  The only extra hypothesis is
the harmless normalization that the initial interval has width at most one;
the bisection width law then supplies the explicit precision modulus. -/
def FiniteInverseSearchCertificate.toRealRaw
    (certificate : FiniteInverseSearchCertificate) : RealRaw where
  compute := fun n =>
    monotoneTargetBisectionIterate certificate.map certificate.target n
      certificate.initialInterval

theorem FiniteInverseSearchCertificate.toRealRaw_valid
    (certificate : FiniteInverseSearchCertificate)
    (hwidth : certificate.initialInterval.width <= 1) :
    certificate.toRealRaw.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <=
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).hi -
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).lo
    have hordered := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered n
    grind
  · intro n m hnm
    change
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target m
            certificate.initialInterval).lo /\
        (monotoneTargetBisectionIterate certificate.map certificate.target m
          certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target m
            certificate.initialInterval).hi /\
        (monotoneTargetBisectionIterate certificate.map certificate.target m
          certificate.initialInterval).hi <=
          (monotoneTargetBisectionIterate certificate.map certificate.target n
            certificate.initialInterval).hi
    have hlater := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hnm
    have hm := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered m
    exact ⟨hlater.1, hm, hlater.2⟩
  · intro eps
    refine ⟨eps.val.den, ?_⟩
    intro n hn
    have hreach := monotoneTargetBisectionIterate_reaches_of_positive_tolerance
      (f := certificate.map) (I := certificate.initialInterval)
      certificate.target hwidth eps
    have hsub := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hn
    change
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).width <= eps.val
    have hwidth_mono :
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).width <=
          (monotoneTargetBisectionIterate certificate.map certificate.target
            eps.val.den certificate.initialInterval).width := by
      change
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target n
              certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target
            eps.val.den certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target
              eps.val.den certificate.initialInterval).lo
      grind [hsub.1, hsub.2]
    exact Rat.le_trans hwidth_mono hreach

def finiteInverseSearchCertificate
    (map : Rat → Rat) (target : Rat) (initialInterval : QInterval)
    (stage : Nat) (ordered : initialInterval.lo ≤ initialInterval.hi)
    (lower_bracket : map initialInterval.lo ≤ target)
    (upper_bracket : target ≤ map initialInterval.hi) :
    FiniteInverseSearchCertificate where
  map := map
  target := target
  initialInterval := initialInterval
  stage := stage
  ordered := ordered
  lower_bracket := lower_bracket
  upper_bracket := upper_bracket

/-- A finite grid cannot jump over a target interval when each successive
image increment is no wider than that interval.  This is the discrete
crossing principle behind constructive inverse approximation: it is entirely
rational and contains no appeal to an attained intermediate value. -/
theorem finiteGrid_interval_crossing
    {f : Rat -> Rat} {v : Nat -> Rat} {N : Nat}
    {lo hi : Rat} (hN : 0 < N)
    (hlo : 0 <= lo) (hhi : hi <= 1) (hlohi : lo <= hi)
    (hstart : f (v 0) = 0) (hend : f (v N) = 1)
    (hstep : forall k, k < N ->
      f (v (k + 1)) - f (v k) <= hi - lo) :
    exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi := by
  by_cases hhit : exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi
  · exact hhit
  · exfalso
    have hno : forall k, k <= N ->
        ¬(lo <= f (v k) /\ f (v k) <= hi) := by
      intro k hk hinside
      exact hhit ⟨k, hk, hinside.1, hinside.2⟩
    have hbelow : forall k, k <= N -> f (v k) < lo := by
      intro k hk
      induction k with
      | zero =>
          have hn := hno 0 (by omega)
          rw [hstart] at hn ⊢
          have hnot : ¬lo <= (0 : Rat) := by
            intro hzero
            apply hn
            exact ⟨hzero, by grind⟩
          exact Rat.not_le.mp hnot
      | succ k ih =>
          have hklt : k < N := by omega
          have hprev := ih (by omega)
          have hs := hstep k hklt
          have hupp : f (v (k + 1)) < hi := by
            have hstrict : f (v k) + (hi - lo) < hi := by grind
            grind [Rat.sub_eq_add_neg]
          have hn := hno (k + 1) hk
          have hnot : ¬lo <= f (v (k + 1)) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_of_lt hupp⟩
          exact Rat.not_le.mp hnot
    have hfinal := hbelow N (by omega)
    rw [hend] at hfinal
    exact by grind

/-- Endpoint-parametric form of `finiteGrid_interval_crossing`, suitable for
interval algorithms whose endpoint enclosures are not normalized to zero and
one. -/
theorem finiteGrid_interval_crossing_between
    {f : Rat -> Rat} {v : Nat -> Rat} {N : Nat}
    {lo hi : Rat} (hN : 0 < N) (hlohi : lo <= hi)
    (hstart : f (v 0) <= hi) (hend : lo <= f (v N))
    (hstep : forall k, k < N ->
      f (v (k + 1)) - f (v k) <= hi - lo) :
    exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi := by
  by_cases hhit : exists k, k <= N /\ lo <= f (v k) /\ f (v k) <= hi
  · exact hhit
  · exfalso
    have hno : forall k, k <= N ->
        ¬(lo <= f (v k) /\ f (v k) <= hi) := by
      intro k hk hbad
      exact hhit ⟨k, hk, hbad.1, hbad.2⟩
    have hbelow : forall k, k <= N -> f (v k) < lo := by
      intro k hk
      induction k with
      | zero =>
          have hn := hno 0 (by omega)
          have hnot : ¬lo <= f (v 0) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_trans hstart (by grind)⟩
          exact Rat.not_le.mp hnot
      | succ k ih =>
          have hklt : k < N := by omega
          have hprev := ih (by omega)
          have hs := hstep k hklt
          have hupp : f (v (k + 1)) < hi := by
            have hstrict : f (v k) + (hi - lo) < hi := by grind
            grind [Rat.sub_eq_add_neg]
          have hn := hno (k + 1) hk
          have hnot : ¬lo <= f (v (k + 1)) := by
            intro hlow
            apply hn
            exact ⟨hlow, Rat.le_of_lt hupp⟩
          exact Rat.not_le.mp hnot
    exact (Rat.not_lt.mpr hend) (hbelow N (by omega))

/-- The rational point at grid index `k` in a closed rational interval. -/
def finiteUniformGridPoint (I : QInterval) (N k : Nat) : Rat :=
  I.lo + I.width * ((k : Rat) / (N : Rat))

theorem finiteUniformGridPoint_zero (I : QInterval) (N : Nat) :
    finiteUniformGridPoint I N 0 = I.lo := by
  simp [finiteUniformGridPoint, Rat.div_def, Rat.zero_mul, Rat.add_zero]

theorem finiteUniformGridPoint_last (I : QInterval) {N : Nat} (hN : 0 < N) :
    finiteUniformGridPoint I N N = I.hi := by
  unfold finiteUniformGridPoint
  rw [Rat.div_def, Rat.mul_inv_cancel _
    (Rat.ne_of_gt ((Rat.natCast_pos).2 hN)), Rat.mul_one]
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Every finite uniform grid point lies in its source interval. -/
theorem finiteUniformGridPoint_mem
    {I : QInterval} {N k : Nat} (hN : 0 < N)
    (hI : I.lo <= I.hi) (hk : k <= N) :
    I.lo <= finiteUniformGridPoint I N k /\
      finiteUniformGridPoint I N k <= I.hi := by
  have hwidth : 0 <= I.width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hden : 0 < (N : Rat) := (Rat.natCast_pos).2 hN
  have hfrac0 : 0 <= (k : Rat) / (N : Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg Rat.natCast_nonneg
      (Rat.le_of_lt (Rat.inv_pos.2 hden))
  have hfrac1 : (k : Rat) / (N : Rat) <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := (N : Rat))
    · rw [Rat.div_def, Rat.mul_assoc,
        Rat.inv_mul_cancel _ (Rat.ne_of_gt hden), Rat.mul_one]
      simpa [Rat.one_mul] using (Rat.natCast_le_natCast.2 hk)
    · exact hden
  constructor
  · unfold finiteUniformGridPoint
    grind [Rat.mul_nonneg hwidth hfrac0]
  · unfold finiteUniformGridPoint
    have hscaled := Rat.mul_le_mul_of_nonneg_left hfrac1 hwidth
    unfold QInterval.width at hscaled ⊢
    grind [Rat.sub_eq_add_neg]

/-- Consecutive uniform grid points are separated by one exact mesh width. -/
theorem finiteUniformGridPoint_succ_sub
    (I : QInterval) {N k : Nat} (hN : 0 < N) :
    finiteUniformGridPoint I N (k + 1) - finiteUniformGridPoint I N k =
      I.width / (N : Rat) := by
  unfold finiteUniformGridPoint
  rw [Rat.div_def, Rat.div_def]
  have hNne : (N : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hN)
  have hnat : ((k + 1 : Nat) : Rat) = (k : Rat) + 1 := by
    norm_cast
  rw [hnat]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.mul_inv_cancel _ hNne]

end ComputableAnalysis
