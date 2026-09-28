import ComputableAnalysis.FiniteNBallVolume

/-!
# Ball coefficients, represented evaluations, and Gaussian finite sums

This constructs the polynomial volume model on valid nonnegative interval
presentations. It does not identify that model with a geometric volume or
identify the half-step coefficient with the Gamma integral.
-/
namespace ComputableAnalysis

/-- Coefficient of `Gamma(n/2+1)`: divide by `sqrt pi` in odd dimensions. -/
def gammaHalfCoeff : Nat → Rat
  | 0 => 1
  | 1 => 1 / 2
  | n + 2 => ((n : Rat) + 2) / 2 * gammaHalfCoeff n

/-- The two independent coefficient recursions cancel in every dimension. -/
theorem nBallCoeff_mul_gammaHalfCoeff : ∀ n,
    nBallCoeff n * gammaHalfCoeff n = 1
  | 0 => by simp [nBallCoeff, gammaHalfCoeff]
  | 1 => by simp [nBallCoeff, gammaHalfCoeff]; grind
  | n + 2 => by
    rw [nBallCoeff_succ_two, gammaHalfCoeff]
    have ih := nBallCoeff_mul_gammaHalfCoeff n
    have hn : (n : Rat) + 2 ≠ 0 := by
      have : 0 ≤ (n : Rat) := Rat.natCast_nonneg
      grind
    have hc := Rat.mul_inv_cancel ((n : Rat) + 2) hn
    grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

/-- The denominator form of the model; valid even at radius zero. -/
theorem nBallVolumeModel_gamma (n : Nat) (p r : Rat) :
    nBallVolumeModel n p r * gammaHalfCoeff n =
      p ^ nBallPiExponent n * r ^ n := by
  have h := nBallCoeff_mul_gammaHalfCoeff n
  unfold nBallVolumeModel
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The triangular sum below the diagonal in a square of sampled masses. -/
def gaussianTriangleSum : List Rat → Rat
  | [] => 0
  | x :: xs => x * finiteRatSum xs + gaussianTriangleSum xs

def gaussianDiagonalSum (xs : List Rat) : Rat :=
  finiteRatSum (xs.map (fun x => x * x))

/-- A literal square-to-two-triangles identity, retaining the diagonal.
For quadrature, each entry includes its cell width. -/
theorem gaussian_square_split (xs : List Rat) :
    finiteRatSum xs * finiteRatSum xs =
      2 * gaussianTriangleSum xs + gaussianDiagonalSum xs := by
  induction xs with
  | nil => simp [finiteRatSum, gaussianTriangleSum, gaussianDiagonalSum]; grind
  | cons x xs ih =>
    simp only [finiteRatSum, gaussianTriangleSum, gaussianDiagonalSum,
      List.map_cons] at *
    grind [Rat.mul_add, Rat.add_mul]

/-- The retained diagonal is bounded by the largest cell mass times total mass. -/
theorem gaussian_diagonal_bound (xs : List Rat) (delta : Rat)
    (h : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ delta) :
    gaussianDiagonalSum xs ≤ delta * finiteRatSum xs := by
  unfold gaussianDiagonalSum
  have hs : finiteRatSum (xs.map (fun x => delta * x)) = delta * finiteRatSum xs := by
    simpa using finiteRatSum_scale xs delta (fun x => x)
  rw [← hs]
  apply finiteRatSum_le
  intro x hx
  exact Rat.mul_le_mul_of_nonneg_right (h x hx).2 (h x hx).1

namespace NBallRaw

private theorem mul_compute {x y : RealRaw} (hx : x.Valid) (hy : y.Valid)
    (hxn : ∀ k, 0 ≤ (x.compute k).lo) (hyn : ∀ k, 0 ≤ (y.compute k).lo)
    (k : Nat) : (x * y).compute k =
      ⟨(x.compute k).lo * (y.compute k).lo,
       (x.compute k).hi * (y.compute k).hi⟩ := by
  exact QBox.mulRealInterval_of_nonneg (hxn k)
    (RealRaw.interval_order_of_valid x hx k) (hyn k)
    (RealRaw.interval_order_of_valid y hy k)

private theorem mul_valid {x y : RealRaw} (hx : x.Valid) (hy : y.Valid)
    (hxn : ∀ k, 0 ≤ (x.compute k).lo) (hyn : ∀ k, 0 ≤ (y.compute k).lo) :
    (x * y).Valid := by
  have bx : 0 < (x.compute 0).hi + 1 := by
    have := RealRaw.interval_order_of_valid x hx 0
    have := hxn 0
    grind
  have by' : 0 < (y.compute 0).hi + 1 := by
    have := RealRaw.interval_order_of_valid y hy 0
    have := hyn 0
    grind
  apply RealRaw.mul_valid_of_nonneg_bounded hx hy bx by'
  · intro k
    have := (hx.2.1 0 k (Nat.zero_le k)).2.2
    exact ⟨hxn k, by grind⟩
  · intro k
    have := (hy.2.1 0 k (Nat.zero_le k)).2.2
    exact ⟨hyn k, by grind⟩

def power (x : RealRaw) : Nat → RealRaw
  | 0 => RealRaw.ofRat 1
  | n + 1 => power x n * x

private theorem power_properties (x : RealRaw) (hx : x.Valid)
    (hxn : ∀ k, 0 ≤ (x.compute k).lo) (n : Nat) :
    (power x n).Valid ∧ (∀ k, 0 ≤ ((power x n).compute k).lo) ∧
    (∀ k, (power x n).compute k =
      ⟨(x.compute k).lo ^ n, (x.compute k).hi ^ n⟩) := by
  induction n with
  | zero =>
    exact ⟨RealRaw.ofRat_valid 1, fun k => by change (0 : Rat) ≤ 1; decide, fun _ => by simp [power]⟩
  | succ n ih =>
    refine ⟨mul_valid ih.1 hx ih.2.1 hxn, ?_, ?_⟩
    · intro k
      change 0 ≤ ((power x n * x).compute k).lo
      rw [mul_compute ih.1 hx ih.2.1 hxn]
      exact Rat.mul_nonneg (ih.2.1 k) (hxn k)
    · intro k
      change (power x n * x).compute k = _
      rw [mul_compute ih.1 hx ih.2.1 hxn, ih.2.2 k]
      simp [Rat.pow_succ]

/-- Literal endpoint evaluation; no search or quotient representative is used. -/
def volume (n : Nat) (p r : RealRaw) : RealRaw where
  compute k := nBallVolumeModelInterval n (p.compute k) (r.compute k)

private theorem volume_compute (n : Nat) (p r : RealRaw)
    (hp : p.Valid) (hr : r.Valid)
    (hpn : ∀ k, 0 ≤ (p.compute k).lo) (hrn : ∀ k, 0 ≤ (r.compute k).lo) :
    (volume n p r).compute =
      (RealRaw.scaleRat (nBallCoeff n) (power p (n / 2) * power r n)).compute := by
  funext k
  have pp := power_properties p hp hpn (n / 2)
  have rp := power_properties r hr hrn n
  simp only [RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos (nBallCoeff_nonneg n)]
  rw [mul_compute pp.1 rp.1 pp.2.1 rp.2.1, pp.2.2 k, rp.2.2 k]
  simp [volume, nBallVolumeModelInterval, nBallVolumeModel, nBallPiExponent,
    Rat.mul_assoc]

/-- Validity for arbitrary supplied nonnegative represented inputs,
including irrational radii. Bounds are inferred internally from stage zero. -/
theorem volume_valid (n : Nat) (p r : RealRaw)
    (hp : p.Valid) (hr : r.Valid)
    (hpn : ∀ k, 0 ≤ (p.compute k).lo) (hrn : ∀ k, 0 ≤ (r.compute k).lo) :
    (volume n p r).Valid := by
  change RealRaw.ValidCompute (volume n p r).compute
  rw [volume_compute n p r hp hr hpn hrn]
  have pp := power_properties p hp hpn (n / 2)
  have rp := power_properties r hr hrn n
  exact RealRaw.scaleRat_valid_of_nonneg (nBallCoeff_nonneg n)
    (mul_valid pp.1 rp.1 pp.2.1 rp.2.1)

/-- Changing either valid presentation preserves the exact represented value. -/
theorem volume_equiv (n : Nat) (p p' r r' : RealRaw)
    (hp : p.Valid) (hp' : p'.Valid) (hr : r.Valid) (hr' : r'.Valid)
    (hpn : ∀ k, 0 ≤ (p.compute k).lo) (hpn' : ∀ k, 0 ≤ (p'.compute k).lo)
    (hrn : ∀ k, 0 ≤ (r.compute k).lo) (hrn' : ∀ k, 0 ≤ (r'.compute k).lo)
    (hpp : p.Equiv p') (hrr : r.Equiv r') :
    (volume n p r).Equiv (volume n p' r') := by
  intro k
  have hpov := (RealRaw.compareAt_overlap_iff p p' k k).1
    (RealRaw.sameStageOverlap_of_equiv hp hp' hpp k)
  have hrov := (RealRaw.compareAt_overlap_iff r r' k k).1
    (RealRaw.sameStageOverlap_of_equiv hr hr' hrr k)
  apply (RealRaw.compareAt_overlap_iff _ _ k k).2
  exact ⟨nBallVolumeModel_mono n (hpn k) hpov.1 (hrn k) hrov.1,
    nBallVolumeModel_mono n (hpn' k) hpov.2 (hrn' k) hrov.2⟩

end NBallRaw
end ComputableAnalysis
