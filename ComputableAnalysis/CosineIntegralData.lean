import ComputableAnalysis.GeometricSineDerivative
import ComputableAnalysis.DovetailedFTC
import ComputableAnalysis.IntervalSelections
import ComputableAnalysis.FiniteRiemannAlgebra

/-! The algorithms and common rational algebra for both cosine integral
proofs. Neither endpoint identity nor any sine derivative theorem is used
in these definitions. -/
namespace ComputableAnalysis
namespace CosineFTC

open IntegralIdentities SinPiIntegral GeometricSineDerivative FiniteRiemannAlgebra

/-- Totalization outside the public chart is used only to write finite
sample lists. The interval-facing API below never samples outside the chart. -/
def sine (B : ArctanInverseBisection) (x : Rat) : RealRaw :=
  if hx : OnHalf x then sinPiRawOfArctan B x hx else RealRaw.zero

def cosine (B : ArctanInverseBisection) (x : Rat) : RealRaw :=
  if hx : OnHalf x then cosPiRawOfArctan B x hx else RealRaw.zero

theorem sine_valid (B : ArctanInverseBisection) (x : Rat) : (sine B x).Valid := by
  unfold sine
  split
  · exact sinPiRawOfArctan_valid B x _
  · exact RealRaw.ofRat_valid 0

theorem cosine_valid (B : ArctanInverseBisection) (x : Rat) : (cosine B x).Valid := by
  unfold cosine
  split
  · exact cosPiRawOfArctan_valid B x _
  · exact RealRaw.ofRat_valid 0

/-- The literal left Riemann sum on a fixed uniform mesh of `k+1` cells. -/
def fixedMesh (B : ArctanInverseBisection) (a b : Rat) (k : Nat) : RealRaw :=
  Integral.finiteRawSum ((List.range (k+1)).map (fun i =>
    RealRaw.scaleRat (mesh a b (k+1)) (cosine B (leftPoint a b (k+1) i))))

theorem fixedMesh_valid (B : ArctanInverseBisection) (a b : Rat) (k : Nat) :
    (fixedMesh B a b k).Valid := by
  apply Integral.finiteRawSum_valid
  intro X hX
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hX
  exact RealRaw.scaleRat_valid (cosine_valid B _)

theorem finiteRawSum_eq_fold (xs : List Nat) (f : Nat -> RealRaw) (q : Nat) :
    ((Integral.finiteRawSum (xs.map f)).compute q) =
      xs.foldl (fun I i => QInterval.addInterval I ((f i).compute q)) {lo := 0, hi := 0} := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      change QInterval.addInterval ((f i).compute q)
        ((Integral.finiteRawSum (xs.map f)).compute q) =
          xs.foldl (fun I j => QInterval.addInterval I ((f j).compute q))
            (QInterval.addInterval {lo := 0, hi := 0} ((f i).compute q))
      rw [QInterval.zero_addInterval, QInterval.addInterval_fold_initial, ih]

/-- The finite sums above are exactly the repository's existing left
Riemann-rectangle computation, not merely equivalent limiting algorithms. -/
theorem fixedMesh_compute_eq_riemannLeftInterval
    (B : ArctanInverseBisection) {a b : Rat} (hab : a <= b) (k q : Nat) :
    (fixedMesh B a b k).compute q =
      riemannLeftInterval
        { domain := OnHalf, compute := fun x n => (cosine B x).compute n }
        a b (k+1) q := by
  have hh := mesh_nonneg_of_le (Nat.succ_pos k) hab
  rw [fixedMesh, finiteRawSum_eq_fold]
  simp only [RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos hh,
    riemannLeftInterval, QInterval.addInterval]

theorem fixedMesh_lo (B : ArctanInverseBisection)
    {a b : Rat} (hab : a <= b) (k q : Nat) :
    ((fixedMesh B a b k).compute q).lo =
      sum (fun i => mesh a b (k+1) *
        ((cosine B (leftPoint a b (k+1) i)).compute q).lo) (k+1) := by
  have hh := mesh_nonneg_of_le (Nat.succ_pos k) hab
  simp only [fixedMesh, finiteRawSum_lo, List.map_map, Function.comp_def, sum,
    RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos hh]

/-- A conservative, explicit discretization error; no sample precision or
endpoint evaluation enters this expression. -/
def error (a b : Rat) (k : Nat) : Rat :=
  4000 * (b-a) * (b-a) / ((k+1 : Nat) : Rat)

theorem error_eq_mesh (a b : Rat) (k : Nat) :
    error a b k = ((k+1 : Nat) : Rat) *
      (4000 * mesh a b (k+1) * mesh a b (k+1)) := by
  have h := natCast_mul_mesh_eq_sub (a := a) (b := b) (Nat.succ_pos k)
  unfold error mesh
  rw [if_neg (Nat.ne_of_gt (Nat.succ_pos k))]
  simp only [Rat.div_def]
  change ((k+1 : Nat) : Rat) * mesh a b (k+1) = b-a at h
  have hne : ((k+1 : Nat) : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 (Nat.succ_pos k))
  have hc := Rat.mul_inv_cancel ((k+1 : Nat) : Rat) hne
  grind

theorem error_shrinks {a b : Rat}
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    ShrinksToZero (error a b) := by
  apply shrinksToZero_of_natOverSuccBound (C := 4000)
  intro k
  rw [show ((4000 : Nat) : Rat) = (4000 : Rat) by decide +kernel]
  have hL0 : 0 <= b-a := by grind
  have hL1 : b-a <= 1 := by
    have ha0 := ha.1
    have hb1 := hb.2
    simp only [Rat.div_def] at hb1
    grind
  have hs := Rat.mul_le_mul_of_nonneg_left hL1 hL0
  have hsq : (b-a)*(b-a) <= 1 := by grind
  have h4000 := Rat.mul_le_mul_of_nonneg_left hsq (by decide : (0 : Rat) <= 4000)
  have hi : 0 <= (((k+1 : Nat) : Rat))⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos k)))
  have hm := Rat.mul_le_mul_of_nonneg_right h4000 hi
  simpa only [error, Rat.div_def, Rat.mul_one, Rat.mul_assoc] using hm

/-- The independently computed endpoint value, in the project's normalized
angle convention rather than the radian convention. -/
def endpoint (B : ArctanInverseBisection) (a b : Rat) : RealRaw :=
  RealRaw.mul reciprocalPiRaw (sine B b - sine B a)

theorem endpoint_valid (B : ArctanInverseBisection) (a b : Rat) :
    (endpoint B a b).Valid :=
  RealRaw.mul_valid reciprocalPiRaw_valid
    (RealRaw.sub_valid (sine_valid B b) (sine_valid B a))

theorem grid_onHalf {a b : Rat} (ha : OnHalf a) (hb : OnHalf b)
    (hab : a <= b) {m i : Nat} (hm : 0 < m) (hi : i <= m) :
    OnHalf (leftPoint a b m i) := by
  have hl := leftPoint_monotone (a := a) (b := b) hm hab (Nat.zero_le i)
  have hu := leftPoint_monotone (a := a) (b := b) hm hab hi
  rw [leftPoint_zero] at hl
  rw [leftPoint_endpoint hm] at hu
  exact ⟨Rat.le_trans ha.1 hl, Rat.le_trans hu hb.2⟩

theorem reciprocal_corner (n : Nat) :
    0 <= (reciprocalPiRaw.compute n).hi ∧
    (reciprocalPiRaw.compute n).hi <= 1 ∧
    (reciprocalPiRaw.compute n).hi * (piCircleArea.compute n).lo = 1 := by
  have hr := reciprocalPiRaw_bounds n
  have ho := RealRaw.interval_order_of_valid _ reciprocalPiRaw_valid n
  have hp := CauchyPi.piCircleArea_valid.2.1 0 n (Nat.zero_le n)
  have hz : piCircleArea.compute 0 = ({lo := 2, hi := 4} : QInterval) := by
    decide +kernel
  rw [hz] at hp
  have hpos : 0 < (piCircleArea.compute n).lo := by dsimp at hp; grind
  refine ⟨by grind, hr.2, ?_⟩
  change (QInterval.inv (piCircleArea.compute n)).hi * _ = 1
  simp only [QInterval.inv, if_pos hpos, Rat.div_def, Rat.one_mul]
  exact Rat.inv_mul_cancel _ (Rat.ne_of_gt hpos)

theorem divide_residual {d p z r e : Rat}
    (hr0 : 0 <= r) (hr1 : r <= 1) (hrp : r*p = 1)
    (he : qabs (d-p*z) <= e) : qabs (r*d-z) <= e := by
  have he0 := Rat.le_trans (qabs_nonneg (d-p*z)) he
  have hm := Rat.mul_le_mul_of_nonneg_left he hr0
  have hb := Rat.mul_le_mul_of_nonneg_right hr1 he0
  have hid : r*d-z = r*(d-p*z) := by grind
  rw [hid, qabs_mul, qabs_eq_self_of_nonneg hr0]
  grind

/-- Restriction of the original public cosine, not a new trigonometric
implementation or a declaration that every continuous function is integrable. -/
def integrand (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) : FunctionOnInterval where
  raw := (cosPiOnHalf B).raw
  lower := a
  upper := b
  defined_on := by
    intro x hx
    exact ⟨Rat.le_trans ha.1 hx.1, Rat.le_trans hx.2 hb.2⟩
  valid_on := (cosPiOnHalf B).valid_on


/-- The unscaled geometric sine, as a raw rational-input function. -/
def sineFun (B : ArctanInverseBisection) : RealFunRaw where
  domain := OnHalf
  compute := fun x n => (sine B x).compute n

/-- Its correctly normalized primitive for the public cosine. -/
def primitive (B : ArctanInverseBisection) (x : Rat) : RealRaw :=
  RealRaw.mul reciprocalPiRaw (sine B x)

def primitiveFun (B : ArctanInverseBisection) : RealFunRaw where
  domain := OnHalf
  compute := fun x n => (primitive B x).compute n

def cosineFun (B : ArctanInverseBisection) : RealFunRaw where
  domain := OnHalf
  compute := fun x n => (cosine B x).compute n

theorem primitive_valid (B : ArctanInverseBisection) (x : Rat) :
    (primitive B x).Valid :=
  RealRaw.mul_valid reciprocalPiRaw_valid (sine_valid B x)

/-- One literal integral program, independent of its correctness proof. -/
def integral (B : ArctanInverseBisection) (a b : Rat)
    (_ha : OnHalf a) (_hb : OnHalf b) (_hab : a <= b) : RealRaw :=
  Integral.Dovetail.raw (fixedMesh B a b) (error a b)

/-- The common proposition inhabited by the two named proofs. -/
def IntegralCosineStatement (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) : Prop :=
  (integral B a b ha hb hab).Equiv
    (RealRaw.mul reciprocalPiRaw
      (sinPiRawOfArctan B b hb - sinPiRawOfArctan B a ha))

end CosineFTC
end ComputableAnalysis
