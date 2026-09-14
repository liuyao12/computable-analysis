import ComputableAnalysis.NormalizedSineDerivative
import ComputableAnalysis.DovetailedFTC
import ComputableAnalysis.ComplexMultiplication

/-!
# Computing the integral of the existing geometric cosine

On rational `0 <= a <= b <= 1/2`, the integral program reads only the existing
`cosPiRawOfArctan` samples. Its value is equivalent to
`reciprocalPiRaw * (sinPiRawOfArctan B b - sinPiRawOfArctan B a)`.

The proof telescopes finite sine increments, using the checked normalized
sine derivative. A fixed mesh and the precision of its samples are separate
parameters. Finite intersections retain all earlier meshes; there is no
runtime search, primitive evaluation, or uniform evaluation-rate assumption.

`B` is precisely the inverse data required to define the existing geometric
sine and cosine. No FTC or differentiability certificate is an extra input.
-/

namespace ComputableAnalysis
namespace CosineFTC

open IntegralIdentities SinPiIntegral GeometricSineDerivative

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

private def sum (f : Nat -> Rat) (n : Nat) : Rat :=
  ratListSum ((List.range n).map f)

private theorem sum_zero (f : Nat -> Rat) : sum f 0 = 0 := rfl

private theorem sum_succ (f : Nat -> Rat) (n : Nat) :
    sum f (n+1) = sum f n + f n := by
  simp only [sum, List.range_succ, List.map_append, ratListSum_append,
    List.map_cons, List.map_nil, ratListSum]
  grind

private theorem finiteRawSum_lo (xs : List RealRaw) (q : Nat) :
    ((Integral.finiteRawSum xs).compute q).lo =
      ratListSum (xs.map (fun X => (X.compute q).lo)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (x.compute q).lo + ((Integral.finiteRawSum xs).compute q).lo = _
      simpa only [List.map_cons, ratListSum] using congrArg (fun z => (x.compute q).lo+z) ih

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

private theorem finiteRawSum_eq_fold (xs : List Nat) (f : Nat -> RealRaw) (q : Nat) :
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

private theorem fixedMesh_lo (B : ArctanInverseBisection)
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

private theorem error_eq_mesh (a b : Rat) (k : Nat) :
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

private theorem error_shrinks {a b : Rat}
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

private theorem grid_onHalf {a b : Rat} (ha : OnHalf a) (hb : OnHalf b)
    (hab : a <= b) {m i : Nat} (hm : 0 < m) (hi : i <= m) :
    OnHalf (leftPoint a b m i) := by
  have hl := leftPoint_monotone (a := a) (b := b) hm hab (Nat.zero_le i)
  have hu := leftPoint_monotone (a := a) (b := b) hm hab hi
  rw [leftPoint_zero] at hl
  rw [leftPoint_endpoint hm] at hu
  exact ⟨Rat.le_trans ha.1 hl, Rat.le_trans hu hb.2⟩

private theorem finite_eventually (P : Nat -> Nat -> Prop) (m : Nat)
    (h : ∀ i, i < m -> ∃ N, ∀ n, N <= n -> P i n) :
    ∃ N, ∀ n, N <= n -> ∀ i, i < m -> P i n := by
  induction m with
  | zero => exact ⟨0, by intros; omega⟩
  | succ m ih =>
      obtain ⟨N, hN⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨M, hM⟩ := h m (by omega)
      refine ⟨max N M, ?_⟩
      intro n hn i hi
      by_cases he : i = m
      · subst i
        exact hM n (by omega)
      · exact hN n (by omega) i (by omega)

/-- Quadratic residual at the literal lower endpoints of late output boxes.
The zero-length case is included, so equal integration endpoints need no
separate convention. -/
private theorem quadratic_residual (B : ArctanInverseBisection)
    {x h : Rat} (hx : OnHalf x) (hy : OnHalf (x+h)) (hh0 : 0 <= h) :
    ∃ N, ∀ n, N <= n ->
      qabs (((sine B (x+h)).compute n).lo - ((sine B x).compute n).lo -
        h * ((piCircleArea.compute n).lo * ((cosine B x).compute n).lo)) <=
          4000*h*h := by
  by_cases hh : h = 0
  · subst h
    refine ⟨0, ?_⟩
    intro n _
    simp only [Rat.add_zero, Rat.zero_mul, Rat.mul_zero, Rat.sub_self]
    decide +kernel
  · have hp : 0 < h := by grind
    let eps : QPos := ⟨4000*h, Rat.mul_pos (by decide) hp⟩
    have hsmall : qabs h <= eps.val/4000 := by
      rw [qabs_eq_self_of_nonneg hh0]
      dsimp [eps]
      simp only [Rat.div_def]
      grind
    obtain ⟨N, hN⟩ := sinPi_derivative_explicit B eps x h hx hy hh hsmall
    refine ⟨N, ?_⟩
    intro n hn
    have h := hN n hn
      ((sinPiRawOfArctan B (x+h) hy).compute n).lo
      ((sinPiRawOfArctan B x hx).compute n).lo
      ((cosPiRawOfArctan B x hx).compute n).lo
      (piCircleArea.compute n).lo
      (Rat.le_refl) (RealRaw.interval_order_of_valid _ (sinPiRawOfArctan_valid B _ hy) n)
      (Rat.le_refl) (RealRaw.interval_order_of_valid _ (sinPiRawOfArctan_valid B _ hx) n)
      (Rat.le_refl) (RealRaw.interval_order_of_valid _ (cosPiRawOfArctan_valid B _ hx) n)
      (Rat.le_refl) (RealRaw.interval_order_of_valid _ CauchyPi.piCircleArea_valid n)
    simpa only [sine, cosine, dif_pos hx, dif_pos hy,
      qabs_eq_self_of_nonneg hh0] using h

/-- The finite FTC estimate is just a telescope plus the triangle inequality. -/
private theorem telescope_bound (s c : Nat -> Rat) (h p e : Rat) (m : Nat)
    (hc : ∀ i, i < m -> qabs (s (i+1)-s i-h*(p*c i)) <= e) :
    qabs (s m-s 0-p*sum (fun i => h*c i) m) <= (m : Rat)*e := by
  induction m with
  | zero =>
      simp only [sum_zero, Rat.mul_zero, Rat.sub_self, show ((0 : Nat) : Rat) = (0 : Rat) by decide +kernel,
        Rat.zero_mul]
      decide +kernel
  | succ m ih =>
      have hm := ih (fun i hi => hc i (by omega))
      have hi := hc m (by omega)
      rw [sum_succ]
      have heq : s (m+1)-s 0-p*(sum (fun i => h*c i) m+h*c m) =
          (s m-s 0-p*sum (fun i => h*c i) m)+(s (m+1)-s m-h*(p*c m)) := by
        grind
      rw [heq]
      have ht := qabs_add_le (s m-s 0-p*sum (fun i => h*c i) m)
        (s (m+1)-s m-h*(p*c m))
      have hcast : ((m+1 : Nat) : Rat) = (m : Rat)+1 := by simp
      rw [hcast]
      grind

private theorem fixedMesh_eventually_close (B : ArctanInverseBisection)
    {a b : Rat} (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) (k : Nat) :
    ∃ N, ∀ n, N <= n ->
      qabs (((sine B b).compute n).lo-((sine B a).compute n).lo -
        (piCircleArea.compute n).lo * ((fixedMesh B a b k).compute n).lo) <=
          error a b k := by
  let m := k+1
  let h := mesh a b m
  let P := fun i n =>
    qabs (((sine B (leftPoint a b m (i+1))).compute n).lo -
      ((sine B (leftPoint a b m i)).compute n).lo -
      h*((piCircleArea.compute n).lo *
        ((cosine B (leftPoint a b m i)).compute n).lo)) <= 4000*h*h
  have hp : ∀ i, i < m -> ∃ N, ∀ n, N <= n -> P i n := by
    intro i hi
    have hx := grid_onHalf ha hb hab (Nat.succ_pos k) (Nat.le_of_lt hi)
    have hy := grid_onHalf ha hb hab (Nat.succ_pos k) (by omega : i+1 <= m)
    have heq : leftPoint a b m i+h = leftPoint a b m (i+1) := by
      have he := leftPoint_step a b m i
      change _ = h at he
      grind
    have H := quadratic_residual B (x := leftPoint a b m i) (h := h) hx
      (by rw [heq]; exact hy)
      (mesh_nonneg_of_le (Nat.succ_pos k) hab)
    dsimp only [P]
    rw [← heq]
    exact H
  obtain ⟨N, hN⟩ := finite_eventually P m hp
  refine ⟨N, ?_⟩
  intro n hn
  have ht := telescope_bound
    (fun i => ((sine B (leftPoint a b m i)).compute n).lo)
    (fun i => ((cosine B (leftPoint a b m i)).compute n).lo)
    h (piCircleArea.compute n).lo (4000*h*h) m (hN n hn)
  rw [leftPoint_zero, leftPoint_endpoint (Nat.succ_pos k)] at ht
  rw [fixedMesh_lo B hab k n, error_eq_mesh]
  exact ht

private theorem reciprocal_corner (n : Nat) :
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

private theorem divide_residual {d p z r e : Rat}
    (hr0 : 0 <= r) (hr1 : r <= 1) (hrp : r*p = 1)
    (he : qabs (d-p*z) <= e) : qabs (r*d-z) <= e := by
  have he0 := Rat.le_trans (qabs_nonneg (d-p*z)) he
  have hm := Rat.mul_le_mul_of_nonneg_left he hr0
  have hb := Rat.mul_le_mul_of_nonneg_right hr1 he0
  have hid : r*d-z = r*(d-p*z) := by grind
  rw [hid, qabs_mul, qabs_eq_self_of_nonneg hr0]
  grind

/-- Every fixed finite Riemann enclosure, widened by its discretization
bound, overlaps every stage of the independently evaluated primitive.
This is the substantive FTC bridge, not an assumption supplied by a client. -/
theorem fixedMesh_overlaps_endpoint (B : ArctanInverseBisection)
    {a b : Rat} (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b)
    (k q t : Nat) :
    (QInterval.expand ((fixedMesh B a b k).compute q) (error a b k)).Overlaps
      ((endpoint B a b).compute t) := by
  obtain ⟨N, hN⟩ := fixedMesh_eventually_close B ha hb hab k
  let n := max N (max q t)
  have hnN : N <= n := by dsimp [n]; omega
  have hnq : q <= n := by dsimp [n]; omega
  have hnt : t <= n := by dsimp [n]; omega
  let d := ((sine B b).compute n).lo-((sine B a).compute n).lo
  let r := (reciprocalPiRaw.compute n).hi
  let z := ((fixedMesh B a b k).compute n).lo
  have hr := reciprocal_corner n
  have herr : qabs (r*d-z) <= error a b k :=
    divide_residual hr.1 hr.2.1 hr.2.2 (hN n hnN)
  have hsA := RealRaw.interval_order_of_valid _ (sine_valid B a) n
  have hsB := RealRaw.interval_order_of_valid _ (sine_valid B b) n
  have hrec := RealRaw.interval_order_of_valid _ reciprocalPiRaw_valid n
  have hd : ((sine B b-sine B a).compute n).lo <= d ∧
      d <= ((sine B b-sine B a).compute n).hi := by
    change ((sine B b).compute n).lo-((sine B a).compute n).hi <= d ∧
      d <= ((sine B b).compute n).hi-((sine B a).compute n).lo
    dsimp [d]
    constructor <;> grind
  have hm : ((endpoint B a b).compute n).lo <= r*d ∧
      r*d <= ((endpoint B a b).compute n).hi :=
    QBox.mulRealInterval_contains hrec (Rat.le_refl) hd.1 hd.2
  have ht := (endpoint_valid B a b).2.1 t n hnt
  have hq := (fixedMesh_valid B a b k).2.1 q n hnq
  have hlow := neg_qabs_le_self (r*d-z)
  have hhigh := self_le_qabs (r*d-z)
  change ((fixedMesh B a b k).compute q).lo - error a b k <=
      ((endpoint B a b).compute t).hi ∧
    ((endpoint B a b).compute t).lo <=
      ((fixedMesh B a b k).compute q).hi + error a b k
  dsimp [z] at hlow hhigh herr
  constructor <;> grind

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

def construction (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    Integral.ConstructionFor (integrand B a b ha hb) :=
  Integral.Dovetail.constructionFor (integrand B a b ha hb)
    (fixedMesh B a b) (error a b) (endpoint B a b)
    (fixedMesh_valid B a b) (endpoint_valid B a b)
    (error_shrinks ha hb hab) (fixedMesh_overlaps_endpoint B ha hb hab)

/-- The fixed-schedule computation of the cosine integral. -/
def integral (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) : RealRaw :=
  Integral.integralFor (integrand B a b ha hb) (construction B a b ha hb hab)

theorem integral_valid (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    (integral B a b ha hb hab).Valid :=
  Integral.integralFor_valid _ _

/-- Computational FTC for the existing geometric sine and cosine. The factor
`1/pi` is required because their rational argument is the normalized angle.
Both sides are independently executable rational-interval programs. -/
theorem integral_cosPi_equiv_sinPi_endpoints
    (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    (integral B a b ha hb hab).Equiv
      (RealRaw.mul reciprocalPiRaw
        (sinPiRawOfArctan B b hb - sinPiRawOfArctan B a ha)) := by
  have h := Integral.Dovetail.raw_equiv_endpoint
    (fixedMesh_overlaps_endpoint B ha hb hab)
  change (Integral.Dovetail.raw (fixedMesh B a b) (error a b)).Equiv _
  simpa only [endpoint, sine, dif_pos ha, dif_pos hb] using h

/-- Inspectable stage equation: only finite cosine sums and rational error
bounds occur in the runtime. Sine endpoints occur in the theorem above. -/
theorem integral_compute (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) (n : Nat) :
    (integral B a b ha hb hab).compute n =
      Integral.Dovetail.intersectMeshes
        (fun k q => QInterval.expand ((fixedMesh B a b k).compute q) (error a b k)) n n := rfl

end CosineFTC
end ComputableAnalysis
