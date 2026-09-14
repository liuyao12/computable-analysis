import ComputableAnalysis.CosineIntegralData
import ComputableAnalysis.GeometricSineDirectBounds

/-! Direct proof of the geometric cosine integral by finite inequalities.
The algorithms are defined in CosineIntegralData, independently of this proof.
No normalized sine derivative, concavity theorem, or concave FTC is used. -/
namespace ComputableAnalysis
namespace CosineFTC
open IntegralIdentities SinPiIntegral GeometricSineDerivative FiniteRiemannAlgebra

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
    obtain ⟨N, hN⟩ := GeometricSineDirectBounds.positive_increment_error B x h hx hy hp
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

def construction (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    Integral.ConstructionFor (integrand B a b ha hb) :=
  Integral.Dovetail.constructionFor (integrand B a b ha hb)
    (fixedMesh B a b) (error a b) (endpoint B a b)
    (fixedMesh_valid B a b) (endpoint_valid B a b)
    (error_shrinks ha hb hab) (fixedMesh_overlaps_endpoint B ha hb hab)

theorem integral_valid (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    (integral B a b ha hb hab).Valid :=
  Integral.Dovetail.raw_valid (fixedMesh_valid B a b) (endpoint_valid B a b)
    (error_shrinks ha hb hab) (fixedMesh_overlaps_endpoint B ha hb hab)

/-- Computational FTC for the existing geometric sine and cosine. The factor
`1/pi` is required because their rational argument is the normalized angle.
Both sides are independently executable rational-interval programs. -/
theorem integral_cosPi_viaInequalities
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

/-- Compatibility name for the original public endpoint theorem. -/
theorem integral_cosPi_equiv_sinPi_endpoints
    (B : ArctanInverseBisection) (a b : Rat)
    (ha : OnHalf a) (hb : OnHalf b) (hab : a <= b) :
    IntegralCosineStatement B a b ha hb hab :=
  integral_cosPi_viaInequalities B a b ha hb hab

end CosineFTC
end ComputableAnalysis
