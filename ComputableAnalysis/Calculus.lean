import ComputableAnalysis.Basic

namespace ComputableAnalysis

def mesh (a b : Rat) (n : Nat) : Rat := if n = 0 then 0 else (b - a) / n
def leftPoint (a b : Rat) (n k : Nat) : Rat := a + (k : Rat) * mesh a b n

/-- The first point of every positive uniform rational mesh is its left
endpoint. -/
theorem leftPoint_zero (a b : Rat) (n : Nat) :
    leftPoint a b n 0 = a := by
  unfold leftPoint
  grind

/-- The last point of a positive uniform rational mesh is its right endpoint.
This is an exact rational identity; no limiting argument is involved. -/
theorem leftPoint_endpoint {a b : Rat} {n : Nat} (hn : 0 < n) :
    leftPoint a b n n = b := by
  have hnat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  unfold leftPoint mesh
  rw [if_neg (Nat.ne_of_gt hn)]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
    Rat.sub_eq_add_neg]

/-- Consecutive points of a uniform rational mesh are separated by precisely
its mesh width. -/
theorem leftPoint_step (a b : Rat) (n k : Nat) :
    leftPoint a b n (k + 1) - leftPoint a b n k = mesh a b n := by
  unfold leftPoint
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm]

/-- The mesh width is nonnegative on an ordered interval. -/
theorem mesh_nonneg_of_le {a b : Rat} {n : Nat}
    (hn : 0 < n) (hab : a <= b) :
    0 <= mesh a b n := by
  unfold mesh
  rw [if_neg (Nat.ne_of_gt hn), Rat.div_def]
  have hden : 0 <= ((n : Rat)⁻¹) :=
    Rat.le_of_lt (Rat.inv_pos.mpr ((Rat.natCast_pos).2 hn))
  exact Rat.mul_nonneg (by grind [Rat.sub_eq_add_neg]) hden

/-- An ordered interval gives an ordered uniform rational mesh. -/
theorem leftPoint_monotone {a b : Rat} {n i j : Nat}
    (hn : 0 < n) (hab : a <= b) (hij : i <= j) :
    leftPoint a b n i <= leftPoint a b n j := by
  have hmesh : 0 <= mesh a b n := mesh_nonneg_of_le hn hab
  have hcast : (i : Rat) <= (j : Rat) := by
    exact_mod_cast hij
  exact (Rat.add_le_add_left).mpr
    (Rat.mul_le_mul_of_nonneg_right hcast hmesh)

/-- Refining a uniform mesh by a positive factor preserves every old mesh
point.  The embedding sends index `i` to `i*n` in the `m*n` mesh. -/
theorem leftPoint_refine_mul_right {a b : Rat} {m n i : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    leftPoint a b (m * n) (i * n) = leftPoint a b m i := by
  have hmrat : (m : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
  have hnrat : (n : Rat) ≠ 0 :=
    Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  unfold leftPoint mesh
  rw [if_neg (Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)),
    if_neg (Nat.ne_of_gt hm)]
  simp only [Rat.natCast_mul]
  grind [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

/-- Under the same refinement, the fine mesh width is the old width divided
by the positive refinement factor. -/
theorem mesh_refine_mul_right {a b : Rat} {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    mesh a b (m * n) = mesh a b m / (n : Rat) := by
  unfold mesh
  rw [if_neg (Nat.mul_ne_zero (Nat.ne_of_gt hm) (Nat.ne_of_gt hn)),
    if_neg (Nat.ne_of_gt hm)]
  simp only [Rat.natCast_mul]
  grind [Rat.div_def, Rat.inv_mul_rev, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

/-- Successive dyadic meshes preserve every previous grid point.  The old
index `k` is the new index `2*k`; this is the exact finite compatibility
behind stagewise dyadic Riemann constructions. -/
theorem dyadic_leftPoint_refines (a b : Rat) (n k : Nat) :
    leftPoint a b (2 ^ (n + 1)) (2 * k) =
      leftPoint a b (2 ^ n) k := by
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have htwo : 0 < 2 := by omega
  simpa [Nat.pow_succ, Nat.mul_comm] using
    leftPoint_refine_mul_right (a := a) (b := b) (i := k) hpow htwo

/-- The dyadic mesh width is halved at every successor stage. -/
theorem dyadic_mesh_refines (a b : Rat) (n : Nat) :
    mesh a b (2 ^ (n + 1)) = mesh a b (2 ^ n) / 2 := by
  have hpow : 0 < 2 ^ n := Nat.pow_pos (by omega : 0 < 2)
  have htwo : 0 < 2 := by omega
  simpa [Nat.pow_succ] using mesh_refine_mul_right
    (a := a) (b := b) hpow htwo

def riemannLeftExact (g : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  let h := mesh a b n
  (List.range n).foldl (fun acc k => acc + h * g (leftPoint a b n k)) 0

def riemannLeftInterval (g : RealFunRaw) (a b : Rat) (n : Nat) (prec : Nat) : QInterval :=
  let h := mesh a b n
  (List.range n).foldl
    (fun acc k => let I := g.compute (leftPoint a b n k) prec; { lo := acc.lo + h * I.lo, hi := acc.hi + h * I.hi })
    { lo := 0, hi := 0 }

/-- The finite left-endpoint sum for the product contribution
`u\,\Delta v`.  This is the rational rectangle area swept when the second
side of a rectangle changes while the first is held at its left endpoint. -/
def leftStieltjesSum (u v : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => leftStieltjesSum u v n + u n * (v (n + 1) - v n)

/-- The complementary finite right-endpoint sum `v_{i+1}\,\Delta u_i`.
Together with `leftStieltjesSum` it fills the endpoint-product rectangle
exactly, before any limiting argument is made. -/
def rightStieltjesSum (u v : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => rightStieltjesSum u v n + v (n + 1) * (u (n + 1) - u n)

/-- The finite corner-rectangle correction obtained if both Stieltjes sums
use left endpoints.  A constructive integration-by-parts proof only has to
show this displayed rational sum tends to zero on its chosen mesh. -/
def quadraticVariationSum (u v : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => quadraticVariationSum u v n +
      (u (n + 1) - u n) * (v (n + 1) - v n)

/-- One cell of the geometric integration-by-parts decomposition: the two
oriented strips exactly make up the change in the endpoint-product rectangle. -/
theorem productIncrement_decomposition
    (u0 u1 v0 v1 : Rat) :
    u1 * v1 - u0 * v0 =
      u0 * (v1 - v0) + v1 * (u1 - u0) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Finite geometric integration by parts.  The two displayed sums tile the
rectangle difference `u_n v_n-u_0v_0`; this is an exact rational identity,
not a statement about unrepresented limiting real numbers. -/
theorem finiteIntegrationByParts (u v : Nat -> Rat) (n : Nat) :
    leftStieltjesSum u v n + rightStieltjesSum u v n =
      u n * v n - u 0 * v 0 := by
  induction n with
  | zero =>
      grind [leftStieltjesSum, rightStieltjesSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [leftStieltjesSum, rightStieltjesSum]
      have hcell := productIncrement_decomposition
        (u n) (u (n + 1)) (v n) (v (n + 1))
      calc
        (leftStieltjesSum u v n + u n * (v (n + 1) - v n)) +
            (rightStieltjesSum u v n + v (n + 1) * (u (n + 1) - u n)) =
          (leftStieltjesSum u v n + rightStieltjesSum u v n) +
            (u n * (v (n + 1) - v n) +
              v (n + 1) * (u (n + 1) - u n)) := by
            grind [Rat.add_assoc, Rat.add_comm]
        _ = (u n * v n - u 0 * v 0) +
            (u n * (v (n + 1) - v n) +
              v (n + 1) * (u (n + 1) - u n)) := by rw [ih]
        _ = u (n + 1) * v (n + 1) - u 0 * v 0 := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- The same rectangle decomposition when both sums use left endpoints.  The
only difference from the exact tiling is the explicitly named corner-area
sum `quadraticVariationSum`. -/
theorem finiteIntegrationByParts_withVariation
    (u v : Nat -> Rat) (n : Nat) :
    leftStieltjesSum u v n + leftStieltjesSum v u n +
        quadraticVariationSum u v n =
      u n * v n - u 0 * v 0 := by
  induction n with
  | zero =>
      grind [leftStieltjesSum, quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [leftStieltjesSum, leftStieltjesSum, quadraticVariationSum]
      have hcell :
          u (n + 1) * v (n + 1) - u n * v n =
            u n * (v (n + 1) - v n) +
              v n * (u (n + 1) - u n) +
              (u (n + 1) - u n) * (v (n + 1) - v n) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      calc
        (leftStieltjesSum u v n + u n * (v (n + 1) - v n)) +
              (leftStieltjesSum v u n + v n * (u (n + 1) - u n)) +
            (quadraticVariationSum u v n +
              (u (n + 1) - u n) * (v (n + 1) - v n)) =
          (leftStieltjesSum u v n + leftStieltjesSum v u n +
              quadraticVariationSum u v n) +
            (u n * (v (n + 1) - v n) +
              v n * (u (n + 1) - u n) +
              (u (n + 1) - u n) * (v (n + 1) - v n)) := by
            grind [Rat.add_assoc, Rat.add_comm]
        _ = (u n * v n - u 0 * v 0) +
            (u n * (v (n + 1) - v n) +
              v n * (u (n + 1) - u n) +
              (u (n + 1) - u n) * (v (n + 1) - v n)) := by rw [ih]
        _ = u (n + 1) * v (n + 1) - u 0 * v 0 := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- On an explicitly nondecreasing rational path, every endpoint displacement
from the initial point is nonnegative.  This is the finite order fact used to
control the corner rectangles in geometric integration by parts. -/
theorem endpointDifference_nonneg_of_step_nonnegative
    (u : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i) (n : Nat) :
    0 <= u n - u 0 := by
  induction n with
  | zero =>
      grind [Rat.sub_eq_add_neg]
  | succ n ih =>
      calc
        0 <= (u n - u 0) + (u (n + 1) - u n) :=
          Rat.add_nonneg ih (hu n)
        _ = u (n + 1) - u 0 := by
          grind [Rat.sub_eq_add_neg]

/-- If the two paths move in the same nondecreasing direction, the finite
corner correction is nonnegative.  Geometrically it is a sum of areas of
ordinary (not signed) corner rectangles. -/
theorem quadraticVariationSum_nonneg_of_step_nonnegative
    (u v : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    0 <= quadraticVariationSum u v n := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum]
      exact Rat.add_nonneg ih (Rat.mul_nonneg (hu n) (hv n))

/-- A mesh-size bound for the corner correction.  If every increment of the
first path is at most `delta` and the second path is nondecreasing, then the
entire correction is at most `delta` times the total variation of the second
path.  This is the finite estimate that will make the correction vanish on a
common rational refinement. -/
theorem quadraticVariationSum_le_stepBound_mul_endpointDifference
    (u v : Nat -> Rat) (delta : Rat)
    (hu : forall i, u (i + 1) - u i <= delta)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    quadraticVariationSum u v n <= delta * (v n - v 0) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [quadraticVariationSum]
      calc
        quadraticVariationSum u v n +
            (u (n + 1) - u n) * (v (n + 1) - v n) <=
          delta * (v n - v 0) +
            (u (n + 1) - u n) * (v (n + 1) - v n) :=
          Rat.add_le_add_right.mpr ih
        _ <= delta * (v n - v 0) +
            delta * (v (n + 1) - v n) :=
          Rat.add_le_add_left.mpr
            (Rat.mul_le_mul_of_nonneg_right (hu n) (hv n))
        _ = delta * (v (n + 1) - v 0) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- With two nondecreasing paths, the corner correction is bounded by the
product of their endpoint variations.  This is the finite rectangle form of
the usual ``variation times mesh'' estimate, before a particular mesh modulus
is supplied. -/
theorem quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    (u v : Nat -> Rat)
    (hu : forall i, 0 <= u (i + 1) - u i)
    (hv : forall i, 0 <= v (i + 1) - v i)
    (n : Nat) :
    quadraticVariationSum u v n <=
      (u n - u 0) * (v n - v 0) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      let du := u (n + 1) - u n
      let dv := v (n + 1) - v n
      let U := u n - u 0
      let V := v n - v 0
      have hU : 0 <= U := by
        dsimp [U]
        exact endpointDifference_nonneg_of_step_nonnegative u hu n
      have hV : 0 <= V := by
        dsimp [V]
        exact endpointDifference_nonneg_of_step_nonnegative v hv n
      have hdu : 0 <= du := by
        dsimp [du]
        exact hu n
      have hdv : 0 <= dv := by
        dsimp [dv]
        exact hv n
      have hcross : 0 <= U * dv + du * V :=
        Rat.add_nonneg (Rat.mul_nonneg hU hdv) (Rat.mul_nonneg hdu hV)
      rw [quadraticVariationSum]
      calc
        quadraticVariationSum u v n + du * dv <= U * V + du * dv := by
          exact Rat.add_le_add_right.mpr ih
        _ <= U * V + du * dv + (U * dv + du * V) := by
          grind [Rat.sub_eq_add_neg]
        _ = (U + du) * (V + dv) := by
          grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
            Rat.mul_assoc, Rat.mul_comm]
        _ = (u (n + 1) - u 0) * (v (n + 1) - v 0) := by
          dsimp [U, V, du, dv]
          grind [Rat.sub_eq_add_neg]

/-- Negating both paths preserves every corner rectangle: its two signed side
increments change sign together.  This transfers the finite estimates from
increasing pieces to decreasing pieces without a Jordan decomposition. -/
theorem quadraticVariationSum_neg_neg
    (u v : Nat -> Rat) (n : Nat) :
    quadraticVariationSum (fun i => -u i) (fun i => -v i) n =
      quadraticVariationSum u v n := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum, quadraticVariationSum, ih]
      grind [Rat.neg_sub, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
        Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

/-- The endpoint-variation bound on an explicitly nonincreasing pair of
paths.  It is obtained by negating both paths, so the correction is still a
sum of ordinary corner areas while the endpoint variations are reversed. -/
theorem quadraticVariationSum_le_endpointVariationProduct_of_step_nonpositive
    (u v : Nat -> Rat)
    (hu : forall i, u (i + 1) - u i <= 0)
    (hv : forall i, v (i + 1) - v i <= 0)
    (n : Nat) :
    quadraticVariationSum u v n <=
      (u 0 - u n) * (v 0 - v n) := by
  have hu' : forall i, 0 <= (-u (i + 1)) - (-u i) := by
    intro i
    have h := hu i
    grind [Rat.neg_sub, Rat.sub_eq_add_neg]
  have hv' : forall i, 0 <= (-v (i + 1)) - (-v i) := by
    intro i
    have h := hv i
    grind [Rat.neg_sub, Rat.sub_eq_add_neg]
  have h := quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    (fun i => -u i) (fun i => -v i) hu' hv' n
  rw [quadraticVariationSum_neg_neg] at h
  calc
    quadraticVariationSum u v n <=
        ((-u n) - (-u 0)) * ((-v n) - (-v 0)) := h
    _ = (u 0 - u n) * (v 0 - v n) := by
      grind [Rat.neg_sub, Rat.neg_mul, Rat.mul_neg, Rat.neg_neg,
        Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

/-- If the two paths have constant rational increments, their corner sum is
exactly the number of cells times one corner rectangle.  This is the finite
calculation behind the elementary mesh-vanishing schedule below. -/
theorem quadraticVariationSum_eq_nat_mul_of_constant_steps
    (u v : Nat -> Rat) (du dv : Rat)
    (hu : forall i, u (i + 1) - u i = du)
    (hv : forall i, v (i + 1) - v i = dv)
    (n : Nat) :
    quadraticVariationSum u v n = (n : Rat) * (du * dv) := by
  induction n with
  | zero =>
      grind [quadraticVariationSum]
  | succ n ih =>
      rw [quadraticVariationSum, hu, hv, ih, Rat.natCast_add]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]

/-- The rational identity path on an `n`-cell unit mesh.  It is a concrete
test case for the geometric integration-by-parts correction. -/
def unitMeshPath (n k : Nat) : Rat := (k : Rat) / (n : Rat)

/-- Every increment of the unit mesh path is exactly `1/n`. -/
theorem unitMeshPath_step (n k : Nat) :
    unitMeshPath n (k + 1) - unitMeshPath n k = 1 / (n : Rat) := by
  unfold unitMeshPath
  rw [Rat.natCast_add, Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- On the positive `n`-cell unit mesh the corner correction is exactly
`1/n`.  This is an explicit rational equality, not a completeness-based
limit assertion. -/
theorem unitMeshPath_quadraticVariation {n : Nat} (hn : 0 < n) :
    quadraticVariationSum (unitMeshPath n) (unitMeshPath n) n =
      1 / (n : Rat) := by
  rw [quadraticVariationSum_eq_nat_mul_of_constant_steps
    (unitMeshPath n) (unitMeshPath n) (1 / (n : Rat)) (1 / (n : Rat))
    (unitMeshPath_step n) (unitMeshPath_step n)]
  have hnat : (n : Rat) ≠ 0 := Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- A fully explicit epsilon schedule for the unit-mesh corner correction.
Choosing `n = eps.den + 1` makes the rational correction at most `eps`. -/
theorem unitMeshPath_quadraticVariation_le_epsilon (eps : QPos) :
    quadraticVariationSum (unitMeshPath (eps.val.den + 1))
      (unitMeshPath (eps.val.den + 1)) (eps.val.den + 1) <= eps.val := by
  rw [unitMeshPath_quadraticVariation (Nat.succ_pos _)]
  exact one_div_den_succ_le_of_pos eps.property

private theorem riemannLeftInterval_point_fold_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi)
    (xs : List Nat) (acc : QInterval) (hacc : acc.lo = acc.hi) :
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).lo =
    (xs.foldl
      (fun acc k =>
        let I := g.compute (leftPoint a b subdivisions k) prec
        { lo := acc.lo + mesh a b subdivisions * I.lo,
          hi := acc.hi + mesh a b subdivisions * I.hi })
      acc).hi := by
  induction xs generalizing acc with
  | nil =>
      simpa using hacc
  | cons k rest ih =>
      apply ih
      dsimp
      rw [hacc, hpoint (leftPoint a b subdivisions k)]

theorem riemannLeftInterval_point_eq
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).lo =
      (riemannLeftInterval g a b subdivisions prec).hi := by
  unfold riemannLeftInterval
  exact riemannLeftInterval_point_fold_eq
    g a b subdivisions prec hpoint (List.range subdivisions)
    { lo := 0, hi := 0 } rfl

theorem riemannLeftInterval_point_width_zero
    (g : RealFunRaw) (a b : Rat) (subdivisions prec : Nat)
    (hpoint : forall x, (g.compute x prec).lo = (g.compute x prec).hi) :
    (riemannLeftInterval g a b subdivisions prec).width = 0 := by
  have h := riemannLeftInterval_point_eq
    g a b subdivisions prec hpoint
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

namespace RealFunRaw

def add (f g : RealFunRaw) : RealFunRaw where
  domain := fun x => f.domain x /\ g.domain x
  compute := fun x n =>
    let F := f.compute x n
    let G := g.compute x n
    { lo := F.lo + G.lo, hi := F.hi + G.hi }

def scaleRat (r : Rat) (f : RealFunRaw) : RealFunRaw where
  domain := f.domain
  compute := fun x n =>
    let F := f.compute x n
    if 0 <= r then
      { lo := r * F.lo, hi := r * F.hi }
    else
      { lo := r * F.hi, hi := r * F.lo }

end RealFunRaw

def precisionAtStage (n : Nat) : QPos :=
  if hn : n = 0 then
      { val := 1, property := by grind }
    else
      { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

def intervalCloseAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.CloseAt I J (precisionAtStage n)

/-- Precision-indexed quantitative closeness for enclosures of possibly
distinct nearby values. -/
def intervalNearAtPrecision (I J : QInterval) (n : Nat) : Prop :=
  QInterval.NearAt I J (precisionAtStage n)

namespace QInterval

/-- A weak interval order: the two interval enclosures are compatible with
some value of the left endpoint being at most some value of the right endpoint.
This is the order notion used for qualitative monotonicity and convexity
certificates, where finite rational enclosures may still overlap. -/
def WeakLe (I J : QInterval) : Prop :=
  I.lo <= J.hi

/-- A strong interval order: every value in the left interval is at most every
value in the right interval.  This is useful for certified bounds. -/
def StrongLe (I J : QInterval) : Prop :=
  I.hi <= J.lo

def addInterval (I J : QInterval) : QInterval :=
  { lo := I.lo + J.lo, hi := I.hi + J.hi }

def scaleByRat (r : Rat) (I : QInterval) : QInterval :=
  if 0 <= r then
    { lo := r * I.lo, hi := r * I.hi }
  else
    { lo := r * I.hi, hi := r * I.lo }

def subInterval (I J : QInterval) : QInterval :=
  { lo := I.lo - J.hi, hi := I.hi - J.lo }

def divByRat (I : QInterval) (h : Rat) : QInterval :=
  scaleByRat (1 / h) I

/-- Interval enclosure of `(Fy - Fx) / dx`.  For a secant slope, `dx` will be
the rational difference `y - x`; the caller carries the proof that `x < y`. -/
def slopeBetween (Fy Fx : QInterval) (dx : Rat) : QInterval :=
  divByRat (subInterval Fy Fx) dx

end QInterval

/-- Effective modulus on a rational interval.

This is legacy pointwise-style continuity data used by the current FTC target.
Given an output precision `n`, it supplies:

* an input precision saying how close rational inputs must be;
* an evaluation precision saying how accurately to compute the function;
* a proof that sufficiently close inputs produce output intervals within the
  requested tolerance.

This is intentionally interval-based rather than topological. -/
structure EffectiveModulusOn (f : RealFunRaw) (a b : Rat) where
  valid : f.Valid
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n,
      a <= x ->
      x <= b ->
      a <= y ->
      y <= b ->
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalNearAtPrecision
          (f.compute x (evalPrecision n))
          (f.compute y (evalPrecision n))
          n

/- Constructive interval-sum integration. -/
namespace Integral

/-- Effective choices for computing an integral to a requested precision. -/
structure Plan where
  subdivisions : Nat
  evalPrecision : Nat

/-- The static dyadic mesh size used by the first integral algorithms.
Stage `n` has `2^n` equal subintervals, independent of the integrand values. -/
def staticDyadicSubdivisions (n : Nat) : Nat :=
  2 ^ n

/-- The default static dyadic Riemann plan: stage `n` uses `2^n` equal
subintervals and asks the integrand for precision `n`. -/
def staticDyadicPlan : Nat -> Plan :=
  fun n => { subdivisions := staticDyadicSubdivisions n, evalPrecision := n }

/-- A rational Lipschitz estimate on the unit interval.  This is the finite
metric datum used by the elementary dyadic Riemann constructor below; it is
not a topological continuity assumption. -/
def LipschitzOnUnit (f : Rat -> Rat) (L : Rat) : Prop :=
  0 <= L /\
  forall s t : Rat,
    0 <= s -> s <= 1 -> 0 <= t -> t <= 1 ->
      qabs (f s - f t) <= L * qabs (t - s)

/-- A lower rectangle certified by a rational Lipschitz constant. -/
def lipschitzLowerCell (f : Rat -> Rat) (L p r : Rat) : Rat :=
  (r - p) * (f p - L * (r - p))

/-- The matching upper rectangle certified by a rational Lipschitz constant. -/
def lipschitzUpperCell (f : Rat -> Rat) (L p r : Rat) : Rat :=
  (r - p) * (f p + L * (r - p))

private theorem midpoint_left {p r : Rat} (hpr : p <= r) :
    p <= (p + r) / 2 := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    calc
      p * 2 <= p + r := by grind
      _ = ((p + r) * (2 : Rat)⁻¹) * 2 := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · native_decide

private theorem midpoint_right {p r : Rat} (hpr : p <= r) :
    (p + r) / 2 <= r := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    calc
      ((p + r) * (2 : Rat)⁻¹) * 2 = p + r := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= r * 2 := by grind
  · native_decide

private theorem midpoint_left_width (p r : Rat) :
    (p + r) / 2 - p = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem midpoint_right_width (p r : Rat) :
    r - (p + r) / 2 = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- Splitting a unit-interval cell at its rational midpoint tightens the
Lipschitz bracket.  This is a purely finite inequality over rationals and is
the local refinement rule used by dyadic Riemann constructions. -/
theorem lipschitzCells_refine
    {f : Rat -> Rat} {L p r : Rat}
    (hlip : LipschitzOnUnit f L)
    (hp0 : 0 <= p) (hpr : p <= r) (hr1 : r <= 1) :
    let q := (p + r) / 2
    lipschitzLowerCell f L p r <=
      lipschitzLowerCell f L p q + lipschitzLowerCell f L q r /\
    lipschitzUpperCell f L p q + lipschitzUpperCell f L q r <=
      lipschitzUpperCell f L p r := by
  intro q
  have hL0 := hlip.1
  have hpq : p <= q := by
    dsimp [q]
    exact midpoint_left hpr
  have hqr : q <= r := by
    dsimp [q]
    exact midpoint_right hpr
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hq1 : q <= 1 := Rat.le_trans hqr hr1
  have hpq_nonneg : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hqr_nonneg : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hqdist : qabs (q - p) = q - p :=
    qabs_eq_self_of_nonneg hpq_nonneg
  have hlip_pq := hlip.2 p q hp0 (Rat.le_trans hpr hr1) hq0 hq1
  have hforward : f p - f q <= L * (q - p) := by
    calc
      f p - f q <= qabs (f p - f q) := self_le_qabs _
      _ <= L * qabs (q - p) := hlip_pq
      _ = L * (q - p) := by rw [hqdist]
  have hreverse : f q - f p <= L * (q - p) := by
    calc
      f q - f p = -(f p - f q) := by
        grind [Rat.sub_eq_add_neg]
      _ <= qabs (-(f p - f q)) := self_le_qabs _
      _ = qabs (f p - f q) := qabs_neg _
      _ <= L * (q - p) := by simpa [hqdist] using hlip_pq
  have hleft_lower :
      f p - L * (r - p) <= f p - L * (q - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth hL0
    grind [Rat.sub_eq_add_neg]
  have hright_lower :
      f p - L * (r - p) <= f q - L * (r - q) := by
    dsimp [q] at hforward ⊢
    rw [midpoint_right_width]
    grind [Rat.sub_eq_add_neg]
  have hleft_upper :
      f p + L * (q - p) <= f p + L * (r - p) := by
    have hwidth : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
    have hscaled := Rat.mul_le_mul_of_nonneg_left hwidth hL0
    grind [Rat.sub_eq_add_neg]
  have hright_upper :
      f q + L * (r - q) <= f p + L * (r - p) := by
    dsimp [q] at hreverse ⊢
    rw [midpoint_right_width]
    grind [Rat.sub_eq_add_neg]
  constructor
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleft_lower hpq_nonneg
    have hright := Rat.mul_le_mul_of_nonneg_left hright_lower hqr_nonneg
    unfold lipschitzLowerCell
    calc
      (r - p) * (f p - L * (r - p)) =
          (q - p) * (f p - L * (r - p)) +
          (r - q) * (f p - L * (r - p)) := by
            grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
              Rat.add_assoc, Rat.add_comm]
      _ <= (q - p) * (f p - L * (q - p)) +
          (r - q) * (f q - L * (r - q)) :=
        rat_add_le_add hleft hright
  · have hleft := Rat.mul_le_mul_of_nonneg_left hleft_upper hpq_nonneg
    have hright := Rat.mul_le_mul_of_nonneg_left hright_upper hqr_nonneg
    unfold lipschitzUpperCell
    calc
      (q - p) * (f p + L * (q - p)) +
          (r - q) * (f q + L * (r - q)) <=
          (q - p) * (f p + L * (r - p)) +
          (r - q) * (f p + L * (r - p)) :=
        rat_add_le_add hleft hright
      _ = (r - p) * (f p + L * (r - p)) := by
        grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_add,
          Rat.add_assoc, Rat.add_comm]

/-- A raw integral algorithm on a rational interval.

Given the requested output precision, choose a number of subintervals and an
evaluation precision, then compute the corresponding interval-valued left
sum. -/
structure Raw where
  integrand : RealFunRaw
  lower : Rat
  upper : Rat
  plan : Nat -> Plan

namespace Raw

def compute (I : Raw) (eps : Nat) : QInterval :=
  let p := I.plan eps
  riemannLeftInterval I.integrand I.lower I.upper p.subdivisions p.evalPrecision

def Valid (I : Raw) : Prop :=
  RealRaw.ValidCompute I.compute

def toRealRaw (I : Raw) (_h : I.Valid) : RealRaw where
  compute := I.compute

end Raw

/-- The certificate that an interval-valued integral-sum algorithm is a
well-defined computable real number: boxes are ordered, nested, and their
widths shrink to zero. -/
structure Certificate (I : Raw) where
  width_nonneg : forall eps, 0 <= (I.compute eps).width
  nested :
    forall eps delta, eps <= delta ->
      (I.compute eps).lo <= (I.compute delta).lo /\
      (I.compute delta).lo <= (I.compute delta).hi /\
      (I.compute delta).hi <= (I.compute eps).hi
  widths_shrink : RealRaw.WidthsShrinkToZero I.compute

namespace Certificate

theorem valid {I : Raw} (cert : Certificate I) :
    I.Valid :=
  ⟨cert.width_nonneg, cert.nested, cert.widths_shrink⟩

def realRaw {I : Raw} (cert : Certificate I) : RealRaw :=
  I.toRealRaw cert.valid

end Certificate

/-- The interval-sum algorithm determined by a function, interval, and plan. -/
def algorithm (f : RealFunRaw) (a b : Rat) (plan : Nat -> Plan) :
    Raw where
  integrand := f
  lower := a
  upper := b
  plan := plan

/-- The unproved static-dyadic raw Riemann algorithm.  Concrete integral
constructions add the certificate proving that these dyadic boxes are ordered,
nested, and shrinking for the integrand at hand. -/
def staticDyadicAlgorithm (f : RealFunRaw) (a b : Rat) : Raw :=
  algorithm f a b staticDyadicPlan

/-- The explicit data needed to construct an integral as a computable
real.  The public object is still `integral`; this structure just stores the
algorithmic choices and the proof that they work. -/
structure Construction (f : RealFunRaw) (a b : Rat) where
  plan : Nat -> Plan
  certificate : Certificate (algorithm f a b plan)

/-- The constructive integral operator. -/
def integral (f : RealFunRaw) (a b : Rat) (c : Construction f a b) : RealRaw :=
  Certificate.realRaw c.certificate

/-- The exact constant integrand `x ↦ c`, as a raw function. -/
def constantFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun _ => c)

/-- The exact linear primitive `x ↦ c*x`, used for the constant-integral
sanity check. -/
def linearPrimitiveFunRaw (c : Rat) : RealFunRaw :=
  RealFunRaw.exact (fun x => c * x)

/-- One-cell Riemann sums already compute constant integrands exactly. -/
def constantPlan : Nat -> Plan :=
  fun _ => { subdivisions := 1, evalPrecision := 0 }

theorem riemannLeftInterval_constant_one
    (c a b : Rat) (prec : Nat) :
    riemannLeftInterval (constantFunRaw c) a b 1 prec =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  unfold riemannLeftInterval constantFunRaw RealFunRaw.exact leftPoint mesh
  simp
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem constant_algorithm_compute
    (c a b : Rat) (n : Nat) :
    (algorithm (constantFunRaw c) a b constantPlan).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [Raw.compute, algorithm, constantPlan]
  exact riemannLeftInterval_constant_one c a b 0

/-- The exact one-cell constant-integrand algorithm is a valid integral
construction on every rational interval. -/
def constantConstruction (c a b : Rat) :
    Construction (constantFunRaw c) a b where
  plan := constantPlan
  certificate := by
    refine ⟨?_, ?_, ?_⟩
    · intro n
      rw [constant_algorithm_compute]
      simp [QInterval.width]
      grind [Rat.sub_eq_add_neg]
    · intro n m _hnm
      rw [constant_algorithm_compute, constant_algorithm_compute]
      simp
    · intro eps
      refine ⟨0, ?_⟩
      intro n _hn
      rw [constant_algorithm_compute]
      show (b - a) * c - (b - a) * c <= eps.val
      grind [Rat.sub_eq_add_neg]

theorem constantIntegral_compute
    (c a b : Rat) (n : Nat) :
    (integral (constantFunRaw c) a b (constantConstruction c a b)).compute n =
      { lo := (b - a) * c, hi := (b - a) * c } := by
  simp [integral, Certificate.realRaw, Raw.toRealRaw, constantConstruction,
    constant_algorithm_compute]

theorem constantIntegral_valid (c a b : Rat) :
    (integral (constantFunRaw c) a b (constantConstruction c a b)).Valid :=
  (constantConstruction c a b).certificate.valid

/-- Constant integrals respect pointwise addition. -/
theorem constantIntegral_add_equiv (c d a b : Rat) :
    (integral (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).Equiv
        { compute := RealRaw.addCompute
            (integral (constantFunRaw c) a b
              (constantConstruction c a b))
            (integral (constantFunRaw d) a b
              (constantConstruction d a b)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw (c + d)) a b
      (constantConstruction (c + d) a b)).compute n)
    (RealRaw.addCompute
      (integral (constantFunRaw c) a b (constantConstruction c a b))
      (integral (constantFunRaw d) a b (constantConstruction d a b)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.addCompute
  rw [constantIntegral_compute c a b n, constantIntegral_compute d a b n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals respect rational scalar multiplication. -/
theorem constantIntegral_scaleRat_equiv (r c a b : Rat) :
    (integral (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).Equiv
        { compute := RealRaw.scaleRatCompute r
            (integral (constantFunRaw c) a b
              (constantConstruction c a b)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw (r * c)) a b
      (constantConstruction (r * c) a b)).compute n)
    (RealRaw.scaleRatCompute r
      (integral (constantFunRaw c) a b (constantConstruction c a b)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.scaleRatCompute
  rw [constantIntegral_compute c a b n]
  unfold QInterval.Overlaps
  by_cases hr : 0 <= r
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]
  · simp [hr]
    constructor <;>
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Constant integrals are additive on adjacent rational intervals. -/
theorem constantIntegral_adjacent_additive (k a b c : Rat) :
    (integral (constantFunRaw k) a c
      (constantConstruction k a c)).Equiv
        { compute := RealRaw.addCompute
            (integral (constantFunRaw k) a b
              (constantConstruction k a b))
            (integral (constantFunRaw k) b c
              (constantConstruction k b c)) } := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  change QInterval.Overlaps
    ((integral (constantFunRaw k) a c
      (constantConstruction k a c)).compute n)
    (RealRaw.addCompute
      (integral (constantFunRaw k) a b (constantConstruction k a b))
      (integral (constantFunRaw k) b c (constantConstruction k b c)) n)
  rw [constantIntegral_compute]
  unfold RealRaw.addCompute
  rw [constantIntegral_compute k a b n, constantIntegral_compute k b c n]
  unfold QInterval.Overlaps
  constructor <;>
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

/-- Linearity in the first argument.  The construction data for
the left and right sides may differ; equality is interval-overlap equivalence
of the resulting computable reals. -/
def Linear : Prop :=
  forall (f g : RealFunRaw) (a b : Rat)
    (cf : Construction f a b)
    (cg : Construction g a b)
    (cadd : Construction (RealFunRaw.add f g) a b)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integral f a b cf) (integral g a b cg))),
      (integral (RealFunRaw.add f g) a b cadd).Equiv
        { compute := RealRaw.addCompute (integral f a b cf) (integral g a b cg) }

/-- Rational scalar compatibility. -/
def CompatibleWithScaleRat : Prop :=
  forall (r : Rat) (f : RealFunRaw) (a b : Rat)
    (cf : Construction f a b)
    (cscale : Construction (RealFunRaw.scaleRat r f) a b)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (integral f a b cf))),
      (integral (RealFunRaw.scaleRat r f) a b cscale).Equiv
        { compute := RealRaw.scaleRatCompute r (integral f a b cf) }

/-- Compatibility with adjoining intervals:
`integral a c f = integral a b f + integral b c f`. -/
def AdditiveOnAdjacentIntervals : Prop :=
  forall (f : RealFunRaw) (a b c : Rat)
    (cab : Construction f a b)
    (cbc : Construction f b c)
    (cac : Construction f a c)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integral f a b cab) (integral f b c cbc))),
      (integral f a c cac).Equiv
        { compute := RealRaw.addCompute (integral f a b cab) (integral f b c cbc) }

end Integral

/-- Target: constructive integrability of a real interval evaluator.

This is the theorem we want for the integral before FTC: under the
right effective continuity and boundedness hypotheses, one should be able to
choose plans whose interval sums form a valid `RealRaw`.  The exact
hypotheses will be sharpened as the continuity layer matures. -/
def Integral.ExistsConstruction (f : RealFunRaw) (a b : Rat) : Prop :=
  Nonempty (Integral.Construction f a b)

def endpointDifferenceInterval (F : RealFunRaw) (a b : Rat) (prec : Nat) : QInterval :=
  let A := F.compute a prec
  let B := F.compute b prec
  { lo := B.lo - A.hi, hi := B.hi - A.lo }

def endpointDifferenceCompute (F : RealFunRaw) (a b : Rat) : Nat -> QInterval :=
  fun prec => endpointDifferenceInterval F a b prec

def endpointDifferenceRaw (F : RealFunRaw) (a b : Rat)
    (_h : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) : RealRaw where
  compute := endpointDifferenceCompute F a b

/-- Endpoint differences are valid whenever the primitive is valid at both
endpoints. -/
theorem endpointDifference_valid_of_fun_valid
    {F : RealFunRaw} (hF : F.Valid) {a b : Rat}
    (ha : F.domain a) (hb : F.domain b) :
    RealRaw.ValidCompute (endpointDifferenceCompute F a b) := by
  let A : RealRaw := F.apply hF a ha
  let B : RealRaw := F.apply hF b hb
  have hA : A.Valid := by
    simpa [A, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hsub := RealRaw.subCompute_valid hB hA
  simpa [A, B, endpointDifferenceCompute, endpointDifferenceInterval,
    RealFunRaw.apply, RealFunRaw.applyCompute, RealRaw.subCompute] using hsub

/-- Endpoint differences telescope over adjacent intervals:
\((F(b)-F(a))+(F(c)-F(b))\sim F(c)-F(a)\). -/
theorem endpointDifferenceRaw_adjacent_additive
    {F : RealFunRaw} (hF : F.Valid) {a b c : Rat}
    (ha : F.domain a) (hb : F.domain b) (hc : F.domain c)
    (hab : RealRaw.ValidCompute (endpointDifferenceCompute F a b))
    (hbc : RealRaw.ValidCompute (endpointDifferenceCompute F b c))
    (hac : RealRaw.ValidCompute (endpointDifferenceCompute F a c)) :
    ((endpointDifferenceRaw F a b hab) +
      (endpointDifferenceRaw F b c hbc)).Equiv
        (endpointDifferenceRaw F a c hac) := by
  let A : RealRaw := F.apply hF a ha
  let B : RealRaw := F.apply hF b hb
  let C : RealRaw := F.apply hF c hc
  have hA : A.Valid := by
    simpa [A, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF a ha
  have hB : B.Valid := by
    simpa [B, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF b hb
  have hC : C.Valid := by
    simpa [C, RealRaw.Valid, RealFunRaw.apply, RealFunRaw.applyCompute] using
      hF c hc
  simpa [A, B, C, endpointDifferenceRaw, endpointDifferenceCompute,
    endpointDifferenceInterval, RealFunRaw.apply, RealFunRaw.applyCompute,
    RealRaw.sub, RealRaw.subCompute] using
      (RealRaw.sub_add_sub_cancel_middle_equiv hA hB hC)

/-- Preferred computable-number form of the definite-integral conclusion:
the integral of `dF` over the specific interval `[a,b]` is equal, as a
computable real number, to `F(b)-F(a)`.

Equality of computable reals is `RealRaw.Equiv`: at every requested precision,
the two rational intervals overlap. -/
def DefiniteIntegralEqualsEndpointDifference
    (F dF : RealFunRaw) (a b : Rat)
    (c : Integral.Construction dF a b)
    (hendpoint : RealRaw.ValidCompute (endpointDifferenceCompute F a b)) : Prop :=
  (Integral.integral dF a b c).Equiv
    (endpointDifferenceRaw F a b hendpoint)

/-- The computable-number conclusion of FTC.

Here `F` is the function being differentiated and `dF` is its derivative.  The
statement says that the definite integral of `dF` over `[a,b]`, computed by
finite interval sums, overlaps the endpoint difference `F(b)-F(a)` at every
requested rational precision.  The derivative certificate itself lives in the
differential layer, where functions carry interval domains. -/
structure EffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseN : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b (chooseN eps) (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

/-- Static-dyadic specialization of `EffectiveFTC`.

This is the certificate shape for the first bounded-integral algorithms:
for each requested rational precision choose a dyadic stage `s`, use
`2^s` equal subintervals of `[a,b]`, and compare the resulting left-Riemann
interval with the endpoint-difference interval. -/
structure StaticDyadicEffectiveFTC (F dF : RealFunRaw) (a b : Rat) where
  chooseStage : QPos -> Nat
  chooseEvalPrecision : QPos -> Nat
  good : forall eps,
    QInterval.CloseAt
      (riemannLeftInterval dF a b
        (Integral.staticDyadicSubdivisions (chooseStage eps))
        (chooseEvalPrecision eps))
      (endpointDifferenceInterval F a b (chooseEvalPrecision eps))
      eps

namespace StaticDyadicEffectiveFTC

/-- Forget that the subdivisions were chosen by the static dyadic mesh. -/
def toEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : StaticDyadicEffectiveFTC F dF a b) :
    EffectiveFTC F dF a b where
  chooseN := fun eps => Integral.staticDyadicSubdivisions (h.chooseStage eps)
  chooseEvalPrecision := h.chooseEvalPrecision
  good := h.good

end StaticDyadicEffectiveFTC

def ftcErrorExact (F dF : Rat -> Rat) (a b : Rat) (n : Nat) : Rat :=
  qabs (riemannLeftExact dF a b n - (F b - F a))

def ftcCheckExact (F dF : Rat -> Rat) (a b tolerance : Rat) (n : Nat) : Bool :=
  decide (ftcErrorExact F dF a b n <= tolerance)

/-- Exact rational-function FTC data.

The hypothesis is explicit: `dF` is an effective derivative of `F`.  The
conclusion is the definite-integral statement: for every positive rational
precision, a finite left sum for `dF` over `[a,b]` is within that precision of
`F(b)-F(a)`. -/
structure EffectiveFTCExact (F dF : Rat -> Rat) (a b : Rat) where
  derivative : EffectiveDerivativeExact F dF
  chooseN : QPos -> Nat
  good : forall eps, ftcErrorExact F dF a b (chooseN eps) <= eps.val

def inDomainInterval (a b x : Rat) : Prop :=
  a <= x /\ x <= b

def subintervalOf (I : QInterval) (a b : Rat) : Prop :=
  a <= I.lo /\ I.lo <= I.hi /\ I.hi <= b

/-- A rational closed subinterval of a rational closed interval.  This is the
piece size used by the convex/concave calculus certificates below. -/
structure RationalSubinterval (a b : Rat) where
  lower : Rat
  upper : Rat
  lower_mem : a <= lower
  ordered : lower <= upper
  upper_mem : upper <= b

namespace RationalSubinterval

def contains {a b : Rat} (C : RationalSubinterval a b) (x : Rat) : Prop :=
  C.lower <= x /\ x <= C.upper

theorem contains_inDomain {a b : Rat} (C : RationalSubinterval a b)
    {x : Rat} (hx : C.contains x) :
    inDomainInterval a b x :=
  And.intro
    (Rat.le_trans C.lower_mem hx.1)
    (Rat.le_trans hx.2 C.upper_mem)

def whole (a b : Rat) (hab : a <= b) : RationalSubinterval a b where
  lower := a
  upper := b
  lower_mem := Rat.le_refl
  ordered := hab
  upper_mem := Rat.le_refl

def width {a b : Rat} (C : RationalSubinterval a b) : Rat :=
  C.upper - C.lower

def scaleBound {a b : Rat} (C : RationalSubinterval a b)
    (B : QInterval) : QInterval :=
  QInterval.scaleByRat C.width B

end RationalSubinterval

/-- A finite rational partition of `[a,b]`, represented by monotone rational
grid points.  The cells are the short intervals on which derivative bounds are
certified. -/
structure RationalPartition (a b : Rat) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = a
  right_endpoint : point pieces = b
  monotone :
    forall i j, i <= j -> j <= pieces -> point i <= point j

namespace RationalPartition

/-- The explicit equally-spaced rational partition of an ordered interval.
Uniform partitions are the first common-refinement interface needed for the
geometric integration-by-parts route: multiplication of the number of pieces
gives a single rational grid containing both input grids. -/
def uniform (a b : Rat) (pieces : Nat)
    (hpieces : 0 < pieces) (hab : a <= b) : RationalPartition a b where
  pieces := pieces
  positive := hpieces
  point := leftPoint a b pieces
  left_endpoint := leftPoint_zero a b pieces
  right_endpoint := leftPoint_endpoint hpieces
  monotone := by
    intro i j hij _hj
    exact leftPoint_monotone hpieces hab hij

/-- The old indices of the `m`-piece uniform grid remain valid in its
`m*n`-piece refinement. -/
theorem uniform_refinement_index_right {m n i : Nat}
    (hi : i <= m) : i * n <= m * n :=
  Nat.mul_le_mul_right n hi

/-- The old indices of the `n`-piece uniform grid remain valid in the common
`m*n` refinement. -/
theorem uniform_refinement_index_left {m n j : Nat}
    (hj : j <= n) : j * m <= m * n := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hj

/-- The `m*n` uniform grid contains the complete `m`-piece grid. -/
theorem uniform_refines_right {a b : Rat} {m n i : Nat}
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    (uniform a b (m * n) (Nat.mul_pos hm hn) hab).point (i * n) =
      (uniform a b m hm hab).point i := by
  simpa [uniform] using leftPoint_refine_mul_right
    (a := a) (b := b) (i := i) hm hn

/-- The `m*n` uniform grid contains the complete `n`-piece grid as well.
Together with `uniform_refines_right` this is an explicit common rational
refinement, not a choice principle over arbitrary partitions. -/
theorem uniform_refines_left {a b : Rat} {m n j : Nat}
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    (uniform a b (m * n) (Nat.mul_pos hm hn) hab).point (j * m) =
      (uniform a b n hn hab).point j := by
  simpa [uniform, Nat.mul_comm] using leftPoint_refine_mul_right
    (a := a) (b := b) (i := j) hn hm

/-- A finite rational partition `fine` refines `coarse` when it explicitly
embeds every coarse grid point into the fine grid, preserving endpoints and
index order.  This is finite data: no supremum, density, or completed real
line is involved. -/
structure Refines {a b : Rat}
    (fine coarse : RationalPartition a b) where
  index : Nat -> Nat
  index_zero : index 0 = 0
  index_last : index coarse.pieces = fine.pieces
  index_mono : forall i j, i <= j -> index i <= index j
  point_eq : forall i, i <= coarse.pieces ->
    fine.point (index i) = coarse.point i

/-- Every embedded coarse index is a valid index in the refining partition. -/
theorem Refines.index_le {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {i : Nat} (hi : i <= coarse.pieces) :
    R.index i <= fine.pieces := by
  calc
    R.index i <= R.index coarse.pieces := R.index_mono i coarse.pieces hi
    _ = fine.pieces := R.index_last

/-- Every fine breakpoint between two consecutive embedded coarse indices lies
in the corresponding coarse cell.  This is the finite order fact needed to
transfer a cellwise derivative, monotonicity, or variation bound to a common
refinement. -/
theorem Refines.point_between_consecutive {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {i j : Nat} (hi : i < coarse.pieces)
    (hleft : R.index i <= j) (hright : j <= R.index (i + 1)) :
    coarse.point i <= fine.point j /\ fine.point j <= coarse.point (i + 1) := by
  have hisucc : i + 1 <= coarse.pieces := Nat.succ_le_of_lt hi
  have hjfine : j <= fine.pieces :=
    Nat.le_trans hright (R.index_le hisucc)
  constructor
  · calc
      coarse.point i = fine.point (R.index i) := (R.point_eq i (Nat.le_of_lt hi)).symm
      _ <= fine.point j := fine.monotone _ _ hleft hjfine
  · calc
      fine.point j <= fine.point (R.index (i + 1)) :=
        fine.monotone _ _ hright (R.index_le hisucc)
      _ = coarse.point (i + 1) := R.point_eq _ hisucc

/-- Every partition refines itself by the identity index map. -/
def Refines.refl {a b : Rat} (P : RationalPartition a b) : Refines P P where
  index := fun i => i
  index_zero := rfl
  index_last := rfl
  index_mono := by
    intro i j hij
    exact hij
  point_eq := by
    intro i _hi
    rfl

/-- Finite refinement certificates compose.  This lets a later construction
refine a mesh in several explicit rational stages without losing the map back
to its original partition. -/
def Refines.trans {a b : Rat}
    {fine middle coarse : RationalPartition a b}
    (Rfine : Refines fine middle) (Rmiddle : Refines middle coarse) :
    Refines fine coarse where
  index := fun i => Rfine.index (Rmiddle.index i)
  index_zero := by
    rw [Rmiddle.index_zero, Rfine.index_zero]
  index_last := by
    rw [Rmiddle.index_last, Rfine.index_last]
  index_mono := by
    intro i j hij
    exact Rfine.index_mono _ _ (Rmiddle.index_mono i j hij)
  point_eq := by
    intro i hi
    calc
      fine.point (Rfine.index (Rmiddle.index i)) =
          middle.point (Rmiddle.index i) :=
        Rfine.point_eq _ (Rmiddle.index_le hi)
      _ = coarse.point i := Rmiddle.point_eq i hi

/-- A common rational refinement carries one finite refinement certificate for
each input grid. -/
structure CommonRefinement {a b : Rat}
    (left right : RationalPartition a b) where
  refinement : RationalPartition a b
  refines_left : Refines refinement left
  refines_right : Refines refinement right

/-- The `m*n` uniform grid is a certified common refinement of the `m` and
`n` grids.  Its two embeddings are the elementary index multiplications
`i ↦ i*n` and `j ↦ j*m`. -/
def uniformCommonRefinement (a b : Rat) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hab : a <= b) :
    CommonRefinement (uniform a b m hm hab) (uniform a b n hn hab) where
  refinement := uniform a b (m * n) (Nat.mul_pos hm hn) hab
  refines_left :=
    { index := fun i => i * n
      index_zero := by grind
      index_last := by simp [uniform]
      index_mono := by
        intro i j hij
        exact Nat.mul_le_mul_right n hij
      point_eq := by
        intro i _hi
        exact uniform_refines_right hm hn hab }
  refines_right :=
    { index := fun j => j * m
      index_zero := by grind
      index_last := by simp [uniform, Nat.mul_comm]
      index_mono := by
        intro i j hij
        exact Nat.mul_le_mul_right m hij
      point_eq := by
        intro j _hj
        exact uniform_refines_left hm hn hab }

/-- Insert one rational breakpoint after cell index `k`.  The new list keeps
all old points in order, placing `x` between `point k` and `point (k+1)`.
Repeated use of this finite operation is the constructive route from explicit
breakpoint lists to a general common refinement. -/
def insertPointValue {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (x : Rat) : Nat -> Rat :=
  fun i => if i <= k then P.point i else
    if i = k + 1 then x else P.point (i - 1)

/-- Scan a finite breakpoint list from the left for a cell whose right
endpoint reaches a specified rational value.  The fuel is explicit so this is
a total rational computation, not a choice of a supremum. -/
def locateInsertionCellAux {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | fuel + 1 =>
      if x <= P.point (i + 1) then i
      else locateInsertionCellAux P x (i + 1) fuel

/-- Locate a cell containing `x` by scanning all cells of a finite rational
partition.  Its correctness proof below supplies the local ordering data for
the subsequent insertion. -/
def locateInsertionCell {a b : Rat} (P : RationalPartition a b)
    (x : Rat) : Nat :=
  locateInsertionCellAux P x 0 P.pieces

/-- Correctness of the finite left-to-right cell scan. -/
theorem locateInsertionCellAux_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) :
    forall (i fuel : Nat),
      0 < fuel ->
      i + fuel <= P.pieces ->
      P.point i <= x ->
      x <= P.point (i + fuel) ->
      let k := locateInsertionCellAux P x i fuel
      i <= k /\ k < i + fuel /\ P.point k <= x /\ x <= P.point (k + 1) := by
  intro i fuel hfuel hbound hleft hright
  induction fuel generalizing i with
  | zero => omega
  | succ fuel ih =>
      simp only [locateInsertionCellAux]
      by_cases hnext : x <= P.point (i + 1)
      · rw [if_pos hnext]
        exact ⟨Nat.le_refl _, by omega, hleft, hnext⟩
      · rw [if_neg hnext]
        cases fuel with
        | zero =>
            exfalso
            apply hnext
            simpa using hright
        | succ fuel =>
            have hnext_left : P.point (i + 1) <= x := by
              exact (Rat.le_total : P.point (i + 1) <= x \/ x <= P.point (i + 1)).resolve_right hnext
            have hbound' : (i + 1) + (fuel + 1) <= P.pieces := by omega
            have hright' : x <= P.point ((i + 1) + (fuel + 1)) := by
              have hindex : (i + 1) + (fuel + 1) = i + (fuel + 1 + 1) := by omega
              simpa [hindex] using hright
            rcases ih (i + 1) (by omega) hbound' hnext_left hright' with
              ⟨hfirst, hsecond, hvalue, hupper⟩
            exact ⟨Nat.le_trans (Nat.le_succ i) hfirst, by omega, hvalue, hupper⟩

/-- A point in the enclosing interval is located in an actual partition cell,
with all bounds obtained by the finite scan. -/
theorem locateInsertionCell_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    locateInsertionCell P x < P.pieces /\
      P.point (locateInsertionCell P x) <= x /\
      x <= P.point (locateInsertionCell P x + 1) := by
  have h := locateInsertionCellAux_spec P x 0 P.pieces P.positive
    (by omega) (by simpa [P.left_endpoint] using hleft)
    (by simpa [P.right_endpoint] using hright)
  simpa [locateInsertionCell] using h

/-- The partition obtained by inserting a rational point in one specified
cell.  Degenerate insertion at an endpoint is allowed: partitions record
monotone, rather than strictly increasing, rational breakpoint data. -/
def insertPoint {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    RationalPartition a b where
  pieces := P.pieces + 1
  positive := by omega
  point := insertPointValue P k x
  left_endpoint := by
    simp [insertPointValue, P.left_endpoint]
  right_endpoint := by
    have hnot : ¬ (P.pieces + 1 <= k) := by omega
    have hneq : P.pieces ≠ k := by omega
    simp [insertPointValue, hnot, hneq, P.right_endpoint]
  monotone := by
    intro i j hij hj
    by_cases hjk : j <= k
    · have hik : i <= k := Nat.le_trans hij hjk
      simp [insertPointValue, hik, hjk]
      exact P.monotone i j hij (Nat.le_trans hjk (Nat.le_of_lt hk))
    · have hkj : k + 1 <= j := by omega
      by_cases hik : i <= k
      · by_cases hjeq : j = k + 1
        · subst j
          simp [insertPointValue, hik, hjk]
          exact Rat.le_trans
            (P.monotone i k hik (Nat.le_of_lt hk)) hleft
        · have hsub : j - 1 <= P.pieces := by omega
          have hisub : i <= j - 1 := by omega
          simp [insertPointValue, hik, hjk, hjeq]
          exact P.monotone i (j - 1) hisub hsub
      · have hki : k + 1 <= i := by omega
        by_cases hieq : i = k + 1
        · subst i
          by_cases hjeq : j = k + 1
          · subst j
            simp [insertPointValue, hjk]
          · have hsub : j - 1 <= P.pieces := by omega
            have hbetween : k + 1 <= j - 1 := by omega
            have hnotik : ¬ (k + 1 <= k) := by omega
            simp [insertPointValue, hjk, hjeq, hnotik]
            exact Rat.le_trans hright (P.monotone (k + 1) (j - 1) hbetween hsub)
        · have hsubi : i - 1 <= P.pieces := by omega
          have hsubj : j - 1 <= P.pieces := by omega
          have hisub : i - 1 <= j - 1 := by omega
          have hjeq : j ≠ k + 1 := by omega
          simp [insertPointValue, hik, hjk, hieq, hjeq]
          exact P.monotone (i - 1) (j - 1) hisub hsubj

/-- Insert a rational point known to lie in the enclosing interval, choosing
its containing cell by the explicit finite scan. -/
def insertLocatedPoint {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) : RationalPartition a b :=
  let h := locateInsertionCell_spec P x hleft hright
  insertPoint P (locateInsertionCell P x) h.1 x h.2.1 h.2.2

/-- The old partition is explicitly embedded in a one-point insertion. -/
def insertPoint_refines {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    Refines (insertPoint P k hk x hleft hright) P where
  index := fun i => if i <= k then i else i + 1
  index_zero := by simp
  index_last := by
    have hnot : ¬ (P.pieces <= k) := by omega
    simp [hnot, insertPoint]
  index_mono := by
    intro i j hij
    by_cases hik : i <= k
    · by_cases hjk : j <= k
      · simp [hik, hjk, hij]
      · have hle : i <= j + 1 := by omega
        simp [hik, hjk, hle]
    · have hjk : ¬ j <= k := by
        intro hjk
        exact hik (Nat.le_trans hij hjk)
      have hle : i + 1 <= j + 1 := Nat.succ_le_succ hij
      simp [hik, hjk, hle]
  point_eq := by
    intro i hi
    by_cases hik : i <= k
    · simp [insertPoint, insertPointValue, hik]
    · have hindex : ¬ (i + 1 <= k) := by omega
      have hneq : i ≠ k := by omega
      simp [insertPoint, insertPointValue, hik, hindex, hneq]

/-- The scan-selected insertion is also a certified refinement of the old
partition. -/
def insertLocatedPoint_refines {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    Refines (insertLocatedPoint P x hleft hright) P := by
  unfold insertLocatedPoint
  dsimp
  exact insertPoint_refines _ _ _ _ _ _

/-- A single arbitrary rational breakpoint yields a certified common
refinement of the old partition and the inserted partition. -/
def insertPointCommonRefinement {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) (x : Rat)
    (hleft : P.point k <= x) (hright : x <= P.point (k + 1)) :
    CommonRefinement P (insertPoint P k hk x hleft hright) where
  refinement := insertPoint P k hk x hleft hright
  refines_left := insertPoint_refines P k hk x hleft hright
  refines_right := Refines.refl _

/-- The scan-selected insertion packages the same common-refinement
certificate without requiring the caller to choose a cell index. -/
def insertLocatedPointCommonRefinement {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    CommonRefinement P (insertLocatedPoint P x hleft hright) where
  refinement := insertLocatedPoint P x hleft hright
  refines_left := insertLocatedPoint_refines P x hleft hright
  refines_right := Refines.refl _

/-- A finite record of successive rational breakpoint insertions.  Each step
has its own cell-membership proof, so the resulting refinement is executable
finite data rather than an existential appeal to density of the rationals. -/
inductive InsertionChain {a b : Rat} :
    RationalPartition a b -> RationalPartition a b -> Type
  | refl (P : RationalPartition a b) : InsertionChain P P
  | insert {base current : RationalPartition a b}
      (chain : InsertionChain base current)
      (k : Nat) (hk : k < current.pieces) (x : Rat)
      (hleft : current.point k <= x) (hright : x <= current.point (k + 1)) :
      InsertionChain base (insertPoint current k hk x hleft hright)

/-- Extend an insertion chain by any rational point in the enclosing interval.
The finite scan chooses its containing cell, so a later list-merging algorithm
can add breakpoints without any external choice operation. -/
def InsertionChain.insertLocated {a b : Rat}
    {base current : RationalPartition a b}
    (chain : InsertionChain base current) (x : Rat)
    (hleft : a <= x) (hright : x <= b) :
    InsertionChain base (insertLocatedPoint current x hleft hright) :=
  let h := locateInsertionCell_spec current x hleft hright
  InsertionChain.insert chain (locateInsertionCell current x) h.1 x h.2.1 h.2.2

/-- Turn any finite list of rational points in `[a,b]` into an explicit
insertion chain.  The returned sigma pair contains both the final partition
and the proof-relevant sequence of finite scan-and-insert steps that produced
it. -/
def insertionChainOfPointList {a b : Rat} (P : RationalPartition a b) :
    (xs : List Rat) ->
    (forall x, x ∈ xs -> a <= x /\ x <= b) ->
    Sigma (InsertionChain P)
  | [], _ => ⟨P, InsertionChain.refl P⟩
  | x :: xs, hinside =>
      let htail : forall y, y ∈ xs -> a <= y /\ y <= b :=
        fun y hy => hinside y (List.mem_cons_of_mem x hy)
      let rest := insertionChainOfPointList P xs htail
      let hx := hinside x (by simp)
      ⟨insertLocatedPoint rest.1 x hx.1 hx.2,
        rest.2.insertLocated x hx.1 hx.2⟩

/-- A rational value occurs among a partition's finite breakpoint list. -/
def ContainsPoint {a b : Rat} (P : RationalPartition a b) (x : Rat) : Prop :=
  exists i, i <= P.pieces /\ P.point i = x

/-- A refinement preserves every explicitly occurring breakpoint. -/
theorem containsPoint_of_refines {a b : Rat}
    {fine coarse : RationalPartition a b} (R : Refines fine coarse)
    {x : Rat} (hx : coarse.ContainsPoint x) : fine.ContainsPoint x := by
  rcases hx with ⟨i, hi, hpoint⟩
  refine ⟨R.index i, R.index_le hi, ?_⟩
  rw [R.point_eq i hi, hpoint]

/-- The scan-selected insertion explicitly contains its inserted value. -/
theorem insertLocatedPoint_contains {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hleft : a <= x) (hright : x <= b) :
    (insertLocatedPoint P x hleft hright).ContainsPoint x := by
  have h := locateInsertionCell_spec P x hleft hright
  refine ⟨locateInsertionCell P x + 1, ?_, ?_⟩
  · change locateInsertionCell P x + 1 <= P.pieces + 1
    omega
  · have hnot : ¬ (locateInsertionCell P x + 1 <= locateInsertionCell P x) := by
      omega
    simp [insertLocatedPoint, insertPoint, insertPointValue, hnot]

/-- Every member of an in-range finite list occurs in the breakpoint list
produced by the scan-and-insert construction. -/
theorem insertionChainOfPointList_contains {a b : Rat}
    (P : RationalPartition a b) :
    forall (xs : List Rat)
      (hinside : forall x, x ∈ xs -> a <= x /\ x <= b)
      {x : Rat}, x ∈ xs ->
        (insertionChainOfPointList P xs hinside).1.ContainsPoint x := by
  intro xs
  induction xs with
  | nil =>
      intro hinside x hx
      simp at hx
  | cons y ys ih =>
      intro hinside x hx
      let htail : forall z, z ∈ ys -> a <= z /\ z <= b :=
        fun z hz => hinside z (List.mem_cons_of_mem y hz)
      let rest := insertionChainOfPointList P ys htail
      have hy : a <= y /\ y <= b := hinside y (by simp)
      change (insertLocatedPoint rest.1 y hy.1 hy.2).ContainsPoint x
      rcases List.mem_cons.mp hx with hxy | hx
      · subst x
        exact insertLocatedPoint_contains rest.1 y hy.1 hy.2
      · exact containsPoint_of_refines
          (insertLocatedPoint_refines rest.1 y hy.1 hy.2)
          (ih htail hx)

/-- Scan a finite breakpoint list for the first occurrence of a rational
value.  The scan is total; its correctness theorem below is used only when
the value is known to occur. -/
def firstOccurrenceAux {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (i fuel : Nat) : Nat :=
  match fuel with
  | 0 => i
  | fuel + 1 =>
      if P.point i = x then i else firstOccurrenceAux P x (i + 1) fuel

/-- The leftmost-occurrence search over all actual breakpoint indices. -/
def firstOccurrence {a b : Rat} (P : RationalPartition a b) (x : Rat) : Nat :=
  firstOccurrenceAux P x 0 (P.pieces + 1)

/-- Correctness of the finite first-occurrence scan. -/
theorem firstOccurrenceAux_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) :
    forall (i fuel j : Nat),
      i <= j -> j < i + fuel -> P.point j = x ->
      let k := firstOccurrenceAux P x i fuel
      i <= k /\ k <= j /\ P.point k = x := by
  intro i fuel
  induction fuel generalizing i with
  | zero =>
      intro j hij hj hpoint
      omega
  | succ fuel ih =>
      intro j hij hj hpoint
      simp only [firstOccurrenceAux]
      by_cases hi : P.point i = x
      · rw [if_pos hi]
        exact ⟨Nat.le_refl _, hij, hi⟩
      · rw [if_neg hi]
        have hijne : i ≠ j := by
          intro heq
          apply hi
          simpa [heq] using hpoint
        have hlt : i < j := Nat.lt_of_le_of_ne hij hijne
        rcases ih (i + 1) j (by omega) (by omega) hpoint with
          ⟨hfirst, hsecond, hvalue⟩
        exact ⟨Nat.le_trans (Nat.le_succ i) hfirst, hsecond, hvalue⟩

/-- If a rational value occurs in a partition, the finite scan finds its
leftmost occurrence and is no later than every other occurrence. -/
theorem firstOccurrence_spec {a b : Rat} (P : RationalPartition a b)
    (x : Rat) (hx : P.ContainsPoint x) :
    firstOccurrence P x <= P.pieces /\
      P.point (firstOccurrence P x) = x /\
      forall j, j <= P.pieces -> P.point j = x -> firstOccurrence P x <= j := by
  rcases hx with ⟨j, hj, hpoint⟩
  have hfound := firstOccurrenceAux_spec P x 0 (P.pieces + 1) j
    (Nat.zero_le _) (by omega) hpoint
  constructor
  · exact Nat.le_trans (by simpa [firstOccurrence] using hfound.2.1) hj
  constructor
  · simpa [firstOccurrence] using hfound.2.2
  · intro i hi hvalue
    have hfirst := firstOccurrenceAux_spec P x 0 (P.pieces + 1) i
      (Nat.zero_le _) (by omega) hvalue
    simpa [firstOccurrence] using hfirst.2.1

/-- The leftmost occurrence of the left endpoint is index zero. -/
theorem firstOccurrence_leftEndpoint {a b : Rat} (P : RationalPartition a b) :
    firstOccurrence P a = 0 := by
  have ha : P.ContainsPoint a := ⟨0, Nat.zero_le _, P.left_endpoint⟩
  apply Nat.eq_zero_of_le_zero
  exact (firstOccurrence_spec P a ha).2.2 0 (Nat.zero_le _) P.left_endpoint

/-- First occurrences preserve the rational order of values that occur in a
monotone partition. -/
theorem firstOccurrence_mono {a b : Rat} (P : RationalPartition a b)
    {x y : Rat} (hx : P.ContainsPoint x) (hy : P.ContainsPoint y)
    (hxy : x <= y) :
    firstOccurrence P x <= firstOccurrence P y := by
  by_cases hEq : x = y
  · subst y
    exact Nat.le_refl _
  · apply Nat.le_of_not_lt
    intro hindex
    have hspecX := firstOccurrence_spec P x hx
    have hspecY := firstOccurrence_spec P y hy
    have hyx : y <= x := by
      calc
        y = P.point (firstOccurrence P y) := hspecY.2.1.symm
        _ <= P.point (firstOccurrence P x) :=
          P.monotone _ _ (Nat.le_of_lt hindex) hspecX.1
        _ = x := hspecX.2.1
    exact hEq (Rat.le_antisymm hxy hyx)

/-- A refinement may be recovered constructively from the information that
every coarse breakpoint occurs somewhere in a fine monotone list. -/
def ContainsAllPoints {a b : Rat}
    (fine coarse : RationalPartition a b) : Prop :=
  forall i, i <= coarse.pieces -> fine.ContainsPoint (coarse.point i)

/-- The index used to recover an ordered refinement from point containment.
After the final coarse breakpoint it stays at the final fine breakpoint, so it
is a monotone total function on natural numbers as required by `Refines`. -/
def refinementIndex {a b : Rat}
    (fine coarse : RationalPartition a b) (i : Nat) : Nat :=
  let j := min i coarse.pieces
  if j = coarse.pieces then fine.pieces else firstOccurrence fine (coarse.point j)

theorem refinementIndex_le {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse) (i : Nat) :
    refinementIndex fine coarse i <= fine.pieces := by
  simp only [refinementIndex]
  split
  · exact Nat.le_refl _
  · exact (firstOccurrence_spec fine _
      (hcontains _ (Nat.min_le_right _ _))).1

theorem refinementIndex_zero {a b : Rat}
    {fine coarse : RationalPartition a b} :
    refinementIndex fine coarse 0 = 0 := by
  have hpositive : coarse.pieces ≠ 0 := Nat.ne_of_gt coarse.positive
  have hmin : min 0 coarse.pieces = 0 := Nat.min_eq_left (Nat.zero_le _)
  have hlast : ¬ (0 = coarse.pieces) := fun h => hpositive h.symm
  rw [refinementIndex, hmin, if_neg hlast]
  simpa [coarse.left_endpoint] using firstOccurrence_leftEndpoint fine

theorem refinementIndex_last {a b : Rat}
    (fine coarse : RationalPartition a b) :
    refinementIndex fine coarse coarse.pieces = fine.pieces := by
  simp [refinementIndex]

theorem refinementIndex_point_eq {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse)
    {i : Nat} (hi : i <= coarse.pieces) :
    fine.point (refinementIndex fine coarse i) = coarse.point i := by
  have hmin : min i coarse.pieces = i := Nat.min_eq_left hi
  rw [refinementIndex, hmin]
  by_cases hlast : i = coarse.pieces
  · rw [if_pos hlast]
    subst i
    rw [fine.right_endpoint, coarse.right_endpoint]
  · rw [if_neg hlast]
    exact (firstOccurrence_spec fine _ (hcontains i hi)).2.1

theorem refinementIndex_mono {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse)
    (i j : Nat) (hij : i <= j) :
    refinementIndex fine coarse i <= refinementIndex fine coarse j := by
  let i' := min i coarse.pieces
  let j' := min j coarse.pieces
  have hi' : i' <= coarse.pieces := Nat.min_le_right _ _
  have hj' : j' <= coarse.pieces := Nat.min_le_right _ _
  have hij' : i' <= j' := by
    dsimp [i', j']
    omega
  by_cases hilast : i' = coarse.pieces
  · have hjlast : j' = coarse.pieces := by
      apply Nat.le_antisymm hj'
      simpa [hilast] using hij'
    simp [refinementIndex, i', j', hilast, hjlast]
  · by_cases hjlast : j' = coarse.pieces
    · simp only [refinementIndex]
      rw [show min i coarse.pieces = i' by rfl,
        show min j coarse.pieces = j' by rfl, if_neg hilast, if_pos hjlast]
      exact (firstOccurrence_spec fine _ (hcontains i' hi')).1
    · simp only [refinementIndex]
      rw [show min i coarse.pieces = i' by rfl,
        show min j coarse.pieces = j' by rfl, if_neg hilast, if_neg hjlast]
      exact firstOccurrence_mono fine (hcontains i' hi') (hcontains j' hj')
        (coarse.monotone i' j' hij' hj')

/-- Point containment is sufficient to build the full finite refinement
certificate, including a monotone embedding of all coarse breakpoint indices. -/
def refinesOfContainsAllPoints {a b : Rat}
    {fine coarse : RationalPartition a b}
    (hcontains : ContainsAllPoints fine coarse) : Refines fine coarse where
  index := refinementIndex fine coarse
  index_zero := refinementIndex_zero
  index_last := refinementIndex_last fine coarse
  index_mono := refinementIndex_mono hcontains
  point_eq := fun _ hi => refinementIndex_point_eq hcontains hi

/-- The explicitly finite list of every breakpoint in a partition. -/
def breakpointList {a b : Rat} (P : RationalPartition a b) : List Rat :=
  (List.range (P.pieces + 1)).map P.point

theorem point_mem_breakpointList {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) : P.point i ∈ P.breakpointList := by
  apply List.mem_map.mpr
  exact ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩

theorem point_in_bounds {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) :
    a <= P.point i /\ P.point i <= b := by
  constructor
  · calc
      a = P.point 0 := P.left_endpoint.symm
      _ <= P.point i := P.monotone 0 i (Nat.zero_le _) hi
  · calc
      P.point i <= P.point P.pieces := P.monotone i P.pieces hi (Nat.le_refl _)
      _ = b := P.right_endpoint

theorem breakpointList_in_bounds {a b : Rat} (P : RationalPartition a b) :
    forall x, x ∈ P.breakpointList -> a <= x /\ x <= b := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, hpoint⟩
  rw [← hpoint]
  apply P.point_in_bounds
  have hindex := List.mem_range.mp hi
  omega

/-- Insert every breakpoint of the right partition into the left one by a
deterministic finite scan.  The following theorem turns the resulting point
containment into both refinement certificates. -/
def partitionPointInsertionChain {a b : Rat}
    (left right : RationalPartition a b) : Sigma (InsertionChain left) :=
  insertionChainOfPointList left right.breakpointList (breakpointList_in_bounds right)

theorem partitionPointInsertionChain_contains {a b : Rat}
    (left right : RationalPartition a b) {i : Nat} (hi : i <= right.pieces) :
    (partitionPointInsertionChain left right).1.ContainsPoint (right.point i) := by
  apply insertionChainOfPointList_contains left right.breakpointList
    (breakpointList_in_bounds right)
  exact right.point_mem_breakpointList hi

/-- A finite insertion chain carries its composite refinement certificate back
to its starting breakpoint list. -/
noncomputable def InsertionChain.refines {a b : Rat}
    {base target : RationalPartition a b} :
    InsertionChain base target -> Refines target base := by
  intro chain
  induction chain with
  | refl =>
      exact Refines.refl _
  | insert chain k hk x hleft hright ih =>
      exact (insertPoint_refines _ k hk x hleft hright).trans ih

/-- Every endpoint of a finite insertion chain is a common refinement of its
initial partition and its final explicitly inserted breakpoint list. -/
noncomputable def InsertionChain.commonRefinement {a b : Rat}
    {base target : RationalPartition a b}
    (chain : InsertionChain base target) : CommonRefinement base target where
  refinement := target
  refines_left := chain.refines
  refines_right := Refines.refl target

/-- A general finite common-refinement construction for arbitrary rational
partitions.  It uses only the supplied breakpoint lists, bounded scans, and
the monotonicity proof already carried by each partition. -/
noncomputable def commonRefinementOfPartitions {a b : Rat}
    (left right : RationalPartition a b) : CommonRefinement left right :=
  let chain := partitionPointInsertionChain left right
  { refinement := chain.1
    refines_left := chain.2.refines
    refines_right := refinesOfContainsAllPoints
      (fun _ hi => partitionPointInsertionChain_contains left right hi) }

def cell {a b : Rat} (P : RationalPartition a b)
    (k : Nat) (hk : k < P.pieces) : RationalSubinterval a b where
  lower := P.point k
  upper := P.point (k + 1)
  lower_mem := by
    have hkPieces : k <= P.pieces := Nat.le_of_lt hk
    have h := P.monotone 0 k (Nat.zero_le k) hkPieces
    simpa [P.left_endpoint] using h
  ordered := by
    exact P.monotone k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk)
  upper_mem := by
    have h := P.monotone (k + 1) P.pieces (Nat.succ_le_of_lt hk) (Nat.le_refl P.pieces)
    simpa [P.right_endpoint] using h

/-- Regard a partition's breakpoint list as a total rational path by holding
its final value constant beyond the last cell.  This permits the finite
corner-sum estimates to apply directly to partition data. -/
def clampedPath {a b : Rat} (P : RationalPartition a b) (i : Nat) : Rat :=
  P.point (min i P.pieces)

theorem clampedPath_eq_point {a b : Rat} (P : RationalPartition a b)
    {i : Nat} (hi : i <= P.pieces) :
    P.clampedPath i = P.point i := by
  simp [clampedPath, Nat.min_eq_left hi]

/-- Successive values of a clamped partition path are nondecreasing. -/
theorem clampedPath_step_nonnegative {a b : Rat}
    (P : RationalPartition a b) (i : Nat) :
    0 <= P.clampedPath (i + 1) - P.clampedPath i := by
  by_cases hi : i < P.pieces
  · have hmin : min i P.pieces = i := Nat.min_eq_left (Nat.le_of_lt hi)
    have hminsucc : min (i + 1) P.pieces = i + 1 :=
      Nat.min_eq_left (Nat.succ_le_of_lt hi)
    have hmono := P.monotone i (i + 1) (Nat.le_succ i) (Nat.succ_le_of_lt hi)
    rw [clampedPath, clampedPath, hmin, hminsucc]
    grind [Rat.sub_eq_add_neg]
  · have hpieces : P.pieces <= i := Nat.le_of_not_gt hi
    have hmin : min i P.pieces = P.pieces := Nat.min_eq_right hpieces
    have hminsucc : min (i + 1) P.pieces = P.pieces :=
      Nat.min_eq_right (Nat.le_trans hpieces (Nat.le_succ i))
    rw [clampedPath, clampedPath, hmin, hminsucc]
    grind [Rat.sub_eq_add_neg]

/-- The nonnegative corner correction for a partition's own monotone
breakpoint path is bounded by the square of its endpoint variation.  This
instantiates the geometric finite integration-by-parts estimate on an actual
rational partition, ready for cellwise mesh bounds. -/
theorem clampedPath_quadraticVariation_le_endpointSquare {a b : Rat}
    (P : RationalPartition a b) :
    quadraticVariationSum P.clampedPath P.clampedPath P.pieces <=
      (b - a) * (b - a) := by
  have h := quadraticVariationSum_le_endpointVariationProduct_of_step_nonnegative
    P.clampedPath P.clampedPath
    (clampedPath_step_nonnegative P) (clampedPath_step_nonnegative P) P.pieces
  simpa [clampedPath, P.left_endpoint, P.right_endpoint] using h

def boundIntegralSum {a b : Rat} (P : RationalPartition a b)
    (bound : (k : Nat) -> k < P.pieces -> QInterval) : QInterval :=
  (List.range P.pieces).foldl
    (fun acc k =>
      if hk : k < P.pieces then
        QInterval.addInterval acc ((P.cell k hk).scaleBound (bound k hk))
      else
        acc)
    { lo := 0, hi := 0 }

end RationalPartition

/-- A certified enclosure of derivative values on one rational subinterval.

This is the FTC-facing primitive: for every rational point in a short cell,
the pointwise derivative enclosure at the chosen evaluation precision is
contained in the supplied rational interval.  No convexity or differentiability
topology is mentioned here. -/
structure DerivativeBoundOnSubinterval
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (evalPrecision n))

/-- Local endpoint control supplied by a derivative bound.  This is the
constructive substitute for invoking a classical mean-value theorem: the
scaled derivative range encloses the endpoint difference of the primitive on
this short cell. -/
structure LocalFTCFromDerivativeBound
    (F dF : RealFunRaw) {a b : Rat}
    (C : RationalSubinterval a b)
    (B : DerivativeBoundOnSubinterval dF C) where
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  endpointPrecision : Nat -> Nat
  endpoint_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (B.bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

/-- Local finite certificate that a candidate derivative matches the computed
secant behavior of the original function on one rational cell.

The `bound` field is the common rational interval enclosure.  The
`candidate_contained` field says the candidate derivative `dF` lies in that
bound at every rational point of the cell.  The
`endpoint_difference_contained` field says the actual endpoint difference of
`F` on the same cell is contained in the cell width times that bound.  Thus the
candidate derivative is not guessed: it is certified against finite secant
inequalities for the concrete algorithm. -/
structure CandidateDerivativeCellControl
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  bound : Nat -> QInterval
  derivativeEvalPrecision : Nat -> Nat
  endpointPrecision : Nat -> Nat
  primitive_domain_lower : F.domain C.lower
  primitive_domain_upper : F.domain C.upper
  candidate_domain_on : forall x, C.contains x -> dF.domain x
  bound_ordered : forall n, 0 <= (bound n).width
  candidate_contained :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (bound n)
        (dF.compute x (derivativeEvalPrecision n))
  endpoint_difference_contained :
    forall n,
      QInterval.ContainsInterval
        (C.scaleBound (bound n))
        (endpointDifferenceInterval F C.lower C.upper (endpointPrecision n))

namespace CandidateDerivativeCellControl

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := H.bound
  evalPrecision := H.derivativeEvalPrecision
  domain_on := H.candidate_domain_on
  bound_ordered := H.bound_ordered
  contains_values := H.candidate_contained

def toLocalFTC
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : CandidateDerivativeCellControl F dF C) :
    LocalFTCFromDerivativeBound F dF C H.toDerivativeBound where
  primitive_domain_lower := H.primitive_domain_lower
  primitive_domain_upper := H.primitive_domain_upper
  endpointPrecision := H.endpointPrecision
  endpoint_contained := H.endpoint_difference_contained

end CandidateDerivativeCellControl

/-- FTC data based on derivative bounds over short rational cells.

The FTC-facing assumption is the derivative-range bound on each cell.  How
those bounds are produced is deliberately separate: monotonicity, convexity,
concavity, power-series tails, or formula-specific interval arithmetic can all
feed the same structure.

For each requested rational precision `eps`, the certificate chooses a rational
partition of `[a,b]`, derivative enclosures on its cells, and an endpoint
evaluation precision for `F(b)-F(a)`.  The summed derivative-bound interval is
the Riemann-style enclosure; the theorem-facing obligations are exactly that
this enclosure has width at most `eps`, the endpoint-difference interval has
width at most `eps`, and the two intervals overlap. -/
structure DerivativeBoundFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  derivativeBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundOnSubinterval dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          (derivativeBound eps k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (derivativeBound eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace DerivativeBoundFTC

def boundedIntegralInterval
    {F dF : RealFunRaw} {a b : Rat}
  (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  (h.choosePartition eps).boundIntegralSum
    (fun k hk => (h.derivativeBound eps k hk).bound (h.chooseBoundStage eps))

def endpointInterval
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) : QInterval :=
  endpointDifferenceInterval F a b (h.chooseEndpointPrecision eps)

theorem closeAt
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) (eps : QPos) :
    QInterval.CloseAt (h.boundedIntegralInterval eps) (h.endpointInterval eps) eps := by
  exact ⟨h.overlap eps, h.riemann_width eps, h.endpoint_width eps⟩

def boundedIntegralCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.boundedIntegralInterval (precisionAtStage n)

def endpointCompute
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : Nat -> QInterval :=
  fun n => h.endpointInterval (precisionAtStage n)

def boundedIntegralRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealRaw where
  compute := h.boundedIntegralCompute

def endpointRaw
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) : RealRaw where
  compute := h.endpointCompute

/-- The derivative-bound FTC bridge, in computable-real form. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hgood := h.closeAt (precisionAtStage n)
  exact (RealRaw.compareAt_overlap_iff
    h.boundedIntegralRaw h.endpointRaw n n).2 hgood.1

end DerivativeBoundFTC

/-- Top-level derivative-bound FTC bridge.

This is the public theorem name for the finite cell-bound route: once the
derivative-bound certificate supplies overlapping bounded-sum and endpoint
intervals at every requested precision, the two raw real algorithms are
equivalent. -/
theorem derivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : DerivativeBoundFTC F dF a b) :
    h.boundedIntegralRaw.Equiv h.endpointRaw :=
  h.equiv_endpoint

/-- Global finite certificate for the "candidate derivative versus computed
secants" strategy.

For each requested precision, choose a rational partition.  On each cell,
`cellControl` supplies one rational interval family that simultaneously:

* contains the candidate derivative values, and
* contains the actual endpoint secant behavior of `F` after scaling by the
  cell width.

The remaining fields are exactly the numerical FTC closure conditions: the
summed bound interval and the endpoint-difference interval are narrow and
overlap. -/
structure CandidateDerivativeFTC (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  cellControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        CandidateDerivativeCellControl F dF ((choosePartition eps).cell k hk)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk => (cellControl eps k hk).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CandidateDerivativeFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk =>
    (h.cellControl eps k hk).toDerivativeBound
  localControl := fun eps k hk =>
    (h.cellControl eps k hk).toLocalFTC
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

/-- The closure theorem for the candidate-derivative strategy. -/
theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CandidateDerivativeFTC

/-- Top-level closure theorem for the candidate-derivative strategy. -/
theorem candidateDerivativeFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CandidateDerivativeFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

inductive MonotonicityKind where
  | nondecreasing
  | nonincreasing
deriving DecidableEq, Repr

def endpointDerivativeBound
    (kind : MonotonicityKind) (dF : RealFunRaw)
    {a b : Rat} (C : RationalSubinterval a b) (prec : Nat) : QInterval :=
  match kind with
  | .nondecreasing =>
      { lo := (dF.compute C.lower prec).lo,
        hi := (dF.compute C.upper prec).hi }
  | .nonincreasing =>
      { lo := (dF.compute C.upper prec).lo,
        hi := (dF.compute C.lower prec).hi }

/-- A common way to produce a derivative bound: prove the derivative is
monotone on the short cell, then use endpoint derivative enclosures as the
range bound. -/
structure MonotoneDerivativeBoundMethod
    (dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : MonotonicityKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> dF.domain x
  endpoint_bound_ordered :
    forall n, 0 <= (endpointDerivativeBound kind dF C (evalPrecision n)).width
  endpoint_contains_values :
    forall n x (_hx : C.contains x),
      QInterval.ContainsInterval
        (endpointDerivativeBound kind dF C (evalPrecision n))
        (dF.compute x (evalPrecision n))

namespace MonotoneDerivativeBoundMethod

def toDerivativeBound
    {dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (M : MonotoneDerivativeBoundMethod dF C) :
    DerivativeBoundOnSubinterval dF C where
  bound := fun n => endpointDerivativeBound M.kind dF C (M.evalPrecision n)
  evalPrecision := M.evalPrecision
  domain_on := M.domain_on
  bound_ordered := M.endpoint_bound_ordered
  contains_values := M.endpoint_contains_values

end MonotoneDerivativeBoundMethod

inductive CurvatureKind where
  | convex
  | concave
deriving DecidableEq, Repr

namespace CurvatureKind

def derivativeMonotonicity : CurvatureKind -> MonotonicityKind
  | .convex => .nondecreasing
  | .concave => .nonincreasing

end CurvatureKind

def secantSlopeIntervalOfRealFun
    (F : RealFunRaw) (x y : Rat) (prec : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y prec) (F.compute x prec) (y - x)

/-- Rational secant-slope formulation of convexity/concavity on a short cell.

This is a helper certificate for producing derivative bounds.  The FTC layer
above only consumes `DerivativeBoundOnSubinterval`; it does not depend on this
curvature data directly. -/
structure CurvatureOnSubinterval
    (F : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  kind : CurvatureKind
  evalPrecision : Nat -> Nat
  domain_on : forall x, C.contains x -> F.domain x
  secant_slope_order :
    forall n w x y z,
      C.contains w ->
      C.contains x ->
      C.contains y ->
      C.contains z ->
      w < x ->
      x <= y ->
      y < z ->
        match kind with
        | .convex =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
        | .concave =>
            QInterval.WeakLe
              (secantSlopeIntervalOfRealFun F y z (evalPrecision n))
              (secantSlopeIntervalOfRealFun F w x (evalPrecision n))

/-- Evidence that a derivative bound was obtained through a curvature
argument: convexity supplies nondecreasing derivative bounds, concavity supplies
nonincreasing derivative bounds.  The result fed to FTC is still just
`toDerivativeBound`. -/
structure DerivativeBoundFromCurvature
    (F dF : RealFunRaw) {a b : Rat} (C : RationalSubinterval a b) where
  curvature : CurvatureOnSubinterval F C
  monotoneDerivative : MonotoneDerivativeBoundMethod dF C
  compatible :
    monotoneDerivative.kind = curvature.kind.derivativeMonotonicity

namespace DerivativeBoundFromCurvature

def toDerivativeBound
    {F dF : RealFunRaw} {a b : Rat} {C : RationalSubinterval a b}
    (H : DerivativeBoundFromCurvature F dF C) :
    DerivativeBoundOnSubinterval dF C :=
  H.monotoneDerivative.toDerivativeBound

end DerivativeBoundFromCurvature

/-- Curvature-facing FTC certificate.

This is the finite certificate-shaped route for primitives whose derivative
bounds come from curvature on each rational partition cell.  It handles both
convex and concave cells: the curvature kind determines whether endpoint
derivative bounds are nondecreasing or nonincreasing, and the result fed to the
FTC layer is still just a derivative-bound certificate. -/
structure CurvatureFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  curvatureBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((curvatureBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((curvatureBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace CurvatureFTCCertificate

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  derivativeBound := fun eps k hk => (h.curvatureBound eps k hk).toDerivativeBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end CurvatureFTCCertificate

/-- Convexity-facing FTC certificate.

This is the current finite certificate-shaped route: convexity supplies
monotone derivative bounds on rational partition cells, and those local
bounds feed the general `DerivativeBoundFTC` endpoint bridge.

The later one-sided convex FTC should construct this certificate from exact
convexity, one-sided derivative data, monotone integrability, and telescoping
secant inequalities. -/
structure ConvexFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  convexBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  convex_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (convexBound eps k hk).curvature.kind = CurvatureKind.convex
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((convexBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((convexBound eps k hk).toDerivativeBound).bound (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

/-- Backward-compatible name for the older blueprint/API wording. -/
abbrev LegacyConvexFTC (F dF : RealFunRaw) (a b : Rat) :=
  ConvexFTCCertificate F dF a b

namespace ConvexFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.convexBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConvexFTCCertificate

/-- Concavity-facing FTC certificate.

This is the mirror of `ConvexFTCCertificate`.  It is the named finite
certificate route for primitives, such as arctangent on `[0,1]`, whose
curvature makes the derivative nonincreasing on each rational partition cell.
The certificate still feeds the same curvature and derivative-bound FTC
machinery. -/
structure ConcaveFTCCertificate (F dF : RealFunRaw) (a b : Rat) where
  primitive_domain_lower : F.domain a
  primitive_domain_upper : F.domain b
  choosePartition : QPos -> RationalPartition a b
  chooseEndpointPrecision : QPos -> Nat
  chooseBoundStage : QPos -> Nat
  concaveBound :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        DerivativeBoundFromCurvature F dF ((choosePartition eps).cell k hk)
  concave_kind :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        (concaveBound eps k hk).curvature.kind = CurvatureKind.concave
  localControl :
    forall eps,
      forall k (hk : k < (choosePartition eps).pieces),
        LocalFTCFromDerivativeBound F dF
          ((choosePartition eps).cell k hk)
          ((concaveBound eps k hk).toDerivativeBound)
  riemann_width :
    forall eps,
      ((choosePartition eps).boundIntegralSum
        (fun k hk =>
          ((concaveBound eps k hk).toDerivativeBound).bound
            (chooseBoundStage eps))).width <=
        eps.val
  endpoint_width :
    forall eps,
      (endpointDifferenceInterval F a b (chooseEndpointPrecision eps)).width <=
        eps.val
  overlap :
    forall eps,
      QInterval.Overlaps
        ((choosePartition eps).boundIntegralSum
          (fun k hk =>
            ((concaveBound eps k hk).toDerivativeBound).bound
              (chooseBoundStage eps)))
        (endpointDifferenceInterval F a b (chooseEndpointPrecision eps))

namespace ConcaveFTCCertificate

def toCurvatureFTCCertificate
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    CurvatureFTCCertificate F dF a b where
  primitive_domain_lower := h.primitive_domain_lower
  primitive_domain_upper := h.primitive_domain_upper
  choosePartition := h.choosePartition
  chooseEndpointPrecision := h.chooseEndpointPrecision
  chooseBoundStage := h.chooseBoundStage
  curvatureBound := h.concaveBound
  localControl := h.localControl
  riemann_width := h.riemann_width
  endpoint_width := h.endpoint_width
  overlap := h.overlap

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    DerivativeBoundFTC F dF a b :=
  h.toCurvatureFTCCertificate.toDerivativeBoundFTC

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.toDerivativeBoundFTC.equiv_endpoint

end ConcaveFTCCertificate

/- Legacy namespace aliases retained for existing references. -/
namespace LegacyConvexFTC

def toDerivativeBoundFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    DerivativeBoundFTC F dF a b :=
  ConvexFTCCertificate.toDerivativeBoundFTC h

theorem equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  ConvexFTCCertificate.equiv_endpoint h

end LegacyConvexFTC

/-- Compatibility theorem for the old convexity-facing FTC name.

Once a convexity certificate has produced derivative bounds on the chosen
rational partition cells, the finite FTC conclusion is exactly the
derivative-bound endpoint equivalence. -/
theorem legacyConvexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : LegacyConvexFTC F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed convexity-facing FTC bridge used by the integral chapter.

This is currently the derivative-bound formulation: convexity supplies the
local monotone derivative bounds, and the general derivative-bound FTC returns
endpoint equivalence for the integral raw real. -/
theorem convexFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConvexFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Completed concavity-facing FTC bridge used by the arctangent-integral
route. -/
theorem concaveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : ConcaveFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- Curvature-facing FTC bridge.  This is the version useful for both convex
and concave primitives, including the arctangent primitive on the unit
interval. -/
theorem curvatureFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : CurvatureFTCCertificate F dF a b) :
    h.toDerivativeBoundFTC.boundedIntegralRaw.Equiv
      h.toDerivativeBoundFTC.endpointRaw :=
  h.equiv_endpoint

/-- A partial function together with a proof that it is defined at every
rational point of a closed rational interval.

This rules out visible rational-domain failures, such as `1/x` on an interval
containing `0`.  It does not by itself rule out a hidden irrational singularity
such as `1 / (x^2 - 2)` on `[1,2]`, because every rational point of `[1,2]`
is still in the pointwise domain.  That stronger exclusion is the job of
`IntervalRegularOn` below. -/
structure FunctionOnInterval where
  raw : PartialRealFunRaw
  lower : Rat
  upper : Rat
  defined_on : forall x, inDomainInterval lower upper x -> raw.definedAt x
  valid_on : forall x h, RealRaw.ValidCompute (raw.compute x h)

namespace FunctionOnInterval

def compute (F : FunctionOnInterval) (x : Rat) (hx : inDomainInterval F.lower F.upper x)
    (n : Nat) : QInterval :=
  F.raw.compute x (F.defined_on x hx) n

/-- A rational-valued formula, viewed as an exact interval function on a
closed rational interval.

This is the standard wrapper for compactified rational densities.  It only
certifies the pointwise evaluator: continuity and integral constructions
remain separate finite obligations. -/
def exactRat (f : Rat -> Rat) (a b : Rat) : FunctionOnInterval where
  raw :=
    { definedAt := fun _ => True
      compute := fun x _ _ => { lo := f x, hi := f x } }
  lower := a
  upper := b
  defined_on := fun _ _ => trivial
  valid_on := by
    intro x _hx
    simpa using RealRaw.ofRat_valid (f x)

theorem exactRat_compute (f : Rat -> Rat) (a b x : Rat)
    (hx : inDomainInterval a b x) (n : Nat) :
    (exactRat f a b).compute x hx n = { lo := f x, hi := f x } :=
  rfl

def secantSlopeInterval (F : FunctionOnInterval)
    (x y : Rat)
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y)
    (n : Nat) : QInterval :=
  QInterval.slopeBetween (F.compute y hy n) (F.compute x hx n) (y - x)

/-- Restrict an interval-certified function to a smaller rational interval. -/
def restrict (F : FunctionOnInterval) (a b : Rat)
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    FunctionOnInterval where
  raw := F.raw
  lower := a
  upper := b
  defined_on := by
    intro x hx
    exact F.defined_on x
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
  valid_on := by
    intro x hx
    exact F.valid_on x hx

/-- Pointwise sum relation for interval-certified functions on the same
rational interval.  This is a theorem-facing relation: it records that `H`
represents `F + G` on the common interval, without choosing a particular
implementation of the sum evaluator. -/
def PointwiseAdd (F G H : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  F.lower = H.lower /\ F.upper = H.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x)
    (hxH : inDomainInterval H.lower H.upper x),
      (H.raw.evalRaw x (H.defined_on x hxH)).Equiv
        ((F.raw.evalRaw x (F.defined_on x hxF)) +
          (G.raw.evalRaw x (G.defined_on x hxG)))

/-- Pointwise rational-scalar relation for interval-certified functions. -/
def PointwiseScaleRat (r : Rat) (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (G.raw.evalRaw x (G.defined_on x hxG)).Equiv
        (RealRaw.scaleRat r
          (F.raw.evalRaw x (F.defined_on x hxF)))

/-- Pointwise order relation for interval-certified functions on the same
rational interval.  This is the order analogue of `PointwiseAdd`: it records
the theorem-facing fact that `F(x) <= G(x)` for every rational point in the
common interval. -/
def PointwiseLe (F G : FunctionOnInterval) : Prop :=
  F.lower = G.lower /\ F.upper = G.upper /\
  forall x
    (hxF : inDomainInterval F.lower F.upper x)
    (hxG : inDomainInterval G.lower G.upper x),
      (F.raw.evalRaw x (F.defined_on x hxF)).Le
        (G.raw.evalRaw x (G.defined_on x hxG))

end FunctionOnInterval

namespace Integral

/-- Project-facing integral construction for a partial function on a whole
rational interval.

The detailed Riemann-sum construction still needs to be proved.  This shape is
only the first domain gate: `FunctionOnInterval` supplies pointwise rational
evaluation, while the intended integral-existence theorem should consume
`IntervalRegularOn` to exclude hidden singularities inside rational
subintervals. -/
structure ConstructionFor (F : FunctionOnInterval) where
  compute : Nat -> QInterval
  certificate : RealRaw.ValidCompute compute

def integralFor (F : FunctionOnInterval) (c : ConstructionFor F) : RealRaw where
  compute := c.compute

theorem integralFor_compute_eq (F : FunctionOnInterval)
    (c : ConstructionFor F) (n : Nat) :
    (integralFor F c).compute n = c.compute n := rfl

theorem integralFor_valid (F : FunctionOnInterval)
    (c : ConstructionFor F) :
    (integralFor F c).Valid :=
  c.certificate

end Integral

def Integral.ExistsConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (Integral.ConstructionFor F)

theorem integral_construction_proves_well_defined_for
    {F : FunctionOnInterval}
    (c : Integral.ConstructionFor F) :
    Integral.ExistsConstructionFor F :=
  ⟨c⟩

/-- Epsilon-delta continuity stated entirely over rational inputs.

For a requested positive rational output tolerance `eps`, the certificate
chooses a positive rational input tolerance and one evaluation precision. Any
two rational points of the stated interval within that tolerance then have
output boxes within `eps` of one another, each of width at most `eps`.  This
is quantitative proximity, not literal overlap: a nonconstant function can
send nearby rational inputs to distinct exact rational values.  No topology,
completed real-valued function space, or implicit exact-value evaluation
occurs here.
`EffectiveModulusFor` below is the stronger computable-modulus presentation
used by the current calculus constructors. -/
def EpsilonDeltaContinuousOn (F : FunctionOnInterval) : Prop :=
  forall eps : QPos, Exists fun delta : QPos => Exists fun evalPrecision : Nat =>
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= delta.val ->
        QInterval.NearAt
          (F.compute x hx evalPrecision)
          (F.compute y hy evalPrecision) eps

/-- Effective modulus for a partial function known to be defined on the whole
interval.  This is the continuity data used by IVT and eventually by the
integral constructor; it includes the domain certificate. -/
structure EffectiveModulusFor (F : FunctionOnInterval) where
  inputPrecision : Nat -> Nat
  evalPrecision : Nat -> Nat
  close :
    forall x y n
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y),
      qabs (y - x) <= (1 / ((inputPrecision n) : Rat)) ->
        intervalNearAtPrecision
          (F.compute x hx (evalPrecision n))
          (F.compute y hy (evalPrecision n))
          n

/-- Generic interval-level regularity.

This is the continuity notion we want calculus theorems to consume.  It does
not mention denominators or formulas.  It says that every sufficiently small
rational subinterval has a computable output interval, and that the output
interval can be made as narrow as requested.  A hidden singularity such as
`1 / (x^2 - 2)` on `[1,2]` should fail this condition, because arbitrarily
small rational subintervals can straddle the irrational pole. -/
structure IntervalRegularOn (F : FunctionOnInterval) where
  evalInterval : (I : QInterval) -> subintervalOf I F.lower F.upper -> Nat -> QInterval
  inputPrecision : Nat -> Nat
  inputPrecision_pos : forall n, 0 < inputPrecision n
  output_width :
    forall I hI n,
      I.width <= (1 / ((inputPrecision n) : Rat)) ->
        0 <= (evalInterval I hI n).width /\
        (evalInterval I hI n).width <= 1 / ((n + 1 : Nat) : Rat)
  contains_point_values :
    forall I hI x hx n,
      I.lo <= x ->
      x <= I.hi ->
      QInterval.ContainsInterval
        (evalInterval I hI n)
        (F.compute x hx n)

/-- An interval-regular evaluator supplies literal rational
epsilon-delta continuity.  The output target at stage `n` is `1/(n+1)`, so
stage zero is meaningful for non-exact interval algorithms.  The proof uses
the finite denominator-derived stage `eps.den`, encloses both point evaluations
in one narrow image interval, and never invokes topology or a completed real
line. -/
theorem IntervalRegularOn.epsilonDeltaContinuous
    {F : FunctionOnInterval} (h : IntervalRegularOn F) :
    EpsilonDeltaContinuousOn F := by
  intro eps
  let n : Nat := eps.val.den
  let delta : QPos :=
    { val := 1 / ((h.inputPrecision n : Nat) : Rat)
      property := one_div_nat_pos (h.inputPrecision_pos n) }
  refine ⟨delta, n, ?_⟩
  intro x y hx hy hxy
  let I : QInterval := { lo := min x y, hi := max x y }
  have hI : subintervalOf I F.lower F.upper := by
    rcases hx with ⟨hxlo, hxhi⟩
    rcases hy with ⟨hylo, hyhi⟩
    dsimp [I]
    constructor
    · grind
    constructor <;> grind
  have hIwidth : I.width = qabs (y - x) := by
    dsimp [I]
    exact QInterval.endpointHull_width x y
  have hsmall : I.width <= 1 / ((h.inputPrecision n : Nat) : Rat) := by
    rw [hIwidth]
    simpa [delta] using hxy
  have houtput := h.output_width I hI n hsmall
  have htarget : 1 / (((n + 1 : Nat) : Rat)) <= eps.val := by
    dsimp [n]
    exact one_div_den_succ_le_of_pos eps.property
  have hYwidth : (h.evalInterval I hI n).width <= eps.val :=
    Rat.le_trans houtput.2 htarget
  have hxlo : I.lo <= x := by
    dsimp [I]
    grind
  have hxhi : x <= I.hi := by
    dsimp [I]
    grind
  have hylo : I.lo <= y := by
    dsimp [I]
    grind
  have hyhi : y <= I.hi := by
    dsimp [I]
    grind
  have hcontainsX := h.contains_point_values I hI x hx n hxlo hxhi
  have hcontainsY := h.contains_point_values I hI y hy n hylo hyhi
  have hXwidth_nonneg := (F.valid_on x (F.defined_on x hx)).1 n
  have hYwidth_nonneg := (F.valid_on y (F.defined_on y hy)).1 n
  have hXordered : (F.compute x hx n).lo <= (F.compute x hx n).hi := by
    change 0 <= (F.compute x hx n).hi - (F.compute x hx n).lo at hXwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hYordered : (F.compute y hy n).lo <= (F.compute y hy n).hi := by
    change 0 <= (F.compute y hy n).hi - (F.compute y hy n).lo at hYwidth_nonneg
    grind [Rat.sub_eq_add_neg]
  have hwidthX : (F.compute x hx n).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsX) hYwidth
  have hwidthY : (F.compute y hy n).width <= eps.val :=
    Rat.le_trans (QInterval.width_le_of_contains hcontainsY) hYwidth
  unfold QInterval.NearAt
  constructor
  · change (F.compute x hx n).lo <= (F.compute y hy n).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  constructor
  · change (F.compute y hy n).lo <= (F.compute x hx n).hi + eps.val
    unfold QInterval.ContainsInterval at hcontainsX hcontainsY
    unfold QInterval.width at hYwidth
    grind [Rat.sub_eq_add_neg]
  exact ⟨hwidthX, hwidthY⟩

/-- A certified continuous function on a rational interval.

This is the theorem-facing package.  `FunctionOnInterval` says the evaluator is
available at rational points on the interval; `regular` is the interval-level
continuity data that lets us choose subdivisions and evaluation precision. -/
structure ContinuousFunctionOnInterval where
  function : FunctionOnInterval
  regular : IntervalRegularOn function

/-- Constructive monotonicity on rational points of the interval.

The field `increasing` means nondecreasing; its negation selects the
nonincreasing case.  This is order data, not yet enough to build an inverse
algorithm by itself. -/
structure MonotoneOnInterval (F : FunctionOnInterval) where
  increasing : Prop
  monotone_inc :
    increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute x hx n).lo <= (F.compute y hy n).hi
  monotone_dec :
    ¬ increasing ->
      forall x y
        (hx : inDomainInterval F.lower F.upper x)
        (hy : inDomainInterval F.lower F.upper y),
        x <= y ->
          forall n,
            (F.compute y hy n).lo <= (F.compute x hx n).hi

/-- Nondecreasing means increasing in the weak order sense used by the
project: rational inputs with `x <= y` have compatible output intervals with
the value at `x` no larger than the value at `y`. -/
def NondecreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute x hx n).lo <= (F.compute y hy n).hi

/-- Nonincreasing is the reversed weak interval order. -/
def NonincreasingOnInterval (F : FunctionOnInterval) : Prop :=
  forall x y
    (hx : inDomainInterval F.lower F.upper x)
    (hy : inDomainInterval F.lower F.upper y),
    x <= y ->
      forall n,
        (F.compute y hy n).lo <= (F.compute x hx n).hi

namespace MonotoneOnInterval

def ofNondecreasing {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := True
  monotone_inc := by
    intro _hinc
    exact h
  monotone_dec := by
    intro hfalse
    exact False.elim (hfalse trivial)

def ofNonincreasing {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F) :
    MonotoneOnInterval F where
  increasing := False
  monotone_inc := by
    intro hfalse
    cases hfalse
  monotone_dec := by
    intro _hdec
    exact h

theorem nondecreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hinc : h.increasing) :
    NondecreasingOnInterval F :=
  h.monotone_inc hinc

theorem nonincreasing {F : FunctionOnInterval}
    (h : MonotoneOnInterval F) (hdec : ¬ h.increasing) :
    NonincreasingOnInterval F :=
  h.monotone_dec hdec

def restrict {F : FunctionOnInterval}
    (h : MonotoneOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneOnInterval (F.restrict a b hlo hab hhi) where
  increasing := h.increasing
  monotone_inc := by
    intro hinc x y hx hy hxy n
    exact h.monotone_inc hinc x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n
  monotone_dec := by
    intro hdec x y hx hy hxy n
    exact h.monotone_dec hdec x y
      ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
      ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
      hxy n

end MonotoneOnInterval

namespace NondecreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NondecreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NondecreasingOnInterval

namespace NonincreasingOnInterval

theorem restrict {F : FunctionOnInterval}
    (h : NonincreasingOnInterval F)
    {a b : Rat}
    (hlo : F.lower <= a) (_hab : a <= b) (hhi : b <= F.upper) :
    NonincreasingOnInterval (F.restrict a b hlo _hab hhi) := by
  intro x y hx hy hxy n
  exact h x y
    ⟨Rat.le_trans hlo hx.1, Rat.le_trans hx.2 hhi⟩
    ⟨Rat.le_trans hlo hy.1, Rat.le_trans hy.2 hhi⟩
    hxy n

end NonincreasingOnInterval

namespace Integral

/-- The first-class integral object for monotone interval functions.

The intended construction is by lower and upper endpoint sums on a static
dyadic mesh, with width controlled by total variation times mesh size.  The
present structure separates that monotonicity certificate from the resulting
valid `ConstructionFor`, so later proofs can build the construction while
downstream calculus can already use the interface. -/
structure MonotoneConstructionFor (F : FunctionOnInterval) where
  monotone : MonotoneOnInterval F
  construction : ConstructionFor F

namespace MonotoneConstructionFor

def restrict {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    MonotoneConstructionFor (F.restrict a b hlo hab hhi) where
  monotone := c.monotone.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end MonotoneConstructionFor

/-- The preferred first case for integrals: a certified nondecreasing
function together with its valid integral construction. -/
structure NondecreasingConstructionFor (F : FunctionOnInterval) where
  nondecreasing : NondecreasingOnInterval F
  construction : ConstructionFor F

namespace NondecreasingConstructionFor

def toMonotoneConstructionFor {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F) :
    MonotoneConstructionFor F where
  monotone := MonotoneOnInterval.ofNondecreasing c.nondecreasing
  construction := c.construction

def restrict {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    {a b : Rat}
    (hlo : F.lower <= a) (hab : a <= b) (hhi : b <= F.upper) :
    NondecreasingConstructionFor (F.restrict a b hlo hab hhi) where
  nondecreasing := c.nondecreasing.restrict hlo hab hhi
  construction :=
    { compute := c.construction.compute
      certificate := c.construction.certificate }

end NondecreasingConstructionFor

def monotoneIntegralFor (F : FunctionOnInterval)
    (c : MonotoneConstructionFor F) : RealRaw :=
  integralFor F c.construction

theorem monotoneIntegralFor_valid (F : FunctionOnInterval)
    (c : MonotoneConstructionFor F) :
    (monotoneIntegralFor F c).Valid :=
  integralFor_valid F c.construction

def ExistsMonotoneConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (MonotoneConstructionFor F)

def nondecreasingIntegralFor (F : FunctionOnInterval)
    (c : NondecreasingConstructionFor F) : RealRaw :=
  integralFor F c.construction

theorem nondecreasingIntegralFor_valid (F : FunctionOnInterval)
    (c : NondecreasingConstructionFor F) :
    (nondecreasingIntegralFor F c).Valid :=
  integralFor_valid F c.construction

theorem nondecreasingIntegralFor_eq_monotoneIntegralFor
    (F : FunctionOnInterval) (c : NondecreasingConstructionFor F) :
    nondecreasingIntegralFor F c =
      monotoneIntegralFor F c.toMonotoneConstructionFor := rfl

def ExistsNondecreasingConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (NondecreasingConstructionFor F)

/-- A piecewise-monotone integral plan: split an interval into finitely many
rational subintervals and supply a monotone construction on each piece. -/
structure PiecewiseMonotoneConstructionFor (F : FunctionOnInterval) where
  pieces : Nat
  positive : 0 < pieces
  point : Nat -> Rat
  left_endpoint : point 0 = F.lower
  right_endpoint : point pieces = F.upper
  point_mem :
    forall i, i <= pieces -> inDomainInterval F.lower F.upper (point i)
  point_mono :
    forall i j, i <= j -> j <= pieces -> point i <= point j
  construction :
    forall k (hk : k < pieces),
      MonotoneConstructionFor
        (F.restrict (point k) (point (k + 1))
          (point_mem k (Nat.le_of_lt hk)).1
          (point_mono k (k + 1) (Nat.le_succ k) (Nat.succ_le_of_lt hk))
          (point_mem (k + 1) (Nat.succ_le_of_lt hk)).2)

namespace PiecewiseMonotoneConstructionFor

/-- Promote one monotone integral construction to the general piecewise
interface by using the one-cell partition `[lower, upper]`. -/
noncomputable def ofMonotone {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneConstructionFor F where
  pieces := 1
  positive := by decide
  point
    | 0 => F.lower
    | _ + 1 => F.upper
  left_endpoint := rfl
  right_endpoint := rfl
  point_mem := by
    intro i _hi
    cases i with
    | zero =>
        exact ⟨Rat.le_refl, hinterval⟩
    | succ _ =>
        exact ⟨hinterval, Rat.le_refl⟩
  point_mono := by
    intro i j hij _hj
    cases i with
    | zero =>
        cases j with
        | zero =>
            exact Rat.le_refl
        | succ _ =>
            exact hinterval
    | succ i' =>
        cases j with
        | zero =>
            exact False.elim (Nat.not_succ_le_zero i' hij)
        | succ _ =>
            exact Rat.le_refl
  construction := by
    intro k hk
    have hk_le_zero : k <= 0 := Nat.le_of_lt_succ hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk_le_zero
    subst k
    simpa using
      c.restrict
        Rat.le_refl
        hinterval
        Rat.le_refl

/-- Promote the preferred nondecreasing integral construction to the general
piecewise interface. -/
noncomputable def ofNondecreasing {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    PiecewiseMonotoneConstructionFor F :=
  ofMonotone c.toMonotoneConstructionFor hinterval

end PiecewiseMonotoneConstructionFor

/-- The integral raw real for a single monotone piece of a piecewise-monotone
construction. -/
def piecewiseMonotoneCellIntegral (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (k : Nat) (hk : k < c.pieces) : RealRaw :=
  monotoneIntegralFor _ (c.construction k hk)

theorem piecewiseMonotoneCellIntegral_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F)
    (k : Nat) (hk : k < c.pieces) :
    (piecewiseMonotoneCellIntegral F c k hk).Valid :=
  monotoneIntegralFor_valid _ (c.construction k hk)

/-- Sum the monotone-piece integrals over the finite rational partition. -/
def piecewiseMonotoneIntegralFor (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F) : RealRaw :=
  (List.range c.pieces).foldl
    (fun acc k =>
      if hk : k < c.pieces then
        acc + piecewiseMonotoneCellIntegral F c k hk
      else
        acc)
    (RealRaw.ofRat 0)

theorem piecewiseMonotoneIntegralFor_valid (F : FunctionOnInterval)
    (c : PiecewiseMonotoneConstructionFor F) :
    (piecewiseMonotoneIntegralFor F c).Valid := by
  let step : RealRaw -> Nat -> RealRaw :=
    fun acc k =>
      if hk : k < c.pieces then
        acc + piecewiseMonotoneCellIntegral F c k hk
      else
        acc
  have hstep : forall acc k, acc.Valid -> (step acc k).Valid := by
    intro acc k hacc
    by_cases hk : k < c.pieces
    · simp [step, hk]
      exact RealRaw.add_valid hacc
        (piecewiseMonotoneCellIntegral_valid F c k hk)
    · simp [step, hk, hacc]
  have hfold :
      forall (xs : List Nat) (acc : RealRaw),
        acc.Valid -> (xs.foldl step acc).Valid := by
    intro xs
    induction xs with
    | nil =>
        intro acc hacc
        simpa using hacc
    | cons k ks ih =>
        intro acc hacc
        simpa [List.foldl] using ih (step acc k) (hstep acc k hacc)
  simpa [piecewiseMonotoneIntegralFor, step] using
    hfold (List.range c.pieces) (RealRaw.ofRat 0) (by
    simpa [RealRaw.Valid, RealRaw.ofRat] using RealRaw.ofRat_valid 0)

/-- A one-piece promotion from a monotone construction computes the same raw
integral as the original monotone construction. -/
theorem piecewiseMonotoneIntegralFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneIntegralFor F c) := by
  simpa [piecewiseMonotoneIntegralFor, piecewiseMonotoneCellIntegral,
    PiecewiseMonotoneConstructionFor.ofMonotone,
    MonotoneConstructionFor.restrict, monotoneIntegralFor, integralFor,
    RealRaw.zero] using
    (RealRaw.zero_add_equiv
      (monotoneIntegralFor_valid F c))

/-- The preferred nondecreasing one-piece promotion is compatible with the
general piecewise-monotone integral. -/
theorem piecewiseMonotoneIntegralFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (piecewiseMonotoneIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingIntegralFor F c) := by
  simpa [PiecewiseMonotoneConstructionFor.ofNondecreasing,
    NondecreasingConstructionFor.toMonotoneConstructionFor,
    nondecreasingIntegralFor, monotoneIntegralFor] using
    (piecewiseMonotoneIntegralFor_ofMonotone_equiv
      (F := F) c.toMonotoneConstructionFor hinterval)

def ExistsPiecewiseMonotoneConstructionFor (F : FunctionOnInterval) : Prop :=
  Nonempty (PiecewiseMonotoneConstructionFor F)

/-- Project-facing name for the general definite integral interface:
construct the integral on monotone pieces and sum over a finite rational
partition. -/
abbrev GeneralConstructionFor (F : FunctionOnInterval) :=
  PiecewiseMonotoneConstructionFor F

def generalIntegralFor (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) : RealRaw :=
  piecewiseMonotoneIntegralFor F c

theorem generalIntegralFor_valid (F : FunctionOnInterval)
    (c : GeneralConstructionFor F) :
    (generalIntegralFor F c).Valid :=
  piecewiseMonotoneIntegralFor_valid F c

/-- The public general-integral alias agrees with the original monotone
construction on a one-piece partition. -/
theorem generalIntegralFor_ofMonotone_equiv
    {F : FunctionOnInterval}
    (c : MonotoneConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofMonotone c hinterval)).Equiv
        (monotoneIntegralFor F c) := by
  simpa [generalIntegralFor] using
    piecewiseMonotoneIntegralFor_ofMonotone_equiv
      (F := F) c hinterval

/-- The public general-integral alias agrees with the preferred
nondecreasing construction on a one-piece partition. -/
theorem generalIntegralFor_ofNondecreasing_equiv
    {F : FunctionOnInterval}
    (c : NondecreasingConstructionFor F)
    (hinterval : F.lower <= F.upper) :
    (generalIntegralFor F
      (PiecewiseMonotoneConstructionFor.ofNondecreasing c hinterval)).Equiv
        (nondecreasingIntegralFor F c) := by
  simpa [generalIntegralFor] using
    piecewiseMonotoneIntegralFor_ofNondecreasing_equiv
      (F := F) c hinterval

abbrev ExistsGeneralConstructionFor (F : FunctionOnInterval) : Prop :=
  ExistsPiecewiseMonotoneConstructionFor F

/-- Domain-aware linearity target for the eventual integral operator. -/
def LinearFor : Prop :=
  forall (F G H : FunctionOnInterval)
    (_hadd : F.PointwiseAdd G H)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G)
    (cH : ConstructionFor H)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute (integralFor F cF) (integralFor G cG))),
      (integralFor H cH).Equiv
        { compute := RealRaw.addCompute (integralFor F cF) (integralFor G cG) }

/-- Domain-aware rational scalar compatibility target. -/
def CompatibleWithScaleRatFor : Prop :=
  forall (r : Rat) (F G : FunctionOnInterval)
    (_hscaleFun : F.PointwiseScaleRat r G)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (integralFor F cF))),
      (integralFor G cG).Equiv
        { compute := RealRaw.scaleRatCompute r (integralFor F cF) }

/-- Domain-aware adjacent-interval additivity target. -/
def AdditiveOnAdjacentIntervalsFor : Prop :=
  forall (F : FunctionOnInterval) (a b c : Rat)
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c) (hc : c <= F.upper)
    (cab : ConstructionFor
      (F.restrict a b ha hab (Rat.le_trans hbc hc)))
    (cbc : ConstructionFor
      (F.restrict b c (Rat.le_trans ha hab) hbc hc))
    (cac : ConstructionFor
      (F.restrict a c ha (Rat.le_trans hab hbc) hc))
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (integralFor (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
        (integralFor (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc))),
      (integralFor (F.restrict a c ha (Rat.le_trans hab hbc) hc) cac).Equiv
        { compute := RealRaw.addCompute
            (integralFor (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
            (integralFor (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc) }

/-- Domain-aware order-preservation target for the eventual integral operator:
pointwise order of integrands should imply order of their integrals. -/
def OrderPreservingFor : Prop :=
  forall (F G : FunctionOnInterval)
    (_hle : F.PointwiseLe G)
    (cF : ConstructionFor F)
    (cG : ConstructionFor G),
      (integralFor F cF).Le (integralFor G cG)

/-- Bundle of the basic algebra laws expected of the domain-aware integral.

The individual fields stay proposition-shaped because `ConstructionFor` is an
arbitrary valid raw algorithm.  Concrete integral constructors, such as the
monotone and piecewise-monotone constructors, should provide this package once
their finite-sum comparison proofs are available. -/
structure BasicPropertiesFor where
  linear : LinearFor
  scaleRat : CompatibleWithScaleRatFor
  adjacent_additive : AdditiveOnAdjacentIntervalsFor
  order_preserving : OrderPreservingFor

/-- Linearity target for the piecewise-monotone integral operator. -/
def PiecewiseMonotoneLinearFor : Prop :=
  forall (F G H : FunctionOnInterval)
    (_hadd : F.PointwiseAdd G H)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G)
    (cH : PiecewiseMonotoneConstructionFor H)
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (piecewiseMonotoneIntegralFor F cF)
        (piecewiseMonotoneIntegralFor G cG))),
      (piecewiseMonotoneIntegralFor H cH).Equiv
        { compute := RealRaw.addCompute
            (piecewiseMonotoneIntegralFor F cF)
            (piecewiseMonotoneIntegralFor G cG) }

/-- Rational scalar compatibility target for the piecewise-monotone integral
operator. -/
def PiecewiseMonotoneCompatibleWithScaleRatFor : Prop :=
  forall (r : Rat) (F G : FunctionOnInterval)
    (_hscaleFun : F.PointwiseScaleRat r G)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G)
    (_hscale : RealRaw.ValidCompute
      (RealRaw.scaleRatCompute r (piecewiseMonotoneIntegralFor F cF))),
      (piecewiseMonotoneIntegralFor G cG).Equiv
        { compute := RealRaw.scaleRatCompute r
            (piecewiseMonotoneIntegralFor F cF) }

/-- Adjacent-interval additivity target for the piecewise-monotone integral
operator. -/
def PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor : Prop :=
  forall (F : FunctionOnInterval) (a b c : Rat)
    (ha : F.lower <= a) (hab : a <= b) (hbc : b <= c) (hc : c <= F.upper)
    (cab : PiecewiseMonotoneConstructionFor
      (F.restrict a b ha hab (Rat.le_trans hbc hc)))
    (cbc : PiecewiseMonotoneConstructionFor
      (F.restrict b c (Rat.le_trans ha hab) hbc hc))
    (cac : PiecewiseMonotoneConstructionFor
      (F.restrict a c ha (Rat.le_trans hab hbc) hc))
    (_hsum : RealRaw.ValidCompute
      (RealRaw.addCompute
        (piecewiseMonotoneIntegralFor
          (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
        (piecewiseMonotoneIntegralFor
          (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc))),
      (piecewiseMonotoneIntegralFor
        (F.restrict a c ha (Rat.le_trans hab hbc) hc) cac).Equiv
        { compute := RealRaw.addCompute
            (piecewiseMonotoneIntegralFor
              (F.restrict a b ha hab (Rat.le_trans hbc hc)) cab)
            (piecewiseMonotoneIntegralFor
              (F.restrict b c (Rat.le_trans ha hab) hbc hc) cbc) }

/-- Order-preservation target for the piecewise-monotone integral operator. -/
def PiecewiseMonotoneOrderPreservingFor : Prop :=
  forall (F G : FunctionOnInterval)
    (_hle : F.PointwiseLe G)
    (cF : PiecewiseMonotoneConstructionFor F)
    (cG : PiecewiseMonotoneConstructionFor G),
      (piecewiseMonotoneIntegralFor F cF).Le
        (piecewiseMonotoneIntegralFor G cG)

/-- Bundle of the basic algebra laws for the intended general integral:
define on monotone pieces, then sum over a finite rational partition. -/
structure PiecewiseMonotoneBasicPropertiesFor where
  linear : PiecewiseMonotoneLinearFor
  scaleRat : PiecewiseMonotoneCompatibleWithScaleRatFor
  adjacent_additive : PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor
  order_preserving : PiecewiseMonotoneOrderPreservingFor

abbrev GeneralLinearFor : Prop :=
  PiecewiseMonotoneLinearFor

abbrev GeneralCompatibleWithScaleRatFor : Prop :=
  PiecewiseMonotoneCompatibleWithScaleRatFor

abbrev GeneralAdditiveOnAdjacentIntervalsFor : Prop :=
  PiecewiseMonotoneAdditiveOnAdjacentIntervalsFor

abbrev GeneralOrderPreservingFor : Prop :=
  PiecewiseMonotoneOrderPreservingFor

abbrev GeneralBasicPropertiesFor :=
  PiecewiseMonotoneBasicPropertiesFor

/-- Exact rational-cell order preservation for an integrand together with a
closed-form integral over rational cells.

This is the finite algebraic version of the order-preservation theorem for
integrals.  If `c` is a lower bound for `eval` on every rational point of
`[p,r]`, then `(r-p)*c` is a lower bound for the exact cell integral.  The
upper statement is analogous. -/
structure ExactCellOrderPreservation
    (eval : Rat -> Rat) (integralBetween : Rat -> Rat -> Rat)
    (a b : Rat) where
  lower_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> c <= eval x) ->
        (r - p) * c <= integralBetween p r
  upper_const :
    forall {p r c : Rat}, a <= p -> p <= r -> r <= b ->
      (forall {x : Rat}, p <= x -> x <= r -> eval x <= c) ->
        integralBetween p r <= (r - p) * c

/-- Exact rational-cell order preservation for a constant integrand.

This is the base case for finite polynomial integral certificates: the exact
integral of the constant `k` over `[p,r]` is `(r-p) * k`.  It uses only the
order of rational multiplication, with no limiting or completeness argument.
-/
theorem exactCellOrderPreservation_constant (a b k : Rat) :
    ExactCellOrderPreservation (fun _ => k) (fun p r => (r - p) * k) a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hck : c <= k :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hck hlen
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hkc : k <= c :=
      hbound (Rat.le_refl : p <= p) hpr
    exact Rat.mul_le_mul_of_nonneg_left hkc hlen

/-- Sum of the weights in a finite rational quadrature rule.  A pair stores a
relative node followed by its weight. -/
def quadratureWeightSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (_, weight) :: rest => weight + quadratureWeightSum rest

/-- Weighted evaluation sum for a finite rational quadrature rule on `[p,r]`.
The first component of each pair is its relative node in `[0,1]`. -/
def quadratureEvalSum (eval : Rat -> Rat) (p r : Rat) :
    List (Rat × Rat) -> Rat
  | [] => 0
  | (node, weight) :: rest =>
      weight * eval (p + node * (r - p)) +
        quadratureEvalSum eval p r rest

private theorem quadratureWeightSum_mul_le_quadratureEvalSum
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> c <= eval x) :
    quadratureWeightSum nodes * c <= quadratureEvalSum eval p r nodes := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : c <= eval (p + node * (r - p)) :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * c <= weight * eval (p + node * (r - p)) :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        (weight + quadratureWeightSum rest) * c =
            weight * c + quadratureWeightSum rest * c := by
          grind [Rat.add_mul]
        _ <= weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest := by
          calc
            weight * c + quadratureWeightSum rest * c <=
                weight * eval (p + node * (r - p)) +
                  quadratureWeightSum rest * c :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_left).2 htail

private theorem quadratureEvalSum_le_quadratureWeightSum_mul
    {eval : Rat -> Rat} {p r c : Rat}
    (nodes : List (Rat × Rat))
    (hpr : p <= r)
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hbound : forall {x : Rat}, p <= x -> x <= r -> eval x <= c) :
    quadratureEvalSum eval p r nodes <= quadratureWeightSum nodes * c := by
  induction nodes with
  | nil =>
      simp [quadratureWeightSum, quadratureEvalSum]
  | cons pair rest ih =>
      rcases pair with ⟨node, weight⟩
      have hnode := hnodes (node, weight) (by simp)
      have hweight : 0 <= weight := hweights (node, weight) (by simp)
      have hlength : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have hnodePointLower : p <= p + node * (r - p) := by
        have hmul : 0 <= node * (r - p) := Rat.mul_nonneg hnode.1 hlength
        grind
      have hnodePointUpper : p + node * (r - p) <= r := by
        have hmul : node * (r - p) <= 1 * (r - p) :=
          Rat.mul_le_mul_of_nonneg_right hnode.2 hlength
        calc
          p + node * (r - p) <= p + 1 * (r - p) :=
            (Rat.add_le_add_left).2 hmul
          _ = r := by grind [Rat.sub_eq_add_neg]
      have hpoint : eval (p + node * (r - p)) <= c :=
        hbound hnodePointLower hnodePointUpper
      have hhead : weight * eval (p + node * (r - p)) <= weight * c :=
        Rat.mul_le_mul_of_nonneg_left hpoint hweight
      have htail := ih
        (fun other hmem => hnodes other (by simp [hmem]))
        (fun other hmem => hweights other (by simp [hmem]))
      simp [quadratureWeightSum, quadratureEvalSum]
      calc
        weight * eval (p + node * (r - p)) +
            quadratureEvalSum eval p r rest <=
            weight * c + quadratureWeightSum rest * c := by
          calc
            weight * eval (p + node * (r - p)) +
                quadratureEvalSum eval p r rest <=
                weight * c + quadratureEvalSum eval p r rest :=
              (Rat.add_le_add_right).2 hhead
            _ <= weight * c + quadratureWeightSum rest * c :=
              (Rat.add_le_add_left).2 htail
        _ = (weight + quadratureWeightSum rest) * c := by
          grind [Rat.add_mul]

/-- A finite positive rational quadrature identity gives exact cell-order
preservation.  It applies to any finite rule whose nodes lie in `[0,1]`, whose
weights are nonnegative and sum to one, and whose formula is exact for the
specified integrand. -/
theorem exactCellOrderPreservation_of_positive_quadrature
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat) (nodes : List (Rat × Rat))
    (hnodes : forall node, node ∈ nodes -> 0 <= node.1 /\ node.1 <= 1)
    (hweights : forall node, node ∈ nodes -> 0 <= node.2)
    (hsum : quadratureWeightSum nodes = 1)
    (hformula : forall p r : Rat,
      integralBetween p r = (r - p) * quadratureEvalSum eval p r nodes) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureWeightSum_mul_le_quadratureEvalSum
      nodes hpr hnodes hweights hbound
    have haverage : c <= quadratureEvalSum eval p r nodes := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    have hsumBound := quadratureEvalSum_le_quadratureWeightSum_mul
      nodes hpr hnodes hweights hbound
    have haverage : quadratureEvalSum eval p r nodes <= c := by
      simpa [hsum] using hsumBound
    have hlength : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    rw [hformula]
    exact Rat.mul_le_mul_of_nonneg_left haverage hlength

/-- A positive Boole quadrature identity gives exact cell-order preservation.

The five rational nodes are the endpoints and the quarter points of a cell.
For a polynomial for which the displayed identity is exact, a pointwise bound
at all rational points bounds its exact integral.  The proof is finite rational
arithmetic; it invokes neither a limit nor real-number completeness. -/
theorem exactCellOrderPreservation_of_boole
    {eval : Rat -> Rat} {integralBetween : Rat -> Rat -> Rat}
    (a b : Rat)
    (hboole : forall p r : Rat,
      integralBetween p r =
        ((r - p) / 90) *
          (7 * eval p +
            32 * eval (p + (r - p) / 4) +
            12 * eval (p + (r - p) / 2) +
            32 * eval (p + 3 * (r - p) / 4) +
            7 * eval r)) :
    ExactCellOrderPreservation eval integralBetween a b where
  lower_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by native_decide) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by native_decide)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : c <= eval p := hbound (Rat.le_refl : p <= p) hpr
    have h1 : c <= eval q₁ := hbound hq₁.1 hq₁.2
    have h2 : c <= eval q₂ := hbound hq₂.1 hq₂.2
    have h3 : c <= eval q₃ := hbound hq₃.1 hq₃.2
    have hr : c <= eval r := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        90 * c <= 7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by native_decide : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by native_decide : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by native_decide : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by native_decide : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by native_decide : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by native_decide)
    rw [hboole]
    change L * c <=
      (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r)
    calc
      L * c = (L / 90) * (90 * c) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
  upper_const := by
    intro p r c _hap hpr _hrb hbound
    let L : Rat := r - p
    let q₁ : Rat := p + L / 4
    let q₂ : Rat := p + L / 2
    let q₃ : Rat := p + 3 * L / 4
    have hL0 : 0 <= L := by
      dsimp [L]
      grind [Rat.sub_eq_add_neg]
    have hq₁ : p <= q₁ /\ q₁ <= r := by
      constructor
      · dsimp [q₁]
        have hdiv : 0 <= L / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₁, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₂ : p <= q₂ /\ q₂ <= r := by
      constructor
      · dsimp [q₂]
        have hdiv : 0 <= L / 2 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hL0 (by native_decide)
        grind
      · dsimp [q₂, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hq₃ : p <= q₃ /\ q₃ <= r := by
      constructor
      · dsimp [q₃]
        have hthreeL : 0 <= 3 * L :=
          Rat.mul_nonneg (by native_decide) hL0
        have hdiv : 0 <= (3 * L) / 4 := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg hthreeL (by native_decide)
        grind
      · dsimp [q₃, L]
        rw [Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    have hp : eval p <= c := hbound (Rat.le_refl : p <= p) hpr
    have h1 : eval q₁ <= c := hbound hq₁.1 hq₁.2
    have h2 : eval q₂ <= c := hbound hq₂.1 hq₂.2
    have h3 : eval q₃ <= c := hbound hq₃.1 hq₃.2
    have hr : eval r <= c := hbound hpr (Rat.le_refl : r <= r)
    have hsum :
        7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r <= 90 * c := by
      have h7p := Rat.mul_le_mul_of_nonneg_left hp
        (by native_decide : (0 : Rat) <= 7)
      have h32q1 := Rat.mul_le_mul_of_nonneg_left h1
        (by native_decide : (0 : Rat) <= 32)
      have h12q2 := Rat.mul_le_mul_of_nonneg_left h2
        (by native_decide : (0 : Rat) <= 12)
      have h32q3 := Rat.mul_le_mul_of_nonneg_left h3
        (by native_decide : (0 : Rat) <= 32)
      have h7r := Rat.mul_le_mul_of_nonneg_left hr
        (by native_decide : (0 : Rat) <= 7)
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc, Rat.add_comm,
        Rat.mul_assoc, Rat.mul_comm]
    have hscale : 0 <= L / 90 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hL0 (by native_decide)
    rw [hboole]
    change (L / 90) *
        (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
          32 * eval q₃ + 7 * eval r) <= L * c
    calc
      (L / 90) *
          (7 * eval p + 32 * eval q₁ + 12 * eval q₂ +
            32 * eval q₃ + 7 * eval r) <=
          (L / 90) * (90 * c) :=
        Rat.mul_le_mul_of_nonneg_left hsum hscale
      _ = L * c := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end Integral

/-- Effective inverse separation.

This is the extra constructive ingredient beyond monotonicity.  It says that
when two rational inputs are separated by the supplied amount, their interval
values are separated enough to locate the inverse at the requested precision.
Without this, a monotone function can be too flat for an effective inverse
algorithm. -/
structure EffectiveInverseSeparation (F : FunctionOnInterval) where
  /-- The one monotone orientation for which the separation certificate is
  supplied.  Requiring both orientations would make every nonconstant
  function fail the interface. -/
  kind : MonotonicityKind
  inputPrecision : Nat -> Nat
  inputPrecision_pos : forall n, 0 < inputPrecision n
  outputPrecision : Nat -> Nat
  separated :
    forall x y
      (hx : inDomainInterval F.lower F.upper x)
      (hy : inDomainInterval F.lower F.upper y)
      n,
      x + (1 / ((inputPrecision n) : Rat)) <= y ->
        match kind with
        | .nondecreasing =>
            (F.compute x hx (outputPrecision n)).hi <
              (F.compute y hy (outputPrecision n)).lo
        | .nonincreasing =>
            (F.compute y hy (outputPrecision n)).hi <
              (F.compute x hx (outputPrecision n)).lo

/-- The input data from which an inverse-function algorithm should be
constructible. -/
structure InvertibleFunctionOnInterval where
  continuous : ContinuousFunctionOnInterval
  /-- An inverse branch is carried on an actual closed source interval. -/
  source_ordered : continuous.function.lower <= continuous.function.upper
  monotone : MonotoneOnInterval continuous.function
  separation : EffectiveInverseSeparation continuous.function
  /-- The strict separation certificate has the same orientation as the weak
  monotonicity certificate. -/
  orientation :
    match separation.kind with
    | .nondecreasing => monotone.increasing
    | .nonincreasing => ¬ monotone.increasing

namespace InvertibleFunctionOnInterval

def function (I : InvertibleFunctionOnInterval) : FunctionOnInterval :=
  I.continuous.function

end InvertibleFunctionOnInterval

/-- The endpoint-value box at the lower end of an invertible interval branch. -/
def InvertibleFunctionOnInterval.lowerValueBox
    (I : InvertibleFunctionOnInterval) (n : Nat) : QInterval :=
  I.function.compute I.function.lower
    ⟨Rat.le_refl, I.source_ordered⟩ n

/-- The endpoint-value box at the upper end of an invertible interval branch. -/
def InvertibleFunctionOnInterval.upperValueBox
    (I : InvertibleFunctionOnInterval) (n : Nat) : QInterval :=
  I.function.compute I.function.upper
    ⟨I.source_ordered, Rat.le_refl⟩ n

/-- An interval box lies in the oriented endpoint range of an invertible
branch.  The endpoint precision is explicit because a target algorithm and a
forward evaluator need not use the same stage schedule. -/
def InvertibleFunctionOnInterval.EndpointRangeContains
    (I : InvertibleFunctionOnInterval) (n : Nat) (Y : QInterval) : Prop :=
  match I.separation.kind with
  | .nondecreasing =>
      (I.lowerValueBox n).lo <= Y.lo /\
        Y.hi <= (I.upperValueBox n).hi
  | .nonincreasing =>
      (I.upperValueBox n).lo <= Y.lo /\
        Y.hi <= (I.lowerValueBox n).hi

/-- A computable target value in the range of an interval function.

The target carries its own raw-real validity certificate and an explicit
endpoint-range enclosure at every target stage.  This is the finite data a
bisection implementation may inspect; a bare proposition saying that a value
is ``in range'' would not support a constructive inverse search. -/
structure InRangeRaw (I : InvertibleFunctionOnInterval) where
  value : RealRaw
  value_valid : value.Valid
  rangePrecision : Nat -> Nat
  in_range : forall n,
    I.EndpointRangeContains (rangePrecision n) (value.compute n)

/-- A raw inverse evaluator on computable real target values.

It is partial because the inverse is only defined on the certified output
range.  The `compute_preimage` field returns a rational interval in the
original domain containing an input whose function value matches the output
target at the requested scale. -/
structure InverseRaw (I : InvertibleFunctionOnInterval) where
  compute_preimage : InRangeRaw I -> Nat -> QInterval
  valid_preimage : forall y, RealRaw.ValidCompute (compute_preimage y)
  preimage_subinterval : forall y n,
    subintervalOf (compute_preimage y n) I.function.lower I.function.upper
  value_overlaps :
    forall y n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage y n)
          (preimage_subinterval y n)
          n)
        (y.value.compute n)

namespace InverseRaw

def apply {I : InvertibleFunctionOnInterval} (inv : InverseRaw I) (y : InRangeRaw I) :
    RealRaw where
  compute := inv.compute_preimage y

theorem apply_valid {I : InvertibleFunctionOnInterval} (inv : InverseRaw I)
    (y : InRangeRaw I) :
    RealRaw.Valid (inv.apply y) :=
  inv.valid_preimage y

theorem apply_stays_in_source {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n, subintervalOf ((inv.apply y).compute n) I.function.lower I.function.upper :=
  inv.preimage_subinterval y

theorem apply_value_overlaps_target {I : InvertibleFunctionOnInterval}
    (inv : InverseRaw I) (y : InRangeRaw I) :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          ((inv.apply y).compute n)
          (apply_stays_in_source inv y n)
          n)
        (y.value.compute n) :=
  inv.value_overlaps y

end InverseRaw

/-- A particular monotone interval branch has a constructive inverse when its
certified output range admits a raw preimage evaluator.  This is deliberately
branch-local: an inverse is only meaningful after its source interval,
orientation, and range certificate have been fixed. -/
def HasInverse (I : InvertibleFunctionOnInterval) : Prop :=
  Nonempty (InverseRaw I)

/-- The remaining algorithmic step for the inverse function theorem:
construct the inverse intervals by bisection/search. -/
structure InverseBisectionSearch (I : InvertibleFunctionOnInterval) (y : InRangeRaw I) where
  compute_preimage : Nat -> QInterval
  valid_preimage : RealRaw.ValidCompute compute_preimage
  preimage_subinterval :
    forall n, subintervalOf (compute_preimage n) I.function.lower I.function.upper
  value_overlaps :
    forall n,
      QInterval.Overlaps
        (I.continuous.regular.evalInterval
          (compute_preimage n)
          (preimage_subinterval n)
          n)
        (y.value.compute n)

/-- Computational data assigning a finite certified search to every target in
the stated range.  This is data, rather than a merely nonempty proposition,
so assembling the inverse does not invoke a choice principle. -/
def HasBisectionSearch (I : InvertibleFunctionOnInterval) :=
  forall y : InRangeRaw I, InverseBisectionSearch I y

def inverseRawOfSearch {I : InvertibleFunctionOnInterval}
    (search : forall y : InRangeRaw I, InverseBisectionSearch I y) :
    InverseRaw I where
  compute_preimage := fun y => (search y).compute_preimage
  valid_preimage := fun y => (search y).valid_preimage
  preimage_subinterval := fun y => (search y).preimage_subinterval
  value_overlaps := fun y => (search y).value_overlaps

theorem inverse_function_from_bisection_search
    {I : InvertibleFunctionOnInterval}
    (hsearch : HasBisectionSearch I) :
    HasInverse I := by
  exact ⟨inverseRawOfSearch hsearch⟩
end ComputableAnalysis
