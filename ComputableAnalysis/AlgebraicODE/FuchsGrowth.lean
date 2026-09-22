import ComputableAnalysis.LinearGrowth
import ComputableAnalysis.ComplexPolynomial

/-! The forward Fuchs theorem along rational complex rays. The original
equation is `z²y'' + z p(z)y' + q(z)y = 0`. Its scaled jet is `(y,z y')`.
Four rational interval coordinates carry its real and imaginary parts. -/
namespace ComputableAnalysis.AlgebraicODE.Fuchs.Growth
open LinearODE

def complexSize (z : QComplex) : Rat := qabs z.re + qabs z.im

theorem complexSize_nonneg (z : QComplex) : 0 ≤ complexSize z := by
  have := qabs_nonneg z.re
  have := qabs_nonneg z.im
  unfold complexSize
  grind

theorem complexSize_add (z w : QComplex) :
    complexSize (QComplex.add z w) ≤ complexSize z + complexSize w := by
  have := qabs_add_le z.re w.re
  have := qabs_add_le z.im w.im
  unfold complexSize QComplex.add
  grind

theorem complexSize_mul (z w : QComplex) :
    complexSize (QComplex.mul z w) ≤ complexSize z * complexSize w := by
  have hr := qabs_sub_le (z.re*w.re) (z.im*w.im)
  have hi := qabs_add_le (z.re*w.im) (z.im*w.re)
  simp only [qabs_mul] at hr hi
  unfold complexSize QComplex.mul
  grind

/-- A literal bound for a complex polynomial on `|z|₁ ≤ r`. -/
def polynomialBound : List QComplex → Rat → Rat
  | [], _ => 0
  | c::cs, r => complexSize c + r * polynomialBound cs r

theorem polynomialBound_nonneg (p : List QComplex) {r : Rat} (hr : 0 ≤ r) :
    0 ≤ polynomialBound p r := by
  induction p with
  | nil => exact Rat.le_refl
  | cons c cs ih =>
      have := Rat.mul_nonneg hr ih
      have := complexSize_nonneg c
      simp only [polynomialBound]
      grind

theorem polynomial_eval_bound (p : List QComplex) {z : QComplex} {r : Rat}
    (hr : 0 ≤ r) (hz : complexSize z ≤ r) :
    complexSize (CPoly.eval p z) ≤ polynomialBound p r := by
  induction p with
  | nil => simp [CPoly.eval, complexSize, QComplex.zero, qabs, polynomialBound]; grind
  | cons c cs ih =>
      have h1 := complexSize_add c (QComplex.mul z (CPoly.eval cs z))
      have h2 := complexSize_mul z (CPoly.eval cs z)
      have h3 := Rat.mul_le_mul_of_nonneg_left ih (complexSize_nonneg z)
      have h4 := Rat.mul_le_mul_of_nonneg_right hz (polynomialBound_nonneg cs hr)
      change complexSize (QComplex.add c (QComplex.mul z (CPoly.eval cs z))) ≤ _
      simp only [polynomialBound]
      grind

/-- Real-coordinate matrix of `[[0,1],[-q,1-p]]` acting on `(y,z y')`. -/
def companion (p q : QComplex) : RatMatrix 4 := fun i j =>
  match i.val, j.val with
  | 0, 2 | 1, 3 => 1
  | 2, 0 | 3, 1 => -q.re
  | 2, 1 => q.im
  | 3, 0 => -q.im
  | 2, 2 | 3, 3 => 1-p.re
  | 2, 3 => p.im
  | 3, 2 => -p.im
  | _, _ => 0

def jetVector (y u : QComplex) : RatVector 4 := fun i =>
  match i.val with
  | 0 => y.re
  | 1 => y.im
  | 2 => u.re
  | _ => u.im

/-- The matrix really is the scaled second-order equation: its first
component is `u`, and its second is `-q*y + (1-p)*u`. -/
theorem companion_apply (p q y u : QComplex) :
    matrixApply (companion p q) (jetVector y u) =
      jetVector u (QComplex.add (QComplex.neg (QComplex.mul q y))
        (QComplex.mul (QComplex.sub QComplex.one p) u)) := by
  funext i
  have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by
    have := i.isLt
    omega
  rcases hi with hi | hi | hi | hi <;>
    simp [matrixApply, finiteSum, companion, jetVector, hi,
      QComplex.add, QComplex.neg, QComplex.mul, QComplex.sub, QComplex.one] <;> grind

theorem companion_bound (p q : QComplex) (j : Fin 4) :
    matrixColumnAbsSum (companion p q) j ≤ 2 + complexSize p + complexSize q := by
  have hp := complexSize_nonneg p
  have hq := complexSize_nonneg q
  have hsub := qabs_sub_le 1 p.re
  have hone : qabs (1 : Rat) = 1 := by decide +kernel
  rw [hone] at hsub
  have hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by
    have := j.isLt
    omega
  rcases hj with hj | hj | hj | hj <;>
    simp [matrixColumnAbsSum, finiteSum, companion, hj, complexSize, qabs] <;>
    unfold complexSize at hp hq <;> unfold qabs at hp hq hsub <;> grind

def rayPoint (direction : QComplex) (t : Rat) : QComplex :=
  QComplex.scaleRat t direction

theorem rayPoint_bound (direction : QComplex) {t R : Rat}
    (ht : 0 ≤ t) (htR : t ≤ R) :
    complexSize (rayPoint direction t) ≤ R * complexSize direction := by
  unfold complexSize rayPoint QComplex.scaleRat
  rw [qabs_mul, qabs_mul, qabs_eq_self_of_nonneg ht]
  have := Rat.mul_le_mul_of_nonneg_right htR (complexSize_nonneg direction)
  unfold complexSize at this
  grind

def rayMatrix (p q : List QComplex) (direction : QComplex) (t : Rat) : RatMatrix 4 :=
  matrixScale (1/t) (companion (CPoly.eval p (rayPoint direction t))
    (CPoly.eval q (rayPoint direction t)))

/-- A solution of the differential equation along a ray, using the existing
raw interval representation for the scaled complex jet. No solution-growth
condition and no Frobenius construction is included in this definition. -/
abbrev RaySolution (p q : List QComplex) (direction : QComplex) (R : Rat) :=
  LinearSolution (rayMatrix p q direction) R

/-- A computable integer exponent; this ceiling is rational arithmetic. -/
def exponent (p q : List QComplex) (direction : QComplex) (R : Rat) : Nat :=
  (2 + polynomialBound p (R*complexSize direction) +
    polynomialBound q (R*complexSize direction)).ceil.natAbs

theorem le_exponent (p q : List QComplex) (direction : QComplex) (R : Rat) :
    2 + polynomialBound p (R*complexSize direction) +
      polynomialBound q (R*complexSize direction) ≤ (exponent p q direction R : Rat) := by
  apply Rat.le_trans Rat.le_ceil
  exact_mod_cast (Int.le_natAbs (a := (2 + polynomialBound p (R*complexSize direction) +
    polynomialBound q (R*complexSize direction)).ceil))

theorem rayMatrix_pole_bound (p q : List QComplex) (direction : QComplex)
    {R t : Rat} (ht : 0 < t) (htR : t ≤ R) (j : Fin 4) :
    t * matrixColumnAbsSum (rayMatrix p q direction t) j ≤
      (exponent p q direction R : Rat) := by
  have hR : 0 ≤ R := by grind
  have hr := Rat.mul_nonneg hR (complexSize_nonneg direction)
  have hz := rayPoint_bound direction (Rat.le_of_lt ht) htR
  have hp := polynomial_eval_bound p hr hz
  have hq := polynomial_eval_bound q hr hz
  have hc := companion_bound (CPoly.eval p (rayPoint direction t))
    (CPoly.eval q (rayPoint direction t)) j
  have he := le_exponent p q direction R
  have hinv : 0 ≤ 1/t := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr ht))
  unfold rayMatrix
  rw [matrixColumnAbsSum_matrixScale, qabs_eq_self_of_nonneg hinv]
  have hcancel : t*(1/t) = 1 := FormalPowerSeries.mul_div_cancel_left (Rat.ne_of_gt ht)
  rw [← Rat.mul_assoc, hcancel, Rat.one_mul]
  grind

/-- Forward Fuchs: every solution, defined by the ODE's local finite
differences, has polynomial growth toward zero along the ray. -/
theorem fuchs_ray_growth (p q : List QComplex) (direction : QComplex) {R : Rat}
    (S : RaySolution p q direction R) {a b M : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) (hM : NormBound (S.value b) M) :
    NormBound (S.value a)
      (b^(exponent p q direction R)*M/a^(exponent p q direction R)) :=
  S.fuchs_growth _ (fun _ ht htR => rayMatrix_pole_bound p q direction ht htR)
    ha hab hb hM

/-- No outer-bound hypothesis is needed: a single computed outer box
supplies the constant in the polynomial bound for every solution. -/
theorem fuchs_ray_moderate (p q : List QComplex) (direction : QComplex) {R : Rat}
    (S : RaySolution p q direction R) {a b : Rat}
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ R) :
    NormBound (S.value a)
      (b^(exponent p q direction R)*normCeiling (S.value b) 0 /
        a^(exponent p q direction R)) :=
  S.moderate_growth _ (fun _ ht htR => rayMatrix_pole_bound p q direction ht htR)
    ha hab hb

end ComputableAnalysis.AlgebraicODE.Fuchs.Growth
