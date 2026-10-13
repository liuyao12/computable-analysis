import ComputableAnalysis.ComplexRawQuotientAlgebra

/-!
# Constructing local scalar ODE coefficients

For arbitrary valid represented complex coefficients of `y' = a(z) y`,
construct all solution coefficients from a represented initial value and prove
validity, the exact coefficient equation, uniqueness, and representation
invariance. This is formal coefficient algebra: convergence, differentiation
of the summed function, and local holomorphic solutions remain separate.
-/
namespace ComputableAnalysis.RiemannHilbert.LocalODE

open ComplexRaw

def sum : List ComplexRaw → ComplexRaw
  | [] => zero
  | z :: zs => add z (sum zs)

theorem sum_valid (zs : List ComplexRaw) (h : ∀ z ∈ zs, z.Valid) : (sum zs).Valid := by
  induction zs with
  | nil => exact ofQComplex_valid QComplex.zero
  | cons z zs ih =>
      exact add_valid (h z (by simp)) (ih (fun w hw => h w (by simp [hw])))

theorem sum_map_congr (is : List Nat) (f g : Nat → ComplexRaw)
    (h : ∀ i ∈ is, (f i).Equiv (g i)) :
    (sum (is.map f)).Equiv (sum (is.map g)) := by
  induction is with
  | nil => exact equiv_refl _ (ofQComplex_valid QComplex.zero)
  | cons i is ih =>
      exact add_equiv (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- Finite convolution; only already constructed indices are read. -/
def convolution (a y : Nat → ComplexRaw) (k : Nat) : ComplexRaw :=
  sum ((List.range (k + 1)).map (fun i =>
    if i ≤ k then mul (a i) (y (k - i)) else zero))

theorem convolution_valid (a y : Nat → ComplexRaw) (k : Nat)
    (ha : ∀ i, (a i).Valid) (hy : ∀ i, i ≤ k → (y i).Valid) :
    (convolution a y k).Valid := by
  apply sum_valid
  intro z hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  split
  · exact mul_valid (ha i) (hy (k-i) (Nat.sub_le _ _))
  · exact ofQComplex_valid QComplex.zero

theorem convolution_congr (a b y z : Nat → ComplexRaw) (k : Nat)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hy : ∀ i, i ≤ k → (y i).Valid) (hz : ∀ i, i ≤ k → (z i).Valid)
    (hab : ∀ i, (a i).Equiv (b i))
    (hyz : ∀ i, i ≤ k → (y i).Equiv (z i)) :
    (convolution a y k).Equiv (convolution b z k) := by
  apply sum_map_congr
  intro i hi
  split
  · exact mul_equiv (ha i) (hb i) (hy _ (Nat.sub_le _ _))
      (hz _ (Nat.sub_le _ _)) (hab i) (hyz _ (Nat.sub_le _ _))
  · exact equiv_refl _ (ofQComplex_valid QComplex.zero)

/-- Well-founded executable recurrence, with arbitrary represented data. -/
def coefficient (a : Nat → ComplexRaw) (initial : ComplexRaw) (k : Nat) : ComplexRaw :=
  match k with
  | 0 => initial
  | k + 1 => scaleRat (1 / ((k + 1 : Nat) : Rat))
      (sum ((List.range (k + 1)).map (fun i =>
        if _h : i ≤ k then mul (a i) (coefficient a initial (k - i)) else zero)))
termination_by k

@[simp] theorem coefficient_zero (a : Nat → ComplexRaw) (initial : ComplexRaw) :
    coefficient a initial 0 = initial := by rw [coefficient]

theorem coefficient_succ (a : Nat → ComplexRaw) (initial : ComplexRaw) (k : Nat) :
    coefficient a initial (k+1) = scaleRat (1 / ((k+1 : Nat) : Rat))
      (convolution a (coefficient a initial) k) := by
  rw [coefficient]
  rfl

theorem coefficient_valid (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (k : Nat) :
    (coefficient a initial k).Valid := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using h0
      | succ k =>
          rw [coefficient_succ]
          exact scaleRat_valid (convolution_valid a _ k ha
            (fun i hi => ih i (by omega)))

theorem succCast_ne_zero (k : Nat) : ((k+1 : Nat) : Rat) ≠ 0 :=
  Rat.ne_of_gt ((Rat.natCast_pos).2 (by omega))

theorem cancel_scale (r : Rat) (hr : r ≠ 0) (z : ComplexRaw) (hz : z.Valid) :
    (scaleRat r (scaleRat (1/r) z)).Equiv z := by
  have h := scaleRat_scaleRat_equiv r (1/r) z hz
  have hc : r * (1/r) = 1 := by
    rw [Rat.div_def, Rat.one_mul, Rat.mul_inv_cancel r hr]
  rw [hc] at h
  exact equiv_trans (scaleRat_valid (scaleRat_valid hz)) (scaleRat_valid hz) hz h
    (scaleRat_one_equiv z hz)

theorem cancel_scale_reverse (r : Rat) (hr : r ≠ 0)
    (z : ComplexRaw) (hz : z.Valid) : (scaleRat (1/r) (scaleRat r z)).Equiv z := by
  have h := scaleRat_scaleRat_equiv (1/r) r z hz
  have hc : (1/r) * r = 1 := by
    rw [Rat.div_def, Rat.one_mul, Rat.mul_comm, Rat.mul_inv_cancel r hr]
  rw [hc] at h
  exact equiv_trans (scaleRat_valid (scaleRat_valid hz)) (scaleRat_valid hz) hz h
    (scaleRat_one_equiv z hz)

/-- Exact coefficient form of the ODE, not an analytic derivative theorem. -/
theorem coefficient_equation (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (k : Nat) :
    (scaleRat ((k+1 : Nat) : Rat) (coefficient a initial (k+1))).Equiv
      (convolution a (coefficient a initial) k) := by
  rw [coefficient_succ]
  exact cancel_scale _ (succCast_ne_zero k) _
    (convolution_valid a _ k ha (fun i _ => coefficient_valid a initial ha h0 i))

/-- Semantic role at the coefficient level, defined independently of the
constructed evaluator. Analytic solutionhood is deliberately not asserted. -/
def CoefficientSolution (a y : Nat → ComplexRaw) (initial : ComplexRaw) : Prop :=
  (∀ k, (y k).Valid) ∧ (y 0).Equiv initial ∧
  ∀ k, (scaleRat ((k+1 : Nat) : Rat) (y (k+1))).Equiv (convolution a y k)

theorem coefficient_solution (a : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) :
    CoefficientSolution a (coefficient a initial) initial :=
  ⟨coefficient_valid a initial ha h0, by
    rw [coefficient_zero]; exact equiv_refl initial h0,
    coefficient_equation a initial ha h0⟩

/-- All valid formal solutions with the supplied initial coefficient agree. -/
theorem coefficient_unique (a y : Nat → ComplexRaw) (initial : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid)
    (hy : CoefficientSolution a y initial) (k : Nat) :
    (y k).Equiv (coefficient a initial k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using hy.2.1
      | succ k =>
          rw [coefficient_succ]
          have hconv := convolution_congr a a y (coefficient a initial) k ha ha
            (fun i _ => hy.1 i)
            (fun i _ => coefficient_valid a initial ha h0 i)
            (fun i => equiv_refl _ (ha i)) (fun i hi => ih i (by omega))
          have hscale := scaleRat_equiv (r := 1 / ((k+1 : Nat) : Rat)) (hy.2.2 k)
          exact equiv_trans (hy.1 (k+1))
            (scaleRat_valid (scaleRat_valid (hy.1 (k+1))))
            (scaleRat_valid (convolution_valid a _ k ha
              (fun i _ => coefficient_valid a initial ha h0 i)))
            (equiv_symm (cancel_scale_reverse _ (succCast_ne_zero k) _ (hy.1 (k+1))))
            (equiv_trans (scaleRat_valid (scaleRat_valid (hy.1 (k+1))))
              (scaleRat_valid (convolution_valid a y k ha (fun i _ => hy.1 i)))
              (scaleRat_valid (convolution_valid a _ k ha
                (fun i _ => coefficient_valid a initial ha h0 i)))
              hscale (scaleRat_equiv hconv))

/-- Replacing coefficient and initial-value implementations preserves all
constructed coefficients, including irrational represented inputs. -/
theorem coefficient_congr (a b : Nat → ComplexRaw) (x y : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hb : ∀ i, (b i).Valid)
    (hx : x.Valid) (hy : y.Valid) (hab : ∀ i, (a i).Equiv (b i)) (hxy : x.Equiv y)
    (k : Nat) : (coefficient a x k).Equiv (coefficient b y k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using hxy
      | succ k =>
          rw [coefficient_succ, coefficient_succ]
          exact scaleRat_equiv (convolution_congr a b _ _ k ha hb
            (fun i _ => coefficient_valid a x ha hx i)
            (fun i _ => coefficient_valid b y hb hy i) hab (fun i hi => ih i (by omega)))

end ComputableAnalysis.RiemannHilbert.LocalODE
