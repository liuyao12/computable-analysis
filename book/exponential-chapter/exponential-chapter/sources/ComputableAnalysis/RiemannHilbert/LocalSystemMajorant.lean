import ComputableAnalysis.RiemannHilbert.LocalSystemCoefficients
import ComputableAnalysis.RiemannHilbert.LocalScalarSolution

/-! Coordinate majorants for the actual finite-rank local ODE recurrence. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory
variable {n : Nat}

def CoordinateBound (x : Fiber n) (C : Rat) : Prop :=
  ∀ i, Small (x.val i) C

theorem bound_congr {x y : Fiber n} {C : Rat} (hxy : x ≈ y)
    (h : CoordinateBound x C) : CoordinateBound y C :=
  fun i => Small.congr (x.property i) (y.property i) (hxy i) (h i)

theorem bound_zero (C : Rat) (hC : 0 ≤ C) : CoordinateBound (Fiber.zero n) C :=
  fun _ => Small.zero hC

theorem bound_add {x y : Fiber n} {C D : Rat}
    (hx : CoordinateBound x C) (hy : CoordinateBound y D) :
    CoordinateBound (Fiber.add x y) (C+D) :=
  fun i => LocalODE.small_add (hx i) (hy i)

theorem bound_ratScale {x : Fiber n} {C r : Rat} (hr : 0 ≤ r)
    (hx : CoordinateBound x C) : CoordinateBound (ratScale r x) (r*C) :=
  fun i => LocalODE.small_scale hr (hx i)

theorem bound_sum_uniform (xs : List (Fiber n)) (C : Rat) (_hC : 0 ≤ C)
    (h : ∀ x ∈ xs, CoordinateBound x C) : CoordinateBound (sum xs) ((xs.length : Rat)*C) := by
  induction xs with
  | nil => exact bound_zero _ (by change 0 ≤ (0 : Rat)*C; rw [Rat.zero_mul]; decide)
  | cons x xs ih =>
    have hs := bound_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
    have he : C+(xs.length : Rat)*C = ((x::xs).length : Rat)*C := by
      simp only [List.length_cons, Rat.natCast_add]
      grind
    rw [he] at hs
    exact hs

/-- A finite-input bound on each supplied operator coefficient. This is
mathematical operator evidence, not an assumed bound on its ODE solution. -/
def OperatorMajorant (a : Nat → ValueMap (Fiber n) (Fiber n)) (M K : Rat) : Prop :=
  ∀ k C, 0 ≤ C → ∀ x, CoordinateBound x C →
    CoordinateBound ((a k).eval x) (2*M*K^k*C)

theorem coefficient_majorant (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) (M C K : Rat) (hM : 0 ≤ M) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (hinit : CoordinateBound initial C) (k : Nat) :
    CoordinateBound (coefficient a initial k) (C*K^k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    cases k with
    | zero => simpa only [coefficient_zero, Rat.pow_zero, Rat.mul_one] using hinit
    | succ k =>
      rw [coefficient_succ]
      have hB : 0 ≤ 2*M*C*K^k :=
        Rat.mul_nonneg (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hM) hC) (Rat.pow_nonneg hK)
      have hconv : CoordinateBound (convolution a (coefficient a initial) k)
          (((k+1 : Nat) : Rat)*(2*M*C*K^k)) := by
        unfold convolution
        have hs := bound_sum_uniform
          ((List.range (k+1)).map (fun i =>
            if i ≤ k then (a i).eval (coefficient a initial (k-i)) else Fiber.zero n))
          (2*M*C*K^k) hB ?_
        · simpa only [List.length_map, List.length_range] using hs
        · intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          have hik : i ≤ k := by have := List.mem_range.mp hi; omega
          rw [if_pos hik]
          have ht := haB i (C*K^(k-i)) (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
            (coefficient a initial (k-i)) (ih (k-i) (by omega))
          have hp : K^i*K^(k-i)=K^k := by
            rw [← LocalODE.rational_pow_add]; congr 1; omega
          have he : 2*M*K^i*(C*K^(k-i))=2*M*C*K^k := by
            calc
              _ = (2*M*C)*(K^i*K^(k-i)) := by grind
              _ = _ := by rw [hp]
          rw [he] at ht
          exact ht
      have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
      have hinv : 0 ≤ 1/((k+1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 hd)
      have hs := bound_ratScale hinv hconv
      have he : (1/((k+1 : Nat) : Rat))*(((k+1 : Nat) : Rat)*(2*M*C*K^k))=2*M*C*K^k := by
        rw [Rat.div_def, Rat.one_mul]
        calc
          _ = (((k+1 : Nat) : Rat)*((k+1 : Nat) : Rat)⁻¹)*(2*M*C*K^k) := by grind
          _ = _ := by rw [Rat.mul_inv_cancel _ (LocalODE.succCast_ne_zero k), Rat.one_mul]
      rw [he] at hs
      intro i
      apply (hs i).mono
      have hh : (2*M)*(C*K^k) ≤ K*(C*K^k) :=
        Rat.mul_le_mul_of_nonneg_right hMK (Rat.mul_nonneg hC (Rat.pow_nonneg hK))
      rw [Rat.pow_succ]
      grind

def finiteBound : List Rat → Rat
  | [] => 0
  | r::rs => max r (finiteBound rs)

theorem finiteBound_nonneg (rs : List Rat) : 0 ≤ finiteBound rs := by
  induction rs with
  | nil => exact Rat.le_refl
  | cons r rs ih => change 0 ≤ max r (finiteBound rs); grind

theorem le_finiteBound (r : Rat) (rs : List Rat) (h : r ∈ rs) : r ≤ finiteBound rs := by
  induction rs with
  | nil => simp at h
  | cons s rs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst r; change s ≤ max s (finiteBound rs); grind
    · have hh := ih h; change r ≤ max s (finiteBound rs); grind

/-- An executable initial-vector bound, also covering rank zero. -/
def initialBound (x : Fiber n) : Rat :=
  finiteBound (List.ofFn (fun i => LocalODE.initialBound (x.val i)))

theorem initialBound_nonneg (x : Fiber n) : 0 ≤ initialBound x := finiteBound_nonneg _

theorem initialBound_valid (x : Fiber n) : CoordinateBound x (initialBound x) := by
  intro i
  apply (LocalODE.initialBound_valid (x.val i) (x.property i)).mono
  exact le_finiteBound _ _ (List.mem_ofFn.mpr ⟨i, rfl⟩)

end ComputableAnalysis.RiemannHilbert.LocalSystem
