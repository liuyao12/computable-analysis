import ComputableAnalysis.RiemannHilbert.LocalODECoefficients
import ComputableAnalysis.RiemannHilbert.FiberAlgebra

/-!
# Formal local systems at every finite rank

Construct the coefficient solution of `y' = A(z)y` for supplied represented
coefficient maps. Valid fibers and their equivalences come from the project
complex-box foundation. For a linear system the supplied coefficient maps
must additionally satisfy `IsLinear`. No series convergence is inferred from
this finite recurrence.
-/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem

variable {n : Nat}

def ratScale (r : Rat) (x : Fiber n) : Fiber n :=
  ⟨fun i => ComplexRaw.scaleRat r (x.val i),
    fun i => ComplexRaw.scaleRat_valid (x.property i)⟩

theorem ratScale_congr (r : Rat) {x y : Fiber n} (h : x ≈ y) :
    ratScale r x ≈ ratScale r y := fun i => ComplexRaw.scaleRat_equiv (h i)

def sum : List (Fiber n) → Fiber n
  | [] => Fiber.zero n
  | x :: xs => Fiber.add x (sum xs)

theorem sum_map_congr (is : List Nat) (f g : Nat → Fiber n)
    (h : ∀ i ∈ is, f i ≈ g i) : sum (is.map f) ≈ sum (is.map g) := by
  induction is with
  | nil => exact Setoid.refl _
  | cons i is ih =>
      exact Fiber.add_congr (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem ratScale_add (r : Rat) (x y : Fiber n) :
    ratScale r (Fiber.add x y) ≈ Fiber.add (ratScale r x) (ratScale r y) :=
  fun i => ComplexRaw.scaleRat_add_equiv r _ _ (x.property i) (y.property i)

theorem ratScale_scale (r : Rat) (a : Scalar) (x : Fiber n) :
    ratScale r (Fiber.scale a x) ≈ Fiber.scale a (ratScale r x) := by
  intro i
  have h1 := ComplexRaw.scaleRat_equiv (r := r)
    (ComplexRaw.mul_comm_equiv a.val (x.val i) a.property (x.property i))
  have h2 := ComplexRaw.scaleRat_mul_equiv r (x.val i) a.val (x.property i) a.property
  have h3 := ComplexRaw.mul_comm_equiv (ComplexRaw.scaleRat r (x.val i)) a.val
    (ComplexRaw.scaleRat_valid (x.property i)) a.property
  exact ComplexRaw.equiv_trans
    (ComplexRaw.scaleRat_valid (ComplexRaw.mul_valid a.property (x.property i)))
    (ComplexRaw.scaleRat_valid (ComplexRaw.mul_valid (x.property i) a.property))
    (ComplexRaw.mul_valid a.property (ComplexRaw.scaleRat_valid (x.property i))) h1
    (ComplexRaw.equiv_trans
      (ComplexRaw.scaleRat_valid (ComplexRaw.mul_valid (x.property i) a.property))
      (ComplexRaw.mul_valid (ComplexRaw.scaleRat_valid (x.property i)) a.property)
      (ComplexRaw.mul_valid a.property (ComplexRaw.scaleRat_valid (x.property i))) h2 h3)

theorem sum_map_add (is : List Nat) (f g : Nat → Fiber n) :
    sum (is.map (fun i => Fiber.add (f i) (g i))) ≈
      Fiber.add (sum (is.map f)) (sum (is.map g)) := by
  induction is with
  | nil => exact Setoid.symm (Fiber.zero_add (Fiber.zero n))
  | cons i is ih =>
      exact Setoid.trans (Fiber.add_congr (Setoid.refl _) ih) (Fiber.add_four _ _ _ _)

theorem sum_map_scale (is : List Nat) (a : Scalar) (f : Nat → Fiber n) :
    sum (is.map (fun i => Fiber.scale a (f i))) ≈ Fiber.scale a (sum (is.map f)) := by
  induction is with
  | nil => exact Setoid.symm (Fiber.scale_zero a)
  | cons i is ih =>
      exact Setoid.trans (Fiber.add_congr (Setoid.refl _) ih) (Setoid.symm (Fiber.scale_add a _ _))

def convolution (a : Nat → ValueMap (Fiber n) (Fiber n)) (y : Nat → Fiber n)
    (k : Nat) : Fiber n :=
  sum ((List.range (k+1)).map (fun i =>
    if i ≤ k then (a i).eval (y (k-i)) else Fiber.zero n))

theorem convolution_congr (a b : Nat → ValueMap (Fiber n) (Fiber n))
    (y z : Nat → Fiber n) (k : Nat) (hab : ∀ i, (a i).Equiv (b i))
    (hyz : ∀ i, i ≤ k → y i ≈ z i) : convolution a y k ≈ convolution b z k := by
  apply sum_map_congr
  intro i hi
  split
  · exact Setoid.trans ((a i).congr (hyz _ (Nat.sub_le _ _))) (hab i _)
  · exact Setoid.refl _

def coefficient (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (k : Nat) : Fiber n :=
  match k with
  | 0 => initial
  | k+1 => ratScale (1 / ((k+1 : Nat) : Rat))
      (sum ((List.range (k+1)).map (fun i =>
        if _h : i ≤ k then (a i).eval (coefficient a initial (k-i)) else Fiber.zero n)))
termination_by k

@[simp] theorem coefficient_zero (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) : coefficient a initial 0 = initial := by rw [coefficient]

theorem coefficient_succ (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) (k : Nat) : coefficient a initial (k+1) =
      ratScale (1 / ((k+1 : Nat) : Rat)) (convolution a (coefficient a initial) k) := by
  rw [coefficient]
  rfl

theorem ratScale_cancel (r : Rat) (hr : r ≠ 0) (x : Fiber n) :
    ratScale r (ratScale (1/r) x) ≈ x :=
  fun i => LocalODE.cancel_scale r hr _ (x.property i)

theorem ratScale_cancel_reverse (r : Rat) (hr : r ≠ 0) (x : Fiber n) :
    ratScale (1/r) (ratScale r x) ≈ x :=
  fun i => LocalODE.cancel_scale_reverse r hr _ (x.property i)

/-- Exact vector coefficient equation at arbitrary finite rank. -/
theorem coefficient_equation (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) (k : Nat) :
    ratScale ((k+1 : Nat) : Rat) (coefficient a initial (k+1)) ≈
      convolution a (coefficient a initial) k := by
  rw [coefficient_succ]
  exact ratScale_cancel _ (LocalODE.succCast_ne_zero k) _

def CoefficientSolution (a : Nat → ValueMap (Fiber n) (Fiber n))
    (y : Nat → Fiber n) (initial : Fiber n) : Prop :=
  y 0 ≈ initial ∧ ∀ k, ratScale ((k+1 : Nat) : Rat) (y (k+1)) ≈ convolution a y k

theorem coefficient_solution (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) : CoefficientSolution a (coefficient a initial) initial :=
  ⟨by rw [coefficient_zero]; exact Setoid.refl _, coefficient_equation a initial⟩

theorem coefficient_unique (a : Nat → ValueMap (Fiber n) (Fiber n))
    (initial : Fiber n) (y : Nat → Fiber n) (hy : CoefficientSolution a y initial)
    (k : Nat) : y k ≈ coefficient a initial k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using hy.1
      | succ k =>
          rw [coefficient_succ]
          exact Setoid.trans (Setoid.symm
            (ratScale_cancel_reverse _ (LocalODE.succCast_ne_zero k) (y (k+1))))
            (Setoid.trans (ratScale_congr _ (hy.2 k))
              (ratScale_congr _ (convolution_congr a a y _ k
                (fun i => ValueMap.equiv_refl (a i)) (fun i hi => ih i (by omega)))))

theorem coefficient_congr (a b : Nat → ValueMap (Fiber n) (Fiber n))
    (x y : Fiber n) (hab : ∀ i, (a i).Equiv (b i)) (hxy : x ≈ y) (k : Nat) :
    coefficient a x k ≈ coefficient b y k := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simpa using hxy
      | succ k =>
          rw [coefficient_succ, coefficient_succ]
          exact ratScale_congr _ (convolution_congr a b _ _ k hab
            (fun i hi => ih i (by omega)))

/-- A represented coefficient evaluator in the initial fiber, preserving
value equivalence without requiring equality of raw programs. -/
def coefficientMap (a : Nat → ValueMap (Fiber n) (Fiber n)) (k : Nat) :
    ValueMap (Fiber n) (Fiber n) :=
  ⟨fun x => coefficient a x k,
    fun h => coefficient_congr a a _ _ (fun i => ValueMap.equiv_refl (a i)) h k⟩

/-- Superposition of the constructed coefficients. -/
theorem coefficient_add (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ i, IsLinear (a i)) (x y : Fiber n) (k : Nat) :
    coefficient a (Fiber.add x y) k ≈ Fiber.add (coefficient a x k) (coefficient a y k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simp only [coefficient_zero]; exact Setoid.refl _
      | succ k =>
          rw [coefficient_succ, coefficient_succ, coefficient_succ]
          have hc : convolution a (coefficient a (Fiber.add x y)) k ≈
              Fiber.add (convolution a (coefficient a x) k) (convolution a (coefficient a y) k) := by
            apply Setoid.trans ?_ (sum_map_add (List.range (k+1))
              (fun i => if i ≤ k then (a i).eval (coefficient a x (k-i)) else Fiber.zero n)
              (fun i => if i ≤ k then (a i).eval (coefficient a y (k-i)) else Fiber.zero n))
            apply sum_map_congr
            intro i hi
            have hik : i ≤ k := by have := List.mem_range.mp hi; omega
            simp only [if_pos hik]
            exact Setoid.trans ((a i).congr (ih (k-i) (by omega))) ((ha i).1 _ _)
          exact Setoid.trans (ratScale_congr _ hc) (ratScale_add _ _ _)

/-- Arbitrary represented complex scalars, not just rational coefficients. -/
theorem coefficient_scale (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ i, IsLinear (a i)) (c : Scalar) (x : Fiber n) (k : Nat) :
    coefficient a (Fiber.scale c x) k ≈ Fiber.scale c (coefficient a x k) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      cases k with
      | zero => simp only [coefficient_zero]; exact Setoid.refl _
      | succ k =>
          rw [coefficient_succ, coefficient_succ]
          have hc : convolution a (coefficient a (Fiber.scale c x)) k ≈
              Fiber.scale c (convolution a (coefficient a x) k) := by
            apply Setoid.trans ?_ (sum_map_scale (List.range (k+1)) c
              (fun i => if i ≤ k then (a i).eval (coefficient a x (k-i)) else Fiber.zero n))
            apply sum_map_congr
            intro i hi
            have hik : i ≤ k := by have := List.mem_range.mp hi; omega
            simp only [if_pos hik]
            exact Setoid.trans ((a i).congr (ih (k-i) (by omega))) ((ha i).2 c _)
          exact Setoid.trans (ratScale_congr _ hc) (ratScale_scale _ c _)

theorem coefficientMap_linear (a : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ i, IsLinear (a i)) (k : Nat) : IsLinear (coefficientMap a k) :=
  ⟨fun x y => coefficient_add a ha x y k, fun c x => coefficient_scale a ha c x k⟩

end ComputableAnalysis.RiemannHilbert.LocalSystem
