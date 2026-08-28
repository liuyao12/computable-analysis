import ComputableAnalysis.Basic

/-!
# A computable volume model for the n-ball

The project treats the volume of an `n`-ball through a finite recurrence rather
than through Lebesgue measure.  The rational coefficient records everything
except the chosen computable approximation to `pi`:

`V₀(r) = 1`, `V₁(r) = 2r`, and
`Vₙ₊₂(r) = (2 * pi * r² / (n+2)) * Vₙ(r)`.

This file formalizes the coefficient and finite evaluation layer.  A later
bridge can replace the rational `pi` input by any valid `RealRaw` presentation.
-/

namespace ComputableAnalysis

def nBallCoeff : Nat -> Rat
  | 0 => 1
  | 1 => 2
  | n + 2 => (2 : Rat) / (n + 2) * nBallCoeff n

def nBallPiExponent (n : Nat) : Nat := n / 2

def nBallVolumeModel (n : Nat) (piApprox radius : Rat) : Rat :=
  nBallCoeff n * piApprox ^ nBallPiExponent n * radius ^ n

/-! A literal finite product-integral surrogate.  The lists are the sampled
coordinates and the functions are rational cell values; no completed domain
or measure is hidden in this definition. -/

def finiteProductSum2D (xs ys : List Rat) (f g : Rat -> Rat) : Rat :=
  (xs.map (fun x =>
    (ys.map (fun y => f x * g y)).foldl (fun acc value => acc + value) 0)).foldl
      (fun acc value => acc + value) 0

private theorem foldl_add_initial (xs : List Rat) (term : Rat -> Rat)
    (initial : Rat) :
    xs.foldl (fun acc value => acc + term value) initial =
      initial + xs.foldl (fun acc value => acc + term value) 0 := by
  induction xs generalizing initial with
  | nil =>
      simp
      grind
  | cons x xs ih =>
      simp only [List.foldl]
      simp only [Rat.zero_add]
      rw [ih]
      rw [ih (initial := term x)]
      grind [Rat.add_assoc]

private theorem foldl_add_map_mul_left (ys : List Rat) (a : Rat)
    (g : Rat -> Rat) :
    (ys.map (fun y => a * g y)).foldl (fun acc value => acc + value) 0 =
      a * (ys.map g).foldl (fun acc value => acc + value) 0 := by
  induction ys with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (ys.map g).foldl (fun acc value => acc + value) (g y) =
            g y + (ys.map g).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (ys.map g) (fun z => z) (g y))
      rw [hright]
      rw [ih]
      grind [Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

private theorem foldl_add_map_mul_right (xs : List Rat) (b : Rat)
    (f : Rat -> Rat) :
    (xs.map (fun x => f x * b)).foldl (fun acc value => acc + value) 0 =
      (xs.map f).foldl (fun acc value => acc + value) 0 * b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright]
      rw [ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.mul_assoc]

private theorem foldl_add_map_mul_right_general {α : Type}
    (xs : List α) (b : Rat) (f : α -> Rat) :
    (xs.map (fun x => f x * b)).foldl (fun acc value => acc + value) 0 =
      (xs.map f).foldl (fun acc value => acc + value) 0 * b := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_initial]
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright, ih]
      grind [Rat.add_mul, Rat.add_assoc, Rat.mul_assoc]

theorem finiteProductSum2D_factorized (xs ys : List Rat) (f g : Rat -> Rat) :
    finiteProductSum2D xs ys f g =
      (xs.map f).foldl (fun acc value => acc + value) 0 *
      (ys.map g).foldl (fun acc value => acc + value) 0 := by
  induction xs with
  | nil =>
      simp [finiteProductSum2D]
  | cons x xs ih =>
      simp only [finiteProductSum2D, List.map_cons, List.foldl]
      simp only [Rat.zero_add]
      rw [foldl_add_map_mul_left ys (f x) g]
      rw [foldl_add_initial]
      have ih' := ih
      have ih'' :
          (xs.map (fun x =>
            (ys.map (fun y => f x * g y)).foldl
              (fun acc value => acc + value) 0)).foldl
              (fun acc value => acc + value) 0 =
            (xs.map f).foldl (fun acc value => acc + value) 0 *
              (ys.map g).foldl (fun acc value => acc + value) 0 := by
        simpa [finiteProductSum2D] using ih'
      rw [ih'']
      have hright :
          (xs.map f).foldl (fun acc value => acc + value) (f x) =
            f x + (xs.map f).foldl (fun acc value => acc + value) 0 := by
        simpa only [id] using
          (foldl_add_initial (xs.map f) (fun z => z) (f x))
      rw [hright]
      grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

/-! A general finite rectangular sum.  Unlike `finiteProductSum2D`, the cell
value may depend on both coordinates arbitrarily; this is the finite Fubini
law used when separability is unavailable. -/

def finiteRatSum : List Rat -> Rat
  | [] => 0
  | value :: rest => value + finiteRatSum rest

def finiteRectangularSum {α β : Type} (xs : List α) (ys : List β)
    (h : α -> β -> Rat) : Rat :=
  match xs with
  | [] => 0
  | x :: rest => finiteRatSum (ys.map (h x)) +
      finiteRectangularSum rest ys h

theorem finiteRatSum_nonneg (xs : List Rat)
    (h : forall x, x ∈ xs -> 0 <= x) :
    0 <= finiteRatSum xs := by
  induction xs with
  | nil => simp [finiteRatSum]
  | cons x xs ih =>
      simp only [finiteRatSum]
      apply Rat.add_nonneg
      · exact h x (by simp)
      · apply ih
        intro y hy
        exact h y (by simp [hy])

theorem finiteRatSum_le {α : Type} (xs : List α)
    (f g : α -> Rat)
    (h : forall x, x ∈ xs -> f x <= g x) :
    finiteRatSum (xs.map f) <= finiteRatSum (xs.map g) := by
  induction xs with
  | nil => simp [finiteRatSum]
  | cons x xs ih =>
      simp only [List.map_cons, finiteRatSum]
      apply rat_add_le_add
      · exact h x (by simp)
      · apply ih
        intro y hy
        exact h y (by simp [hy])

theorem finiteRatSum_add {α : Type} (xs : List α)
    (f g : α -> Rat) :
    finiteRatSum (xs.map (fun x => f x + g x)) =
      finiteRatSum (xs.map f) + finiteRatSum (xs.map g) := by
  induction xs with
  | nil => grind [finiteRatSum]
  | cons x xs ih =>
      simp only [List.map_cons, finiteRatSum]
      rw [ih]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem finiteRatSum_scale {α : Type} (xs : List α)
    (scale : Rat) (f : α -> Rat) :
    finiteRatSum (xs.map (fun x => scale * f x)) =
      scale * finiteRatSum (xs.map f) := by
  induction xs with
  | nil => grind [finiteRatSum]
  | cons x xs ih =>
      simp only [List.map_cons, finiteRatSum]
      rw [ih]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc]

theorem finiteRatSum_congr {α : Type} (xs : List α)
    (f g : α -> Rat) (h : forall x, x ∈ xs -> f x = g x) :
    finiteRatSum (xs.map f) = finiteRatSum (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, finiteRatSum]
      rw [h x (by simp)]
      rw [ih (by
        intro y hy
        exact h y (by simp [hy]))]

theorem finiteRectangularSum_nonneg {α β : Type} (xs : List α) (ys : List β)
    (cellValue : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys -> 0 <= cellValue x y) :
    0 <= finiteRectangularSum xs ys cellValue := by
  induction xs with
  | nil => simp [finiteRectangularSum]
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      apply Rat.add_nonneg
      · apply finiteRatSum_nonneg
        intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨y, hy, rfl⟩
        exact h x (by simp) y hy
      · apply ih
        intro x' hx' y hy
        exact h x' (by simp [hx']) y hy

theorem finiteRectangularSum_add {α β : Type}
    (xs : List α) (ys : List β)
    (f g : α -> β -> Rat) :
    finiteRectangularSum xs ys (fun x y => f x y + g x y) =
      finiteRectangularSum xs ys f + finiteRectangularSum xs ys g := by
  induction xs with
  | nil => grind [finiteRectangularSum]
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      rw [finiteRatSum_add, ih]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem finiteRectangularSum_scale {α β : Type}
    (xs : List α) (ys : List β) (scale : Rat) (f : α -> β -> Rat) :
    finiteRectangularSum xs ys (fun x y => scale * f x y) =
      scale * finiteRectangularSum xs ys f := by
  induction xs with
  | nil => grind [finiteRectangularSum]
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      rw [finiteRatSum_scale, ih]
      grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc]

theorem finiteRectangularSum_congr {α β : Type}
    (xs : List α) (ys : List β)
    (f g : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys -> f x y = g x y) :
    finiteRectangularSum xs ys f = finiteRectangularSum xs ys g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      rw [finiteRatSum_congr]
      · rw [ih]
        intro x' hx' y hy
        exact h x' (by simp [hx']) y hy
      · intro y hy
        exact h x (by simp) y hy

theorem finiteRectangularSum_mono {α β : Type} (xs : List α) (ys : List β)
    (lower upper : α -> β -> Rat)
    (h : forall x, x ∈ xs -> forall y, y ∈ ys ->
      lower x y <= upper x y) :
    finiteRectangularSum xs ys lower <=
      finiteRectangularSum xs ys upper := by
  induction xs with
  | nil => simp [finiteRectangularSum]
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      apply rat_add_le_add
      · apply finiteRatSum_le
        intro y hy
        exact h x (by simp) y hy
      · apply ih
        intro x' hx' y hy
        exact h x' (by simp [hx']) y hy

private theorem finiteRectangularSum_empty_right {α β : Type} (xs : List α)
    (h : α -> β -> Rat) :
    finiteRectangularSum xs [] h = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [finiteRectangularSum, List.map_nil, finiteRatSum]
      rw [ih]
      grind

private theorem finiteRectangularSum_right_cons {α β : Type}
    (xs : List α) (ys : List β) (y : β) (h : α -> β -> Rat) :
    finiteRectangularSum xs (y :: ys) h =
      finiteRectangularSum xs ys h +
        finiteRatSum (xs.map (fun x => h x y)) := by
  induction xs with
  | nil =>
      simp [finiteRectangularSum, finiteRatSum]
      grind
  | cons x xs ih =>
      simp only [finiteRectangularSum, List.map_cons, finiteRatSum]
      rw [ih]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem finiteRectangularSum_swap {α β : Type} (xs : List α) (ys : List β)
    (h : α -> β -> Rat) :
    finiteRectangularSum xs ys h =
      finiteRectangularSum ys xs (fun y x => h x y) := by
  induction xs with
  | nil =>
      exact (finiteRectangularSum_empty_right ys (fun y x => h x y)).symm
  | cons x xs ih =>
      simp only [finiteRectangularSum]
      rw [ih]
      rw [finiteRectangularSum_right_cons]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

/-! Weighted cell form for two finite coordinate partitions. -/

def finiteWeightedRectangularSum
    (xs ys : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat) : Rat :=
  finiteRectangularSum xs ys
    (fun x y => x.2 * y.2 * cellValue x.1 y.1)

theorem finiteWeightedRectangularSum_swap
    (xs ys : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys cellValue =
      finiteWeightedRectangularSum ys xs (fun y x => cellValue x y) := by
  simpa [finiteWeightedRectangularSum, Rat.mul_comm] using
    (finiteRectangularSum_swap xs ys
      (fun x y => x.2 * y.2 * cellValue x.1 y.1))

theorem finiteWeightedRectangularSum_nonneg
    (xs ys : List (Rat × Rat)) (cellValue : Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      0 <= cellValue x.1 y.1) :
    0 <= finiteWeightedRectangularSum xs ys cellValue := by
  apply finiteRectangularSum_nonneg
  intro x hx y hy
  apply Rat.mul_nonneg
  · apply Rat.mul_nonneg (hwidthX x hx) (hwidthY y hy)
  · exact hvalue x hx y hy

theorem finiteWeightedRectangularSum_mono
    (xs ys : List (Rat × Rat))
    (lower upper : Rat -> Rat -> Rat)
    (hwidthX : forall cell, cell ∈ xs -> 0 <= cell.2)
    (hwidthY : forall cell, cell ∈ ys -> 0 <= cell.2)
    (hvalue : forall x, x ∈ xs -> forall y, y ∈ ys ->
      lower x.1 y.1 <= upper x.1 y.1) :
    finiteWeightedRectangularSum xs ys lower <=
      finiteWeightedRectangularSum xs ys upper := by
  apply finiteRectangularSum_mono
  intro x hx y hy
  apply Rat.mul_le_mul_of_nonneg_left
  · exact hvalue x hx y hy
  · exact Rat.mul_nonneg (hwidthX x hx) (hwidthY y hy)

theorem finiteWeightedRectangularSum_add
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys (fun x y => f x y + g x y) =
      finiteWeightedRectangularSum xs ys f +
        finiteWeightedRectangularSum xs ys g := by
  simpa [finiteWeightedRectangularSum, Rat.mul_add] using
    (finiteRectangularSum_add xs ys
      (fun x y => x.2 * y.2 * f x.1 y.1)
      (fun x y => x.2 * y.2 * g x.1 y.1))

theorem finiteWeightedRectangularSum_scale
    (xs ys : List (Rat × Rat)) (scale : Rat)
    (f : Rat -> Rat -> Rat) :
    finiteWeightedRectangularSum xs ys (fun x y => scale * f x y) =
      scale * finiteWeightedRectangularSum xs ys f := by
  simpa [finiteWeightedRectangularSum, Rat.mul_assoc, Rat.mul_comm] using
    (finiteRectangularSum_scale xs ys scale
      (fun x y => x.2 * y.2 * f x.1 y.1))

/-! The same finite algebra in arbitrary dimension.  A list of sample lists
and a list of one-variable factors describes a separable rectangular sum. -/

def finiteProductNestedSum : List (List Rat) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | samples :: restSamples, factor :: restFactors =>
      (samples.map (fun x =>
        factor x * finiteProductNestedSum restSamples restFactors)).foldl
        (fun acc value => acc + value) 0
  | _, _ => 0

def finiteProductSum : List (List Rat) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | samples :: restSamples, factor :: restFactors =>
      (samples.map factor).foldl (fun acc value => acc + value) 0 *
        finiteProductSum restSamples restFactors
  | _, _ => 0

theorem finiteProductNestedSum_factorized
    (samples : List (List Rat)) (factors : List (Rat -> Rat)) :
    finiteProductNestedSum samples factors =
      finiteProductSum samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> rfl
  | cons sample rest ih =>
      cases factors with
      | nil => rfl
      | cons factor restFactors =>
          simp only [finiteProductNestedSum, finiteProductSum]
          induction sample with
          | nil => simp
          | cons x xs ihx =>
              simp only [List.map_cons, List.foldl]
              rw [foldl_add_initial]
              rw [ihx]
              have htail := ih restFactors
              rw [htail]
              have hright :
                  (xs.map factor).foldl (fun acc value => acc + value)
                      (factor x) =
                    factor x +
                      (xs.map factor).foldl
                        (fun acc value => acc + value) 0 := by
                simpa only [id] using
                  (foldl_add_initial (xs.map factor) (fun z => z)
                    (factor x))
              simp only [Rat.zero_add]
              rw [hright]
              grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.mul_assoc]

def finiteProductIntegralNestedSum :
    List (List (Rat × Rat)) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | cells :: restCells, factor :: restFactors =>
      (cells.map (fun cell =>
        cell.2 * factor cell.1 *
          finiteProductIntegralNestedSum restCells restFactors)).foldl
        (fun acc value => acc + value) 0
  | _, _ => 0

def finiteProductIntegralSum :
    List (List (Rat × Rat)) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | cells :: restCells, factor :: restFactors =>
      (cells.map (fun cell => cell.2 * factor cell.1)).foldl
          (fun acc value => acc + value) 0 *
        finiteProductIntegralSum restCells restFactors
  | _, _ => 0

/-! Public recursive presentation of a separable finite integral.  Exposing
the factor product lets downstream applications state the arbitrary-
dimensional factorization without unfolding the implementation. -/
def finiteProductIntegralFactorProduct :
    List (List (Rat × Rat)) -> List (Rat -> Rat) -> Rat
  | [], [] => 1
  | cells :: restCells, factor :: restFactors =>
      (cells.map (fun cell => cell.2 * factor cell.1)).foldl
          (fun acc value => acc + value) 0 *
        finiteProductIntegralFactorProduct restCells restFactors
  | _, _ => 0

theorem finiteProductIntegralSum_eq_factorProduct
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat)) :
    finiteProductIntegralSum samples factors =
      finiteProductIntegralFactorProduct samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> rfl
  | cons cells rest ih =>
      cases factors with
      | nil => rfl
      | cons factor restFactors =>
          simp only [finiteProductIntegralSum,
            finiteProductIntegralFactorProduct]
          rw [ih]

theorem finiteProductIntegralNestedSum_factorized
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat)) :
    finiteProductIntegralNestedSum samples factors =
      finiteProductIntegralSum samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> rfl
  | cons cells rest ih =>
      cases factors with
      | nil => rfl
      | cons factor restFactors =>
          simp only [finiteProductIntegralNestedSum, finiteProductIntegralSum]
          rw [foldl_add_map_mul_right_general cells
            (finiteProductIntegralNestedSum rest restFactors)
            (fun cell => cell.2 * factor cell.1)]
          rw [ih]

/-! The weighted form is the rectangle-integral interface: each sample carries
its rational cell width.  It is definitionally a separable product sum, so the
factorization theorem above supplies the algebraic multiple-integral law. -/

def finiteProductIntegralSum2D (xs ys : List (Rat × Rat))
    (f g : Rat -> Rat) : Rat :=
  finiteProductSum2D
    (xs.map (fun cell => cell.2 * f cell.1))
    (ys.map (fun cell => cell.2 * g cell.1))
    (fun value => value) (fun value => value)

theorem finiteProductIntegralSum2D_factorized
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat) :
    finiteProductIntegralSum2D xs ys f g =
      (xs.map (fun cell => cell.2 * f cell.1)).foldl
          (fun acc value => acc + value) 0 *
        (ys.map (fun cell => cell.2 * g cell.1)).foldl
          (fun acc value => acc + value) 0 := by
  simpa [finiteProductIntegralSum2D, Function.comp_def] using
    (finiteProductSum2D_factorized
      (xs.map (fun cell => cell.2 * f cell.1))
      (ys.map (fun cell => cell.2 * g cell.1))
      (fun value => value) (fun value => value))

private theorem foldl_add_nonneg {α : Type} (xs : List α)
    (term : α -> Rat) (initial : Rat) (hinitial : 0 <= initial)
    (hterm : forall x, x ∈ xs -> 0 <= term x) :
    0 <= xs.foldl (fun acc value => acc + term value) initial := by
  induction xs generalizing initial with
  | nil =>
      simpa using hinitial
  | cons x xs ih =>
      apply ih (initial := initial + term x)
      · exact Rat.add_nonneg hinitial (hterm x (by simp))
      · intro y hy
        exact hterm y (by simp [hy])

/-! Finite order preservation for a separable weighted rectangle sum.  This is
the positive-integrand fact used by later Gaussian and volume certificates. -/
theorem finiteProductIntegralSum2D_nonneg
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat)
    (hx : forall cell, cell ∈ xs -> 0 <= cell.2 * f cell.1)
    (hy : forall cell, cell ∈ ys -> 0 <= cell.2 * g cell.1) :
    0 <= finiteProductIntegralSum2D xs ys f g := by
  rw [finiteProductIntegralSum2D_factorized]
  apply Rat.mul_nonneg
  · apply foldl_add_nonneg
    · exact Rat.le_refl
    · intro value hvalue
      rcases List.mem_map.mp hvalue with ⟨cell, hcell, hvalue⟩
      simpa [hvalue] using hx cell hcell
  · apply foldl_add_nonneg
    · exact Rat.le_refl
    · intro value hvalue
      rcases List.mem_map.mp hvalue with ⟨cell, hcell, hvalue⟩
      simpa [hvalue] using hy cell hcell

/-! The same positivity argument scales to any finite number of separable
coordinates.  The hypotheses expose exactly the finite certificate needed by
the rectangular computation: cell widths are nonnegative and each sampled
factor is nonnegative. -/
theorem finiteProductIntegralNestedSum_nonneg
    (samples : List (List (Rat × Rat))) (factors : List (Rat -> Rat))
    (hwidth : forall cells, cells ∈ samples ->
      forall cell, cell ∈ cells -> 0 <= cell.2)
    (hfactor : forall factor, factor ∈ factors ->
      forall x, 0 <= factor x) :
    0 <= finiteProductIntegralNestedSum samples factors := by
  induction samples generalizing factors with
  | nil =>
      cases factors <;> simp [finiteProductIntegralNestedSum] <;> native_decide
  | cons cells rest ih =>
      cases factors with
      | nil =>
          simp [finiteProductIntegralNestedSum]
      | cons factor restFactors =>
          simp only [finiteProductIntegralNestedSum]
          apply foldl_add_nonneg
          · exact Rat.le_refl
          · intro value hvalue
            rcases List.mem_map.mp hvalue with ⟨cell, hcell, rfl⟩
            exact Rat.mul_nonneg
              (Rat.mul_nonneg
                (hwidth cells (by simp) cell hcell)
                (hfactor factor (by simp) cell.1))
              (ih
                  (factors := restFactors)
                  (by
                    intro cells' hcells' cell' hcell'
                    exact hwidth cells' (by simp [hcells']) cell' hcell')
              (by
                    intro factor' hfactor' x
                    exact hfactor factor' (by simp [hfactor']) x))

/-! Repeating one weighted coordinate rule across a finite number of axes is
the rectangular analogue of a product measure, but it is only list recursion:
there is no infinite product or measure construction here. -/

def repeatIntegralAxis (axis : List (Rat × Rat)) : Nat -> List (List (Rat × Rat))
  | 0 => []
  | count + 1 => axis :: repeatIntegralAxis axis count

theorem finiteProductIntegralFactorProduct_repeat_axis
    (axis : List (Rat × Rat)) (factor : Rat -> Rat) (dimension : Nat) :
    finiteProductIntegralFactorProduct
      (repeatIntegralAxis axis dimension)
      (List.replicate dimension factor) =
      ((axis.map (fun cell => cell.2 * factor cell.1)).foldl
        (fun acc value => acc + value) 0) ^ dimension := by
  induction dimension with
  | zero => simp [repeatIntegralAxis, finiteProductIntegralFactorProduct]
  | succ dimension ih =>
      simp only [repeatIntegralAxis, List.replicate_succ,
        finiteProductIntegralFactorProduct]
      rw [ih, Rat.pow_succ]
      grind [Rat.mul_comm]

theorem finiteProductIntegralNestedSum_repeat_axis_factorized
    (axis : List (Rat × Rat)) (factor : Rat -> Rat) (dimension : Nat) :
    finiteProductIntegralNestedSum
      (repeatIntegralAxis axis dimension)
  (List.replicate dimension factor) =
      ((axis.map (fun cell => cell.2 * factor cell.1)).foldl
        (fun acc value => acc + value) 0) ^ dimension := by
  rw [finiteProductIntegralNestedSum_factorized]
  rw [finiteProductIntegralSum_eq_factorProduct]
  exact finiteProductIntegralFactorProduct_repeat_axis axis factor dimension

/- A concrete weighted rectangular computation.  The two sample lists carry
cell widths, so this is a finite two-dimensional integral cell sum rather than
an unweighted Cartesian product. -/
theorem finiteProductIntegralSum2D_weighted_stage :
    finiteProductIntegralSum2D
      [(0, 1 / 2), (1, 1 / 2)]
      [(0, 1), (1, 1)]
      (fun x => x + 1) (fun y => 2 - y) = 9 / 2 := by
  native_decide

theorem finiteProductIntegralNestedSum_two_factor
    (xs ys : List (Rat × Rat)) (f g : Rat -> Rat) :
    finiteProductIntegralNestedSum [xs, ys] [f, g] =
      finiteProductIntegralSum2D xs ys f g := by
  rw [finiteProductIntegralNestedSum_factorized]
  rw [finiteProductIntegralSum2D_factorized]
  simp [finiteProductIntegralSum]

def gaussianProductModel (n : Nat) (oneDimensionalGaussian : Rat) : Rat :=
  oneDimensionalGaussian ^ n

private theorem rat_pow_add (q : Rat) (m n : Nat) :
    q ^ (m + n) = q ^ m * q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, Rat.pow_succ, ih, Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]

theorem gaussianProductModel_split (m n : Nat) (oneDimensionalGaussian : Rat) :
    gaussianProductModel (m + n) oneDimensionalGaussian =
      gaussianProductModel m oneDimensionalGaussian *
        gaussianProductModel n oneDimensionalGaussian := by
  unfold gaussianProductModel
  rw [rat_pow_add]

theorem finiteProductSum2D_separable_stage :
    finiteProductSum2D [0, 1, 2] [0, 1] (fun x => x + 1) (fun y => 2 - y) = 18 := by
  native_decide

theorem finiteProductSum2D_separable_stage_factorized :
    finiteProductSum2D [0, 1, 2] [0, 1] (fun x => x + 1) (fun y => 2 - y) =
      (([0, 1, 2].map (fun x => x + 1)).foldl (fun acc value => acc + value) 0) *
        (([0, 1].map (fun y => 2 - y)).foldl (fun acc value => acc + value) 0) := by
  native_decide

theorem nBallCoeff_zero : nBallCoeff 0 = 1 := by
  rfl

theorem nBallCoeff_one : nBallCoeff 1 = 2 := by
  rfl

theorem nBallCoeff_succ_two (n : Nat) :
    nBallCoeff (n + 2) = (2 : Rat) / (n + 2) * nBallCoeff n := by
  rfl

theorem nBallVolumeModel_zero (piApprox radius : Rat) :
    nBallVolumeModel 0 piApprox radius = 1 := by
  simp [nBallVolumeModel, nBallCoeff, nBallPiExponent]

theorem nBallVolumeModel_one (piApprox radius : Rat) :
    nBallVolumeModel 1 piApprox radius = 2 * radius := by
  unfold nBallVolumeModel nBallCoeff nBallPiExponent
  simp [Rat.pow_one, Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_two (piApprox radius : Rat) :
    nBallVolumeModel 2 piApprox radius = piApprox * radius ^ 2 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_three (piApprox radius : Rat) :
    nBallVolumeModel 3 piApprox radius =
      (4 / 3 : Rat) * piApprox * radius ^ 3 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_four (piApprox radius : Rat) :
    nBallVolumeModel 4 piApprox radius =
      (1 / 2 : Rat) * piApprox ^ 2 * radius ^ 4 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_five (piApprox radius : Rat) :
    nBallVolumeModel 5 piApprox radius =
      (8 / 15 : Rat) * piApprox ^ 2 * radius ^ 5 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_six (piApprox radius : Rat) :
    nBallVolumeModel 6 piApprox radius =
      (1 / 6 : Rat) * piApprox ^ 3 * radius ^ 6 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_seven (piApprox radius : Rat) :
    nBallVolumeModel 7 piApprox radius =
      (16 / 105 : Rat) * piApprox ^ 3 * radius ^ 7 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_eight (piApprox radius : Rat) :
    nBallVolumeModel 8 piApprox radius =
      (1 / 24 : Rat) * piApprox ^ 4 * radius ^ 8 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_nine (piApprox radius : Rat) :
    nBallVolumeModel 9 piApprox radius =
      (32 / 945 : Rat) * piApprox ^ 4 * radius ^ 9 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_ten (piApprox radius : Rat) :
    nBallVolumeModel 10 piApprox radius =
      (1 / 120 : Rat) * piApprox ^ 5 * radius ^ 10 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_eleven (piApprox radius : Rat) :
    nBallVolumeModel 11 piApprox radius =
      (64 / 10395 : Rat) * piApprox ^ 5 * radius ^ 11 := by
  have hc : nBallCoeff 11 = (64 / 10395 : Rat) := by
    native_decide
  unfold nBallVolumeModel nBallPiExponent
  rw [hc]

theorem nBallVolumeModel_twelve (piApprox radius : Rat) :
    nBallVolumeModel 12 piApprox radius =
      (1 / 720 : Rat) * piApprox ^ 6 * radius ^ 12 := by
  unfold nBallVolumeModel nBallPiExponent
  simp [nBallCoeff]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_thirteen (piApprox radius : Rat) :
    nBallVolumeModel 13 piApprox radius =
      (128 / 135135 : Rat) * piApprox ^ 6 * radius ^ 13 := by
  have hc : nBallCoeff 13 = (128 / 135135 : Rat) := by
    native_decide
  unfold nBallVolumeModel nBallPiExponent
  rw [hc]

theorem nBallVolumeModel_recurrence (n : Nat) (piApprox radius : Rat) :
    nBallVolumeModel (n + 2) piApprox radius =
      (2 * piApprox * radius * radius / (n + 2)) *
        nBallVolumeModel n piApprox radius := by
  unfold nBallVolumeModel nBallPiExponent
  have hexp : (n + 2) / 2 = n / 2 + 1 := by omega
  rw [nBallCoeff_succ_two, hexp, Rat.pow_succ]
  rw [rat_pow_add radius n 2]
  grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm]

theorem nBallVolumeModel_scale (n : Nat) (piApprox radius scale : Rat) :
    nBallVolumeModel n piApprox (radius * scale) =
      nBallVolumeModel n piApprox radius * scale ^ n := by
  unfold nBallVolumeModel
  have hpow : ∀ k : Nat, (radius * scale) ^ k = radius ^ k * scale ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Rat.pow_succ, ih, Rat.pow_succ, Rat.pow_succ]
        grind [Rat.mul_assoc, Rat.mul_comm]
  rw [hpow]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem nBallCoeff_nonneg : ∀ n, 0 <= nBallCoeff n := by
  have heven : ∀ k, 0 <= nBallCoeff (2 * k) := by
    intro k
    induction k with
    | zero =>
        native_decide
    | succ k ih =>
        have hindex : 2 * (k + 1) = 2 * k + 2 := by omega
        rw [hindex, nBallCoeff_succ_two]
        have hden : 0 < ((2 * k : Nat) : Rat) + 2 := by
          have hk : 0 <= (k : Rat) := Rat.natCast_nonneg
          grind
        have hfactor : 0 <= (2 : Rat) / ((2 * k : Nat) + 2) := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg (by native_decide)
            (Rat.le_of_lt ((Rat.inv_pos).2 hden))
        exact Rat.mul_nonneg hfactor ih
  have hodd : ∀ k, 0 <= nBallCoeff (2 * k + 1) := by
    intro k
    induction k with
    | zero =>
        native_decide
    | succ k ih =>
        have hindex : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
        rw [hindex, nBallCoeff_succ_two]
        have hden : 0 < ((2 * k + 1 : Nat) : Rat) + 2 := by
          have hk : 0 <= (k : Rat) := Rat.natCast_nonneg
          grind
        have hfactor : 0 <= (2 : Rat) / ((2 * k + 1 : Nat) + 2) := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg (by native_decide)
            (Rat.le_of_lt ((Rat.inv_pos).2 hden))
        exact Rat.mul_nonneg hfactor ih
  intro n
  by_cases he : n % 2 = 0
  · have hindex : n = 2 * (n / 2) := by omega
    rw [hindex]
    exact heven _
  · have hindex : n = 2 * (n / 2) + 1 := by omega
    rw [hindex]
    exact hodd _

theorem nBallVolumeModel_nonneg
    (n : Nat) {piApprox radius : Rat}
    (hpi : 0 <= piApprox) (hradius : 0 <= radius) :
    0 <= nBallVolumeModel n piApprox radius := by
  unfold nBallVolumeModel
  exact Rat.mul_nonneg
    (Rat.mul_nonneg (nBallCoeff_nonneg n)
      (Rat.pow_nonneg hpi))
    (Rat.pow_nonneg hradius)

private theorem rat_pow_le_pow_of_nonneg {a b : Rat}
    (ha : 0 <= a) (hab : a <= b) : forall k : Nat, a ^ k <= b ^ k
  | 0 => by simp
  | k + 1 => by
      rw [Rat.pow_succ, Rat.pow_succ]
      calc
        a ^ k * a <= b ^ k * a :=
          Rat.mul_le_mul_of_nonneg_right
            (rat_pow_le_pow_of_nonneg ha hab k) ha
        _ <= b ^ k * b :=
          Rat.mul_le_mul_of_nonneg_left hab (Rat.pow_nonneg (by grind))

/-! Refining either rational input refines the finite volume model.  This is
the order theorem used when a `piApprox` or radius is supplied by nested
rational intervals. -/
theorem nBallVolumeModel_mono
    (n : Nat) {pi₁ pi₂ r₁ r₂ : Rat}
    (hpi₁ : 0 <= pi₁) (hpi : pi₁ <= pi₂)
    (hr₁ : 0 <= r₁) (hr : r₁ <= r₂) :
    nBallVolumeModel n pi₁ r₁ <= nBallVolumeModel n pi₂ r₂ := by
  unfold nBallVolumeModel
  have hcoeff : 0 <= nBallCoeff n := nBallCoeff_nonneg n
  have hpi₂ : 0 <= pi₂ := Rat.le_trans hpi₁ hpi
  have hpiPow : pi₁ ^ nBallPiExponent n <= pi₂ ^ nBallPiExponent n :=
    rat_pow_le_pow_of_nonneg hpi₁ hpi _
  have hrPow : r₁ ^ n <= r₂ ^ n :=
    rat_pow_le_pow_of_nonneg hr₁ hr _
  have hpiFactor_le :
      nBallCoeff n * pi₁ ^ nBallPiExponent n <=
        nBallCoeff n * pi₂ ^ nBallPiExponent n := by
    exact Rat.mul_le_mul_of_nonneg_left hpiPow hcoeff
  calc
    nBallCoeff n * pi₁ ^ nBallPiExponent n * r₁ ^ n <=
        nBallCoeff n * pi₂ ^ nBallPiExponent n * r₁ ^ n :=
      Rat.mul_le_mul_of_nonneg_right hpiFactor_le (Rat.pow_nonneg hr₁)
    _ <= nBallCoeff n * pi₂ ^ nBallPiExponent n * r₂ ^ n :=
      Rat.mul_le_mul_of_nonneg_left hrPow
        (Rat.mul_nonneg hcoeff (Rat.pow_nonneg hpi₂))

/-! Monotonicity turns independent rational input boxes into a volume box.
The endpoint hypotheses are the finite domain certificate; no real-valued
evaluation is needed to propagate the enclosure. -/
def nBallVolumeModelInterval
    (n : Nat) (piBox radiusBox : QInterval) : QInterval :=
  { lo := nBallVolumeModel n piBox.lo radiusBox.lo
    hi := nBallVolumeModel n piBox.hi radiusBox.hi }

theorem nBallVolumeModelInterval_contains
    (n : Nat) (piBox radiusBox : QInterval)
    {pi radius : Rat}
    (hpi_lo_nonneg : 0 <= piBox.lo)
    (hpi : piBox.lo <= pi /\ pi <= piBox.hi)
    (hradius_lo_nonneg : 0 <= radiusBox.lo)
    (hradius : radiusBox.lo <= radius /\ radius <= radiusBox.hi) :
    (nBallVolumeModelInterval n piBox radiusBox).ContainsInterval
      { lo := nBallVolumeModel n pi radius
        hi := nBallVolumeModel n pi radius } := by
  unfold nBallVolumeModelInterval QInterval.ContainsInterval
  constructor
  · exact nBallVolumeModel_mono n hpi_lo_nonneg hpi.1
      hradius_lo_nonneg hradius.1
  · exact nBallVolumeModel_mono n (Rat.le_trans hpi_lo_nonneg hpi.1)
      hpi.2 (Rat.le_trans hradius_lo_nonneg hradius.1) hradius.2

theorem nBallVolumeModelInterval_ordered
    (n : Nat) (piBox radiusBox : QInterval)
    {pi radius : Rat}
    (hpi_lo_nonneg : 0 <= piBox.lo)
    (hpi : piBox.lo <= pi /\ pi <= piBox.hi)
    (hradius_lo_nonneg : 0 <= radiusBox.lo)
    (hradius : radiusBox.lo <= radius /\ radius <= radiusBox.hi) :
    (nBallVolumeModelInterval n piBox radiusBox).lo <=
      (nBallVolumeModelInterval n piBox radiusBox).hi := by
  have hcontains := nBallVolumeModelInterval_contains n piBox radiusBox
    hpi_lo_nonneg hpi hradius_lo_nonneg hradius
  exact Rat.le_trans hcontains.1 hcontains.2

theorem nBallVolumeModelInterval_nested
    (n : Nat) (outerPi outerRadius innerPi innerRadius : QInterval)
    (hpi_outer_nonneg : 0 <= outerPi.lo)
    (hpi_nested : outerPi.lo <= innerPi.lo /\ innerPi.hi <= outerPi.hi)
    (hpi_inner_ordered : innerPi.lo <= innerPi.hi)
    (hradius_outer_nonneg : 0 <= outerRadius.lo)
    (hradius_nested : outerRadius.lo <= innerRadius.lo /\
      innerRadius.hi <= outerRadius.hi)
    (hradius_inner_ordered : innerRadius.lo <= innerRadius.hi) :
    (nBallVolumeModelInterval n outerPi outerRadius).ContainsInterval
      (nBallVolumeModelInterval n innerPi innerRadius) := by
  unfold nBallVolumeModelInterval QInterval.ContainsInterval
  constructor
  · exact nBallVolumeModel_mono n hpi_outer_nonneg hpi_nested.1
      hradius_outer_nonneg hradius_nested.1
  · exact nBallVolumeModel_mono n
      (Rat.le_trans (Rat.le_trans hpi_outer_nonneg hpi_nested.1)
        hpi_inner_ordered)
      hpi_nested.2
      (Rat.le_trans (Rat.le_trans hradius_outer_nonneg hradius_nested.1)
        hradius_inner_ordered)
      hradius_nested.2

theorem nBallVolumeModel_stage_six :
    nBallVolumeModel 6 (355 / 113) 1 = 44738875 / 8657382 := by
  native_decide

theorem nBallVolumeModel_stage_seven :
    nBallVolumeModel 7 (355 / 113) 1 = 143164400 / 30300837 := by
  native_decide

theorem nBallVolumeModel_stage_ten :
    nBallVolumeModel 10 (355 / 113) 1 = 1127643344375 / 442184443032 := by
  native_decide

theorem nBallVolumeModel_stage_eleven :
    nBallVolumeModel 11 (355 / 113) 1 = 72169174040000 / 38304227377647 := by
  native_decide

theorem nBallVolumeModel_stage_twelve :
    nBallVolumeModel 12 (355 / 113) 1 =
      400313387253125 / 299801052375696 := by
  native_decide

theorem nBallVolumeModel_stage_thirteen :
    nBallVolumeModel 13 (355 / 113) 1 =
      51240113568400000 / 56268910017763443 := by
  native_decide

end ComputableAnalysis
