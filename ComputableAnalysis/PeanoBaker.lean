import ComputableAnalysis.Differential

/-!
# Finite Peano--Baker algebra

This module deliberately begins before a general continuous ODE theorem.  It
contains only finite rational data: matrices, sampled linear recurrences, and
the noncommutative word expansion underlying the Peano--Baker series.

For a continuous system, the words will be evaluated by iterated *certified*
integrals over ordered rational simplexes.  That analytic layer must provide
its own interval-enclosure, nesting, and tail certificates; this file does
not invoke a limit, an ambient matrix library, or completeness of the reals.
-/

namespace ComputableAnalysis

namespace LinearODE

/-- A finite-dimensional rational state vector.  The dimension is explicit so
that every later finite sum is an executable traversal of `Fin dimension`. -/
abbrev RatVector (dimension : Nat) := Fin dimension -> Rat

/-- A finite-dimensional rational matrix.  This is intentionally a local
definition, rather than an import of a general matrix theory. -/
abbrev RatMatrix (dimension : Nat) := Fin dimension -> Fin dimension -> Rat

def vectorZero (dimension : Nat) : RatVector dimension := fun _ => 0

def matrixZero (dimension : Nat) : RatMatrix dimension := fun _ _ => 0

def matrixIdentity (dimension : Nat) : RatMatrix dimension :=
  fun i j => if i = j then 1 else 0

def vectorAdd {dimension : Nat} (x y : RatVector dimension) : RatVector dimension :=
  fun i => x i + y i

def matrixAdd {dimension : Nat} (A B : RatMatrix dimension) : RatMatrix dimension :=
  fun i j => A i j + B i j

def matrixScale {dimension : Nat} (r : Rat) (A : RatMatrix dimension) :
    RatMatrix dimension :=
  fun i j => r * A i j

/-- The finite rational sum used by matrix multiplication and matrix action.
No infinite sum is hidden in this definition.  The recursive form keeps the
additivity proofs entirely in Lean's finite `Fin` layer. -/
def finiteSum : {dimension : Nat} -> (Fin dimension -> Rat) -> Rat
  | 0, _ => 0
  | _ + 1, f => f 0 + finiteSum (fun i => f i.succ)

theorem finiteSum_zero (dimension : Nat) :
    finiteSum (fun _ : Fin dimension => 0) = 0 := by
  induction dimension with
  | zero => simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem finiteSum_add {dimension : Nat} (f g : Fin dimension -> Rat) :
    finiteSum (fun i => f i + g i) = finiteSum f + finiteSum g := by
  induction dimension with
  | zero =>
      simp [finiteSum]
      grind [Rat.add_assoc, Rat.add_comm]
  | succ dimension ih =>
      simp [finiteSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem finiteSum_ite_eq {dimension : Nat} (j : Fin dimension) (f : Fin dimension -> Rat) :
    finiteSum (fun i => if i = j then f i else 0) = f j := by
  induction dimension with
  | zero => exact Fin.elim0 j
  | succ dimension ih =>
      refine Fin.cases ?_ ?_ j
      · have htail :
          finiteSum (fun i : Fin dimension => if i.succ = 0 then f i.succ else 0) = 0 := by
            rw [show (fun i : Fin dimension => if i.succ = 0 then f i.succ else 0) =
              (fun _ => 0) by
                funext i
                split
                · rename_i h
                  exact False.elim ((Fin.succ_ne_zero i) h)
                · rfl]
            exact finiteSum_zero dimension
        rw [finiteSum, htail]
        grind [Rat.add_assoc, Rat.add_comm]
      · intro j
        have hzero : ¬ ((0 : Fin (dimension + 1)) = j.succ) := by
          intro h
          exact (Fin.succ_ne_zero j) h.symm
        simp [finiteSum, ih, hzero]
        exact Rat.zero_add _

def matrixMul {dimension : Nat} (A B : RatMatrix dimension) : RatMatrix dimension :=
  fun i j => finiteSum (fun k => A i k * B k j)

def matrixApply {dimension : Nat} (A : RatMatrix dimension) (x : RatVector dimension) :
    RatVector dimension :=
  fun i => finiteSum (fun j => A i j * x j)

theorem vectorAdd_zero_right {dimension : Nat} (x : RatVector dimension) :
    vectorAdd x (vectorZero dimension) = x := by
  funext i
  exact Rat.add_zero _

theorem vectorAdd_assoc {dimension : Nat} (x y z : RatVector dimension) :
    vectorAdd (vectorAdd x y) z = vectorAdd x (vectorAdd y z) := by
  funext i
  exact Rat.add_assoc _ _ _

theorem matrixApply_zero {dimension : Nat} (A : RatMatrix dimension) :
    matrixApply A (vectorZero dimension) = vectorZero dimension := by
  funext i
  unfold matrixApply vectorZero
  rw [show (fun j => A i j * 0) = (fun _ => 0) by
    funext j
    exact Rat.mul_zero _]
  exact finiteSum_zero dimension

theorem matrixApply_vectorAdd {dimension : Nat}
    (A : RatMatrix dimension) (x y : RatVector dimension) :
    matrixApply A (vectorAdd x y) =
      vectorAdd (matrixApply A x) (matrixApply A y) := by
  funext i
  unfold matrixApply vectorAdd
  calc
    finiteSum (fun j => A i j * (x j + y j)) =
        finiteSum (fun j => A i j * x j + A i j * y j) := by
          congr 1
          funext j
          exact Rat.mul_add _ _ _
    _ = finiteSum (fun j => A i j * x j) +
        finiteSum (fun j => A i j * y j) :=
      finiteSum_add _ _

theorem matrixAdd_zero_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixAdd (matrixZero dimension) A = A := by
  funext i j
  exact Rat.zero_add _

theorem matrixAdd_zero_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixAdd A (matrixZero dimension) = A := by
  funext i j
  exact Rat.add_zero _

theorem matrixAdd_assoc {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixAdd (matrixAdd A B) C = matrixAdd A (matrixAdd B C) := by
  funext i j
  exact Rat.add_assoc _ _ _

theorem matrixMul_zero_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul A (matrixZero dimension) = matrixZero dimension := by
  funext i j
  unfold matrixMul matrixZero
  rw [show (fun k => A i k * 0) = (fun _ => 0) by
    funext k
    exact Rat.mul_zero _]
  exact finiteSum_zero dimension

theorem matrixMul_add_left {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul (matrixAdd A B) C = matrixAdd (matrixMul A C) (matrixMul B C) := by
  funext i j
  unfold matrixMul matrixAdd
  calc
    finiteSum (fun k => (A i k + B i k) * C k j) =
        finiteSum (fun k => A i k * C k j + B i k * C k j) := by
          congr 1
          funext k
          exact Rat.add_mul _ _ _
    _ = finiteSum (fun k => A i k * C k j) +
        finiteSum (fun k => B i k * C k j) :=
          finiteSum_add _ _

theorem matrixMul_add_right {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul A (matrixAdd B C) = matrixAdd (matrixMul A B) (matrixMul A C) := by
  funext i j
  unfold matrixMul matrixAdd
  calc
    finiteSum (fun k => A i k * (B k j + C k j)) =
        finiteSum (fun k => A i k * B k j + A i k * C k j) := by
          congr 1
          funext k
          exact Rat.mul_add _ _ _
    _ = finiteSum (fun k => A i k * B k j) +
        finiteSum (fun k => A i k * C k j) :=
          finiteSum_add _ _

theorem finiteSum_ite_eq_left {dimension : Nat} (j : Fin dimension)
    (f : Fin dimension -> Rat) :
    finiteSum (fun i => if j = i then f i else 0) = f j := by
  calc
    finiteSum (fun i => if j = i then f i else 0) =
        finiteSum (fun i => if i = j then f i else 0) := by
          congr 1
          funext i
          split
          · rename_i h
            have h' : i = j := h.symm
            exact (if_pos h').symm
          · rename_i h
            have h' : ¬ i = j := by
              intro h'
              exact h h'.symm
            exact (if_neg h').symm
    _ = f j := finiteSum_ite_eq j f

theorem matrixMul_identity_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul (matrixIdentity dimension) A = A := by
  funext i j
  unfold matrixMul matrixIdentity
  calc
    finiteSum (fun k => (if i = k then 1 else 0) * A k j) =
        finiteSum (fun k => if i = k then A k j else 0) := by
          congr 1
          funext k
          split
          · rename_i h
            exact Rat.one_mul _
          · rename_i h
            exact Rat.zero_mul _
    _ = A i j := finiteSum_ite_eq_left i (fun k => A k j)

/-- A sampled, possibly inhomogeneous, linear recurrence
`x_(k+1) = step(k) * x_k + forcing(k)`.  For an Euler discretization of
`x' = A(t)x+b(t)`, use `step(k) = I + h A(t_k)` and
`forcing(k) = h b(t_k)`. -/
structure DiscreteLinearSystem (dimension : Nat) where
  step : Nat -> RatMatrix dimension
  forcing : Nat -> RatVector dimension

namespace DiscreteLinearSystem

def trajectory (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    Nat -> RatVector dimension
  | 0 => initial
  | n + 1 => vectorAdd
      (matrixApply (system.step n) (trajectory system initial n))
      (system.forcing n)

theorem trajectory_zero (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) :
    system.trajectory initial 0 = initial := rfl

theorem trajectory_succ (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (n : Nat) :
    system.trajectory initial (n + 1) =
      vectorAdd (matrixApply (system.step n) (system.trajectory initial n))
        (system.forcing n) := rfl

/-- The homogeneous part of a sampled linear system, retaining the literal
time order of the successive matrix actions. -/
def homogeneousTrajectory (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) : Nat -> RatVector dimension
  | 0 => initial
  | n + 1 => matrixApply (system.step n)
      (homogeneousTrajectory system initial n)

theorem homogeneousTrajectory_zero (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) :
    system.homogeneousTrajectory initial 0 = initial := rfl

theorem homogeneousTrajectory_succ (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (n : Nat) :
    system.homogeneousTrajectory initial (n + 1) =
      matrixApply (system.step n) (system.homogeneousTrajectory initial n) := rfl

/-- Exact finite variation of constants for a sampled linear system.

The second summand is the trajectory from zero initial data, so its recursion
is the chronological finite Duhamel sum of the forcing samples.  This proof
uses only finite rational matrix actions; no limiting ODE theorem is hidden in
the statement. -/
theorem trajectory_eq_homogeneous_add_zeroInitial
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    forall n,
      system.trajectory initial n =
        vectorAdd (system.homogeneousTrajectory initial n)
          (system.trajectory (vectorZero dimension) n)
  | 0 => by
      unfold trajectory homogeneousTrajectory vectorAdd vectorZero
      funext i
      exact (Rat.add_zero _).symm
  | n + 1 => by
      change
        vectorAdd (matrixApply (system.step n) (system.trajectory initial n))
            (system.forcing n) =
          vectorAdd
            (matrixApply (system.step n)
              (system.homogeneousTrajectory initial n))
            (vectorAdd
              (matrixApply (system.step n)
                (system.trajectory (vectorZero dimension) n))
              (system.forcing n))
      rw [trajectory_eq_homogeneous_add_zeroInitial system initial n]
      rw [matrixApply_vectorAdd]
      exact vectorAdd_assoc _ _ _

/-- A sampled system has no inhomogeneous contribution when every forcing
sample is the zero vector. -/
def ForcingZero (system : DiscreteLinearSystem dimension) : Prop :=
  forall k, system.forcing k = vectorZero dimension

theorem trajectory_zeroInitial_of_forcingZero
    (system : DiscreteLinearSystem dimension) (hzero : system.ForcingZero) :
    forall n, system.trajectory (vectorZero dimension) n = vectorZero dimension
  | 0 => rfl
  | n + 1 => by
      change
        vectorAdd (matrixApply (system.step n)
            (system.trajectory (vectorZero dimension) n))
          (system.forcing n) = vectorZero dimension
      rw [trajectory_zeroInitial_of_forcingZero system hzero n, hzero n,
        matrixApply_zero]
      funext i
      exact Rat.zero_add _

theorem trajectory_eq_homogeneous_of_forcingZero
    (system : DiscreteLinearSystem dimension) (hzero : system.ForcingZero)
    (initial : RatVector dimension) (n : Nat) :
    system.trajectory initial n = system.homogeneousTrajectory initial n := by
  rw [trajectory_eq_homogeneous_add_zeroInitial]
  rw [trajectory_zeroInitial_of_forcingZero system hzero n]
  exact vectorAdd_zero_right _

/-- The constant-coefficient discrete specialization. -/
def ConstantStep (system : DiscreteLinearSystem dimension) : Prop :=
  forall k, system.step k = system.step 0

/-- The commuting-coefficient discrete specialization.  This is the exact
finite hypothesis behind collapsing a time-ordered product to an ordinary
exponential later on. -/
def PairwiseCommutingSteps (system : DiscreteLinearSystem dimension) : Prop :=
  forall i j, matrixMul (system.step i) (system.step j) =
    matrixMul (system.step j) (system.step i)

end DiscreteLinearSystem

/-- All strictly time-ordered selections from the first `steps` sample times.

The newest selected time is put on the left.  Thus `[3, 1, 0]` denotes the
ordered product `B_3 * B_1 * B_0`, the order required for a noncommuting
linear system. -/
def orderedIndexWords : Nat -> List (List Nat)
  | 0 => [[]]
  | n + 1 => orderedIndexWords n ++
    (orderedIndexWords n).map (fun word => n :: word)

/-- Finite addition of matrices, kept recursive so it is visibly executable. -/
def matrixListSum {dimension : Nat} : List (RatMatrix dimension) -> RatMatrix dimension
  | [] => matrixZero dimension
  | A :: rest => matrixAdd A (matrixListSum rest)

theorem matrixListSum_append {dimension : Nat} (xs ys : List (RatMatrix dimension)) :
    matrixListSum (xs ++ ys) = matrixAdd (matrixListSum xs) (matrixListSum ys) := by
  induction xs with
  | nil =>
      simp only [List.nil_append, matrixListSum]
      exact (matrixAdd_zero_left _).symm
  | cons A xs ih =>
      simp only [List.cons_append, matrixListSum]
      rw [ih, matrixAdd_assoc]

theorem matrixMul_matrixListSum {dimension : Nat} (B : RatMatrix dimension) :
    forall xs : List (RatMatrix dimension),
      matrixMul B (matrixListSum xs) = matrixListSum (xs.map (matrixMul B)) := by
  intro xs
  induction xs with
  | nil =>
      simp [matrixListSum, matrixMul_zero_right]
  | cons A xs ih =>
      simp only [matrixListSum, List.map_cons]
      rw [matrixMul_add_right, ih]

/-- Evaluate one time-ordered word in a rational matrix sequence. -/
def timeOrderedProduct {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    List Nat -> RatMatrix dimension
  | [] => matrixIdentity dimension
  | k :: rest => matrixMul (B k) (timeOrderedProduct B rest)

/-- The finite, noncommutative Peano--Baker expansion.  It has one term for
every ordered subset of the sampled times.  A continuous Peano--Baker series
will replace each word by an iterated simplex integral. -/
def peanoBakerDiscreteSum {dimension : Nat} (B : Nat -> RatMatrix dimension) (steps : Nat) :
    RatMatrix dimension :=
  matrixListSum ((orderedIndexWords steps).map (timeOrderedProduct B))

/-- The corresponding chronological product of Euler step matrices. -/
def chronologicalProduct {dimension : Nat} (B : Nat -> RatMatrix dimension) : Nat ->
    RatMatrix dimension
  | 0 => matrixIdentity dimension
  | n + 1 => matrixMul (matrixAdd (matrixIdentity dimension) (B n))
      (chronologicalProduct B n)

/-- Natural powers of a matrix, with the newest factor on the left.  This is
the exact constant-step specialization of a chronological product. -/
def matrixPow {dimension : Nat} (A : RatMatrix dimension) : Nat -> RatMatrix dimension
  | 0 => matrixIdentity dimension
  | n + 1 => matrixMul A (matrixPow A n)

theorem matrixPow_identity {dimension : Nat} :
    forall n, matrixPow (matrixIdentity dimension) n = matrixIdentity dimension
  | 0 => rfl
  | n + 1 => by
      rw [matrixPow, matrixPow_identity n, matrixMul_identity_left]

/-- When all Euler increments are the same matrix `B`, time ordering reduces
to the finite power `(I + B)^N`. -/
theorem chronologicalProduct_constant {dimension : Nat} (B : RatMatrix dimension) :
    forall steps,
      chronologicalProduct (fun _ => B) steps =
        matrixPow (matrixAdd (matrixIdentity dimension) B) steps
  | 0 => rfl
  | steps + 1 => by
      change
        matrixMul (matrixAdd (matrixIdentity dimension) B)
            (chronologicalProduct (fun _ => B) steps) =
          matrixMul (matrixAdd (matrixIdentity dimension) B)
            (matrixPow (matrixAdd (matrixIdentity dimension) B) steps)
      rw [chronologicalProduct_constant B steps]

theorem peanoBakerDiscreteSum_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    peanoBakerDiscreteSum B (steps + 1) =
      matrixAdd (peanoBakerDiscreteSum B steps)
        (matrixMul (B steps) (peanoBakerDiscreteSum B steps)) := by
  unfold peanoBakerDiscreteSum
  rw [orderedIndexWords, List.map_append, matrixListSum_append]
  have hmap :
      ((orderedIndexWords steps).map (fun word => steps :: word)).map (timeOrderedProduct B) =
        ((orderedIndexWords steps).map (timeOrderedProduct B)).map (matrixMul (B steps)) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [hmap]
  rw [← matrixMul_matrixListSum]

theorem chronologicalProduct_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    chronologicalProduct B (steps + 1) =
      matrixAdd (chronologicalProduct B steps)
        (matrixMul (B steps) (chronologicalProduct B steps)) := by
  change matrixMul (matrixAdd (matrixIdentity dimension) (B steps))
      (chronologicalProduct B steps) = _
  rw [matrixMul_add_left, matrixMul_identity_left]

/-- The finite Peano--Baker identity, kept as a named proposition so that
continuous constructions can depend on the algebraic result separately. -/
def DiscretePeanoBakerExpansion {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall steps, chronologicalProduct B steps = peanoBakerDiscreteSum B steps

theorem discretePeanoBakerExpansion {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    DiscretePeanoBakerExpansion B := by
  intro steps
  induction steps with
  | zero =>
      change matrixIdentity dimension = matrixAdd (matrixIdentity dimension) (matrixZero dimension)
      funext i j
      exact (Rat.add_zero _).symm
  | succ steps ih =>
      rw [chronologicalProduct_succ, ih, peanoBakerDiscreteSum_succ]

/-- Constant Euler increments give the familiar finite constant-coefficient
Peano--Baker formula `(I + B)^N`. -/
theorem peanoBakerDiscreteSum_constant {dimension : Nat} (B : RatMatrix dimension)
    (steps : Nat) :
    peanoBakerDiscreteSum (fun _ => B) steps =
      matrixPow (matrixAdd (matrixIdentity dimension) B) steps := by
  rw [← discretePeanoBakerExpansion]
  exact chronologicalProduct_constant B steps

/-- The zero coefficient has the identity as its finite Peano--Baker state
transition at every number of sample steps. -/
theorem peanoBakerDiscreteSum_zeroCoefficient {dimension : Nat} (steps : Nat) :
    peanoBakerDiscreteSum (fun _ => matrixZero dimension) steps =
      matrixIdentity dimension := by
  rw [peanoBakerDiscreteSum_constant]
  rw [matrixAdd_zero_right, matrixPow_identity]

@[simp] theorem orderedIndexWords_zero : orderedIndexWords 0 = [[]] := rfl

@[simp] theorem orderedIndexWords_one : orderedIndexWords 1 = [[], [0]] := rfl

@[simp] theorem orderedIndexWords_two :
    orderedIndexWords 2 = [[], [0], [1], [1, 0]] := rfl

@[simp] theorem timeOrderedProduct_nil {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    timeOrderedProduct B [] = matrixIdentity dimension := rfl

/-- The enumerator has exactly `2^steps` finite terms. -/
theorem orderedIndexWords_length (steps : Nat) :
    (orderedIndexWords steps).length = 2 ^ steps := by
  induction steps with
  | zero => native_decide
  | succ steps ih =>
      rw [orderedIndexWords, List.length_append, List.length_map, ih]
      omega

/-- The first three Peano--Baker expansions are executable definitions. They
exhibit the necessary noncommutative order used by the general theorem. -/
@[simp] theorem peanoBakerDiscreteSum_zero {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 0 =
      matrixAdd (matrixIdentity dimension) (matrixZero dimension) := rfl

@[simp] theorem peanoBakerDiscreteSum_one {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 1 = matrixAdd (matrixIdentity dimension)
      (matrixAdd (matrixMul (B 0) (matrixIdentity dimension)) (matrixZero dimension)) := rfl

@[simp] theorem peanoBakerDiscreteSum_two {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    peanoBakerDiscreteSum B 2 =
      matrixAdd (matrixIdentity dimension)
        (matrixAdd (matrixMul (B 0) (matrixIdentity dimension))
          (matrixAdd (matrixMul (B 1) (matrixIdentity dimension))
            (matrixAdd (matrixMul (B 1)
              (matrixMul (B 0) (matrixIdentity dimension))) (matrixZero dimension)))) := rfl

/-- Common-domain input data for the continuous linear system
`x' = A(t)x+b(t)`.  Entries are the existing interval-certified scalar
functions, so no completed real-valued function space is assumed. -/
structure IntervalLinearSystem (dimension : Nat) (lower upper : Rat) where
  coefficient : Fin dimension -> Fin dimension -> FunctionOnInterval
  forcing : Fin dimension -> FunctionOnInterval
  coefficient_interval : forall i j,
    (coefficient i j).lower = lower /\ (coefficient i j).upper = upper
  forcing_interval : forall i,
    (forcing i).lower = lower /\ (forcing i).upper = upper

/-- The regularity obligation needed before constructing componentwise
simplex-integral boxes for the continuous Peano--Baker series. -/
def IntervalLinearSystem.CoefficientsRegular
    (system : IntervalLinearSystem dimension lower upper) : Prop :=
  (forall i j, Nonempty (IntervalRegularOn (system.coefficient i j))) /\
  (forall i, Nonempty (IntervalRegularOn (system.forcing i)))

end LinearODE

end ComputableAnalysis
