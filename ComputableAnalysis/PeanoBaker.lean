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

theorem finiteSum_mul_left {dimension : Nat} (a : Rat) (f : Fin dimension -> Rat) :
    a * finiteSum f = finiteSum (fun i => a * f i) := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih, Rat.mul_add]

theorem finiteSum_mul_right {dimension : Nat} (a : Rat) (f : Fin dimension -> Rat) :
    finiteSum f * a = finiteSum (fun i => f i * a) := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp [finiteSum, ih, Rat.add_mul]

/-- Finite rational sums may be enumerated in either order.  This is the
local Fubini calculation used to prove associativity of the project-local
matrix product; it is only a double traversal of finite index types. -/
theorem finiteSum_swap :
    forall (m n : Nat) (f : Fin m -> Fin n -> Rat),
      finiteSum (fun i => finiteSum (f i)) =
        finiteSum (fun j => finiteSum (fun i => f i j))
  | 0, n, _ => by
      change 0 = finiteSum (fun _ : Fin n => 0)
      exact (finiteSum_zero n).symm
  | m + 1, n, f => by
      simp only [finiteSum]
      rw [finiteSum_swap m n (fun i j => f i.succ j)]
      rw [← finiteSum_add]

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

/-- Associativity of the local rational matrix product.  This is proved from
finite distributivity and the finite-sum interchange above, without importing
a general matrix library. -/
theorem matrixMul_assoc {dimension : Nat} (A B C : RatMatrix dimension) :
    matrixMul (matrixMul A B) C = matrixMul A (matrixMul B C) := by
  funext i j
  unfold matrixMul
  calc
    finiteSum (fun k =>
        finiteSum (fun l => A i l * B l k) * C k j) =
        finiteSum (fun k =>
          finiteSum (fun l => (A i l * B l k) * C k j)) := by
            congr 1
            funext k
            exact finiteSum_mul_right (C k j) (fun l => A i l * B l k)
    _ = finiteSum (fun l =>
          finiteSum (fun k => (A i l * B l k) * C k j)) :=
        finiteSum_swap dimension dimension
          (fun k l => (A i l * B l k) * C k j)
    _ = finiteSum (fun k =>
          A i k * finiteSum (fun l => B k l * C l j)) := by
            congr 1
            funext k
            calc
              finiteSum (fun l => (A i k * B k l) * C l j) =
                  finiteSum (fun l => A i k * (B k l * C l j)) := by
                    congr 1
                    funext l
                    exact Rat.mul_assoc _ _ _
              _ = A i k * finiteSum (fun l => B k l * C l j) :=
                (finiteSum_mul_left (A i k) (fun l => B k l * C l j)).symm

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

/-- The identity matrix acts as the identity on a finite rational vector. -/
theorem matrixApply_identity {dimension : Nat} (x : RatVector dimension) :
    matrixApply (matrixIdentity dimension) x = x := by
  funext i
  unfold matrixApply matrixIdentity
  calc
    finiteSum (fun j => (if i = j then 1 else 0) * x j) =
        finiteSum (fun j => if j = i then x j else 0) := by
          congr 1
          funext j
          by_cases h : j = i
          · subst j
            simp
          · have h' : ¬ i = j := by
              intro hij
              exact h hij.symm
            simp [h, h']
    _ = x i :=
      finiteSum_ite_eq i x

/-- Matrix action respects the project-local finite matrix product.  This is
the finite reassociation used to turn a homogeneous recurrence into one
chronological transition matrix. -/
theorem matrixApply_matrixMul {dimension : Nat}
    (A B : RatMatrix dimension) (x : RatVector dimension) :
    matrixApply (matrixMul A B) x =
      matrixApply A (matrixApply B x) := by
  funext i
  unfold matrixApply matrixMul
  calc
    finiteSum (fun j => finiteSum (fun k => A i k * B k j) * x j) =
        finiteSum (fun j => finiteSum (fun k => (A i k * B k j) * x j)) := by
          congr 1
          funext j
          rw [finiteSum_mul_right]
    _ = finiteSum (fun k => finiteSum (fun j => (A i k * B k j) * x j)) :=
      finiteSum_swap dimension dimension
        (fun j k => (A i k * B k j) * x j)
    _ = finiteSum (fun k => A i k * finiteSum (fun j => B k j * x j)) := by
          congr 1
          funext k
          calc
            finiteSum (fun j => (A i k * B k j) * x j) =
                finiteSum (fun j => A i k * (B k j * x j)) := by
                  congr 1
                  funext j
                  exact Rat.mul_assoc _ _ _
            _ = A i k * finiteSum (fun j => B k j * x j) :=
              (finiteSum_mul_left (A i k) (fun j => B k j * x j)).symm

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

theorem matrixMul_identity_right {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul A (matrixIdentity dimension) = A := by
  funext i j
  unfold matrixMul matrixIdentity
  calc
    finiteSum (fun k => A i k * (if k = j then 1 else 0)) =
        finiteSum (fun k => if k = j then A i k else 0) := by
          congr 1
          funext k
          split
          · rename_i h
            exact Rat.mul_one _
          · rename_i h
            exact Rat.mul_zero _
    _ = A i j := finiteSum_ite_eq j (fun k => A i k)

theorem matrixMul_zero_left {dimension : Nat} (A : RatMatrix dimension) :
    matrixMul (matrixZero dimension) A = matrixZero dimension := by
  funext i j
  unfold matrixMul matrixZero
  rw [show (fun k => 0 * A k j) = (fun _ => 0) by
    funext k
    exact Rat.zero_mul _]
  exact finiteSum_zero dimension

/-- The exact transition matrix of a sampled linear recurrence, starting at a
given index and taking a prescribed number of chronological updates.  The
newest sample occurs on the left, so this convention agrees with the
Peano--Baker word order. -/
def chronologicalStepProduct {dimension : Nat} (S : Nat -> RatMatrix dimension)
    (start : Nat) : Nat -> RatMatrix dimension
  | 0 => matrixIdentity dimension
  | steps + 1 =>
      matrixMul (S (start + steps))
        (chronologicalStepProduct S start steps)

@[simp] theorem chronologicalStepProduct_zero {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start : Nat) :
    chronologicalStepProduct S start 0 = matrixIdentity dimension := rfl

@[simp] theorem chronologicalStepProduct_succ {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start steps : Nat) :
    chronologicalStepProduct S start (steps + 1) =
      matrixMul (S (start + steps))
        (chronologicalStepProduct S start steps) := rfl

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

/-- A candidate solution of the sampled inhomogeneous recurrence.  Stating the
recurrence separately from the recursive evaluator makes finite uniqueness a
checked theorem rather than a property of one chosen implementation. -/
structure SolvesRecurrence (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (candidate : Nat -> RatVector dimension) : Prop where
  initial_eq : candidate 0 = initial
  step_eq : forall n,
    candidate (n + 1) =
      vectorAdd (matrixApply (system.step n) (candidate n))
        (system.forcing n)

/-- A candidate solution of the homogeneous sampled recurrence.  This is the
finite rational core of the zero-initial uniqueness argument used later for
linear Peano--Baker systems. -/
structure SolvesHomogeneousRecurrence (system : DiscreteLinearSystem dimension)
    (initial : RatVector dimension) (candidate : Nat -> RatVector dimension) : Prop where
  initial_eq : candidate 0 = initial
  step_eq : forall n,
    candidate (n + 1) =
      matrixApply (system.step n) (candidate n)

/-- The recursive evaluator is a solution of its sampled recurrence. -/
theorem trajectory_solvesRecurrence
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    system.SolvesRecurrence initial (system.trajectory initial) :=
  { initial_eq := rfl
    step_eq := fun _ => rfl }

/-- The recursive homogeneous evaluator is a solution of the homogeneous
sampled recurrence. -/
theorem homogeneousTrajectory_solvesHomogeneousRecurrence
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    system.SolvesHomogeneousRecurrence initial
      (system.homogeneousTrajectory initial) :=
  { initial_eq := rfl
    step_eq := fun _ => rfl }

/-- Finite uniqueness for a sampled inhomogeneous linear system.  The proof is
induction over a finite list of rational matrix updates; it invokes neither a
limit nor an inverse transition matrix. -/
theorem solvesRecurrence_eq_trajectory
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesRecurrence initial candidate) :
    forall n, candidate n = system.trajectory initial n
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n, trajectory_succ,
        solvesRecurrence_eq_trajectory system initial candidate hsolution n]

/-- Finite uniqueness for the homogeneous sampled recurrence. -/
theorem solvesHomogeneousRecurrence_eq_homogeneousTrajectory
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesHomogeneousRecurrence initial candidate) :
    forall n, candidate n = system.homogeneousTrajectory initial n
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n, homogeneousTrajectory_succ,
        solvesHomogeneousRecurrence_eq_homogeneousTrajectory
          system initial candidate hsolution n]

/-- The exact zero-initial homogeneous uniqueness certificate.  This is the
finite form of the comparison step for two candidate continuous solutions:
their difference has zero initial data, and a later enclosure argument must
pass this finite conclusion through refining sampled systems. -/
theorem solvesHomogeneousRecurrence_zero
    (system : DiscreteLinearSystem dimension) (candidate : Nat -> RatVector dimension)
    (hsolution : system.SolvesHomogeneousRecurrence
      (vectorZero dimension) candidate) :
    forall n, candidate n = vectorZero dimension
  | 0 => hsolution.initial_eq
  | n + 1 => by
      rw [hsolution.step_eq n,
        solvesHomogeneousRecurrence_zero system candidate hsolution n,
        matrixApply_zero]

/-- A homogeneous sampled trajectory is the action of its exact
chronological transition matrix on the initial state. -/
theorem homogeneousTrajectory_eq_chronologicalStepProduct
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory initial n =
        matrixApply (chronologicalStepProduct system.step 0 n) initial
  | 0 => by
      exact (matrixApply_identity initial).symm
  | n + 1 => by
      rw [homogeneousTrajectory_succ, chronologicalStepProduct_succ]
      simp only [Nat.zero_add]
      rw [homogeneousTrajectory_eq_chronologicalStepProduct system initial n]
      exact (matrixApply_matrixMul _ _ _).symm

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

/-- Exact finite variation of constants with the homogeneous term displayed
as its chronological transition matrix. -/
theorem trajectory_eq_transition_add_zeroInitial
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (system.trajectory (vectorZero dimension) n) := by
  rw [trajectory_eq_homogeneous_add_zeroInitial]
  rw [homogeneousTrajectory_eq_chronologicalStepProduct system initial n]

/-- The literal finite sum of a vector-valued sequence.  It is kept separate
from matrix sums because the inhomogeneous Peano--Baker formula transports
forcing *vectors*, not additional matrices. -/
def vectorSequenceSum {dimension : Nat} (f : Nat -> RatVector dimension) :
    Nat -> RatVector dimension
  | 0 => vectorZero dimension
  | n + 1 => vectorAdd (vectorSequenceSum f n) (f n)

theorem vectorSequenceSum_congr_on {dimension : Nat}
    (f g : Nat -> RatVector dimension) :
    forall n, (forall k, k < n -> f k = g k) ->
      vectorSequenceSum f n = vectorSequenceSum g n
  | 0, _ => rfl
  | n + 1, h => by
      rw [vectorSequenceSum, vectorSequenceSum,
        vectorSequenceSum_congr_on f g n (fun k hk => h k (by omega)),
        h n (by omega)]

theorem matrixApply_vectorSequenceSum {dimension : Nat}
    (A : RatMatrix dimension) (f : Nat -> RatVector dimension) :
    forall n,
      matrixApply A (vectorSequenceSum f n) =
        vectorSequenceSum (fun k => matrixApply A (f k)) n
  | 0 => by
      change matrixApply A (vectorZero dimension) = vectorZero dimension
      exact matrixApply_zero A
  | n + 1 => by
      change matrixApply A (vectorAdd (vectorSequenceSum f n) (f n)) =
        vectorAdd (vectorSequenceSum (fun k => matrixApply A (f k)) n)
          (matrixApply A (f n))
      rw [matrixApply_vectorAdd, matrixApply_vectorSequenceSum A f n]

/-- The transition carrying the forcing sample at time `k` to the final
sample time `final`.  The first step after the force is `k + 1`; hence a
force applied at the final step itself is transported by the identity. -/
def forcingTransition (system : DiscreteLinearSystem dimension)
    (final k : Nat) : RatMatrix dimension :=
  chronologicalStepProduct system.step (k + 1) (final - (k + 1))

/-- The `k`th time-ordered forcing contribution to the state at `final`. -/
def duhamelTerm (system : DiscreteLinearSystem dimension)
    (final k : Nat) : RatVector dimension :=
  matrixApply (forcingTransition system final k) (system.forcing k)

/-- The finite Duhamel sum for the zero-initial sampled system:
`∑_{k < N} S_{N-1} ⋯ S_{k+1} g_k`.  Every factor is a literal
rational transition product; no continuous integral or limiting argument is
hidden in this definition. -/
def duhamelSum (system : DiscreteLinearSystem dimension) (final : Nat) :
    RatVector dimension :=
  vectorSequenceSum (duhamelTerm system final) final

private theorem forcingTransition_succ
    (system : DiscreteLinearSystem dimension) (n k : Nat) (hk : k < n) :
    forcingTransition system (n + 1) k =
      matrixMul (system.step n) (forcingTransition system n k) := by
  unfold forcingTransition
  have hlength : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by
    omega
  have hindex : k + 1 + (n - (k + 1)) = n := by
    exact Nat.add_sub_of_le (by omega)
  rw [hlength, chronologicalStepProduct_succ]
  rw [hindex]

private theorem duhamelTerm_succ
    (system : DiscreteLinearSystem dimension) (n k : Nat) (hk : k < n) :
    duhamelTerm system (n + 1) k =
      matrixApply (system.step n) (duhamelTerm system n k) := by
  unfold duhamelTerm
  rw [forcingTransition_succ system n k hk, matrixApply_matrixMul]

private theorem duhamelTerm_latest
    (system : DiscreteLinearSystem dimension) (n : Nat) :
    duhamelTerm system (n + 1) n = system.forcing n := by
  unfold duhamelTerm forcingTransition
  simp [matrixApply_identity]

private theorem duhamelSum_prefix_succ
    (system : DiscreteLinearSystem dimension) (n : Nat) :
    vectorSequenceSum (duhamelTerm system (n + 1)) n =
      matrixApply (system.step n) (duhamelSum system n) := by
  calc
    vectorSequenceSum (duhamelTerm system (n + 1)) n =
        vectorSequenceSum
          (fun k => matrixApply (system.step n) (duhamelTerm system n k)) n :=
      vectorSequenceSum_congr_on _ _ n
        (fun k hk => duhamelTerm_succ system n k hk)
    _ = matrixApply (system.step n) (duhamelSum system n) := by
      unfold duhamelSum
      exact (matrixApply_vectorSequenceSum (system.step n)
        (duhamelTerm system n) n).symm

/-- Exact finite variation of constants for the zero-initial sampled system.
The recursive forcing response is the explicit chronological Duhamel sum. -/
theorem trajectory_zeroInitial_eq_duhamelSum
    (system : DiscreteLinearSystem dimension) :
    forall n, system.trajectory (vectorZero dimension) n = duhamelSum system n
  | 0 => rfl
  | n + 1 => by
      rw [trajectory_succ,
        trajectory_zeroInitial_eq_duhamelSum system n]
      unfold duhamelSum
      rw [vectorSequenceSum, duhamelSum_prefix_succ,
        duhamelTerm_latest]
      rfl

/-- Exact finite variation of constants with both the homogeneous state
transition and the explicit time-ordered Duhamel sum displayed. -/
theorem trajectory_eq_transition_add_duhamelSum
    (system : DiscreteLinearSystem dimension) (initial : RatVector dimension)
    (n : Nat) :
    system.trajectory initial n =
      vectorAdd
        (matrixApply (chronologicalStepProduct system.step 0 n) initial)
        (duhamelSum system n) := by
  rw [trajectory_eq_transition_add_zeroInitial,
    trajectory_zeroInitial_eq_duhamelSum]

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

/- The familiar forced harmonic oscillator, represented as the two-dimensional
Euler system that the finite Peano--Baker layer actually computes.  This is a
finite rational seed for the later continuous rotation and exponential
identifications; it does not presuppose sine, cosine, or a completed real
line. -/
namespace HarmonicOscillator

/-- Position/velocity state vector. -/
def state (position velocity : Rat) : RatVector 2 :=
  fun i => if i = 0 then position else velocity

/-- Position coordinate of a two-dimensional state. -/
def position (x : RatVector 2) : Rat := x 0

/-- Velocity coordinate of a two-dimensional state. -/
def velocity (x : RatVector 2) : Rat := x 1

theorem state_position (q v : Rat) :
    position (state q v) = q := by
  simp [position, state]

theorem state_velocity (q v : Rat) :
    velocity (state q v) = v := by
  simp [state, velocity]

private theorem finiteSum_two (f : Fin 2 -> Rat) :
    finiteSum f = f 0 + f 1 := by
  change f 0 + (f 1 + 0) = f 0 + f 1
  rw [Rat.add_zero]

/-- The generator with rows `(0, 1)` and `(-omega^2, 0)`. -/
def generator (omega : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 0 (fun _ => 1) j)
      (fun _ j => Fin.cases (-(omega * omega)) (fun _ => 0) j)
      i

/-- One forward Euler step for the oscillator generator. -/
def eulerStep (step omega : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 1 (fun _ => step) j)
      (fun _ j => Fin.cases (-(step * omega * omega)) (fun _ => 1) j)
      i

@[simp] theorem eulerStep_00 (step omega : Rat) :
    eulerStep step omega 0 0 = 1 := by rfl

@[simp] theorem eulerStep_01 (step omega : Rat) :
    eulerStep step omega 0 1 = step := by rfl

@[simp] theorem eulerStep_10 (step omega : Rat) :
    eulerStep step omega 1 0 = -(step * omega * omega) := by rfl

@[simp] theorem eulerStep_11 (step omega : Rat) :
    eulerStep step omega 1 1 = 1 := by rfl

/-- Applying the oscillator Euler step produces the familiar position update. -/
theorem eulerStep_position (step omega : Rat) (x : RatVector 2) :
    position (matrixApply (eulerStep step omega) x) =
      position x + step * velocity x := by
  unfold position velocity matrixApply
  rw [finiteSum_two]
  rw [eulerStep_00, eulerStep_01]
  simp

/-- Applying the oscillator Euler step produces the familiar velocity update. -/
theorem eulerStep_velocity (step omega : Rat) (x : RatVector 2) :
    velocity (matrixApply (eulerStep step omega) x) =
      velocity x - step * omega * omega * position x := by
  unfold position velocity matrixApply
  rw [finiteSum_two]
  rw [eulerStep_10, eulerStep_11]
  simp
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_assoc,
    Rat.mul_comm]

/-- Force samples enter only the velocity coordinate. -/
def forcing (step : Rat) (drive : Nat -> Rat) : Nat -> RatVector 2 :=
  fun n => state 0 (step * drive n)

/-- The sampled inhomogeneous oscillator system. -/
def eulerSystem (step omega : Rat) (drive : Nat -> Rat) :
    DiscreteLinearSystem 2 where
  step := fun _ => eulerStep step omega
  forcing := forcing step drive

theorem forcing_position (step : Rat) (drive : Nat -> Rat) (n : Nat) :
    position (forcing step drive n) = 0 := by
  simp [forcing, state_position]

theorem forcing_velocity (step : Rat) (drive : Nat -> Rat) (n : Nat) :
    velocity (forcing step drive n) = step * drive n := by
  simp [forcing, state_velocity]

/-- The vector Euler system has exactly the expected discrete position update. -/
theorem trajectory_position_succ
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    position ((eulerSystem step omega drive).trajectory initial (n + 1)) =
      position ((eulerSystem step omega drive).trajectory initial n) +
        step * velocity ((eulerSystem step omega drive).trajectory initial n) := by
  rw [DiscreteLinearSystem.trajectory_succ]
  change
    position
      (vectorAdd
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n))
        (forcing step drive n)) = _
  change
    position
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n)) +
      position (forcing step drive n) = _
  rw [eulerStep_position]
  rw [forcing_position, Rat.add_zero]

/-- The vector Euler system has exactly the expected discrete velocity update. -/
theorem trajectory_velocity_succ
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    velocity ((eulerSystem step omega drive).trajectory initial (n + 1)) =
      velocity ((eulerSystem step omega drive).trajectory initial n) -
          step * omega * omega *
            position ((eulerSystem step omega drive).trajectory initial n) +
        step * drive n := by
  rw [DiscreteLinearSystem.trajectory_succ]
  change
    velocity
      (vectorAdd
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n))
        (forcing step drive n)) = _
  change
    velocity
        (matrixApply (eulerStep step omega)
          ((eulerSystem step omega drive).trajectory initial n)) +
      velocity (forcing step drive n) = _
  rw [eulerStep_velocity]
  rw [forcing_velocity]

/-- Eliminating velocity gives the exact second-order finite Euler recurrence.
It is the discrete counterpart of the forced oscillator equation, with no
limiting argument hidden in the statement. -/
theorem trajectory_position_secondDifference
    (step omega : Rat) (drive : Nat -> Rat) (initial : RatVector 2) (n : Nat) :
    position ((eulerSystem step omega drive).trajectory initial (n + 2)) -
        2 * position ((eulerSystem step omega drive).trajectory initial (n + 1)) +
        position ((eulerSystem step omega drive).trajectory initial n) =
      -(step * step * omega * omega *
          position ((eulerSystem step omega drive).trajectory initial n)) +
        step * step * drive n := by
  have hq0 := trajectory_position_succ step omega drive initial n
  have hv0 := trajectory_velocity_succ step omega drive initial n
  have hq1 := trajectory_position_succ step omega drive initial (n + 1)
  rw [show n + 2 = (n + 1) + 1 by omega, hq1, hv0, hq0]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.mul_add,
    Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

end HarmonicOscillator

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

/-- The general sampled transition specializes exactly to the
Peano--Baker chronological product for Euler increments. -/
theorem chronologicalStepProduct_eulerIncrement {dimension : Nat}
    (B : Nat -> RatMatrix dimension) :
    forall steps,
      chronologicalStepProduct
        (fun k => matrixAdd (matrixIdentity dimension) (B k)) 0 steps =
        chronologicalProduct B steps
  | 0 => rfl
  | steps + 1 => by
      rw [chronologicalStepProduct_succ, chronologicalProduct]
      simp only [Nat.zero_add]
      rw [chronologicalStepProduct_eulerIncrement B steps]

/-- Splitting a sampled time interval preserves chronological order: increments
from the later subinterval occur on the left of the earlier transition. -/
theorem chronologicalProduct_split {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (first second : Nat) :
    chronologicalProduct B (first + second) =
      matrixMul (chronologicalProduct (fun k => B (first + k)) second)
        (chronologicalProduct B first) := by
  induction second with
  | zero =>
      simp [chronologicalProduct, matrixMul_identity_left]
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega]
      rw [chronologicalProduct, ih]
      change matrixMul (matrixAdd (matrixIdentity dimension) (B (first + second)))
          (matrixMul (chronologicalProduct (fun k => B (first + k)) second)
            (chronologicalProduct B first)) =
        matrixMul
          (matrixMul (matrixAdd (matrixIdentity dimension) (B (first + second)))
            (chronologicalProduct (fun k => B (first + k)) second))
          (chronologicalProduct B first)
      exact (matrixMul_assoc _ _ _).symm

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

/-- The finite sum of a sampled matrix family over the first `steps` times. -/
def matrixSequenceSum {dimension : Nat} (B : Nat -> RatMatrix dimension) : Nat ->
    RatMatrix dimension
  | 0 => matrixZero dimension
  | n + 1 => matrixAdd (matrixSequenceSum B n) (B n)

theorem matrixSequenceSum_zero {dimension : Nat} (B : Nat -> RatMatrix dimension) :
    matrixSequenceSum B 0 = matrixZero dimension := rfl

theorem matrixSequenceSum_succ {dimension : Nat} (B : Nat -> RatMatrix dimension)
    (steps : Nat) :
    matrixSequenceSum B (steps + 1) =
      matrixAdd (matrixSequenceSum B steps) (B steps) := rfl

/-- A sampled coefficient family whose every product of two samples vanishes.

This is the finite square-zero (and hence nilpotent) special case of the
Peano--Baker expansion.  It is intentionally stronger than mere pairwise
commutation: the strength makes all words of length at least two vanish by a
direct finite calculation. -/
def PairwiseProductZero {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall i j, matrixMul (B i) (B j) = matrixZero dimension

/-- Pairwise commutation of the sampled increments.  Unlike the square-zero
condition, this does not make higher Peano--Baker words vanish; it is the
finite algebra hypothesis behind the later commuting-coefficient formula. -/
def PairwiseCommuting {dimension : Nat} (B : Nat -> RatMatrix dimension) : Prop :=
  forall i j, matrixMul (B i) (B j) = matrixMul (B j) (B i)

theorem matrixMul_commutes_identity_add {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hcomm : PairwiseCommuting B) (i j : Nat) :
    matrixMul (B i) (matrixAdd (matrixIdentity dimension) (B j)) =
      matrixMul (matrixAdd (matrixIdentity dimension) (B j)) (B i) := by
  rw [matrixMul_add_right, matrixMul_add_left, matrixMul_identity_right,
    matrixMul_identity_left, hcomm]

/-- Under pairwise commuting increments, each sample commutes with the finite
chronological transition accumulated from any number of earlier samples. -/
theorem matrixMul_commutes_chronologicalProduct {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hcomm : PairwiseCommuting B) (i : Nat) :
    forall steps,
      matrixMul (B i) (chronologicalProduct B steps) =
        matrixMul (chronologicalProduct B steps) (B i)
  | 0 => by
      rw [chronologicalProduct, matrixMul_identity_right, matrixMul_identity_left]
  | steps + 1 => by
      rw [chronologicalProduct]
      rw [← matrixMul_assoc, matrixMul_commutes_identity_add B hcomm]
      rw [matrixMul_assoc]
      rw [matrixMul_commutes_chronologicalProduct B hcomm i steps]
      rw [← matrixMul_assoc]

theorem matrixMul_sequenceSum_eq_zero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B) :
    forall i steps,
      matrixMul (B i) (matrixSequenceSum B steps) = matrixZero dimension
  | i, 0 => by
      rw [matrixSequenceSum_zero, matrixMul_zero_right]
  | i, steps + 1 => by
      rw [matrixSequenceSum_succ, matrixMul_add_right,
        matrixMul_sequenceSum_eq_zero B hzero i steps, hzero i steps,
        matrixAdd_zero_right]

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

/-- In the square-zero specialization, every Peano--Baker word of length at
least two is zero, so the finite state transition is exactly the identity plus
the finite sum of the sampled increments. -/
theorem chronologicalProduct_pairwiseProductZero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B) :
    forall steps,
      chronologicalProduct B steps =
        matrixAdd (matrixIdentity dimension) (matrixSequenceSum B steps)
  | 0 => by
      exact (matrixAdd_zero_right _).symm
  | steps + 1 => by
      rw [chronologicalProduct_succ,
        chronologicalProduct_pairwiseProductZero B hzero steps,
        matrixMul_add_right, matrixMul_identity_right,
        matrixMul_sequenceSum_eq_zero B hzero, matrixAdd_zero_right]
      exact matrixAdd_assoc _ _ _

theorem peanoBakerDiscreteSum_pairwiseProductZero {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (hzero : PairwiseProductZero B)
    (steps : Nat) :
    peanoBakerDiscreteSum B steps =
      matrixAdd (matrixIdentity dimension) (matrixSequenceSum B steps) := by
  rw [← discretePeanoBakerExpansion]
  exact chronologicalProduct_pairwiseProductZero B hzero steps

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
