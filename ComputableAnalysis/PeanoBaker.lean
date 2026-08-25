import ComputableAnalysis.Differential
import ComputableAnalysis.PowerSeries

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

def vectorScale {dimension : Nat} (r : Rat) (x : RatVector dimension) :
    RatVector dimension :=
  fun i => r * x i

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

theorem finiteSum_le {dimension : Nat} {f g : Fin dimension -> Rat}
    (h : forall i, f i <= g i) : finiteSum f <= finiteSum g := by
  induction dimension with
  | zero =>
      simp [finiteSum]
  | succ dimension ih =>
      simp only [finiteSum]
      exact rat_add_le_add (h 0) (ih (fun i => h i.succ))

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

theorem finiteSum_mul_le_of_nonneg {dimension : Nat}
    (f g : Fin dimension -> Rat) (c : Rat)
    (hf : forall i, 0 <= f i) (hg : forall i, g i <= c) :
    finiteSum (fun i => f i * g i) <= c * finiteSum f := by
  calc
    finiteSum (fun i => f i * g i) <=
        finiteSum (fun i => f i * c) := by
      exact finiteSum_le (fun i =>
        Rat.mul_le_mul_of_nonneg_left (hg i) (hf i))
    _ = finiteSum f * c := (finiteSum_mul_right c f).symm
    _ = c * finiteSum f := Rat.mul_comm _ _

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

/-- Rational scaling is compatible with the local matrix product on the
right.  This finite distributivity calculation is the scalar algebra behind
the constant-coefficient Peano--Baker simplex terms. -/
theorem matrixMul_matrixScale_right {dimension : Nat}
    (A B : RatMatrix dimension) (r : Rat) :
    matrixMul A (matrixScale r B) = matrixScale r (matrixMul A B) := by
  funext i j
  unfold matrixMul matrixScale
  calc
    finiteSum (fun k => A i k * (r * B k j)) =
        finiteSum (fun k => r * (A i k * B k j)) := by
          congr 1
          funext k
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = r * finiteSum (fun k => A i k * B k j) :=
      (finiteSum_mul_left r (fun k => A i k * B k j)).symm

theorem matrixMul_matrixScale_left {dimension : Nat}
    (A B : RatMatrix dimension) (r : Rat) :
    matrixMul (matrixScale r A) B = matrixScale r (matrixMul A B) := by
  funext i j
  unfold matrixMul matrixScale
  calc
    finiteSum (fun k => (r * A i k) * B k j) =
        finiteSum (fun k => r * (A i k * B k j)) := by
          congr 1
          funext k
          exact Rat.mul_assoc _ _ _
    _ = r * finiteSum (fun k => A i k * B k j) :=
      (finiteSum_mul_left r (fun k => A i k * B k j)).symm

theorem matrixScale_comp {dimension : Nat} (r s : Rat)
    (A : RatMatrix dimension) :
    matrixScale r (matrixScale s A) = matrixScale (r * s) A := by
  funext i j
  unfold matrixScale
  exact (Rat.mul_assoc _ _ _).symm

theorem matrixScale_one {dimension : Nat} (A : RatMatrix dimension) :
    matrixScale 1 A = A := by
  funext i j
  unfold matrixScale
  exact Rat.one_mul _

/-- Two scalar multiples of one finite rational matrix combine by addition of
their rational coefficients. -/
theorem matrixAdd_scale_same {dimension : Nat} (r s : Rat)
    (A : RatMatrix dimension) :
    matrixAdd (matrixScale r A) (matrixScale s A) = matrixScale (r + s) A := by
  funext i j
  exact (Rat.add_mul _ _ _).symm

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

/-! Absolute-value estimates are kept at the finite-sum level.  They are the
entrywise substitute for importing a normed matrix space: every bound below
is an executable rational traversal of a finite index type. -/
theorem finiteSum_qabs_mul_le {dimension : Nat} (f g : Fin dimension -> Rat) :
    qabs (finiteSum (fun i => f i * g i)) <=
      finiteSum (fun i => qabs (f i) * qabs (g i)) := by
  induction dimension with
  | zero =>
      simp [finiteSum, qabs]
  | succ dimension ih =>
      simp only [finiteSum]
      calc
        qabs (f 0 * g 0 + finiteSum (fun i : Fin dimension =>
          f i.succ * g i.succ)) <=
            qabs (f 0 * g 0) +
              qabs (finiteSum (fun i : Fin dimension =>
                f i.succ * g i.succ)) := qabs_add_le _ _
        _ <= qabs (f 0) * qabs (g 0) +
              finiteSum (fun i : Fin dimension =>
                qabs (f i.succ) * qabs (g i.succ)) := by
          apply rat_add_le_add
          · rw [qabs_mul]
            exact Rat.le_refl
          · exact ih (fun i => f i.succ) (fun i => g i.succ)

theorem matrixApply_qabs_le {dimension : Nat}
    (A : RatMatrix dimension) (x : RatVector dimension) (i : Fin dimension) :
    qabs (matrixApply A x i) <=
      finiteSum (fun j => qabs (A i j) * qabs (x j)) := by
  unfold matrixApply
  exact finiteSum_qabs_mul_le (fun j => A i j) x

theorem matrixMul_qabs_le {dimension : Nat}
    (A B : RatMatrix dimension) (i j : Fin dimension) :
    qabs (matrixMul A B i j) <=
      finiteSum (fun k => qabs (A i k) * qabs (B k j)) := by
  unfold matrixMul
  exact finiteSum_qabs_mul_le (fun k => A i k) (fun k => B k j)

def matrixRowAbsSum {dimension : Nat} (A : RatMatrix dimension) (i : Fin dimension) : Rat :=
  finiteSum (fun j => qabs (A i j))

theorem matrixRowAbsSum_identity {dimension : Nat} (i : Fin dimension) :
    matrixRowAbsSum (matrixIdentity dimension) i = 1 := by
  unfold matrixRowAbsSum matrixIdentity
  rw [show (fun j => qabs (if i = j then 1 else 0)) =
      (fun j => if j = i then 1 else 0) by
        funext j
        by_cases h : i = j
        · rw [if_pos h, if_pos h.symm]
          native_decide
        · have h' : ¬ j = i := by
            intro hji
            exact h hji.symm
          rw [if_neg h, if_neg h']
          native_decide
      ]
  change finiteSum (fun j => if j = i then (1 : Rat) else 0) =
    (fun _ => (1 : Rat)) i
  exact finiteSum_ite_eq i (fun _ => (1 : Rat))

theorem matrixRowAbsSum_matrixScale {dimension : Nat}
    (r : Rat) (A : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixScale r A) i =
      qabs r * matrixRowAbsSum A i := by
  unfold matrixRowAbsSum matrixScale
  rw [show (fun j => qabs (r * A i j)) =
      (fun j => qabs r * qabs (A i j)) by
        funext j
        exact qabs_mul r (A i j)]
  exact (finiteSum_mul_left (qabs r) (fun j => qabs (A i j))).symm

theorem matrixRowAbsSum_matrixAdd_le {dimension : Nat}
    (A B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixAdd A B) i <=
      matrixRowAbsSum A i + matrixRowAbsSum B i := by
  unfold matrixRowAbsSum matrixAdd
  calc
    finiteSum (fun j => qabs (A i j + B i j)) <=
        finiteSum (fun j => qabs (A i j) + qabs (B i j)) := by
      exact finiteSum_le (fun j => qabs_add_le _ _)
    _ = finiteSum (fun j => qabs (A i j)) +
        finiteSum (fun j => qabs (B i j)) := finiteSum_add _ _

theorem matrixRowAbsSum_affineStep_le {dimension : Nat}
    (B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixAdd (matrixIdentity dimension) B) i <=
      1 + matrixRowAbsSum B i := by
  have h := matrixRowAbsSum_matrixAdd_le (matrixIdentity dimension) B i
  rw [matrixRowAbsSum_identity] at h
  exact h

theorem matrixMul_rowAbsSum_le {dimension : Nat}
    (A B : RatMatrix dimension) (i : Fin dimension) :
    matrixRowAbsSum (matrixMul A B) i <=
      finiteSum (fun k => qabs (A i k) * matrixRowAbsSum B k) := by
  calc
    matrixRowAbsSum (matrixMul A B) i =
        finiteSum (fun j => qabs (matrixMul A B i j)) := rfl
    _ <= finiteSum (fun j =>
        finiteSum (fun k => qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_le (fun j => matrixMul_qabs_le A B i j)
    _ = finiteSum (fun k =>
        finiteSum (fun j => qabs (A i k) * qabs (B k j))) := by
      exact finiteSum_swap dimension dimension
        (fun j k => qabs (A i k) * qabs (B k j))
    _ = finiteSum (fun k => qabs (A i k) * matrixRowAbsSum B k) := by
      congr 1
      funext k
      unfold matrixRowAbsSum
      exact (finiteSum_mul_left (qabs (A i k))
        (fun j => qabs (B k j))).symm

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

theorem matrixApply_vectorScale {dimension : Nat}
    (A : RatMatrix dimension) (r : Rat) (x : RatVector dimension) :
    matrixApply A (vectorScale r x) =
      vectorScale r (matrixApply A x) := by
  funext i
  unfold matrixApply vectorScale
  rw [show (fun j => A i j * (r * x j)) =
      (fun j => r * (A i j * x j)) by
        funext j
        grind [Rat.mul_assoc, Rat.mul_comm]]
  exact (finiteSum_mul_left r (fun j => A i j * x j)).symm

theorem matrixApply_matrixAdd {dimension : Nat}
    (A B : RatMatrix dimension) (x : RatVector dimension) :
    matrixApply (matrixAdd A B) x =
      vectorAdd (matrixApply A x) (matrixApply B x) := by
  funext i
  unfold matrixApply matrixAdd vectorAdd
  rw [show (fun j => (A i j + B i j) * x j) =
      (fun j => A i j * x j + B i j * x j) by
        funext j
        exact Rat.add_mul _ _ _]
  exact finiteSum_add _ _

theorem matrixApply_matrixScale {dimension : Nat}
    (A : RatMatrix dimension) (r : Rat) (x : RatVector dimension) :
    matrixApply (matrixScale r A) x =
      vectorScale r (matrixApply A x) := by
  funext i
  unfold matrixApply matrixScale vectorScale
  rw [show (fun j => (r * A i j) * x j) =
      (fun j => r * (A i j * x j)) by
        funext j
        exact Rat.mul_assoc _ _ _]
  exact (finiteSum_mul_left r (fun j => A i j * x j)).symm

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

/-- Regroup four finite matrix summands into their first-and-third and
second-and-fourth pairs. -/
theorem matrixAdd_group_even_odd {dimension : Nat}
    (A B C D : RatMatrix dimension) :
    matrixAdd (matrixAdd (matrixAdd A B) C) D =
      matrixAdd (matrixAdd A C) (matrixAdd B D) := by
  funext i j
  change ((A i j + B i j) + C i j) + D i j =
    (A i j + C i j) + (B i j + D i j)
  ac_rfl

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

/-- Exact composition of time-shifted sampled transitions.  The transition
over the later block occurs on the left, as required by chronological time
ordering.  This is the finite semigroup law behind the future continuous
identity `Phi(t,r) * Phi(r,s) = Phi(t,s)`. -/
theorem chronologicalStepProduct_split {dimension : Nat}
    (S : Nat -> RatMatrix dimension) (start first second : Nat) :
    chronologicalStepProduct S start (first + second) =
      matrixMul
        (chronologicalStepProduct S (start + first) second)
        (chronologicalStepProduct S start first) := by
  induction second with
  | zero =>
      change chronologicalStepProduct S start first =
        matrixMul (matrixIdentity dimension) (chronologicalStepProduct S start first)
      exact (matrixMul_identity_left _).symm
  | succ second ih =>
      rw [show first + (second + 1) = (first + second) + 1 by omega]
      rw [chronologicalStepProduct_succ, ih]
      change
        matrixMul (S (start + (first + second)))
          (matrixMul (chronologicalStepProduct S (start + first) second)
            (chronologicalStepProduct S start first)) =
          matrixMul
            (matrixMul (S ((start + first) + second))
              (chronologicalStepProduct S (start + first) second))
            (chronologicalStepProduct S start first)
      rw [show start + (first + second) = (start + first) + second by omega]
      exact (matrixMul_assoc _ _ _).symm

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

/-! The finite homogeneous trajectory already has the linearity expected of
the solution operator.  This is an induction over sampled matrix updates, not
an appeal to a completed vector-valued function space. -/
theorem homogeneousTrajectory_vectorAdd
    (system : DiscreteLinearSystem dimension)
    (x y : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory (vectorAdd x y) n =
        vectorAdd (system.homogeneousTrajectory x n)
          (system.homogeneousTrajectory y n)
  | 0 => rfl
  | n + 1 => by
      rw [homogeneousTrajectory_succ, homogeneousTrajectory_succ,
        homogeneousTrajectory_succ,
        homogeneousTrajectory_vectorAdd system x y n,
        matrixApply_vectorAdd]

theorem homogeneousTrajectory_vectorScale
    (system : DiscreteLinearSystem dimension)
    (r : Rat) (x : RatVector dimension) :
    forall n,
      system.homogeneousTrajectory (vectorScale r x) n =
        vectorScale r (system.homogeneousTrajectory x n)
  | 0 => rfl
  | n + 1 => by
      rw [homogeneousTrajectory_succ, homogeneousTrajectory_succ,
        homogeneousTrajectory_vectorScale system r x n,
        matrixApply_vectorScale]

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

/-! ## A finite Cayley--Hamilton core -/

/-- An explicit rational `2 x 2` matrix, used for small linear-algebra
certificates without importing an ambient matrix library. -/
def twoByTwoMatrix (a b c d : Rat) : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases a (fun _ => b) j)
      (fun _ j => Fin.cases c (fun _ => d) j)
      i

@[simp] theorem twoByTwoMatrix_00 (a b c d : Rat) :
    twoByTwoMatrix a b c d 0 0 = a := by rfl

@[simp] theorem twoByTwoMatrix_01 (a b c d : Rat) :
    twoByTwoMatrix a b c d 0 1 = b := by rfl

@[simp] theorem twoByTwoMatrix_10 (a b c d : Rat) :
    twoByTwoMatrix a b c d 1 0 = c := by rfl

@[simp] theorem twoByTwoMatrix_11 (a b c d : Rat) :
    twoByTwoMatrix a b c d 1 1 = d := by rfl

def twoByTwoTrace (a _b _c d : Rat) : Rat := a + d

def twoByTwoDeterminant (a b c d : Rat) : Rat := a * d - b * c

/-- The adjugate of an explicit rational `2 x 2` matrix.  Keeping this
construction at the concrete dimension two makes the inverse certificate
executable and avoids importing a general determinant or inverse theory. -/
def twoByTwoAdjugate (a b c d : Rat) : RatMatrix 2 :=
  twoByTwoMatrix d (-b) (-c) a

/-- The finite adjugate identity on the right.  This is the algebraic
certificate behind reversing a nonsingular sampled transition. -/
theorem twoByTwo_mul_adjugate (a b c d : Rat) :
    matrixMul (twoByTwoMatrix a b c d) (twoByTwoAdjugate a b c d) =
      matrixScale (twoByTwoDeterminant a b c d) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant,
        matrixMul, matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The finite adjugate identity on the left. -/
theorem twoByTwo_adjugate_mul (a b c d : Rat) :
    matrixMul (twoByTwoAdjugate a b c d) (twoByTwoMatrix a b c d) =
      matrixScale (twoByTwoDeterminant a b c d) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant,
        matrixMul, matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoAdjugate, twoByTwoDeterminant, matrixMul, matrixScale, matrixIdentity,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The exact rational inverse of a nonsingular concrete `2 x 2` matrix. -/
def twoByTwoInverse (a b c d : Rat) : RatMatrix 2 :=
  matrixScale (twoByTwoDeterminant a b c d)⁻¹
    (twoByTwoAdjugate a b c d)

theorem twoByTwo_mul_inverse {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0) :
    matrixMul (twoByTwoMatrix a b c d) (twoByTwoInverse a b c d) =
      matrixIdentity 2 := by
  unfold twoByTwoInverse
  rw [matrixMul_matrixScale_right, twoByTwo_mul_adjugate,
    matrixScale_comp]
  have hcancel :
      (twoByTwoDeterminant a b c d)⁻¹ * twoByTwoDeterminant a b c d = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel _ hdet
  rw [hcancel, matrixScale_one]

theorem twoByTwo_inverse_mul {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0) :
    matrixMul (twoByTwoInverse a b c d) (twoByTwoMatrix a b c d) =
      matrixIdentity 2 := by
  unfold twoByTwoInverse
  rw [matrixMul_matrixScale_left, twoByTwo_adjugate_mul,
    matrixScale_comp]
  have hcancel :
      (twoByTwoDeterminant a b c d)⁻¹ * twoByTwoDeterminant a b c d = 1 := by
    rw [Rat.mul_comm]
    exact Rat.mul_inv_cancel _ hdet
  rw [hcancel, matrixScale_one]

theorem twoByTwo_inverse_unique_right {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (B : RatMatrix 2)
    (hB : matrixMul (twoByTwoMatrix a b c d) B = matrixIdentity 2) :
    B = twoByTwoInverse a b c d := by
  calc
    B = matrixMul (matrixIdentity 2) B :=
      (matrixMul_identity_left B).symm
    _ = matrixMul
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) B := by
      exact (congrArg (fun M => matrixMul M B)
        (twoByTwo_inverse_mul hdet)).symm
    _ = matrixMul (twoByTwoInverse a b c d)
        (matrixMul (twoByTwoMatrix a b c d) B) :=
      matrixMul_assoc _ _ _
    _ = matrixMul (twoByTwoInverse a b c d) (matrixIdentity 2) := by
      rw [hB]
    _ = twoByTwoInverse a b c d := matrixMul_identity_right _

theorem twoByTwo_inverse_unique_left {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (B : RatMatrix 2)
    (hB : matrixMul B (twoByTwoMatrix a b c d) = matrixIdentity 2) :
    B = twoByTwoInverse a b c d := by
  calc
    B = matrixMul B (matrixIdentity 2) :=
      (matrixMul_identity_right B).symm
    _ = matrixMul B
        (matrixMul (twoByTwoMatrix a b c d)
          (twoByTwoInverse a b c d)) := by
      exact (congrArg (fun M => matrixMul B M)
        (twoByTwo_mul_inverse hdet)).symm
    _ = matrixMul (matrixMul B (twoByTwoMatrix a b c d))
        (twoByTwoInverse a b c d) :=
      (matrixMul_assoc _ _ _).symm
    _ = matrixMul (matrixIdentity 2) (twoByTwoInverse a b c d) := by
      rw [hB]
    _ = twoByTwoInverse a b c d := matrixMul_identity_left _

theorem twoByTwo_inverse_solves {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (x : RatVector 2) :
    matrixApply (twoByTwoMatrix a b c d)
        (matrixApply (twoByTwoInverse a b c d) x) = x := by
  calc
    matrixApply (twoByTwoMatrix a b c d)
        (matrixApply (twoByTwoInverse a b c d) x) =
        matrixApply
          (matrixMul (twoByTwoMatrix a b c d)
            (twoByTwoInverse a b c d)) x :=
      (matrixApply_matrixMul _ _ _).symm
    _ = matrixApply (matrixIdentity 2) x := by
      rw [twoByTwo_mul_inverse hdet]
    _ = x := matrixApply_identity x

theorem twoByTwo_solution_unique {a b c d : Rat}
    (hdet : twoByTwoDeterminant a b c d ≠ 0)
    (rhs u v : RatVector 2)
    (hu : matrixApply (twoByTwoMatrix a b c d) u = rhs)
    (hv : matrixApply (twoByTwoMatrix a b c d) v = rhs) :
    u = v := by
  have huv : matrixApply (twoByTwoMatrix a b c d) u =
      matrixApply (twoByTwoMatrix a b c d) v := hu.trans hv.symm
  calc
    u = matrixApply (matrixIdentity 2) u := (matrixApply_identity u).symm
    _ = matrixApply
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) u := by
      rw [twoByTwo_inverse_mul hdet]
    _ = matrixApply (twoByTwoInverse a b c d)
        (matrixApply (twoByTwoMatrix a b c d) u) :=
      matrixApply_matrixMul _ _ _
    _ = matrixApply (twoByTwoInverse a b c d)
        (matrixApply (twoByTwoMatrix a b c d) v) :=
      congrArg (matrixApply (twoByTwoInverse a b c d)) huv
    _ = matrixApply
        (matrixMul (twoByTwoInverse a b c d)
          (twoByTwoMatrix a b c d)) v :=
      (matrixApply_matrixMul _ _ _).symm
    _ = matrixApply (matrixIdentity 2) v := by
      rw [twoByTwo_inverse_mul hdet]
    _ = v := matrixApply_identity v

/-- The Cayley--Hamilton identity for an explicit rational `2 x 2` matrix.
This is the finite matrix core of benchmark item 49; arbitrary dimensions and
an abstract characteristic-polynomial interface remain outside the project
boundary. -/
theorem twoByTwo_cayley_hamilton (a b c d : Rat) :
    let A := twoByTwoMatrix a b c d
    matrixAdd (matrixMul A A)
        (matrixAdd
          (matrixScale (-(twoByTwoTrace a b c d)) A)
          (matrixScale (twoByTwoDeterminant a b c d)
            (matrixIdentity 2))) =
      matrixZero 2 := by
  dsimp [twoByTwoTrace, twoByTwoDeterminant]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
          finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
        finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [matrixAdd, matrixMul, matrixScale, matrixIdentity, matrixZero,
          finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-- The trace read directly from an arbitrary rational `2 x 2` matrix. -/
def ratMatrixTwoTrace (A : RatMatrix 2) : Rat := A 0 0 + A 1 1

/-- The determinant read directly from an arbitrary rational `2 x 2` matrix.
This is a finite four-entry formula, not an imported determinant API. -/
def ratMatrixTwoDeterminant (A : RatMatrix 2) : Rat :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- Every rational `2 x 2` matrix is extensionally its explicit four-entry
presentation.  This finite extensionality bridge makes the concrete
Cayley--Hamilton certificate reusable for arbitrary matrix data. -/
theorem ratMatrix_twoByTwo_eq_explicit (A : RatMatrix 2) :
    A = twoByTwoMatrix (A 0 0) (A 0 1) (A 1 0) (A 1 1) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      rfl
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · rfl
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      rfl

/-- General rational `2 x 2` Cayley--Hamilton certificate.  For arbitrary
matrix data `A`, the finite characteristic polynomial identity is
`A² - trace(A) A + det(A) I = 0`; no completed reals, limits, or continuous
ODE theorem are involved. -/
theorem ratMatrix_twoByTwo_cayley_hamilton (A : RatMatrix 2) :
    matrixAdd (matrixMul A A)
        (matrixAdd
          (matrixScale (-(ratMatrixTwoTrace A)) A)
          (matrixScale (ratMatrixTwoDeterminant A)
            (matrixIdentity 2))) =
      matrixZero 2 := by
  have hA := ratMatrix_twoByTwo_eq_explicit A
  unfold ratMatrixTwoTrace ratMatrixTwoDeterminant
  rw [hA]
  simpa only [twoByTwoMatrix_00, twoByTwoMatrix_01, twoByTwoMatrix_10,
    twoByTwoMatrix_11, twoByTwoTrace, twoByTwoDeterminant] using
    (twoByTwo_cayley_hamilton (A 0 0) (A 0 1) (A 1 0) (A 1 1))

private theorem finiteSum_three (f : Fin 3 -> Rat) :
    finiteSum f = f 0 + f 1 + f 2 := by
  change f 0 + (f 1 + (f 2 + 0)) = f 0 + f 1 + f 2
  grind [Rat.add_assoc]

/-- An explicit rational `3 x 3` matrix for the next finite
characteristic-polynomial certificate. -/
def threeByThreeMatrix
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : RatMatrix 3 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases a00 (fun j => Fin.cases a01 (fun _ => a02) j) j)
      (fun i => Fin.cases
        (fun j => Fin.cases a10 (fun j => Fin.cases a11 (fun _ => a12) j) j)
        (fun i => Fin.cases
          (fun j => Fin.cases a20 (fun j => Fin.cases a21 (fun _ => a22) j) j)
          (fun i => Fin.elim0 i) i) i) i

@[simp] theorem threeByThreeMatrix_00 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 0 = a00 := by rfl
@[simp] theorem threeByThreeMatrix_01 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 1 = a01 := by rfl
@[simp] theorem threeByThreeMatrix_02 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 0 2 = a02 := by rfl
@[simp] theorem threeByThreeMatrix_10 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 0 = a10 := by rfl
@[simp] theorem threeByThreeMatrix_11 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 1 = a11 := by rfl
@[simp] theorem threeByThreeMatrix_12 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 1 2 = a12 := by rfl
@[simp] theorem threeByThreeMatrix_20 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 0 = a20 := by rfl
@[simp] theorem threeByThreeMatrix_21 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 1 = a21 := by rfl
@[simp] theorem threeByThreeMatrix_22 (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22 2 2 = a22 := by rfl

def threeByThreeTrace (a00 _a01 _a02 _a10 a11 _a12 _a20 _a21 a22 : Rat) : Rat :=
  a00 + a11 + a22

def threeByThreeSecondCoeff
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : Rat :=
  a00 * a11 + a00 * a22 + a11 * a22 - a01 * a10 - a02 * a20 - a12 * a21

def threeByThreeDeterminant
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) : Rat :=
  a00 * (a11 * a22 - a12 * a21) -
    a01 * (a10 * a22 - a12 * a20) +
    a02 * (a10 * a21 - a11 * a20)

/-- The finite rational `3 x 3` Cayley--Hamilton identity
`A^3 - tr(A) A^2 + s₂(A) A - det(A) I = 0`, where `s₂` is the second
elementary characteristic coefficient.  This is a higher-dimensional
certificate-level extension of the project's general `2 x 2` result; it
still uses only explicit finite sums and rational ring identities. -/
theorem threeByThree_cayley_hamilton
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Rat) :
    let A := threeByThreeMatrix a00 a01 a02 a10 a11 a12 a20 a21 a22
    matrixAdd (matrixMul A (matrixMul A A))
        (matrixAdd
          (matrixScale (-(threeByThreeTrace a00 a01 a02 a10 a11 a12 a20 a21 a22))
            (matrixMul A A))
          (matrixAdd
            (matrixScale
              (threeByThreeSecondCoeff a00 a01 a02 a10 a11 a12 a20 a21 a22) A)
            (matrixScale
              (-(threeByThreeDeterminant a00 a01 a02 a10 a11 a12 a20 a21 a22))
              (matrixIdentity 3)))) =
      matrixZero 3 := by
  dsimp [threeByThreeTrace, threeByThreeSecondCoeff,
    threeByThreeDeterminant]
  funext i j
  have hi : i = 0 \/ i = 1 \/ i = 2 := by omega
  have hj : j = 0 \/ j = 1 \/ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl <;>
      simp [matrixAdd, matrixMul, matrixScale,
        matrixIdentity, matrixZero, finiteSum_three,
        threeByThreeMatrix_00, threeByThreeMatrix_01,
        threeByThreeMatrix_02, threeByThreeMatrix_10,
        threeByThreeMatrix_11, threeByThreeMatrix_12,
        threeByThreeMatrix_20, threeByThreeMatrix_21,
        threeByThreeMatrix_22] <;>
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

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

def ratProduct (f : Nat -> Rat) : Nat -> Rat
  | 0 => 1
  | n + 1 => ratProduct f n * f n

theorem ratProduct_nonneg (f : Nat -> Rat) (hf : forall n, 0 <= f n) :
    forall n, 0 <= ratProduct f n
  | 0 => by
      change (0 : Rat) <= 1
      native_decide
  | n + 1 => by
      rw [ratProduct]
      exact Rat.mul_nonneg (ratProduct_nonneg f hf n) (hf n)

theorem ratProduct_const_eq_pow (c : Rat) :
    forall n, ratProduct (fun _ => c) n = c ^ n
  | 0 => by
      rw [ratProduct, Rat.pow_zero]
  | n + 1 => by
      rw [ratProduct, ratProduct_const_eq_pow c n, Rat.pow_succ]

theorem chronologicalProduct_rowAbsSum_le {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (bound : Nat -> Rat)
    (hbound : forall n i,
      matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B n)) i <= bound n)
    (hbound_nonneg : forall n, 0 <= bound n) :
    forall steps i,
      matrixRowAbsSum (chronologicalProduct B steps) i <= ratProduct bound steps
  | 0, i => by
      rw [chronologicalProduct, matrixRowAbsSum_identity, ratProduct]
      native_decide
  | steps + 1, i => by
      rw [chronologicalProduct]
      have hmul := matrixMul_rowAbsSum_le
        (matrixAdd (matrixIdentity dimension) (B steps))
        (chronologicalProduct B steps) i
      have hprevious : forall k,
          matrixRowAbsSum (chronologicalProduct B steps) k <=
            ratProduct bound steps :=
        fun k => chronologicalProduct_rowAbsSum_le B bound hbound
          hbound_nonneg steps k
      have hweighted := finiteSum_mul_le_of_nonneg
        (fun k => qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k))
        (fun k => matrixRowAbsSum (chronologicalProduct B steps) k)
        (ratProduct bound steps)
        (fun k => qabs_nonneg _)
        hprevious
      calc
        matrixRowAbsSum (matrixMul
            (matrixAdd (matrixIdentity dimension) (B steps))
            (chronologicalProduct B steps)) i <=
            finiteSum (fun k =>
              qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k) *
                matrixRowAbsSum (chronologicalProduct B steps) k) :=
          hmul
        _ <= ratProduct bound steps *
              finiteSum (fun k =>
                qabs ((matrixAdd (matrixIdentity dimension) (B steps)) i k)) :=
          hweighted
        _ = ratProduct bound steps *
            matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B steps)) i := rfl
        _ <= ratProduct bound steps * bound steps := by
          exact Rat.mul_le_mul_of_nonneg_left (hbound steps i)
            (ratProduct_nonneg bound hbound_nonneg steps)
        _ = ratProduct bound (steps + 1) := by
          rw [ratProduct]

theorem chronologicalProduct_rowAbsSum_le_pow {dimension : Nat}
    (B : Nat -> RatMatrix dimension) (c : Rat)
    (hbound : forall n i,
      matrixRowAbsSum (matrixAdd (matrixIdentity dimension) (B n)) i <= c)
    (hc : 0 <= c) :
    forall steps i,
      matrixRowAbsSum (chronologicalProduct B steps) i <= c ^ steps := by
  intro steps i
  have hgeneral := chronologicalProduct_rowAbsSum_le B (fun _ => c)
    (fun n j => hbound n j) (fun _ => hc) steps i
  rw [ratProduct_const_eq_pow c steps] at hgeneral
  exact hgeneral

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

/-- Matrix powers split at a finite degree.  This is the local algebra used
to group constant Peano--Baker terms into their even and odd parts. -/
theorem matrixPow_add {dimension : Nat} (A : RatMatrix dimension) :
    forall m n, matrixPow A (m + n) = matrixMul (matrixPow A m) (matrixPow A n)
  | 0, n => by
      simp [matrixPow, matrixMul_identity_left]
  | m + 1, n => by
      rw [show (m + 1) + n = (m + n) + 1 by omega]
      rw [matrixPow, matrixPow, matrixPow_add A m n]
      exact (matrixMul_assoc _ _ _).symm

/-- Every finite power of an arbitrary rational `2 x 2` matrix reduces by its
characteristic polynomial.  This is the executable Cayley--Hamilton power
recurrence

`A^(n+2) = trace(A) A^(n+1) - det(A) A^n`.

The statement is entirely finite: powers are natural recursive products and
the coefficients are the four-entry rational trace and determinant above.
It is a certificate for discrete matrix algebra, not a continuous ODE
theorem or a convergence assertion. -/
theorem ratMatrix_twoByTwo_matrixPow_succ_succ_recurrence (A : RatMatrix 2) :
    forall n,
      matrixPow A (n + 2) =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A)
            (matrixPow A (n + 1)))
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (matrixPow A n)) := by
  have hbase :
      matrixMul A A =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A) A)
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (matrixIdentity 2)) := by
    have hCH := HarmonicOscillator.ratMatrix_twoByTwo_cayley_hamilton A
    funext i j
    have hij := congrFun (congrFun hCH i) j
    dsimp [matrixAdd, matrixScale, matrixZero] at hij ⊢
    grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  intro n
  rw [show n + 2 = 2 + n by omega, matrixPow_add A 2 n]
  change matrixMul (matrixMul A (matrixMul A (matrixIdentity 2)))
      (matrixPow A n) = _
  rw [matrixMul_identity_right, hbase, matrixMul_add_left,
    matrixMul_matrixScale_left, matrixMul_matrixScale_left,
    matrixMul_identity_left]
  rw [show n + 1 = 1 + n by omega, matrixPow_add A 1 n]
  simp only [matrixPow, matrixMul_identity_right]

/-- Any rational matrix sequence with the same first two values and the
characteristic recurrence is the corresponding finite matrix-power sequence.
This is a bounded induction certificate for the Cayley--Hamilton reduction:
it compares only finitely many rational matrices at any requested stage. -/
theorem ratMatrix_twoByTwo_matrixPow_recurrence_unique (A : RatMatrix 2)
    (X : Nat -> RatMatrix 2)
    (h0 : X 0 = matrixIdentity 2)
    (h1 : X 1 = A)
    (hrec : forall n,
      X (n + 2) =
        matrixAdd
          (matrixScale (HarmonicOscillator.ratMatrixTwoTrace A) (X (n + 1)))
          (matrixScale (-(HarmonicOscillator.ratMatrixTwoDeterminant A))
            (X n))) :
    forall n, X n = matrixPow A n
  | 0 => h0
  | 1 => by
      change X 1 = matrixMul A (matrixIdentity 2)
      rw [matrixMul_identity_right]
      exact h1
  | n + 2 => by
      rw [hrec n, ratMatrix_twoByTwo_matrixPow_succ_succ_recurrence A n]
      rw [ratMatrix_twoByTwo_matrixPow_recurrence_unique A X h0 h1 hrec (n + 1),
        ratMatrix_twoByTwo_matrixPow_recurrence_unique A X h0 h1 hrec n]

namespace HarmonicOscillator

/-- The first nontrivial power reduction supplied by the explicit
Cayley--Hamilton certificate.  This is a finite rational evaluation identity:
the third power of a `2 x 2` matrix is reduced to the matrix itself and the
identity, with coefficients given by its trace and determinant. -/
theorem twoByTwo_matrixPow_three (a b c d : Rat) :
    matrixPow (twoByTwoMatrix a b c d) 3 =
      matrixAdd
        (matrixScale
          ((twoByTwoTrace a b c d) ^ 2 - twoByTwoDeterminant a b c d)
          (twoByTwoMatrix a b c d))
        (matrixScale
          (-(twoByTwoTrace a b c d * twoByTwoDeterminant a b c d))
          (matrixIdentity 2)) := by
  change matrixMul (twoByTwoMatrix a b c d)
      (matrixMul (twoByTwoMatrix a b c d)
        (matrixMul (twoByTwoMatrix a b c d) (matrixIdentity 2))) = _
  rw [matrixMul_identity_right]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

/-! The next finite Cayley--Hamilton reduction, still entirely rational. -/

theorem twoByTwo_matrixPow_four (a b c d : Rat) :
    matrixPow (twoByTwoMatrix a b c d) 4 =
      matrixAdd
        (matrixScale
          ((twoByTwoTrace a b c d) ^ 3 -
            2 * twoByTwoTrace a b c d * twoByTwoDeterminant a b c d)
          (twoByTwoMatrix a b c d))
        (matrixScale
          (twoByTwoDeterminant a b c d ^ 2 -
            twoByTwoTrace a b c d ^ 2 * twoByTwoDeterminant a b c d)
          (matrixIdentity 2)) := by
  change matrixMul (twoByTwoMatrix a b c d)
      (matrixMul (twoByTwoMatrix a b c d)
        (matrixMul (twoByTwoMatrix a b c d)
          (matrixMul (twoByTwoMatrix a b c d) (matrixIdentity 2)))) = _
  rw [matrixMul_identity_right]
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
        matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp [twoByTwoTrace, twoByTwoDeterminant, matrixAdd, matrixMul,
          matrixScale, matrixIdentity, finiteSum_two]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

end HarmonicOscillator

/-- The degree-`r` ordered-simplex term for a constant coefficient matrix.
The scalar factor `T^r/r!` is the exact rational volume of the ordered
simplex of duration `T`; the matrix factor keeps the chronological order
visible.  This is a finite term, not yet an infinite matrix series. -/
def orderedSimplexVolume (T : Rat) : Nat -> Rat
  | 0 => 1
  | degree + 1 =>
      T / ((degree + 1 : Nat) : Rat) * orderedSimplexVolume T degree

theorem orderedSimplexVolume_eq_closed (T : Rat) (degree : Nat) :
    orderedSimplexVolume T degree = T ^ degree / factorialRat degree := by
  induction degree with
  | zero =>
      unfold orderedSimplexVolume factorialRat factorial
      rw [Rat.pow_zero]
      native_decide
  | succ degree ih =>
      rw [orderedSimplexVolume, ih, Rat.pow_succ,
        FormalPowerSeries.factorialRat_succ]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
      grind [Rat.mul_assoc, Rat.mul_comm]

def constantPeanoBakerSimplexTerm {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (degree : Nat) : RatMatrix dimension :=
  matrixScale (T ^ degree / factorialRat degree) (matrixPow A degree)

theorem constantPeanoBakerSimplexTerm_eq_orderedSimplexVolume
    {dimension : Nat} (A : RatMatrix dimension) (T : Rat) (degree : Nat) :
    constantPeanoBakerSimplexTerm A T degree =
      matrixScale (orderedSimplexVolume T degree) (matrixPow A degree) := by
  rw [orderedSimplexVolume_eq_closed]
  rfl

/-- A finite constant-coefficient Peano--Baker polynomial, assembled in
increasing degree order from its explicit ordered-simplex terms. -/
def constantPeanoBakerSimplexPartial {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) : Nat -> RatMatrix dimension
  | 0 => matrixZero dimension
  | terms + 1 => matrixAdd
      (constantPeanoBakerSimplexPartial A T terms)
      (constantPeanoBakerSimplexTerm A T terms)

theorem constantPeanoBakerSimplexTerm_zero {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) :
    constantPeanoBakerSimplexTerm A T 0 = matrixIdentity dimension := by
  unfold constantPeanoBakerSimplexTerm
  have hscalar : T ^ 0 / factorialRat 0 = (1 : Rat) := by
    rw [Rat.pow_zero]
    unfold factorialRat factorial
    native_decide
  change matrixScale (T ^ 0 / factorialRat 0) (matrixIdentity dimension) =
    matrixIdentity dimension
  rw [hscalar, matrixScale_one]

/-- Adjacent constant-coefficient simplex terms satisfy the expected
Peano--Baker recurrence: prepend the coefficient matrix and multiply by the
next time-volume factor `T/(r+1)`. -/
theorem constantPeanoBakerSimplexTerm_succ {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (degree : Nat) :
    constantPeanoBakerSimplexTerm A T (degree + 1) =
      matrixScale (T / ((degree + 1 : Nat) : Rat))
        (matrixMul A (constantPeanoBakerSimplexTerm A T degree)) := by
  unfold constantPeanoBakerSimplexTerm
  rw [matrixMul_matrixScale_right, matrixScale_comp]
  rw [Rat.pow_succ, FormalPowerSeries.factorialRat_succ]
  congr 1
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.inv_mul_rev]
  grind [Rat.mul_assoc, Rat.mul_comm]

theorem constantPeanoBakerSimplexPartial_succ {dimension : Nat}
    (A : RatMatrix dimension) (T : Rat) (terms : Nat) :
    constantPeanoBakerSimplexPartial A T (terms + 1) = matrixAdd
      (constantPeanoBakerSimplexPartial A T terms)
      (constantPeanoBakerSimplexTerm A T terms) := rfl

/-! ## Finite rotation-series core

The continuous rotation system is a later analytic construction.  Its
constant-coefficient Peano--Baker coefficients already have the familiar
finite even/odd split, which is the exact algebraic core of the eventual
comparison with cosine and sine. -/

namespace RotationSystem

/-- The counter-clockwise quarter-turn generator. -/
def generator : RatMatrix 2 :=
  fun i =>
    Fin.cases
      (fun j => Fin.cases 0 (fun _ => -1) j)
      (fun _ j => Fin.cases 1 (fun _ => 0) j)
      i

/-- Squaring the rotation generator is minus the identity.  This is a closed
finite rational matrix calculation. -/
theorem generator_square :
    matrixMul generator generator = matrixScale (-1) (matrixIdentity 2) := by
  funext i j
  refine Fin.cases ?_ ?_ i
  · refine Fin.cases ?_ ?_ j
    · native_decide
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      native_decide
  · intro i
    refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    refine Fin.cases ?_ ?_ j
    · native_decide
    · intro j
      refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      native_decide

/-- The matrix-power normalization of the preceding square identity. -/
theorem generator_pow_two :
    matrixPow generator 2 = matrixScale (-1) (matrixIdentity 2) := by
  change matrixMul generator (matrixMul generator (matrixIdentity 2)) =
    matrixScale (-1) (matrixIdentity 2)
  rw [matrixMul_identity_right]
  exact generator_square

/-- Even powers of the rotation generator are alternating scalar identities. -/
theorem generator_pow_even (k : Nat) :
    matrixPow generator (2 * k) =
      matrixScale ((-1 : Rat) ^ k) (matrixIdentity 2) := by
  induction k with
  | zero =>
      simp [matrixPow, matrixScale_one]
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 + 2 * k by omega]
      rw [matrixPow_add, generator_pow_two, ih]
      rw [matrixMul_matrixScale_right, matrixMul_identity_right,
        matrixScale_comp, Rat.pow_succ]

/-- Odd powers of the rotation generator are the same alternating scalar
times one quarter turn. -/
theorem generator_pow_odd (k : Nat) :
    matrixPow generator (2 * k + 1) =
      matrixScale ((-1 : Rat) ^ k) generator := by
  rw [matrixPow]
  rw [generator_pow_even]
  rw [matrixMul_matrixScale_right, matrixMul_identity_right]

/-- The even constant Peano--Baker coefficient for rotation has exactly the
alternating cosine-series matrix form. -/
theorem simplexTerm_even (T : Rat) (k : Nat) :
    constantPeanoBakerSimplexTerm generator T (2 * k) =
      matrixScale
        (T ^ (2 * k) / factorialRat (2 * k) * ((-1 : Rat) ^ k))
        (matrixIdentity 2) := by
  unfold constantPeanoBakerSimplexTerm
  rw [generator_pow_even, matrixScale_comp]

/-- The odd constant Peano--Baker coefficient for rotation has exactly the
alternating sine-series matrix form. -/
theorem simplexTerm_odd (T : Rat) (k : Nat) :
    constantPeanoBakerSimplexTerm generator T (2 * k + 1) =
      matrixScale
        (T ^ (2 * k + 1) / factorialRat (2 * k + 1) * ((-1 : Rat) ^ k))
        generator := by
  unfold constantPeanoBakerSimplexTerm
  rw [generator_pow_odd, matrixScale_comp]

/-- The degree-`2k` coefficient of the finite rotation polynomial. -/
def cosineCoefficient (T : Rat) (k : Nat) : Rat :=
  T ^ (2 * k) / factorialRat (2 * k) * ((-1 : Rat) ^ k)

/-- The degree-`2k+1` coefficient of the finite rotation polynomial. -/
def sineCoefficient (T : Rat) (k : Nat) : Rat :=
  T ^ (2 * k + 1) / factorialRat (2 * k + 1) * ((-1 : Rat) ^ k)

/-- An executable finite cosine-type prefix. -/
def cosinePrefix (T : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => cosinePrefix T n + cosineCoefficient T n

/-- An executable finite sine-type prefix. -/
def sinePrefix (T : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => sinePrefix T n + sineCoefficient T n

/-- The first `2n` constant Peano--Baker terms for the rotation system split
exactly into their cosine- and sine-type rational prefixes.  This is finite
matrix algebra only; it does not yet sum a continuous ODE or a complex raw
exponential. -/
theorem simplexPartial_even_split (T : Rat) (n : Nat) :
    constantPeanoBakerSimplexPartial generator T (2 * n) =
      matrixAdd
        (matrixScale (cosinePrefix T n) (matrixIdentity 2))
        (matrixScale (sinePrefix T n) generator) := by
  induction n with
  | zero =>
      simp only [constantPeanoBakerSimplexPartial, cosinePrefix, sinePrefix]
      funext i j
      unfold matrixZero matrixAdd matrixScale
      rw [Rat.zero_mul, Rat.zero_mul, Rat.zero_add]
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
      rw [constantPeanoBakerSimplexPartial_succ]
      rw [show 2 * n + 1 = (2 * n) + 1 by omega]
      rw [constantPeanoBakerSimplexPartial_succ, ih]
      rw [simplexTerm_even, simplexTerm_odd, matrixAdd_group_even_odd]
      rw [matrixAdd_scale_same, matrixAdd_scale_same]
      rfl

/-! The neighboring odd prefix is the same finite parity decomposition with
one additional even (cosine) coefficient.  Exposing both parities keeps the
finite ODE algebra aligned with the truncation index used by the power-series
and rotation evaluators. -/
theorem simplexPartial_odd_split (T : Rat) (n : Nat) :
    constantPeanoBakerSimplexPartial generator T (2 * n + 1) =
      matrixAdd
        (matrixScale (cosinePrefix T (n + 1)) (matrixIdentity 2))
        (matrixScale (sinePrefix T n) generator) := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  rw [constantPeanoBakerSimplexPartial_succ]
  rw [simplexPartial_even_split, simplexTerm_even]
  have hcomm (A B : RatMatrix 2) : matrixAdd A B = matrixAdd B A := by
    funext i j
    unfold matrixAdd
    exact Rat.add_comm _ _
  rw [matrixAdd_assoc, hcomm
    (matrixScale (sinePrefix T n) generator)
    (matrixScale (T ^ (2 * n) / factorialRat (2 * n) * ((-1 : Rat) ^ n))
      (matrixIdentity 2)), ← matrixAdd_assoc, matrixAdd_scale_same]
  rfl

end RotationSystem

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

/-- The scalar majorant for the terms omitted from a Peano--Baker transition
series.  If a submultiplicative matrix norm bounds `A` by `M` on an interval
of length `T`, its degree-`r` simplex contribution is bounded by
`(M*T)^r/r!`; this definition is the literal finite rational prefix of that
tail. -/
def peanoBakerFactorialTail (M T : Rat) (start : Nat) : Nat -> Rat :=
  RationalMajorant.factorialTailPartial (M * T) start

/-- A computable Peano--Baker factorial-tail prefix is bounded by twice its
first omitted term.  This is an all-finite statement: `terms` is arbitrary,
so it can be used to enclose every finite truncation before a raw matrix
algorithm is constructed. -/
theorem peanoBakerFactorialTail_bound {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (terms : Nat) :
    peanoBakerFactorialTail M T (RationalMajorant.factorialTailStart (M * T)) terms <=
      2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T)) := by
  unfold peanoBakerFactorialTail
  apply RationalMajorant.factorialTailPartial_bound_at_start
  exact Rat.mul_nonneg hM hT

/-- The same tail certificate records its explicit geometric decay after the
computable start.  This is the modulus needed for the eventual continuous
Peano--Baker raw-matrix construction. -/
theorem peanoBakerFactorialTail_shifted_bound {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (shift terms : Nat) :
    peanoBakerFactorialTail M T
        (RationalMajorant.factorialTailStart (M * T) + shift) terms <=
      2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T)) * ((1 : Rat) / 2) ^ shift := by
  unfold peanoBakerFactorialTail
  exact RationalMajorant.factorialTailPartial_shifted_bound
    (Rat.mul_nonneg hM hT)
    (RationalMajorant.factorialTailStart_satisfies (M * T)) shift terms

/-- The executable shift which turns the Peano--Baker factorial majorant
into a requested positive rational error budget. -/
def peanoBakerFactorialTailShift (M T : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (2 * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T))) eps

/-- After the displayed computable shift, every finite prefix of the omitted
Peano--Baker factorial tail is within the requested rational tolerance.  This
is the tail-modulus component needed for constructive matrix-series
uniqueness, independent of a completed function space. -/
theorem peanoBakerFactorialTail_shifted_le_eps {M T : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (eps : QPos) (terms : Nat) :
    peanoBakerFactorialTail M T
      (RationalMajorant.factorialTailStart (M * T) +
        peanoBakerFactorialTailShift M T eps) terms <= eps.val := by
  unfold peanoBakerFactorialTail peanoBakerFactorialTailShift
  exact RationalMajorant.factorialTailPartial_shifted_le_eps
    (Rat.mul_nonneg hM hT) eps terms

/-- The computable iteration count used in the zero-initial Volterra
uniqueness argument.  The factor B is a rational enclosure bound for a
candidate difference, while the remaining factor is the usual Peano--Baker
factorial-tail radius. -/
def zeroInitialVolterraIterationShift (M T B : Rat) (eps : QPos) : Nat :=
  RationalMajorant.halfDecayShift
    (B * (2 * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T)))) eps

/-- After this many ordered substitutions, a zero-initial Volterra estimate
of the form B * (M*T)^n / n! is below any requested positive rational
tolerance.  This is a finite rational estimate, not an appeal to a complete
space of functions. -/
theorem zeroInitialVolterra_iteration_le_eps {M T B : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (hB : 0 <= B) (eps : QPos) :
    B * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T) +
        zeroInitialVolterraIterationShift M T B eps) <= eps.val := by
  let shift := zeroInitialVolterraIterationShift M T B eps
  have htail := peanoBakerFactorialTail_shifted_bound hM hT shift 1
  have htailTerm :
      RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T) + shift) <=
        2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)) *
            ((1 : Rat) / 2) ^ shift := by
    simpa [peanoBakerFactorialTail,
      RationalMajorant.factorialTailPartial, Rat.zero_add] using htail
  have hscaled := Rat.mul_le_mul_of_nonneg_left htailTerm hB
  have htermNonneg : 0 <= RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T)) :=
    RationalMajorant.factorialTailTerm_nonneg (Rat.mul_nonneg hM hT) _
  have hradiusNonneg :
      0 <= B * (2 * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T))) := by
    exact Rat.mul_nonneg hB (Rat.mul_nonneg (by native_decide) htermNonneg)
  calc
    B * RationalMajorant.factorialTailTerm (M * T)
        (RationalMajorant.factorialTailStart (M * T) + shift) <=
        B * (2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)) *
            ((1 : Rat) / 2) ^ shift) := hscaled
    _ = (B * (2 * RationalMajorant.factorialTailTerm (M * T)
          (RationalMajorant.factorialTailStart (M * T)))) *
            ((1 : Rat) / 2) ^ shift := by
      grind [Rat.mul_assoc]
    _ <= eps.val := by
      simpa [zeroInitialVolterraIterationShift, shift] using
        RationalMajorant.halfDecayShift_spec hradiusNonneg eps

/-- A scalar error satisfying the repeated zero-initial Volterra estimate is
literally zero.  A continuous uniqueness proof need only establish this
finite bound for the norm of the difference of two candidate solutions; the
factorial-tail kernel below then closes the equality without a supremum or a
completeness argument. -/
def ZeroInitialVolterraIterationBound (M T B error : Rat) : Prop :=
  0 <= error /\
  forall iterations : Nat,
    error <= B * RationalMajorant.factorialTailTerm (M * T)
      (RationalMajorant.factorialTailStart (M * T) + iterations)

theorem zeroInitialVolterraIterationBound_eq_zero {M T B error : Rat}
    (hM : 0 <= M) (hT : 0 <= T) (hB : 0 <= B)
    (herror : ZeroInitialVolterraIterationBound M T B error) :
    error = 0 := by
  rcases herror with ⟨herrorNonneg, hiterations⟩
  by_cases hzero : error = 0
  · exact hzero
  · have herrorPos : 0 < error :=
      Rat.lt_of_le_of_ne herrorNonneg (Ne.symm hzero)
    let eps : QPos :=
      ⟨error / 2, by
        rw [Rat.div_def]
        exact Rat.mul_pos herrorPos
          ((Rat.inv_pos).2 (by native_decide : (0 : Rat) < 2))⟩
    have hiteration := hiterations
      (zeroInitialVolterraIterationShift M T B eps)
    have hsmall := zeroInitialVolterra_iteration_le_eps hM hT hB eps
    have hhalf : error <= error / 2 := by
      exact Rat.le_trans hiteration hsmall
    have hstrict : error / 2 < error := by
      rw [Rat.div_def]
      have hinv : (2 : Rat)⁻¹ < 1 := by native_decide
      calc
        error * (2 : Rat)⁻¹ < error * 1 :=
          Rat.mul_lt_mul_of_pos_left hinv herrorPos
        _ = error := Rat.mul_one _
    have hnot : ¬ error <= error / 2 := by
      simpa [Rat.not_le] using hstrict
    exact False.elim (hnot hhalf)

/-- A constructive uniqueness certificate for two interval-valued solutions
of `f' = f`.

The analytic layer supplies a nonnegative rational error at every rational
input and proves the iterated Volterra bound for that error.  This finite
Peano--Baker module then turns the factorial-tail estimate into pointwise
function agreement.  No norm completion, supremum, or completed real line is
part of this interface. -/
structure SelfDerivativeVolterraComparison
    (f g : FunctionOnInterval)
    (_hf : SolvesSelfDerivativeOnInterval f)
    (_hg : SolvesSelfDerivativeOnInterval g) where
  same_lower : f.lower = g.lower
  same_upper : f.upper = g.upper
  matrix_bound : Rat
  time_bound : Rat
  initial_error_bound : Rat
  matrix_bound_nonneg : 0 <= matrix_bound
  time_bound_nonneg : 0 <= time_bound
  initial_error_bound_nonneg : 0 <= initial_error_bound
  error : Rat -> Rat
  error_iterated :
    forall x,
      ZeroInitialVolterraIterationBound
        matrix_bound time_bound initial_error_bound (error x)
  equivalent_of_error_zero :
    forall x
      (hxF : inDomainInterval f.lower f.upper x)
      (hxG : inDomainInterval g.lower g.upper x),
      error x = 0 ->
        (PartialRealFunRaw.apply f.raw f.valid_on x (f.defined_on x hxF)).Equiv
          (PartialRealFunRaw.apply g.raw g.valid_on x (g.defined_on x hxG))

namespace SelfDerivativeVolterraComparison

/-- The factorial-tail comparison closes the requested pointwise agreement. -/
theorem equivalent
    {f g : FunctionOnInterval}
    {hf : SolvesSelfDerivativeOnInterval f}
    {hg : SolvesSelfDerivativeOnInterval g}
    (comparison : SelfDerivativeVolterraComparison f g hf hg) :
    FunctionOnInterval.Equivalent f g := by
  refine ⟨comparison.same_lower, comparison.same_upper, ?_⟩
  intro x hxF hxG
  apply comparison.equivalent_of_error_zero x hxF hxG
  exact zeroInitialVolterraIterationBound_eq_zero
    comparison.matrix_bound_nonneg
    comparison.time_bound_nonneg
    comparison.initial_error_bound_nonneg
    (comparison.error_iterated x)

end SelfDerivativeVolterraComparison

/-- The remaining analytic task for continuous Peano--Baker uniqueness,
stated as a reusable finite-certificate provider.  It is invoked only after
the two candidates have been shown to share both their rational initial point
and their certified raw-real initial value. -/
def SelfDerivativeVolterraUniqueness : Prop :=
  forall f g,
    (hf : SolvesSelfDerivativeOnInterval f) ->
    (hg : SolvesSelfDerivativeOnInterval g) ->
    hf.initial = hg.initial ->
    hf.initial_value.Equiv hg.initial_value ->
    Nonempty (SelfDerivativeVolterraComparison f g hf hg)

/-- A supply of finite Volterra comparison certificates proves the project's
topology-free uniqueness principle for `f' = f` with a common initial value. -/
theorem selfDerivativeInitialValueUnique_of_volterra
    (hvolterra : SelfDerivativeVolterraUniqueness) :
    SelfDerivativeInitialValueUnique := by
  intro f g hf hg hinitial hvalue
  rcases hvolterra f g hf hg hinitial hvalue with ⟨comparison⟩
  exact comparison.equivalent

end LinearODE

end ComputableAnalysis
