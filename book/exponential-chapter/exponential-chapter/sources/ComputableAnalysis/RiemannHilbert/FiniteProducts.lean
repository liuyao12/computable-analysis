import ComputableAnalysis.RiemannHilbert.ScalarAlgebra

/-! Finite triangular and rectangular products, before any infinite sum. -/
namespace ComputableAnalysis.RiemannHilbert.FiniteProducts
open ScalarAlgebra

def partialSum (f : Nat → Value) : Nat → Value
  | 0 => 0
  | n+1 => partialSum f n + f n

def block (f : Nat → Value) (N k : Nat) : Value := partialSum (fun j => f (N+j)) k

def diagonal (f g : Nat → Value) (N : Nat) : Value :=
  partialSum (fun i => f i*g (N-i)) (N+1)

def triangle (f g : Nat → Value) (N : Nat) : Value :=
  partialSum (fun i => f i*partialSum g (N-i)) N

def missing (f g : Nat → Value) (N : Nat) : Value :=
  partialSum (fun i => f i*block g (N-i) i) N

theorem prefix_congr (f g : Nat → Value) (N : Nat) (h : ∀ i, i<N → f i=g i) :
    partialSum f N = partialSum g N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [partialSum, partialSum, ih (fun i hi => h i (by omega)), h N (by omega)]

theorem prefix_add (f g : Nat → Value) (N : Nat) :
    partialSum (fun i => f i+g i) N = partialSum f N + partialSum g N := by
  induction N with
  | zero => change (0 : Value)=0+0; grind
  | succ N ih => rw [partialSum, partialSum, partialSum, ih]; grind

theorem prefix_mul (f : Nat → Value) (v : Value) (N : Nat) :
    partialSum (fun i => f i*v) N = partialSum f N * v := by
  induction N with
  | zero => change (0 : Value)=0*v; grind
  | succ N ih => rw [partialSum, partialSum, ih]; grind

theorem prefix_append (f : Nat → Value) (N k : Nat) :
    partialSum f (N+k) = partialSum f N + block f N k := by
  induction k with
  | zero => change partialSum f N=partialSum f N+0; grind
  | succ k ih =>
    change partialSum f (N+k)+f (N+k) = partialSum f N+(block f N k+f (N+k))
    rw [ih]; grind

theorem triangle_succ (f g : Nat → Value) (N : Nat) :
    triangle f g (N+1) = triangle f g N + diagonal f g N := by
  unfold triangle diagonal
  rw [partialSum]
  have he : partialSum (fun i => f i*partialSum g (N+1-i)) N =
      partialSum (fun i => f i*partialSum g (N-i)+f i*g (N-i)) N := by
    apply prefix_congr
    intro i hi
    have hidx : N+1-i = (N-i)+1 := by omega
    rw [hidx, partialSum]
    grind
  rw [he]
  rw [prefix_add]
  have hN : N+1-N = 1 := by omega
  rw [hN]
  change (partialSum (fun i => f i*partialSum g (N-i)) N+partialSum (fun i => f i*g (N-i)) N)+
    f N*(0+g 0) =
    partialSum (fun i => f i*partialSum g (N-i)) N+
      (partialSum (fun i => f i*g (N-i)) N+f N*g (N-N))
  rw [Nat.sub_self]
  grind

theorem triangle_diagonals (f g : Nat → Value) (N : Nat) :
    triangle f g N = partialSum (fun k => diagonal f g k) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [triangle_succ, partialSum, ih]

/-- The discrepancy between the rectangular product and the first diagonals
consists precisely of the omitted upper-triangular finite blocks. -/
theorem rectangular_triangle (f g : Nat → Value) (N : Nat) :
    partialSum f N * partialSum g N = triangle f g N + missing f g N := by
  rw [← prefix_mul]
  have he : partialSum (fun i => f i*partialSum g N) N =
      partialSum (fun i => f i*partialSum g (N-i)+f i*block g (N-i) i) N := by
    apply prefix_congr
    intro i hi
    have hidx : N-i+i=N := by omega
    have hp := prefix_append g (N-i) i
    rw [hidx] at hp
    rw [hp]
    grind
  rw [he, prefix_add]
  rfl

/-- Triangular summation for an arbitrary two-index kernel. This also covers
operator coefficients whose factors do not commute. -/
def kernelTriangle (f : Nat → Nat → Value) (N : Nat) : Value :=
  partialSum (fun i => partialSum (f i) (N-i)) N

def kernelDiagonal (f : Nat → Nat → Value) (N : Nat) : Value :=
  partialSum (fun i => f i (N-i)) (N+1)

theorem kernelTriangle_succ (f : Nat → Nat → Value) (N : Nat) :
    kernelTriangle f (N+1) = kernelTriangle f N + kernelDiagonal f N := by
  unfold kernelTriangle kernelDiagonal
  rw [partialSum]
  have he : partialSum (fun i => partialSum (f i) (N+1-i)) N =
      partialSum (fun i => partialSum (f i) (N-i)+f i (N-i)) N := by
    apply prefix_congr
    intro i hi
    have hidx : N+1-i = (N-i)+1 := by omega
    rw [hidx, partialSum]
  rw [he, prefix_add]
  have hN : N+1-N=1 := by omega
  rw [hN]
  change (partialSum (fun i => partialSum (f i) (N-i)) N +
      partialSum (fun i => f i (N-i)) N)+(0+f N 0) =
    partialSum (fun i => partialSum (f i) (N-i)) N+
      (partialSum (fun i => f i (N-i)) N+f N (N-N))
  rw [Nat.sub_self]
  grind

theorem kernelTriangle_diagonals (f : Nat → Nat → Value) (N : Nat) :
    kernelTriangle f N = partialSum (fun k => kernelDiagonal f k) N := by
  induction N with
  | zero => rfl
  | succ N ih => rw [kernelTriangle_succ, partialSum, ih]

theorem rectangular_kernel (f : Nat → Nat → Value) (N : Nat) :
    partialSum (fun i => partialSum (f i) N) N =
      kernelTriangle f N + partialSum (fun i => block (f i) (N-i) i) N := by
  have he : partialSum (fun i => partialSum (f i) N) N =
      partialSum (fun i => partialSum (f i) (N-i)+block (f i) (N-i) i) N := by
    apply prefix_congr
    intro i hi
    have hidx : N-i+i=N := by omega
    have hp := prefix_append (f i) (N-i) i
    rw [hidx] at hp
    exact hp
  rw [he, prefix_add]
  rfl

end ComputableAnalysis.RiemannHilbert.FiniteProducts
