import ComputableAnalysis.ZetaReal.Binomial
import ComputableAnalysis.DirichletSeries

/-! Finite rational moments for the generalized-binomial zeta construction. -/
namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries DirichletSeries

def reciprocal (n : Nat) : Rat := 1/((n : Rat)+1)
def node (n : Nat) : Rat := 1-reciprocal n
def kernel (k n : Nat) : Rat := reciprocal n^2*node n^k
def moment (k N : Nat) : Rat := sumBelow (kernel k) N

theorem reciprocal_bounds (n : Nat) : 0 < reciprocal n ∧ reciprocal n ≤ 1 := by
  have hn := Rat.natCast_nonneg (a := n)
  have hi := Rat.mul_inv_cancel ((n : Rat)+1) (by grind)
  have hp := Rat.inv_pos.mpr (by grind : 0 < (n : Rat)+1)
  have hh := Rat.mul_nonneg hn (Rat.le_of_lt hp)
  unfold reciprocal
  rw [Rat.div_def]
  grind only

theorem node_bounds (n : Nat) : 0 ≤ node n ∧ node n ≤ 1 := by
  have := reciprocal_bounds n
  unfold node
  grind only

@[simp] theorem node_zero : node 0=0 := by decide +kernel

theorem node_step (n : Nat) : node n ≤ node (n+1) ∧ reciprocal n^2 ≤ 2*(node (n+1)-node n) := by
  have hn := Rat.natCast_nonneg (a := n)
  have h1 := Rat.mul_inv_cancel ((n : Rat)+1) (by grind)
  have h2 := Rat.mul_inv_cancel ((n : Rat)+2) (by grind)
  have hp1 := Rat.inv_pos.mpr (by grind : 0 < (n : Rat)+1)
  have hp2 := Rat.inv_pos.mpr (by grind : 0 < (n : Rat)+2)
  have he : ((n : Rat)+1)⁻¹-((n : Rat)+2)⁻¹ = ((n : Rat)+1)⁻¹*((n : Rat)+2)⁻¹ := by grind only
  have hprod := Rat.mul_nonneg (Rat.le_of_lt hp1) (Rat.le_of_lt hp2)
  have hnon := Rat.mul_nonneg hn (Rat.mul_nonneg
    (Rat.mul_nonneg (Rat.le_of_lt hp1) (Rat.le_of_lt hp1)) (Rat.le_of_lt hp2))
  have hid : 2*(((n : Rat)+1)⁻¹-((n : Rat)+2)⁻¹)-((n : Rat)+1)⁻¹*((n : Rat)+1)⁻¹ =
      (n : Rat)*((n : Rat)+1)⁻¹*((n : Rat)+1)⁻¹*((n : Rat)+2)⁻¹ := by grind only
  simp only [node, reciprocal, Rat.div_def, Rat.natCast_add, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  have hecast : (n : Rat)+1+1=(n : Rat)+2 := by grind
  constructor <;> grind only

private theorem power_tangent {a b : Rat} (ha : 0 ≤ a) (hab : a ≤ b) (k : Nat) :
    ((k : Rat)+1)*a^k*(b-a) ≤ b^(k+1)-a^(k+1) := by
  induction k with
  | zero => simp only [Rat.pow_zero, Rat.pow_succ, Rat.one_mul]; grind only
  | succ k ih =>
    have h1 := Rat.mul_le_mul_of_nonneg_left ih ha
    have hp := pow_base_mono ha hab (k+1)
    have h2 := Rat.mul_le_mul_of_nonneg_right hp (by grind : 0 ≤ b-a)
    simp only [Rat.pow_succ, Rat.natCast_add] at *
    grind only

private theorem node_power_le_one (n k : Nat) : node n^k ≤ 1 := by
  have h := pow_base_mono (node_bounds n).1 (node_bounds n).2 k
  have h1 : (1 : Rat)^k=1 := by
    clear h
    induction k with
    | zero => rfl
    | succ k ih => rw [Rat.pow_succ, ih]; decide +kernel
  rwa [h1] at h

theorem kernel_nonneg (k n : Nat) : 0 ≤ kernel k n :=
  Rat.mul_nonneg (Rat.pow_nonneg (Rat.le_of_lt (reciprocal_bounds n).1))
    (Rat.pow_nonneg (node_bounds n).1)

theorem kernel_le_square (k n : Nat) : kernel k n ≤ zetaTwoTerm n := by
  have h := Rat.mul_le_mul_of_nonneg_left (node_power_le_one n k)
    (Rat.pow_nonneg (n := 2) (Rat.le_of_lt (reciprocal_bounds n).1))
  have he : reciprocal n^2=zetaTwoTerm n := by
    simp only [reciprocal, zetaTwoTerm, Rat.div_def, Rat.inv_mul_rev,
      Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.natCast_add]
    grind only
  unfold kernel
  rw [← he]
  grind only

/-- A finite telescoping estimate replaces an appeal to an improper integral. -/
theorem kernel_telescope (k n : Nat) :
    ((k : Rat)+1)*kernel k n ≤ 2*(node (n+1)^(k+1)-node n^(k+1)) := by
  have h1 := Rat.mul_le_mul_of_nonneg_left (node_step n).2
    (Rat.mul_nonneg (by have := Rat.natCast_nonneg (a := k); grind : 0 ≤ (k : Rat)+1)
      (Rat.pow_nonneg (n := k) (node_bounds n).1))
  have h2 := power_tangent (node_bounds n).1 (node_step n).1 k
  unfold kernel
  grind only

theorem moment_nonneg (k N : Nat) : 0 ≤ moment k N := by
  induction N with
  | zero => exact Rat.le_refl
  | succ N ih =>
    unfold moment at *
    rw [sumBelow_succ]
    exact Rat.add_nonneg ih (kernel_nonneg k N)

theorem moment_bound (k N : Nat) : ((k : Rat)+1)*moment k N ≤ 2 := by
  have all (N : Nat) : ((k : Rat)+1)*moment k N ≤ 2*node N^(k+1) := by
    induction N with
    | zero => simp [moment, Rat.pow_succ]
    | succ N ih =>
      have h := kernel_telescope k N
      unfold moment at *
      rw [sumBelow_succ]
      grind only
  have h := all N
  have h1 := node_power_le_one N (k+1)
  grind only

theorem moment_tail {N : Nat} (hN : 0 < N) (k L : Nat) :
    0 ≤ moment k (N+L)-moment k N ∧ moment k (N+L)-moment k N ≤ 1/(N : Rat) := by
  have all (L : Nat) : 0 ≤ moment k (N+L)-moment k N ∧
      moment k (N+L)-moment k N ≤ zetaTwoFiniteTail N L := by
    induction L with
    | zero => simp [zetaTwoFiniteTail]; grind
    | succ L ih =>
      have hn := kernel_nonneg k (N+L)
      have hb := kernel_le_square k (N+L)
      unfold moment at *
      rw [show N+(L+1)=(N+L)+1 by omega, sumBelow_succ, zetaTwoFiniteTail_succ]
      grind only
  exact ⟨(all L).1, Rat.le_trans (all L).2 (zetaTwoFiniteTail_le_tailBound N hN L)⟩

end ComputableAnalysis.ZetaReal
