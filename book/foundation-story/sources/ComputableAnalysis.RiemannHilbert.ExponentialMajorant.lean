import ComputableAnalysis.RiemannHilbert.ExponentialCoefficients

/-! Factorial decay converted into an executable geometric majorant at any
positive rate. This is the convergence step needed for an entire exponential,
including arbitrary represented matrix entries. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def weight (B : Rat) : Nat → Rat
  | 0 => 1
  | k+1 => (B/((k+1 : Nat) : Rat))*weight B k

theorem weight_nonneg (B : Rat) (hB : 0 ≤ B) (k : Nat) : 0 ≤ weight B k := by
  induction k with
  | zero => exact (by decide : (0 : Rat) ≤ 1)
  | succ k ih =>
      have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
      have hr : 0 ≤ B/((k+1 : Nat) : Rat) := by
        rw [Rat.div_def]
        exact Rat.mul_nonneg hB (Rat.le_of_lt ((Rat.inv_pos).2 hd))
      exact Rat.mul_nonneg hr ih

def cutoff (T : Rat) : Nat := T.num.natAbs+1

theorem le_cutoff (T : Rat) : T ≤ (cutoff T : Rat) := by
  by_cases hpos : 0 < T
  · have hd : 0 < (T.den : Rat) := (Rat.natCast_pos).2 (Nat.pos_of_ne_zero T.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := (T.den : Rat)) ?_ hd
    rw [Rat.mul_comm T (T.den : Rat), rat_den_mul_self]
    have hnum : 0 ≤ T.num := Int.le_of_lt (rat_num_pos_of_pos hpos)
    have he : (T.num.natAbs : Rat) = (T.num : Rat) := by
      exact_mod_cast Int.natAbs_of_nonneg hnum
    calc
      (T.num : Rat) = (T.num.natAbs : Rat) := he.symm
      _ ≤ (cutoff T : Rat) := by exact_mod_cast Nat.le_succ T.num.natAbs
      _ ≤ (cutoff T : Rat)*(T.den : Rat) := by
        exact_mod_cast Nat.le_mul_of_pos_right (cutoff T) (Nat.pos_of_ne_zero T.den_nz)
  · exact Rat.le_trans (by grind : T ≤ 0) Rat.natCast_nonneg

def budget (T : Rat) : Rat := finiteBound ((List.range (cutoff T+1)).map (weight T))

theorem budget_nonneg (T : Rat) : 0 ≤ budget T := finiteBound_nonneg _

theorem weight_le_budget (T : Rat) (hT : 0 ≤ T) (k : Nat) : weight T k ≤ budget T := by
  induction k with
  | zero => exact le_finiteBound _ _ (List.mem_map.mpr ⟨0, by simp, rfl⟩)
  | succ k ih =>
      by_cases hk : k+1 ≤ cutoff T
      · exact le_finiteBound _ _ (List.mem_map.mpr ⟨k+1, List.mem_range.mpr (by omega), rfl⟩)
      · have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
        have ht : T ≤ ((k+1 : Nat) : Rat) :=
          Rat.le_trans (le_cutoff T) (by exact_mod_cast (show cutoff T ≤ k+1 by omega))
        have hr : T/((k+1 : Nat) : Rat) ≤ 1 := by
          apply Rat.le_of_mul_le_mul_right (c := ((k+1 : Nat) : Rat))
          · rw [Rat.div_mul_cancel (Rat.ne_of_gt hd), Rat.one_mul]; exact ht
          · exact hd
        exact Rat.le_trans
          (by change (T/((k+1 : Nat) : Rat))*weight T k ≤ weight T k
              have := Rat.mul_le_mul_of_nonneg_right hr (weight_nonneg T hT k)
              simpa only [Rat.one_mul] using this) ih

theorem weight_rescale (B K : Rat) (hK : 0 < K) (k : Nat) :
    weight B k = weight (B/K) k*K^k := by
  induction k with
  | zero => simp [weight]
  | succ k ih =>
      change (B/((k+1 : Nat) : Rat))*weight B k =
        ((B/K)/((k+1 : Nat) : Rat))*weight (B/K) k*K^(k+1)
      rw [ih, Rat.pow_succ]
      have he : ((B/K)/((k+1 : Nat) : Rat))*K = B/((k+1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.div_def, Rat.div_def]
        calc
          _ = (B*((k+1 : Nat) : Rat)⁻¹)*(K*K⁻¹) := by grind
          _ = _ := by rw [Rat.mul_inv_cancel K (Rat.ne_of_gt hK), Rat.mul_one]
      calc
        _ = (((B/K)/((k+1 : Nat) : Rat))*K)*weight (B/K) k*K^k := by rw [he]; grind
        _ = _ := by grind

def geometricBudget (B K : Rat) : Rat := budget (B/K)

theorem geometricBudget_nonneg (B K : Rat) : 0 ≤ geometricBudget B K := budget_nonneg _

theorem weight_geometric (B K : Rat) (hB : 0 ≤ B) (hK : 0 < K) (k : Nat) :
    weight B k ≤ geometricBudget B K*K^k := by
  rw [weight_rescale B K hK k]
  have hT : 0 ≤ B/K := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hB (Rat.le_of_lt ((Rat.inv_pos).2 hK))
  exact Rat.mul_le_mul_of_nonneg_right
    (weight_le_budget (B/K) hT k) (Rat.pow_nonneg (Rat.le_of_lt hK))

theorem coefficient_weight_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (E : Rat) (hE : 0 ≤ E) (hx : CoordinateBound x E) (k : Nat) :
    CoordinateBound (coefficient A x k) (weight (ValueMap.linearBound A) k*E) := by
  induction k with
  | zero => simpa only [coefficient, weight, Rat.one_mul] using hx
  | succ k ih =>
      have hd : 0 < ((k+1 : Nat) : Rat) := (Rat.natCast_pos).2 (by omega)
      have hr : 0 ≤ 1/((k+1 : Nat) : Rat) := by
        rw [Rat.div_def, Rat.one_mul]
        exact Rat.le_of_lt ((Rat.inv_pos).2 hd)
      have hs := bound_ratScale hr
        (ValueMap.linear_bound A hA _
          (Rat.mul_nonneg (weight_nonneg _ (ValueMap.linearBound_nonneg A) k) hE) _ ih)
      change CoordinateBound (coefficient A x (k+1)) _ at hs
      have he : (1/((k+1 : Nat) : Rat))*(ValueMap.linearBound A*(weight (ValueMap.linearBound A) k*E)) =
          weight (ValueMap.linearBound A) (k+1)*E := by
        simp only [weight, Rat.div_def, Rat.one_mul]; grind
      rw [he] at hs; exact hs

theorem coefficient_geometric_bound (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (K : Rat) (hK : 0 < K) (x : Fiber n) (E : Rat) (hE : 0 ≤ E)
    (hx : CoordinateBound x E) (k : Nat) :
    CoordinateBound (coefficient A x k) ((geometricBudget (ValueMap.linearBound A) K*E)*K^k) := by
  intro i
  apply (coefficient_weight_bound A hA x E hE hx k i).mono
  have := Rat.mul_le_mul_of_nonneg_right
    (weight_geometric _ K (ValueMap.linearBound_nonneg A) hK k) hE
  grind

/-- Every positive geometric rate is available; the prefactor is constructed,
not supplied as a convergence hypothesis. -/
theorem coefficientMap_majorant (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (K : Rat) (hK : 0 < K) :
    OperatorMajorant (coefficientMap A) (geometricBudget (ValueMap.linearBound A) K) K := by
  intro k E hE x hx i
  apply (coefficient_geometric_bound A hA K hK x E hE hx k i).mono
  have hB : 0 ≤ geometricBudget (ValueMap.linearBound A) K*K^k*E :=
    Rat.mul_nonneg (Rat.mul_nonneg (geometricBudget_nonneg (ValueMap.linearBound A) K)
      (Rat.pow_nonneg (n := k) (Rat.le_of_lt hK))) hE
  grind

end ComputableAnalysis.RiemannHilbert.MatrixExponential
