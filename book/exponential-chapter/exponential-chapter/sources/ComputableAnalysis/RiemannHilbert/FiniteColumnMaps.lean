import ComputableAnalysis.RiemannHilbert.FiniteFiberBasis

/-! Actual finite matrix operators constructed from arbitrary valid represented
columns. Their evaluator uses only finite sums and scalar products, including
rank zero. Linearity and basis agreement are derived from the computation. -/
namespace ComputableAnalysis.RiemannHilbert.ValueMap
open ComplexRaw FunctionTheory
variable {n m : Nat}

def columnPrefix (C : Fin n → Fiber m) (x : Fiber n) : Nat → Fiber m
  | 0 => Fiber.zero m
  | k+1 => if hk : k < n then
      Fiber.add (columnPrefix C x k) (Fiber.scale (Fiber.coordinate x ⟨k,hk⟩) (C ⟨k,hk⟩))
    else columnPrefix C x k

theorem columnPrefix_congr (C E : Fin n → Fiber m) (hCE : ∀ i, C i ≈ E i)
    (x y : Fiber n) (hxy : x ≈ y) (k : Nat) : columnPrefix C x k ≈ columnPrefix E y k := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
    rw [columnPrefix,columnPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk,dif_pos hk]
      exact Fiber.add_congr ih (Fiber.scale_congr (hxy ⟨k,hk⟩) (hCE ⟨k,hk⟩))
    · rw [dif_neg hk,dif_neg hk]
      exact ih

theorem columnPrefix_add (C : Fin n → Fiber m) (x y : Fiber n) (k : Nat) :
    columnPrefix C (Fiber.add x y) k ≈ Fiber.add (columnPrefix C x k) (columnPrefix C y k) := by
  induction k with
  | zero => exact Setoid.symm (Fiber.zero_add _)
  | succ k ih =>
    rw [columnPrefix,columnPrefix,columnPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk,dif_pos hk,dif_pos hk]
      have ht : Fiber.scale (Fiber.coordinate (Fiber.add x y) ⟨k,hk⟩) (C ⟨k,hk⟩) ≈
          Fiber.add (Fiber.scale (Fiber.coordinate x ⟨k,hk⟩) (C ⟨k,hk⟩))
            (Fiber.scale (Fiber.coordinate y ⟨k,hk⟩) (C ⟨k,hk⟩)) :=
        fun j => add_mul_equiv _ _ _ (x.property ⟨k,hk⟩) (y.property ⟨k,hk⟩) ((C ⟨k,hk⟩).property j)
      exact Setoid.trans (Fiber.add_congr ih ht) (Fiber.add_four _ _ _ _)
    · rw [dif_neg hk,dif_neg hk,dif_neg hk]
      exact ih

theorem columnPrefix_scale (C : Fin n → Fiber m) (a : Scalar) (x : Fiber n) (k : Nat) :
    columnPrefix C (Fiber.scale a x) k ≈ Fiber.scale a (columnPrefix C x k) := by
  induction k with
  | zero => exact Setoid.symm (Fiber.scale_zero a)
  | succ k ih =>
    rw [columnPrefix,columnPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk,dif_pos hk]
      exact Setoid.trans (Fiber.add_congr ih
        (Setoid.symm (Fiber.scale_scale a (Fiber.coordinate x ⟨k,hk⟩) (C ⟨k,hk⟩))))
        (Setoid.symm (Fiber.scale_add a _ _))
    · rw [dif_neg hk,dif_neg hk]
      exact ih

theorem columnPrefix_basis (C : Fin n → Fiber m) (i : Fin n) (k : Nat) :
    columnPrefix C (Fiber.basis i) k ≈ (if i.val < k then C i else Fiber.zero m) := by
  induction k with
  | zero =>
    rw [if_neg (by omega)]
    exact Setoid.refl _
  | succ k ih =>
    rw [columnPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk]
      by_cases hi : i.val = k
      · have he : (⟨k,hk⟩ : Fin n) = i := Fin.ext hi.symm
        have hp : columnPrefix C (Fiber.basis i) k ≈ Fiber.zero m := by
          simpa only [if_neg (show ¬ i.val < k by omega)] using ih
        have ht : Fiber.scale (Fiber.coordinate (Fiber.basis i) ⟨k,hk⟩) (C ⟨k,hk⟩) ≈ C i := by
          rw [he]
          intro j
          change (mul (if i = i then one else zero) ((C i).val j)).Equiv ((C i).val j)
          simp only [if_pos rfl]
          exact one_mul_equiv _ ((C i).property j)
        rw [if_pos (show i.val < k+1 by omega)]
        exact Setoid.trans (Fiber.add_congr hp ht) (Fiber.zero_add _)
      · have he : (⟨k,hk⟩ : Fin n) ≠ i := fun h => hi (congrArg Fin.val h).symm
        have ht : Fiber.scale (Fiber.coordinate (Fiber.basis i) ⟨k,hk⟩) (C ⟨k,hk⟩) ≈ Fiber.zero m := by
          intro j
          change (mul (if (⟨k,hk⟩ : Fin n) = i then one else zero) ((C ⟨k,hk⟩).val j)).Equiv zero
          rw [if_neg he]
          exact zero_mul_equiv _ ((C ⟨k,hk⟩).property j)
        have hh : (i.val < k+1) = (i.val < k) := propext (by omega)
        simp only [hh]
        exact Setoid.trans (Fiber.add_congr ih ht) (Fiber.add_zero _)
    · rw [dif_neg hk]
      have hp : i.val < k := by have := i.isLt; omega
      rw [if_pos (show i.val < k+1 by omega)]
      simpa only [if_pos hp] using ih

def ofColumns (C : Fin n → Fiber m) : ValueMap (Fiber n) (Fiber m) where
  eval x := columnPrefix C x n
  congr hxy := columnPrefix_congr C C (fun _ => Setoid.refl _) _ _ hxy n

theorem ofColumns_linear (C : Fin n → Fiber m) : IsLinear (ofColumns C) :=
  ⟨fun x y => columnPrefix_add C x y n,fun a x => columnPrefix_scale C a x n⟩

theorem ofColumns_basis (C : Fin n → Fiber m) (i : Fin n) : (ofColumns C).eval (Fiber.basis i) ≈ C i := by
  change columnPrefix C (Fiber.basis i) n ≈ C i
  simpa only [if_pos i.isLt] using columnPrefix_basis C i n

theorem ofColumns_congr (C E : Fin n → Fiber m) (hCE : ∀ i, C i ≈ E i) :
    (ofColumns C).Equiv (ofColumns E) := fun x => columnPrefix_congr C E hCE x x (Setoid.refl _) n

theorem ofColumns_reconstruct (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) :
    (ofColumns (fun i => f.eval (Fiber.basis i))).Equiv f :=
  (linear_equiv_iff_basis _ _ (ofColumns_linear _) hf).mpr (fun i => ofColumns_basis _ i)

end ComputableAnalysis.RiemannHilbert.ValueMap
