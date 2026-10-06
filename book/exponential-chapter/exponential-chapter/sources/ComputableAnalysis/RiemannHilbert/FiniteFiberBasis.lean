import ComputableAnalysis.RiemannHilbert.VectorFiniteSums

/-! Finite basis expansion and a computed bound for every supplied linear map.
The bound evaluates the map on finitely many rational basis vectors. No
operator norm, completed scalar field, or continuity assumption is used. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory LocalSystem

namespace Fiber

def coordinate (x : Fiber n) (i : Fin n) : Scalar := ⟨x.val i, x.property i⟩

def basis (i : Fin n) : Fiber n :=
  ⟨fun j => if j = i then ComplexRaw.one else ComplexRaw.zero,
    fun j => by change (if j = i then ComplexRaw.one else ComplexRaw.zero).Valid; split <;> exact ofQComplex_valid _⟩

theorem basis_term (x : Fiber n) (i j : Fin n) :
    ((scale (coordinate x i) (basis i)).val j).Equiv
      (if j = i then x.val j else ComplexRaw.zero) := by
  by_cases h : j = i
  · subst j
    change (mul (x.val i) (if i = i then ComplexRaw.one else ComplexRaw.zero)).Equiv
      (if i = i then x.val i else ComplexRaw.zero)
    simp only
    exact mul_one_equiv _ (x.property i)
  · change (mul (x.val i) (if j = i then ComplexRaw.one else ComplexRaw.zero)).Equiv
      (if j = i then x.val j else ComplexRaw.zero)
    rw [if_neg h, if_neg h]
    exact mul_zero_equiv _ (x.property i)

def basisPrefix (x : Fiber n) : Nat → Fiber n
  | 0 => zero n
  | k+1 => if hk : k < n then
      add (basisPrefix x k) (scale (coordinate x ⟨k,hk⟩) (basis ⟨k,hk⟩))
    else basisPrefix x k

theorem basisPrefix_coordinate (x : Fiber n) (k : Nat) (i : Fin n) :
    ((basisPrefix x k).val i).Equiv (if i.val < k then x.val i else ComplexRaw.zero) := by
  induction k with
  | zero =>
    rw [if_neg (by omega)]
    exact equiv_refl _ (ofQComplex_valid _)
  | succ k ih =>
    rw [basisPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk]
      by_cases hi : i.val = k
      · have he : i = (⟨k,hk⟩ : Fin n) := Fin.ext hi
        have hnext : i.val < k+1 := by omega
        have hp : ((basisPrefix x k).val i).Equiv ComplexRaw.zero := by
          simpa only [if_neg (show ¬i.val < k by omega)] using ih
        have ht : ((scale (coordinate x ⟨k,hk⟩) (basis ⟨k,hk⟩)).val i).Equiv (x.val i) := by
          simpa only [if_pos he] using basis_term x ⟨k,hk⟩ i
        rw [if_pos hnext]
        exact equiv_trans ((add (basisPrefix x k) (scale (coordinate x ⟨k,hk⟩) (basis ⟨k,hk⟩))).property i)
          (add_valid (ofQComplex_valid _) (x.property i)) (x.property i)
          (add_equiv hp ht) (zero_add_equiv _ (x.property i))
      · have he : i ≠ (⟨k,hk⟩ : Fin n) := fun h => hi (congrArg Fin.val h)
        have ht : ((scale (coordinate x ⟨k,hk⟩) (basis ⟨k,hk⟩)).val i).Equiv ComplexRaw.zero := by
          simpa only [if_neg he] using basis_term x ⟨k,hk⟩ i
        have hh : (i.val < k+1) = (i.val < k) := propext (by omega)
        simp only [hh]
        have hv : (if i.val < k then x.val i else ComplexRaw.zero).Valid := by
          split
          · exact x.property i
          · exact ofQComplex_valid _
        exact equiv_trans ((add (basisPrefix x k) (scale (coordinate x ⟨k,hk⟩) (basis ⟨k,hk⟩))).property i)
          (add_valid hv (ofQComplex_valid _)) hv (add_equiv ih ht) (add_zero_equiv _ hv)
    · rw [dif_neg hk]
      have hprev : i.val < k := by have := i.isLt; omega
      rw [if_pos (show i.val < k+1 by omega)]
      simpa only [if_pos hprev] using ih

/-- Exact finite basis expansion for arbitrary valid represented coordinates. -/
theorem basis_expansion (x : Fiber n) : basisPrefix x n ≈ x := by
  intro i
  simpa only [if_pos i.isLt] using basisPrefix_coordinate x n i

end Fiber

namespace ValueMap

def imageBasisPrefix (f : ValueMap (Fiber n) (Fiber m)) (x : Fiber n) : Nat → Fiber m
  | 0 => Fiber.zero m
  | k+1 => if hk : k < n then
      Fiber.add (imageBasisPrefix f x k)
        (Fiber.scale (Fiber.coordinate x ⟨k,hk⟩) (f.eval (Fiber.basis ⟨k,hk⟩)))
    else imageBasisPrefix f x k

theorem basisPrefix_image (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f)
    (x : Fiber n) (k : Nat) :
    f.eval (Fiber.basisPrefix x k) ≈ imageBasisPrefix f x k := by
  induction k with
  | zero => exact hf.zero
  | succ k ih =>
    rw [Fiber.basisPrefix, imageBasisPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk, dif_pos hk]
      exact Setoid.trans (hf.1 _ _) (Fiber.add_congr ih (hf.2 _ _))
    · rw [dif_neg hk, dif_neg hk]
      exact ih

/-- A supplied linear operator agrees exactly with its finite matrix action.
The scalar coefficients range over all valid represented complex values. -/
theorem matrix_action (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) (x : Fiber n) :
    f.eval x ≈ imageBasisPrefix f x n :=
  Setoid.trans (f.congr (Setoid.symm (Fiber.basis_expansion x))) (basisPrefix_image f hf x n)

theorem imageBasisPrefix_congr (f g : ValueMap (Fiber n) (Fiber m))
    (h : ∀ i : Fin n, f.eval (Fiber.basis i) ≈ g.eval (Fiber.basis i))
    (x : Fiber n) (k : Nat) : imageBasisPrefix f x k ≈ imageBasisPrefix g x k := by
  induction k with
  | zero => exact Setoid.refl _
  | succ k ih =>
    rw [imageBasisPrefix, imageBasisPrefix]
    by_cases hk : k < n
    · rw [dif_pos hk, dif_pos hk]
      exact Fiber.add_congr ih
        (Fiber.scale_congr (ComplexRaw.equiv_refl (x.val ⟨k,hk⟩) (x.property ⟨k,hk⟩)) (h ⟨k,hk⟩))
    · rw [dif_neg hk, dif_neg hk]
      exact ih

/-- Finite basis agreement determines equality of arbitrary supplied linear
maps as represented values; no scalar equality decision is used. -/
theorem linear_equiv_iff_basis (f g : ValueMap (Fiber n) (Fiber m))
    (hf : IsLinear f) (hg : IsLinear g) :
    f.Equiv g ↔ ∀ i : Fin n, f.eval (Fiber.basis i) ≈ g.eval (Fiber.basis i) := by
  constructor
  · exact fun h i => h (Fiber.basis i)
  · intro h x
    exact Setoid.trans (matrix_action f hf x)
      (Setoid.trans (imageBasisPrefix_congr f g h x n) (Setoid.symm (matrix_action g hg x)))

def basisBound (f : ValueMap (Fiber n) (Fiber m)) : Rat :=
  finiteBound (List.ofFn (fun i : Fin n => initialBound (f.eval (Fiber.basis i))))

theorem basisBound_nonneg (f : ValueMap (Fiber n) (Fiber m)) : 0 ≤ basisBound f :=
  finiteBound_nonneg _

theorem basisBound_valid (f : ValueMap (Fiber n) (Fiber m)) (i : Fin n) :
    CoordinateBound (f.eval (Fiber.basis i)) (basisBound f) := by
  intro j
  apply (initialBound_valid (f.eval (Fiber.basis i)) j).mono
  exact le_finiteBound _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

def linearBound (f : ValueMap (Fiber n) (Fiber m)) : Rat :=
  (n : Rat) * (2 * basisBound f)

theorem linearBound_nonneg (f : ValueMap (Fiber n) (Fiber m)) : 0 ≤ linearBound f :=
  Rat.mul_nonneg (Rat.natCast_nonneg)
    (Rat.mul_nonneg (by decide) (basisBound_nonneg f))

theorem basisPrefix_bound (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f)
    (x : Fiber n) (C : Rat) (hC : 0 ≤ C) (hx : CoordinateBound x C)
    (k : Nat) (hk : k ≤ n) :
    CoordinateBound (f.eval (Fiber.basisPrefix x k))
      ((k : Rat) * (2 * C * basisBound f)) := by
  induction k with
  | zero =>
    apply bound_congr (Setoid.symm hf.zero)
    simpa using (bound_zero (n := m) 0 Rat.le_refl)
  | succ k ih =>
    have hkn : k < n := by omega
    rw [Fiber.basisPrefix, dif_pos hkn]
    have hp := ih (by omega)
    have ht : CoordinateBound
        (Fiber.scale (Fiber.coordinate x ⟨k,hkn⟩) (f.eval (Fiber.basis ⟨k,hkn⟩)))
        (2*C*basisBound f) :=
      bound_scale hC (basisBound_nonneg f) (hx ⟨k,hkn⟩) (basisBound_valid f ⟨k,hkn⟩)
    have hterm : CoordinateBound
        (f.eval (Fiber.scale (Fiber.coordinate x ⟨k,hkn⟩) (Fiber.basis ⟨k,hkn⟩)))
        (2*C*basisBound f) := bound_congr
      (Setoid.symm (hf.2 (Fiber.coordinate x ⟨k,hkn⟩) (Fiber.basis ⟨k,hkn⟩))) ht
    have hs := bound_congr (Setoid.symm (hf.1 _ _)) (bound_add hp hterm)
    have he : (k : Rat)*(2*C*basisBound f)+2*C*basisBound f =
        ((k+1 : Nat) : Rat)*(2*C*basisBound f) := by
      rw [Rat.natCast_add]
      grind
    rw [he] at hs
    exact hs

/-- Every supplied finite-rank linear map has a computed operator bound. -/
theorem linear_bound (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f)
    (C : Rat) (hC : 0 ≤ C) (x : Fiber n) (hx : CoordinateBound x C) :
    CoordinateBound (f.eval x) (linearBound f * C) := by
  have h := bound_congr (f.congr (Fiber.basis_expansion x))
    (basisPrefix_bound f hf x C hC hx n (Nat.le_refl n))
  have he : (n : Rat)*(2*C*basisBound f) = linearBound f*C := by
    unfold linearBound
    grind
  rw [he] at h
  exact h

end ValueMap
end ComputableAnalysis.RiemannHilbert
