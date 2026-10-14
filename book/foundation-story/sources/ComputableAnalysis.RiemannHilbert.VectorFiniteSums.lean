import ComputableAnalysis.RiemannHilbert.LocalSystemHolomorphic

/-! Finite vector algebra and transport of finite sums by justified linear maps. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory

namespace Fiber
variable {n : Nat}

def neg (x : Fiber n) : Fiber n := ⟨fun i => ComplexRaw.neg (x.val i), fun i => neg_valid (x.property i)⟩
def sub (x y : Fiber n) : Fiber n :=
  ⟨fun i => ComplexRaw.sub (x.val i) (y.val i), fun i => sub_valid (x.property i) (y.property i)⟩

theorem sub_congr {x x' y y' : Fiber n} (hx : x ≈ x') (hy : y ≈ y') :
    sub x y ≈ sub x' y' := fun i => FunctionTheory.sub_congr (hx i) (hy i)

theorem zero_scale (x : Fiber n) : scale ⟨ComplexRaw.zero, ofQComplex_valid _⟩ x ≈ Fiber.zero n :=
  fun i => zero_mul_equiv _ (x.property i)

theorem neg_as_scale (x : Fiber n) :
    neg x ≈ scale ⟨scaleRat (-1) one, scaleRat_valid (ofQComplex_valid _)⟩ x := by
  intro i
  have hs := neg_equiv_scaleRat_neg_one (x.val i) (x.property i)
  have hm := scaleRat_equiv (r := (-1 : Rat))
    (equiv_symm (one_mul_equiv (x.val i) (x.property i)))
  exact equiv_trans (neg_valid (x.property i)) (scaleRat_valid (x.property i))
    (mul_valid (scaleRat_valid (ofQComplex_valid _)) (x.property i)) hs
    (equiv_trans (scaleRat_valid (x.property i))
      (scaleRat_valid (mul_valid (ofQComplex_valid _) (x.property i)))
      (mul_valid (scaleRat_valid (ofQComplex_valid _)) (x.property i)) hm
      (scaleRat_mul_equiv (-1) one (x.val i) (ofQComplex_valid _) (x.property i)))

theorem scale_scale (a b : Scalar) (x : Fiber n) :
    scale a (scale b x) ≈ scale ⟨mul a.val b.val, mul_valid a.property b.property⟩ x :=
  fun i => equiv_symm (mul_assoc_equiv _ _ _ a.property b.property (x.property i))

theorem difference_decompose (x y p q : Fiber n) :
    sub x y ≈ add (add (sub x p) (sub p q)) (sub q y) :=
  fun i => SeriesLimitLaws.difference_via _ _ _ _ (x.property i) (y.property i) (p.property i) (q.property i)

end Fiber

namespace IsLinear
variable {n m : Nat} {f : ValueMap (Fiber n) (Fiber m)}

theorem zero (hf : IsLinear f) : f.eval (Fiber.zero n) ≈ Fiber.zero m :=
  Setoid.trans (f.congr (Setoid.symm (Fiber.zero_scale (Fiber.zero n))))
    (Setoid.trans (hf.2 ⟨ComplexRaw.zero, ofQComplex_valid _⟩ (Fiber.zero n)) (Fiber.zero_scale _))

theorem neg (hf : IsLinear f) (x : Fiber n) : f.eval (Fiber.neg x) ≈ Fiber.neg (f.eval x) :=
  Setoid.trans (f.congr (Fiber.neg_as_scale x))
    (Setoid.trans (hf.2 _ x) (Setoid.symm (Fiber.neg_as_scale _)))

theorem sub (hf : IsLinear f) (x y : Fiber n) :
    f.eval (Fiber.sub x y) ≈ Fiber.sub (f.eval x) (f.eval y) := by
  have hleft : Fiber.sub x y ≈ Fiber.add x (Fiber.neg y) :=
    fun i => equiv_refl _ (sub_valid (x.property i) (y.property i))
  have hright : Fiber.add (f.eval x) (Fiber.neg (f.eval y)) ≈ Fiber.sub (f.eval x) (f.eval y) :=
    fun i => equiv_refl _ (sub_valid ((f.eval x).property i) ((f.eval y).property i))
  exact Setoid.trans (f.congr hleft)
    (Setoid.trans (hf.1 x (Fiber.neg y))
      (Setoid.trans (Fiber.add_congr (Setoid.refl _) (IsLinear.neg hf y)) hright))

end IsLinear

namespace LocalSystem
variable {n : Nat}

theorem bound_sub {x y : Fiber n} {C D : Rat} (hx : CoordinateBound x C) (hy : CoordinateBound y D) :
    CoordinateBound (Fiber.sub x y) (C+D) := fun i => SeriesLimitLaws.small_sub (hx i) (hy i)

theorem bound_scale {x : Fiber n} {c : Scalar} {B C : Rat}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : Small c.val B) (hx : CoordinateBound x C) :
    CoordinateBound (Fiber.scale c x) (2*B*C) :=
  fun i => Small.mul c.property (x.property i) hB hC hc (hx i)

def vectorBlock (t : Nat → Fiber n) (N : Nat) : Nat → Fiber n
  | 0 => Fiber.zero n
  | k+1 => Fiber.add (vectorBlock t N k) (t (N+k))

theorem vectorBlock_coordinate (t : Nat → Fiber n) (N k : Nat) (i : Fin n) :
    (vectorBlock t N k).val i = ScalarSeries.block (fun j => (t j).val i) N k := by
  induction k with
  | zero => rfl
  | succ k ih => change ComplexRaw.add ((vectorBlock t N k).val i) _ = _
                 rw [ih]; rfl

theorem vectorBlock_congr (t u : Nat → Fiber n) (h : ∀ j, t j ≈ u j) (N k : Nat) :
    vectorBlock t N k ≈ vectorBlock u N k := by
  intro i
  rw [vectorBlock_coordinate, vectorBlock_coordinate]
  exact ScalarSeries.block_congr _ _ (fun j => h j i) N k

theorem vectorBlock_append (t : Nat → Fiber n) (N k : Nat) :
    vectorBlock t 0 (N+k) ≈ Fiber.add (vectorBlock t 0 N) (vectorBlock t N k) := by
  induction k with
  | zero => exact Setoid.symm (Fiber.add_zero _)
  | succ k ih =>
    change Fiber.add (vectorBlock t 0 (N+k)) (t (0+(N+k))) ≈
      Fiber.add (vectorBlock t 0 N) (Fiber.add (vectorBlock t N k) (t (N+k)))
    simp only [Nat.zero_add]
    exact Setoid.trans (Fiber.add_congr ih (Setoid.refl _)) (Fiber.add_assoc _ _ _)

theorem vectorBlock_map {m : Nat} (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f)
    (t : Nat → Fiber n) (N k : Nat) :
    f.eval (vectorBlock t N k) ≈ vectorBlock (fun j => f.eval (t j)) N k := by
  induction k with
  | zero => exact hf.zero
  | succ k ih => exact Setoid.trans (hf.1 _ _) (Fiber.add_congr ih (Setoid.refl _))

theorem vectorBlock_scale (c : Scalar) (t : Nat → Fiber n) (N k : Nat) :
    Fiber.scale c (vectorBlock t N k) ≈ vectorBlock (fun j => Fiber.scale c (t j)) N k := by
  induction k with
  | zero => exact Fiber.scale_zero c
  | succ k ih => exact Setoid.trans (Fiber.scale_add c _ _) (Fiber.add_congr ih (Setoid.refl _))

theorem vectorBlock_bound (t : Nat → Fiber n) (C q : Rat)
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hlocal : q ≤ (1 : Rat)/2)
    (ht : ∀ j, CoordinateBound (t j) (2*C*q^j)) (N k : Nat) :
    CoordinateBound (vectorBlock t N k) (4*C*q^N) := by
  intro i
  rw [vectorBlock_coordinate]
  exact ScalarSeries.block_bound _ C q hC hq hlocal (fun j => ht j i) N k

theorem vectorBlock_uniform (t : Nat → Fiber n) (B : Rat) (hB : 0 ≤ B) (N k : Nat)
    (ht : ∀ j, j<k → CoordinateBound (t (N+j)) B) :
    CoordinateBound (vectorBlock t N k) ((k : Rat)*B) := by
  intro i
  rw [vectorBlock_coordinate]
  exact ScalarSeries.block_uniform _ B hB N k (fun j hj => ht j hj i)

end LocalSystem
end ComputableAnalysis.RiemannHilbert
