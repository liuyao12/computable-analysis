import ComputableAnalysis.RiemannHilbert.VectorFiniteSums

/-! Actual represented sums of supplied geometrically bounded vector coefficients. -/
namespace ComputableAnalysis.RiemannHilbert.VectorSeries
open ComplexRaw FunctionTheory LocalODE LocalSystem
variable {n : Nat}

def term (t : Nat → Fiber n) (z : Scalar) (k : Nat) : Fiber n :=
  Fiber.scale ⟨power z.val k, power_valid z.val z.property k⟩ (t k)

def block (t : Nat → Fiber n) (z : Scalar) (N k : Nat) : Fiber n :=
  vectorBlock (term t z) N k

theorem block_coordinate (t : Nat → Fiber n) (z : Scalar) (N k : Nat) (i : Fin n) :
    ((block t z N k).val i).Equiv (ScalarSeries.block (seriesTerm (fun j => (t j).val i) z.val) N k) := by
  rw [block, vectorBlock_coordinate]
  exact ScalarSeries.block_congr _ _ (fun j => mul_comm_equiv _ _ (power_valid z.val z.property j) ((t j).property i)) N k

theorem term_bound (t : Nat → Fiber n) (z : Scalar) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hz : Small z.val R) (k : Nat) :
    CoordinateBound (term t z k) (2*C*(2*K*R)^k) := by
  have hp := power_small z.val z.property R hR hz k
  have hs := bound_scale (x := t k) (c := ⟨power z.val k, power_valid z.val z.property k⟩)
    (B := (2*R)^k) (C := C*K^k) (Rat.pow_nonneg (Rat.mul_nonneg (by decide) hR))
    (Rat.mul_nonneg hC (Rat.pow_nonneg hK)) hp (ht k)
  have he : 2*(2*R)^k*(C*K^k)=2*C*(2*K*R)^k := by
    have hpow : (2*R)^k*K^k=(2*K*R)^k := by
      rw [← rational_mul_pow]; congr 1; grind
    calc
      _ = (2*C)*((2*R)^k*K^k) := by grind
      _ = _ := by rw [hpow]
  rw [he] at hs; exact hs

theorem block_bound (t : Nat → Fiber n) (z : Scalar) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hz : Small z.val R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N k : Nat) :
    CoordinateBound (block t z N k) (4*C*(2*K*R)^N) :=
  vectorBlock_bound _ C (2*K*R) hC (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hK) hR)
    hlocal (term_bound t z C K R hC hK hR ht hz) N k

def value (t : Nat → Fiber n) (z : Scalar) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hz : Small z.val R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) : Fiber n :=
  ⟨fun i => coefficientSum (fun j => (t j).val i) z.val (fun j => (t j).property i) z.property C K R,
    fun i => coefficientSum_valid _ _ (fun j => (t j).property i) z.property C K R hC hK hR
      (fun j => ht j i) hz hlocal⟩

theorem value_close (t : Nat → Fiber n) (z : Scalar) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hz : Small z.val R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) (N : Nat) :
    CoordinateBound (Fiber.sub (value t z C K R hC hK hR ht hz hlocal) (block t z 0 N))
      (4*C*(2*K*R)^N) := by
  intro i
  have hs := coefficientSum_close _ z.val (fun j => (t j).property i) z.property
    C K R hC hK hR (fun j => ht j i) hz hlocal N
  have hp := ScalarSeries.block_valid _ (seriesTerm_valid _ z.val (fun j => (t j).property i) z.property) 0 N
  exact Small.congr
    (sub_valid ((value t z C K R hC hK hR ht hz hlocal).property i) hp)
    ((Fiber.sub (value t z C K R hC hK hR ht hz hlocal) (block t z 0 N)).property i)
    (FunctionTheory.sub_congr (equiv_refl _ ((value t z C K R hC hK hR ht hz hlocal).property i))
      (equiv_symm (block_coordinate t z 0 N i))) hs

theorem value_bound (t : Nat → Fiber n) (z : Scalar) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hz : Small z.val R)
    (hlocal : 2*K*R ≤ (1 : Rat)/2) :
    CoordinateBound (value t z C K R hC hK hR ht hz hlocal) (4*C) :=
  fun i => coefficientSum_bound _ z.val (fun j => (t j).property i) z.property
    C K R hC hK hR (fun j => ht j i) hz hlocal

theorem value_congr (t u : Nat → Fiber n) (z w : Scalar) (htu : ∀ k, t k ≈ u k) (hzw : z.val.Equiv w.val)
    (C K R D L S : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (ht : ∀ k, CoordinateBound (t k) (C*K^k)) (hu : ∀ k, CoordinateBound (u k) (D*L^k))
    (hz : Small z.val R) (hw : Small w.val S)
    (hq : 2*K*R ≤ (1 : Rat)/2) (hr : 2*L*S ≤ (1 : Rat)/2) :
    value t z C K R hC hK hR ht hz hq ≈ value u w D L S hD hL hS hu hw hr :=
  fun i => coefficientSum_congr_of_bounds _ _ z.val w.val (fun j => (t j).property i) (fun j => (u j).property i)
    z.property w.property (fun j => htu j i) hzw C K R D L S hC hK hR hD hL hS
    (fun j => ht j i) (fun j => hu j i) hz hw hq hr

end ComputableAnalysis.RiemannHilbert.VectorSeries
