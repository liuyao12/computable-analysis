import ComputableAnalysis.RiemannHilbert.CoefficientSeries
import ComputableAnalysis.RiemannHilbert.LocalODEDerivativeSum

/-! Exact evaluation of finite coefficient convolutions and derivative prefixes. -/
namespace ComputableAnalysis.RiemannHilbert.FiniteProducts
open ScalarAlgebra

def listSum : List Value → Value
  | [] => 0
  | x::xs => x+listSum xs

theorem listSum_append (xs ys : List Value) : listSum (xs++ys)=listSum xs+listSum ys := by
  induction xs with
  | nil => change listSum ys=0+listSum ys; grind
  | cons x xs ih => simp only [List.cons_append, listSum]; rw [ih]; grind

theorem partialSum_list (f : Nat → Value) (N : Nat) :
    partialSum f N = listSum ((List.range N).map f) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [partialSum, List.range_succ, List.map_append, listSum_append, ← ih]
    change partialSum f N+f N=partialSum f N+(f N+0)
    grind

theorem listSum_map_congr (is : List Nat) (f g : Nat → Value) (h : ∀ i∈is, f i=g i) :
    listSum (is.map f)=listSum (is.map g) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change f i+listSum (is.map f)=g i+listSum (is.map g)
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

end ComputableAnalysis.RiemannHilbert.FiniteProducts

namespace ComputableAnalysis.RiemannHilbert.LocalODE
open ComplexRaw

theorem sum_map_image (f : Nat → ComplexRaw) (hf : ∀ i, (f i).Valid) (is : List Nat) :
    ComplexRawQuotient.ofRaw (sum (is.map f))
      (sum_valid _ (by intro z hz; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz; exact hf i)) =
      FiniteProducts.listSum (is.map (fun i => ComplexRawQuotient.ofRaw (f i) (hf i))) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    change ComplexRawQuotient.ofRaw (f i) (hf i)+
      ComplexRawQuotient.ofRaw (sum (is.map f))
        (sum_valid _ (by intro z hz; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz; exact hf j)) =
      ComplexRawQuotient.ofRaw (f i) (hf i)+_
    rw [ih]

theorem convolution_image (a y : Nat → ComplexRaw) (ha : ∀ i, (a i).Valid)
    (hy : ∀ i, (y i).Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (convolution a y N)
      (convolution_valid a y N ha (fun i _ => hy i)) =
      FiniteProducts.partialSum (fun i => ComplexRawQuotient.ofRaw (a i) (ha i)*
        ComplexRawQuotient.ofRaw (y (N-i)) (hy (N-i))) (N+1) := by
  let f := fun i => if i≤N then mul (a i) (y (N-i)) else zero
  have hf : ∀ i, (f i).Valid := by
    intro i; dsimp [f]; split
    · exact mul_valid (ha i) (hy _)
    · exact ofQComplex_valid _
  change ComplexRawQuotient.ofRaw (sum ((List.range (N+1)).map f))
    (sum_valid _ (by intro z hz; obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz; exact hf i)) = _
  rw [sum_map_image f hf (List.range (N+1)), FiniteProducts.partialSum_list]
  apply FiniteProducts.listSum_map_congr
  intro i hi
  have hiN : i≤N := by have := List.mem_range.mp hi; omega
  dsimp [f]
  simp only [if_pos hiN]
  rfl

theorem convolution_term_image (a y : Nat → ComplexRaw) (z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (hy : ∀ i, (y i).Valid) (hz : z.Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (mul (convolution a y N) (power z N))
      (mul_valid (convolution_valid a y N ha (fun i _ => hy i)) (power_valid z hz N)) =
      FiniteProducts.diagonal
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm a z i) (seriesTerm_valid a z ha hz i))
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm y z i) (seriesTerm_valid y z hy hz i)) N := by
  change ComplexRawQuotient.ofRaw (convolution a y N)
      (convolution_valid a y N ha (fun i _ => hy i)) *
    ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N) = _
  rw [convolution_image, ScalarAlgebra.ofRaw_power z hz N, ← FiniteProducts.prefix_mul]
  apply FiniteProducts.prefix_congr
  intro i hi
  have hiN : i≤N := by omega
  change (ComplexRawQuotient.ofRaw (a i) (ha i)*ComplexRawQuotient.ofRaw (y (N-i)) (hy _))*
    (ComplexRawQuotient.ofRaw z hz)^N =
    (ComplexRawQuotient.ofRaw (a i) (ha i)*
      ComplexRawQuotient.ofRaw (power z i) (power_valid z hz i)) *
    (ComplexRawQuotient.ofRaw (y (N-i)) (hy _)*
      ComplexRawQuotient.ofRaw (power z (N-i)) (power_valid z hz (N-i)))
  rw [ScalarAlgebra.ofRaw_power z hz i, ScalarAlgebra.ofRaw_power z hz (N-i)]
  have hp : (ComplexRawQuotient.ofRaw z hz)^i*(ComplexRawQuotient.ofRaw z hz)^(N-i) =
      (ComplexRawQuotient.ofRaw z hz)^N := by
    rw [← Lean.Grind.Semiring.pow_add]
    congr 1
    omega
  grind

theorem derivativeTerm_diagonal (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (derivativeTerm a initial z N) (derivativeTerm_valid a initial z ha h0 hz N) =
      FiniteProducts.diagonal
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm a z i) (seriesTerm_valid a z ha hz i))
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm (coefficient a initial) z i)
          (seriesTerm_valid _ z (coefficient_valid a initial ha h0) hz i)) N := by
  have he : ComplexRawQuotient.scaleRat ((N+1 : Nat) : Rat)
      (ComplexRawQuotient.ofRaw (coefficient a initial (N+1)) (coefficient_valid a initial ha h0 _)) =
      ComplexRawQuotient.ofRaw (convolution a (coefficient a initial) N)
        (convolution_valid a _ N ha (fun i _ => coefficient_valid a initial ha h0 i)) :=
    ComplexRawQuotient.ofRaw_eq_ofRaw (coefficient_equation a initial ha h0 N)
  change ComplexRawQuotient.scaleRat ((N+1 : Nat) : Rat)
    (ComplexRawQuotient.ofRaw (coefficient a initial (N+1)) (coefficient_valid a initial ha h0 _)*
      ComplexRawQuotient.ofRaw (power z N) (power_valid z hz N)) = _
  rw [ComplexRawQuotient.scaleRat_mul, he]
  exact convolution_term_image a _ z ha (coefficient_valid a initial ha h0) hz N

theorem derivativeBlock_triangle (a : Nat → ComplexRaw) (initial z : ComplexRaw)
    (ha : ∀ i, (a i).Valid) (h0 : initial.Valid) (hz : z.Valid) (N : Nat) :
    ComplexRawQuotient.ofRaw (derivativeBlock a initial z 0 N) (derivativeBlock_valid a initial z ha h0 hz 0 N) =
      FiniteProducts.triangle
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm a z i) (seriesTerm_valid a z ha hz i))
        (fun i => ComplexRawQuotient.ofRaw (seriesTerm (coefficient a initial) z i)
          (seriesTerm_valid _ z (coefficient_valid a initial ha h0) hz i)) N := by
  rw [FiniteProducts.triangle_diagonals]
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [derivativeBlock.eq_2, Nat.zero_add]
    change ComplexRawQuotient.ofRaw (derivativeBlock a initial z 0 N) (derivativeBlock_valid a initial z ha h0 hz 0 N)+
      ComplexRawQuotient.ofRaw (derivativeTerm a initial z N) (derivativeTerm_valid a initial z ha h0 hz N) = _
    rw [ih, derivativeTerm_diagonal a initial z ha h0 hz N]
    rfl

end ComputableAnalysis.RiemannHilbert.LocalODE
