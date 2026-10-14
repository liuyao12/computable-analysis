import ComputableAnalysis.RiemannHilbert.OperatorBounds

/-! Literal operator/vector finite computations reflected in coordinate kernels. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

def powerScalar (z : Scalar) (k : Nat) : Scalar := ⟨power z.val k, power_valid z.val z.property k⟩

theorem powerScalar_product (z : Scalar) (i j : Nat) :
    (mul (powerScalar z i).val (powerScalar z j).val).Equiv (powerScalar z (i+j)).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (powerScalar z i).property (powerScalar z j).property)
    (hright := (powerScalar z (i+j)).property)
  change ComplexRawQuotient.ofRaw (power z.val i) (power_valid z.val z.property i)*
    ComplexRawQuotient.ofRaw (power z.val j) (power_valid z.val z.property j) =
    ComplexRawQuotient.ofRaw (power z.val (i+j)) (power_valid z.val z.property (i+j))
  rw [ScalarAlgebra.ofRaw_power z.val z.property i, ScalarAlgebra.ofRaw_power z.val z.property j,
    ScalarAlgebra.ofRaw_power z.val z.property (i+j), Lean.Grind.Semiring.pow_add]

theorem vectorBlock_image (t : Nat → Fiber n) (N k : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw ((vectorBlock t N k).val d) ((vectorBlock t N k).property d) =
      FiniteProducts.block (fun j => ComplexRawQuotient.ofRaw ((t j).val d) ((t j).property d)) N k := by
  simpa only [vectorBlock_coordinate] using
    ScalarSeries.block_image (fun j => (t j).val d) (fun j => (t j).property d) N k

def kernelTerm (a : Nat → ValueMap (Fiber n) (Fiber n)) (t : Nat → Fiber n) (z : Scalar) (i j : Nat) : Fiber n :=
  Fiber.scale (powerScalar z (i+j)) ((a i).eval (t j))

def kernelValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (t : Nat → Fiber n) (z : Scalar)
    (d : Fin n) (i j : Nat) : ScalarAlgebra.Value :=
  ComplexRawQuotient.ofRaw ((kernelTerm a t z i j).val d) ((kernelTerm a t z i j).property d)

/-- Applying one operator row to a finite solution block expands into its
two-index kernel, using the operator's proved complex linearity. -/
theorem row_expand (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ i, IsLinear (a i))
    (t : Nat → Fiber n) (z : Scalar) (i N k : Nat) :
    Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z N k)) ≈
      vectorBlock (kernelTerm a t z i) N k := by
  have hm := vectorBlock_map (a i) (ha i) (VectorSeries.term t z) N k
  have hs := Fiber.scale_congr (equiv_refl _ (powerScalar z i).property) hm
  apply Setoid.trans hs
  apply Setoid.trans (vectorBlock_scale (powerScalar z i) _ N k)
  apply vectorBlock_congr
  intro j
  exact Setoid.trans
    (Fiber.scale_congr (equiv_refl _ (powerScalar z i).property) ((ha i).2 (powerScalar z j) (t j)))
    (Setoid.trans (Fiber.scale_scale (powerScalar z i) (powerScalar z j) _)
      (Fiber.scale_congr (powerScalar_product z i j) (Setoid.refl _)))

theorem row_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ i, IsLinear (a i))
    (t : Nat → Fiber n) (z : Scalar) (i N k : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw
      ((Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z N k))).val d)
      ((Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z N k))).property d) =
      FiniteProducts.block (kernelValue a t z d i) N k := by
  rw [ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z N k))).property d)
    (hright := (vectorBlock (kernelTerm a t z i) N k).property d)
    (row_expand a ha t z i N k d), vectorBlock_image]
  rfl

theorem operatorRectangle_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ i, IsLinear (a i))
    (t : Nat → Fiber n) (z : Scalar) (N : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw
      (((operatorPrefixMap a z N).eval (VectorSeries.block t z 0 N)).val d)
      (((operatorPrefixMap a z N).eval (VectorSeries.block t z 0 N)).property d) =
      FiniteProducts.partialSum (fun i => FiniteProducts.partialSum (kernelValue a t z d i) N) N := by
  change ComplexRawQuotient.ofRaw
    ((vectorBlock (fun i => Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z 0 N))) 0 N).val d) _ = _
  rw [vectorBlock_image]
  apply FiniteProducts.prefix_congr
  intro i hi
  simpa only [FiniteProducts.block, Nat.zero_add] using row_image a ha t z i 0 N d

def vectorMissing (a : Nat → ValueMap (Fiber n) (Fiber n)) (t : Nat → Fiber n) (z : Scalar) (N : Nat) : Fiber n :=
  vectorBlock (fun i => Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z (N-i) i))) 0 N

theorem vectorMissing_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ i, IsLinear (a i))
    (t : Nat → Fiber n) (z : Scalar) (N : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw ((vectorMissing a t z N).val d) ((vectorMissing a t z N).property d) =
      FiniteProducts.partialSum (fun i => FiniteProducts.block (kernelValue a t z d i) (N-i) i) N := by
  change ComplexRawQuotient.ofRaw
    ((vectorBlock (fun i => Fiber.scale (powerScalar z i) ((a i).eval (VectorSeries.block t z (N-i) i))) 0 N).val d) _ = _
  rw [vectorBlock_image]
  apply FiniteProducts.prefix_congr
  intro i hi
  simpa only [Nat.zero_add] using row_image a ha t z i (N-i) i d

theorem sum_coordinate (xs : List (Fiber n)) (d : Fin n) :
    (sum xs).val d = LocalODE.sum (xs.map (fun x => x.val d)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => change ComplexRaw.add (x.val d) ((sum xs).val d) = _
                    rw [ih]; rfl

theorem convolution_coordinate_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (t : Nat → Fiber n)
    (N : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw ((convolution a t N).val d) ((convolution a t N).property d) =
      FiniteProducts.partialSum (fun i =>
        ComplexRawQuotient.ofRaw (((a i).eval (t (N-i))).val d) (((a i).eval (t (N-i))).property d)) (N+1) := by
  let f := fun i => if i≤N then (a i).eval (t (N-i)) else Fiber.zero n
  have hcoord : (convolution a t N).val d = LocalODE.sum ((List.range (N+1)).map (fun i => (f i).val d)) := by
    simp only [convolution, f, sum_coordinate, List.map_map]
    rfl
  simp only [hcoord]
  rw [LocalODE.sum_map_image _ (fun i => (f i).property d) (List.range (N+1)), FiniteProducts.partialSum_list]
  apply FiniteProducts.listSum_map_congr
  intro i hi
  have hik : i≤N := by have := List.mem_range.mp hi; omega
  dsimp [f]
  simp only [if_pos hik]

def derivativeVectorTerm (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (k : Nat) : Fiber n :=
  Fiber.scale (powerScalar z k) (ratScale ((k+1 : Nat) : Rat) (coefficient a initial (k+1)))

def derivativeVectorBlock (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (N : Nat) : Fiber n := vectorBlock (derivativeVectorTerm a initial z) 0 N

theorem derivativeVectorTerm_coordinate (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (k : Nat) (d : Fin n) :
    ((derivativeVectorTerm a initial z k).val d).Equiv
      (BoundedSeries.derivativeTerm (coordinateSeries a initial d) z.val k) := by
  exact equiv_trans ((derivativeVectorTerm a initial z k).property d)
    (mul_valid (scaleRat_valid ((coefficient a initial (k+1)).property d)) (powerScalar z k).property)
    (BoundedSeries.derivativeTerm_valid _ z.val (coordinateSeries_valid a initial d) z.property k)
    (mul_comm_equiv _ _ (powerScalar z k).property (scaleRat_valid ((coefficient a initial (k+1)).property d)))
    (equiv_symm (scaleRat_mul_equiv ((k+1 : Nat) : Rat) ((coefficient a initial (k+1)).val d)
      (powerScalar z k).val ((coefficient a initial (k+1)).property d) (powerScalar z k).property))

theorem derivativeVectorBlock_coordinate (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (N : Nat) (d : Fin n) :
    ((derivativeVectorBlock a initial z N).val d).Equiv
      (BoundedSeries.derivativeBlock (coordinateSeries a initial d) z.val 0 N) := by
  rw [derivativeVectorBlock, vectorBlock_coordinate, BoundedSeries.derivativeBlock_as_terms]
  exact ScalarSeries.block_congr _ _ (fun k => derivativeVectorTerm_coordinate a initial z k d) 0 N

theorem derivativeVectorTerm_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (k : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw ((derivativeVectorTerm a initial z k).val d)
      ((derivativeVectorTerm a initial z k).property d) =
      FiniteProducts.kernelDiagonal (kernelValue a (coefficient a initial) z d) k := by
  have he := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (ratScale ((k+1 : Nat) : Rat) (coefficient a initial (k+1))).property d)
    (hright := (convolution a (coefficient a initial) k).property d) (coefficient_equation a initial k d)
  change ComplexRawQuotient.ofRaw (powerScalar z k).val (powerScalar z k).property *
    ComplexRawQuotient.ofRaw ((ratScale ((k+1 : Nat) : Rat) (coefficient a initial (k+1))).val d)
      ((ratScale ((k+1 : Nat) : Rat) (coefficient a initial (k+1))).property d) = _
  rw [he, convolution_coordinate_image a (coefficient a initial) k d]
  rw [ComplexRawQuotient.mul_comm, ← FiniteProducts.prefix_mul]
  apply FiniteProducts.prefix_congr
  intro i hi
  have hik : i≤k := by omega
  have hidx : i+(k-i)=k := by omega
  change ComplexRawQuotient.ofRaw (((a i).eval (coefficient a initial (k-i))).val d)
      (((a i).eval (coefficient a initial (k-i))).property d) *
      ComplexRawQuotient.ofRaw (powerScalar z k).val (powerScalar z k).property =
    ComplexRawQuotient.ofRaw (powerScalar z (i+(k-i))).val (powerScalar z (i+(k-i))).property *
      ComplexRawQuotient.ofRaw (((a i).eval (coefficient a initial (k-i))).val d)
        (((a i).eval (coefficient a initial (k-i))).property d)
  rw [hidx, ComplexRawQuotient.mul_comm]

theorem derivativeVectorBlock_image (a : Nat → ValueMap (Fiber n) (Fiber n)) (initial : Fiber n)
    (z : Scalar) (N : Nat) (d : Fin n) :
    ComplexRawQuotient.ofRaw ((derivativeVectorBlock a initial z N).val d)
      ((derivativeVectorBlock a initial z N).property d) =
      FiniteProducts.kernelTriangle (kernelValue a (coefficient a initial) z d) N := by
  change ComplexRawQuotient.ofRaw ((vectorBlock (derivativeVectorTerm a initial z) 0 N).val d) _ = _
  rw [vectorBlock_image, FiniteProducts.kernelTriangle_diagonals]
  apply FiniteProducts.prefix_congr
  intro k hk
  simpa only [Nat.zero_add] using derivativeVectorTerm_image a initial z k d

end ComputableAnalysis.RiemannHilbert.LocalSystem
