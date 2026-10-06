import ComputableAnalysis.RiemannHilbert.EntireExponentialODE
import ComputableAnalysis.RiemannHilbert.NilpotentShear

/-! Exact identification of the entire exponential with the finite shear
when the supplied represented residue has square zero. The formula applies
to all represented arguments and operators, including irrational entries. -/
namespace ComputableAnalysis.RiemannHilbert.MatrixExponential
open ComplexRaw FunctionTheory LocalSystem LocalODE
variable {n : Nat}

theorem value_of_stabilized_prefix (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (x : Fiber n) (z : Scalar) (s : Nat) (v : Fiber n)
    (h : ∀ N, (finitePrefix A z (N+s)).eval x ≈ v) : (value A hA z).eval x ≈ v := by
  let R := pointRadius z
  let E := LocalSystem.initialBound x
  have he := SeriesLimitLaws.shrinks_shift _ (prefix_error_shrinks A R E (LocalSystem.initialBound_nonneg x)) s
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 _ he
  intro N
  have hs := value_prefix_close A hA R z (pointRadius_inside z) E (LocalSystem.initialBound_nonneg x)
    x (LocalSystem.initialBound_valid x) (N+s) i
  simpa only [Rat.zero_add, Fiber.sub] using Small.congr
    ((Fiber.sub ((value A hA z).eval x) ((finitePrefix A z (N+s)).eval x)).property i)
    ((Fiber.sub ((value A hA z).eval x) v).property i)
    (FunctionTheory.sub_congr (equiv_refl _ (((value A hA z).eval x).property i)) (h N i)) hs

theorem coefficient_one (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) :
    coefficient A x 1 ≈ A.eval x := by
  intro i
  change (scaleRat (1/((0+1 : Nat) : Rat)) ((A.eval x).val i)).Equiv ((A.eval x).val i)
  have he : (1/((0+1 : Nat) : Rat)) = 1 := by decide +kernel
  rw [he]
  exact scaleRat_one_equiv ((A.eval x).val i) ((A.eval x).property i)

theorem coefficient_nil_tail (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hNil : ∀ x, A.eval (A.eval x) ≈ Fiber.zero n) (x : Fiber n) (k : Nat) :
    coefficient A x (k+2) ≈ Fiber.zero n := by
  induction k with
  | zero =>
      exact Setoid.trans (ratScale_congr _ (Setoid.trans (A.congr (coefficient_one A x)) (hNil x)))
        (fun _ => scaleRat_zero_equiv _)
  | succ k ih =>
      have he : k+1+2 = (k+2)+1 := by omega
      rw [he, coefficient_succ]
      exact Setoid.trans (ratScale_congr _ (Setoid.trans (A.congr ih) hA.zero))
        (fun _ => scaleRat_zero_equiv _)

theorem nil_prefix_two (A : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) (z : Scalar) :
    (finitePrefix A z 2).eval x ≈ (NilpotentShear.forward A z).eval x := by
  change Fiber.add (Fiber.add (Fiber.zero n) (Fiber.scale ⟨one, ofQComplex_valid _⟩ x))
    (Fiber.scale ⟨power z.val 1, power_valid z.val z.property 1⟩ (coefficient A x 1)) ≈ _
  exact Fiber.add_congr
    (Setoid.trans (Fiber.zero_add _) (fun i => one_mul_equiv _ (x.property i)))
    (Fiber.scale_congr (one_mul_equiv _ z.property) (coefficient_one A x))

theorem nil_prefix_stabilizes (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hNil : ∀ x, A.eval (A.eval x) ≈ Fiber.zero n) (x : Fiber n) (z : Scalar) (N : Nat) :
    (finitePrefix A z (N+2)).eval x ≈ (NilpotentShear.forward A z).eval x := by
  induction N with
  | zero => exact nil_prefix_two A x z
  | succ N ih =>
      have he : N+1+2 = (N+2)+1 := by omega
      rw [he]
      change VectorSeries.block (coefficient A x) z 0 ((N+2)+1) ≈ _
      change Fiber.add (vectorBlock (VectorSeries.term (coefficient A x) z) 0 (N+2))
        (VectorSeries.term (coefficient A x) z (0+(N+2))) ≈ _
      rw [Nat.zero_add]
      exact Setoid.trans
        (Fiber.add_congr (Setoid.refl _)
          (Setoid.trans (Fiber.scale_congr (equiv_refl _ (power_valid z.val z.property (N+2)))
            (coefficient_nil_tail A hA hNil x N)) (Fiber.scale_zero _)))
        (Setoid.trans (Fiber.add_zero _) ih)

/-- The entire exponential equals its finite closed form for a square-zero
residue; both sides accept arbitrary valid represented data. -/
theorem value_nilpotent (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hNil : ∀ x, A.eval (A.eval x) ≈ Fiber.zero n) (z : Scalar) :
    (value A hA z).Equiv (NilpotentShear.forward A z) :=
  fun x => value_of_stabilized_prefix A hA x z 2 _ (nil_prefix_stabilizes A hA hNil x z)

theorem nilpotent_derivative (A : ValueMap (Fiber n) (Fiber n)) (hA : IsLinear A)
    (hNil : ∀ x, A.eval (A.eval x) ≈ Fiber.zero n) (x : Fiber n)
    (hH : DomainVectorFunctions.Holomorphic (vector A hA x)) (z : Scalar) :
    DomainVectorFunctions.derivative (vector A hA x) hH z True.intro ≈ A.eval x :=
  Setoid.trans (vector_derivative_ode_of_holomorphic A hA x hH z)
    (Setoid.trans (A.congr (value_nilpotent A hA hNil z x)) (NilpotentShear.operator_forward A hA hNil z x))

end ComputableAnalysis.RiemannHilbert.MatrixExponential
