import ComputableAnalysis.RiemannHilbert.ContourConstructedTaylor
import ComputableAnalysis.RiemannHilbert.ContourConstructedMomentInvariance
import ComputableAnalysis.RiemannHilbert.SeriesMatrixFields
import ComputableAnalysis.RiemannHilbert.FiberTopology
import ComputableAnalysis.RiemannHilbert.RadialGrowthArithmetic

/-! Common computed Cauchy-series data for a supplied holomorphic matrix
field. Finite maxima and minima include empty rectangular ranks. An actual
open-domain witness remains necessary when there are no matrix entries. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedMatrixTaylor
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField RectangularContour
set_option autoImplicit false
variable {n m : Nat} {D : Scalar → Prop}

def finiteEntries {α : Type} (v : Fin n → Fin m → α) : List α :=
  (List.ofFn (fun i => List.ofFn (v i))).flatten

theorem finiteEntries_mem {α : Type} (v : Fin n → Fin m → α) (i : Fin n) (j : Fin m) :
    v i j ∈ finiteEntries v :=
  List.mem_flatten.mpr ⟨List.ofFn (v i),List.mem_ofFn.mpr ⟨i,rfl⟩,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

variable (G : Field (n := n) (m := m) D) (O : ScalarTopology.OpenData D)
    (hG : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hM : MatrixHolomorphic G O.invariant hG) (b : Scalar) (hb : D b)

def coefficients (i : Fin n) (j : Fin m) : Nat → ComplexRaw :=
  localCauchyTaylorCoefficients (entryMap G O.invariant hG i j) (hM i j) b hb

theorem coefficients_valid (i : Fin n) (j : Fin m) (k : Nat) :
    (coefficients G O hG hM b hb i j k).Valid :=
  localCauchyTaylorCoefficients_valid (entryMap G O.invariant hG i j) (hM i j) b hb k

def bound : Rat := finiteBound (finiteEntries (fun i j =>
  (localCauchyCoefficientBound (entryMap G O.invariant hG i j) b hb).val))

theorem bound_nonneg : 0≤bound G O hG b hb := finiteBound_nonneg _

theorem entry_bound_le (i : Fin n) (j : Fin m) :
    (localCauchyCoefficientBound (entryMap G O.invariant hG i j) b hb).val≤bound G O hG b hb :=
  le_finiteBound _ _ (finiteEntries_mem _ i j)

def rate : QPos :=
  ⟨finiteBound (finiteEntries (fun i j =>
      (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val))
    +2*(n : Rat)*bound G O hG b hb+1,
    by have hf := finiteBound_nonneg (finiteEntries (fun i j =>
         (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val))
       have hp : 0≤2*(n : Rat)*bound G O hG b hb := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.natCast_nonneg (a := n)))
         (bound_nonneg G O hG b hb)
       grind only⟩

theorem entry_rate_le (i : Fin n) (j : Fin m) :
    (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val≤(rate G O hG hM b hb).val := by
  have hf := le_finiteBound _ _ (finiteEntries_mem (fun i j =>
    (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val) i j)
  have hp : 0≤2*(n : Rat)*bound G O hG b hb := Rat.mul_nonneg (Rat.mul_nonneg (by decide +kernel) (Rat.natCast_nonneg (a := n)))
    (bound_nonneg G O hG b hb)
  change _≤finiteBound (finiteEntries (fun i j =>
    (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val))+2*(n : Rat)*bound G O hG b hb+1
  grind only

theorem rate_dominates : 2*((n : Rat)*bound G O hG b hb)≤(rate G O hG hM b hb).val := by
  have hf := finiteBound_nonneg (finiteEntries (fun i j =>
    (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val))
  change _≤finiteBound (finiteEntries (fun i j =>
    (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).val))+2*(n : Rat)*bound G O hG b hb+1
  grind only

theorem coefficients_bound (i : Fin n) (j : Fin m) (k : Nat) :
    Small (coefficients G O hG hM b hb i j k) (bound G O hG b hb*(rate G O hG hM b hb).val^k) := by
  have hs := localCauchyMoment_majorant (entryMap G O.invariant hG i j) (hM i j) b hb k
  apply hs.mono
  have hp := RadialGrowthArithmetic.power_mono _ _
    (Rat.le_of_lt (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).property)
    (entry_rate_le G O hG hM b hb i j) k
  exact Rat.le_trans (Rat.mul_le_mul_of_nonneg_right (entry_bound_le G O hG b hb i j)
    (Rat.pow_nonneg (Rat.le_of_lt (localCauchyCoefficientRate (entryMap G O.invariant hG i j) (hM i j) b hb).property)))
    (Rat.mul_le_mul_of_nonneg_left hp (bound_nonneg G O hG b hb))

def radius : QPos := minRadius (minRadius (O.radius b hb)
  (FiberTopology.finiteRadius (finiteEntries (fun i j =>
    localCauchyTaylorRadius (entryMap G O.invariant hG i j) (hM i j) b hb))))
  (LocalODE.solutionRadius (rate G O hG hM b hb).val (Rat.le_of_lt (rate G O hG hM b hb).property))

theorem radius_ode_le : (radius G O hG hM b hb).val≤
    (LocalODE.solutionRadius (rate G O hG hM b hb).val (Rat.le_of_lt (rate G O hG hM b hb).property)).val :=
  minRadius_right _ _

theorem radius_entry_le (i : Fin n) (j : Fin m) : (radius G O hG hM b hb).val≤
    (localCauchyTaylorRadius (entryMap G O.invariant hG i j) (hM i j) b hb).val :=
  Rat.le_trans (minRadius_left _ _) (Rat.le_trans (minRadius_right _ _)
    (FiberTopology.finiteRadius_le _ _ (finiteEntries_mem _ i j)))

theorem radius_budget : 8*(rate G O hG hM b hb).val*(radius G O hG hM b hb).val≤(1:Rat)/2 :=
  Rat.le_trans (Rat.mul_le_mul_of_nonneg_left (radius_ode_le G O hG hM b hb)
    (Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt (rate G O hG hM b hb).property)))
    (LocalODE.solutionRadius_small _ (Rat.le_of_lt (rate G O hG hM b hb).property))

theorem radius_domain (z : Scalar) (hz : Centered.domain b (radius G O hG hM b hb).val z) : D z :=
  O.inside b hb z ((LocalODE.interior_bound _ _ hz).mono
    (Rat.le_trans (minRadius_left _ _) (minRadius_left _ _)))

theorem radius_entry_domain (i : Fin n) (j : Fin m) (z : Scalar)
    (hz : Centered.domain b (radius G O hG hM b hb).val z) :
    (localCauchyTaylor (entryMap G O.invariant hG i j) (hM i j) b hb).domain z := by
  obtain ⟨r,hr,hrR,hs⟩ := hz
  have hi := radius_entry_le G O hG hM b hb i j
  exact ⟨r,hr,by change r<(localCauchyTaylorRadius (entryMap G O.invariant hG i j) (hM i j) b hb).val; grind only,hs⟩

theorem coefficients_congr (hN : MatrixHolomorphic G O.invariant hG) (c : Scalar) (hc : D c)
    (hbc : b≈c) (i : Fin n) (j : Fin m) (k : Nat) :
    (coefficients G O hG hM b hb i j k).Equiv (coefficients G O hG hN c hc i j k) :=
  localCauchyMoment_congr (entryMap G O.invariant hG i j) (hM i j) (hN i j) b c hb hc hbc k

theorem coefficients_data_congr (P : ScalarTopology.OpenData D)
    (hNnames : ∀ z w hz hw, z≈w → (G z hz).Equiv (G w hw))
    (hN : MatrixHolomorphic G P.invariant hNnames) (c : Scalar) (hc : D c)
    (hbc : b≈c) (i : Fin n) (j : Fin m) (k : Nat) :
    (coefficients G O hG hM b hb i j k).Equiv (coefficients G P hNnames hN c hc i j k) :=
  localCauchyMoment_congr (entryMap G O.invariant hG i j) (hM i j) (hN i j) b c hb hc hbc k

end ComputableAnalysis.RiemannHilbert.ConstructedMatrixTaylor
