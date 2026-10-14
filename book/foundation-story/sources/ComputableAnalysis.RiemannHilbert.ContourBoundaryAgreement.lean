import ComputableAnalysis.RiemannHilbert.ContourCellEstimates

/-! Exact boundary agreement needs samples only on the supplied rectangle.
The finite sums respect arbitrary equivalent represented sample names. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem gridScalarSum_congr_bounded (n : Nat) (f g : Nat → Scalar)
    (he : ∀ j, j<n → (f j).val.Equiv (g j).val) :
    (gridScalarSum n f).val.Equiv (gridScalarSum n g).val := by
  induction n with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ n ih => exact add_equiv (ih (fun j hj => he j (by omega))) (he n (by omega))

theorem gridCoordinate_mem (I : QInterval) (M : Nat) (u : Rat)
    (hI : I.lo≤I.hi) (hM : 0<M) (hu0 : 0≤u) (hu1 : u≤(M:Rat)) :
    I.lo≤I.lo+u*(I.width/(M:Rat)) ∧ I.lo+u*(I.width/(M:Rat))≤I.hi := by
  have hm : 0<(M:Rat) := Rat.natCast_pos.mpr hM
  have hw : 0≤I.width := by unfold QInterval.width; grind only
  have hs : 0≤I.width/(M:Rat) := by
    rw [Rat.div_def]; exact Rat.mul_nonneg hw (Rat.le_of_lt (Rat.inv_pos.mpr hm))
  have h0 := Rat.mul_nonneg hu0 hs
  have h1 := Rat.mul_le_mul_of_nonneg_right hu1 hs
  have he : (M:Rat)*(I.width/(M:Rat))=I.width := by
    rw [Rat.mul_comm]; exact Rat.div_mul_cancel (Rat.ne_of_gt hm)
  rw [he] at h1
  unfold QInterval.width at h1
  unfold QInterval.width at h0 ⊢
  constructor <;> grind only

theorem rectangleGridHorizontalPoint_mem (J : QInterval × QInterval) (M j k : Nat)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hM : 0<M) (hj : j<M) (hk : k≤M) :
    rationalRectangleContains J (rectangleGridHorizontalPoint J M j k) := by
  have hjr : (j:Rat)+1≤(M:Rat) := by
    have h : ((j+1:Nat):Rat)≤(M:Rat) := by exact_mod_cast (show j+1≤M by omega)
    simpa only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel] using h
  have hkr : (k:Rat)≤(M:Rat) := by exact_mod_cast hk
  have hj0 : 0≤(j:Rat) := Rat.natCast_nonneg
  have hx := gridCoordinate_mem J.1 M ((j:Rat)+1/2) hX hM (by grind only) (by grind only)
  have hy := gridCoordinate_mem J.2 M (k:Rat) hY hM Rat.natCast_nonneg hkr
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem rectangleGridVerticalPoint_mem (J : QInterval × QInterval) (M j k : Nat)
    (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (hM : 0<M) (hj : j≤M) (hk : k<M) :
    rationalRectangleContains J (rectangleGridVerticalPoint J M j k) := by
  have hkr : (k:Rat)+1≤(M:Rat) := by
    have h : ((k+1:Nat):Rat)≤(M:Rat) := by exact_mod_cast (show k+1≤M by omega)
    simpa only [Rat.natCast_add,show ((1:Nat):Rat)=1 by decide +kernel] using h
  have hjr : (j:Rat)≤(M:Rat) := by exact_mod_cast hj
  have hk0 : 0≤(k:Rat) := Rat.natCast_nonneg
  have hx := gridCoordinate_mem J.1 M (j:Rat) hX hM Rat.natCast_nonneg hjr
  have hy := gridCoordinate_mem J.2 M ((k:Rat)+1/2) hY hM (by grind only) (by grind only)
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem rectangleGridBoundary_congr (f g : QComplex → Scalar) (J : QInterval × QInterval)
    (M : Nat) (hX : J.1.lo≤J.1.hi) (hY : J.2.lo≤J.2.hi)
    (he : ∀ q, rationalRectangleContains J q → (f q).val.Equiv (g q).val) :
    (rectangleGridBoundary f J M).val.Equiv (rectangleGridBoundary g J M).val := by
  by_cases hM : 0<M
  · have hor (j k : Nat) (hj : j<M) (hk : k≤M) :
        (rectangleGridHorizontal f J M j k).val.Equiv (rectangleGridHorizontal g J M j k).val :=
      mul_equiv (f _).property (g _).property (rationalRectangleScalar _).property
        (rationalRectangleScalar _).property
        (he _ (rectangleGridHorizontalPoint_mem J M j k hX hY hM hj hk))
        (equiv_refl _ (rationalRectangleScalar _).property)
    have ver (j k : Nat) (hj : j≤M) (hk : k<M) :
        (rectangleGridVertical f J M j k).val.Equiv (rectangleGridVertical g J M j k).val :=
      mul_equiv (f _).property (g _).property (rationalRectangleScalar _).property
        (rationalRectangleScalar _).property
        (he _ (rectangleGridVerticalPoint_mem J M j k hX hY hM hj hk))
        (equiv_refl _ (rationalRectangleScalar _).property)
    exact add_equiv
      (gridScalarSum_congr_bounded M _ _ (fun j hj => FunctionTheory.sub_congr
        (hor j 0 hj (Nat.zero_le M)) (hor j M hj (Nat.le_refl M))))
      (gridScalarSum_congr_bounded M _ _ (fun k hk => FunctionTheory.sub_congr
        (ver M k (Nat.le_refl M) hk) (ver 0 k (Nat.zero_le M) hk)))
  · have hz : M=0 := by omega
    subst M
    exact equiv_refl _ (rectangleGridBoundary f J 0).property

end ComputableAnalysis.RiemannHilbert.RectangularContour
