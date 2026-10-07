import ComputableAnalysis.ModularForms.UpperLatticeRectangleSum
import ComputableAnalysis.ModularForms.SymmetricLatticeCoordinates
import ComputableAnalysis.ModularForms.IntegerPowerTranslationPrefixes

/-! Actual positive-height lattice rows as reciprocal-power rows at scaled inputs. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory QuadraticOrder163

/-- Executable integer scaling, retaining the actual affine evaluator. -/
def integerScaleScalar (z : Scalar) (y : Int) : Scalar :=
  ⟨integerAffine y 0 z.val,integerAffine_valid _ _ z.property⟩

theorem integerScaleScalar_upper (z : Scalar) (hz : InUpperHalfPlane z.val)
    (y : Int) (hy : 0<y) : InUpperHalfPlane (integerScaleScalar z y).val := by
  obtain ⟨N,hN⟩ := hz
  change 0<(z.val.compute N).lo.im at hN
  have hyq : (0:Rat)<(y:Rat) := by exact_mod_cast hy
  refine ⟨N,?_⟩
  simpa only [integerScaleScalar,integerAffine,translate,scaleRat,QBox.scaleRat,
    imagPart,ComplexRaw.add,if_pos (Rat.le_of_lt hyq),ofQComplex,QBox.add,QComplex.add,
    Rat.intCast_zero,Rat.add_zero] using Rat.mul_pos hyq hN

private theorem positiveRowPoint_nonzero (x y : Int) (hy : 0<y) :
    (⟨x,y⟩ : QuadraticOrder163)≠QuadraticOrder163.zero := by
  intro he
  have he' := congrArg QuadraticOrder163.y he
  change y=0 at he'
  omega

theorem latticeVector_positiveRow (z : Scalar) (x y : Int) :
    (latticeVector z ⟨x,y⟩).val.Equiv
      (integerShiftScalar (integerScaleScalar z y) x).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeVector z ⟨x,y⟩).property)
    (hright := (integerShiftScalar (integerScaleScalar z y) x).property)
  change ComplexRawQuotient.ofRaw (integerAffine y x z.val) _=
    ComplexRawQuotient.ofRaw (integerAffine 1 x (integerScaleScalar z y).val) _
  rw [integerAffine_class,integerAffine_class]
  change (y:ScalarAlgebra.Value)*ComplexRawQuotient.ofRaw z.val z.property+(x:ScalarAlgebra.Value)=
    ((1:Int):ScalarAlgebra.Value)*ComplexRawQuotient.ofRaw (integerAffine y 0 z.val)
      (integerAffine_valid _ _ z.property)+(x:ScalarAlgebra.Value)
  rw [integerAffine_class]
  grind only

/-- This compares actual reciprocal algorithms; it is not a formal symbolic identity. -/
theorem upperPointPower_positiveRow (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (x y : Int) (hy : 0<y) :
    (upperPointPower z hz k ⟨x,y⟩).Equiv
      ((integerReciprocalPowerMap x k).eval (integerScaleScalar z y)
        (integerScaleScalar_upper z hz y hy)).val := by
  simp only [upperPointPower,dif_pos (positiveRowPoint_nonzero x y hy)]
  let w := integerScaleScalar z y
  have hw := integerScaleScalar_upper z hz y hy
  have hI := RepresentedReciprocal.inverse_congr
    (latticeVector z ⟨x,y⟩) (integerShiftScalar w x)
    (latticeVector_nonzero z hz ⟨x,y⟩ (positiveRowPoint_nonzero x y hy))
    (upperScalar_nonzero _ (integerShiftScalar_upper w hw x))
    (latticeVector_positiveRow z x y)
  exact LocalODE.power_congr _ _
    (latticeInverse z hz ⟨x,y⟩ (positiveRowPoint_nonzero x y hy)).property
    (upperIntegerReciprocal w hw x).property hI k

private theorem positiveRowPoints (N : Nat) (y : Int) (hy : 0<y) :
    latticeRowPoints N y=(latticeCoordinates N).map (fun x => (⟨x,y⟩ : QuadraticOrder163)) := by
  apply List.filter_eq_self.mpr
  intro u hu
  obtain ⟨x,_,rfl⟩ := List.mem_map.mp hu
  exact decide_eq_true (positiveRowPoint_nonzero x y hy)

/-- Each positive-height finite row is exactly an integer row prefix at the scaled input. -/
theorem upperLatticeFiniteRow_positive_integerPrefix (z : Scalar)
    (hz : InUpperHalfPlane z.val) (k N : Nat) (y : Int) (hy : 0<y) :
    (upperLatticeFiniteRow z hz k N y).val.Equiv
      (integerPowerRowPrefix (integerScaleScalar z y)
        (integerScaleScalar_upper z hz y hy) k N) := by
  let w := integerScaleScalar z y
  have hw := integerScaleScalar_upper z hz y hy
  have he := representedSum_map_equiv (latticeCoordinates N)
    (fun x => upperPointPower z hz k ⟨x,y⟩)
    (fun x => ((integerReciprocalPowerMap x k).eval w hw).val)
    (fun x => upperPointPower_positiveRow z hz k x y hy)
  have hrow : (upperLatticeFiniteRow z hz k N y).val=
      LocalODE.sum ((latticeCoordinates N).map (fun x => upperPointPower z hz k ⟨x,y⟩)) := by
    change LocalODE.sum ((latticeRowPoints N y).map (upperPointPower z hz k))=_
    rw [positiveRowPoints N y hy,List.map_map]
    rfl
  rw [hrow]
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := by rw [← hrow]; exact (upperLatticeFiniteRow z hz k N y).property)
    (hright := integerPowerRowPrefix_valid w hw k N)
  have hclass := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := by rw [← hrow]; exact (upperLatticeFiniteRow z hz k N y).property)
    (hright := LocalODE.sum_valid _ (by
      intro zz hzz
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hzz
      exact ((integerReciprocalPowerMap x k).eval w hw).property)) he
  rw [hclass,representedSum_latticeCoordinates,integerPowerRowPrefix_class]
  rfl

/-- Finite positive lattice rows converge with the proved integer-row error schedule. -/
theorem upperLatticeFiniteRow_positive_close (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k B : Nat) (hk : 2≤k) (y : Int) (hy : 0<y)
    (hB : Small (integerScaleScalar z y).val (B:Rat)) (N : Nat) :
    Small (sub (integerPowerRowAssembly (integerScaleScalar z y)
        (integerScaleScalar_upper z hz y hy) k B)
      (upperLatticeFiniteRow z hz k (4*B+(N+1)) y).val)
      (((2*32^k:Nat):Rat)*(((N+1:Nat):Rat))⁻¹) := by
  let w := integerScaleScalar z y
  have hw := integerScaleScalar_upper z hz y hy
  exact Small.congr
    (sub_valid (integerPowerRowAssembly_valid w hw k B hk hB)
      (integerPowerRowPrefix_valid w hw k _))
    (sub_valid (integerPowerRowAssembly_valid w hw k B hk hB)
      (upperLatticeFiniteRow z hz k _ y).property)
    (FunctionTheory.sub_congr (equiv_refl _ (integerPowerRowAssembly_valid w hw k B hk hB))
      (equiv_symm (upperLatticeFiniteRow_positive_integerPrefix z hz k _ y hy)))
    (integerPowerRowAssembly_close w hw k B hk hB N)

end ComputableAnalysis.ModularForms
