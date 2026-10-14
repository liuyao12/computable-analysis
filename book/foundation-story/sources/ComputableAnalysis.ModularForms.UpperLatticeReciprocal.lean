import ComputableAnalysis.ModularForms.LatticeActionIdentity

/-! Certified lattice reciprocals at arbitrary represented upper-half-plane points. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert

def latticeVector (z : Scalar) (u : QuadraticOrder163) : Scalar :=
  ⟨integerAffine u.y u.x z.val,integerAffine_valid _ _ z.property⟩

theorem latticeVector_nonzero (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    NonzeroBoxSearch.Nonzero (latticeVector z u) := by
  intro hzero
  change (integerAffine u.y u.x z.val).Equiv ComplexRaw.zero at hzero
  obtain ⟨N, hN⟩ := hz
  change 0 < (z.val.compute N).lo.im at hN
  have ho := (compareAt_overlap_iff _ _ N N).mp (hzero N)
  by_cases hc : 0 ≤ (u.y : Rat)
  · simp only [integerAffine, translate, add, scaleRat, ofQComplex,
      QBox.add, QComplex.add, QBox.scaleRat, if_pos hc, zero] at ho
    rcases ho with ⟨⟨hr₁, hi₁⟩, ⟨hr₂, hi₂⟩⟩
    dsimp [QComplex.zero] at hr₁ hi₁ hr₂ hi₂
    by_cases he : (u.y : Rat) = 0
    · simp only [he, Rat.zero_mul, Rat.zero_add, Rat.add_zero] at hr₁ hi₁ hr₂ hi₂
      have hdz : (u.x : Rat) = 0 := by grind only
      have hy : u.y=0 := by exact_mod_cast he
      have hx : u.x=0 := by exact_mod_cast hdz
      exact hu (QuadraticOrder163.ext hx hy)
    · have hp : 0 < (u.y : Rat) := Rat.lt_of_le_of_ne hc (Ne.symm he)
      have hh := Rat.mul_pos hp hN
      change 0 < (u.y : Rat)*(z.val.compute N).lo.im at hh
      grind only
  · simp only [integerAffine, translate, add, scaleRat, ofQComplex,
      QBox.add, QComplex.add, QBox.scaleRat, if_neg hc, zero] at ho
    rcases ho with ⟨⟨hr₁, hi₁⟩, ⟨hr₂, hi₂⟩⟩
    dsimp [QComplex.zero] at hr₁ hi₁ hr₂ hi₂
    have hn : (u.y : Rat) < 0 := (Rat.not_le).mp hc
    have hh : (u.y : Rat)*(z.val.compute N).lo.im < 0 := by
      have hp := Rat.mul_pos (show 0 < -(u.y : Rat) by grind only) hN
      rw [Rat.neg_mul] at hp
      grind only
    grind only


def latticeInverse (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) : Scalar :=
  RepresentedReciprocal.inverse (latticeVector z u) (latticeVector_nonzero z hz u hu)

theorem latticeInverse_product (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    (mul (latticeVector z u).val (latticeInverse z hz u hu).val).Equiv ComplexRaw.one :=
  RepresentedReciprocal.mul_inverse _ (latticeVector_nonzero z hz u hu)

end ComputableAnalysis.ModularForms
