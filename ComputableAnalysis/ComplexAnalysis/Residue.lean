import ComputableAnalysis.ComplexAnalysis.Cauchy
import ComputableAnalysis.ComplexAnalysis.SquarePole
import ComputableAnalysis.ComplexMultiplication
import ComputableAnalysis.ComplexAffine

/-!
# A local residue identity on rational squares

The singular part is computed by sampled reciprocal pullbacks, independently
normalized by arctangent. The regular part is computed by two triangle
contours. The coefficient is an arbitrary valid represented complex number.

This is a local simple-pole theorem. It does not assert a general residue
theorem for unspecified meromorphic functions or unspecified contour transport.
-/
namespace ComputableAnalysis.ComplexAnalysis
open QComplex

structure Square where
  center : QComplex
  radius : Rat
  positive : 0 < radius

def Square.a (s : Square) : QComplex := add s.center ⟨-s.radius,-s.radius⟩
def Square.b (s : Square) : QComplex := add s.center ⟨s.radius,-s.radius⟩
def Square.c (s : Square) : QComplex := add s.center ⟨s.radius,s.radius⟩
def Square.d (s : Square) : QComplex := add s.center ⟨-s.radius,s.radius⟩
def Square.lower (s : Square) : Triangle := ⟨s.a,s.b,s.c⟩
def Square.upper (s : Square) : Triangle := ⟨s.a,s.c,s.d⟩

def Square.boundarySum (s : Square) (f : QComplex → QComplex) (n : Nat) : QComplex :=
  add (edgeSum f s.a s.b n) (add (edgeSum f s.b s.c n)
    (add (edgeSum f s.c s.d n) (edgeSum f s.d s.a n)))

/-- The common diagonal cancels, leaving precisely the outer polygon. -/
theorem Square.triangulate (s : Square) (f : QComplex → QComplex) (n : Nat) :
    add (s.lower.sum f n) (s.upper.sum f n) = s.boundarySum f n := by
  simp only [Square.lower,Square.upper,Triangle.sum,Square.boundarySum]
  rw [edgeSum_reverse f s.a s.c n]
  simp only [add,neg,QComplex.mk.injEq]
  constructor <;> grind

structure Square.Regular (s : Square) (g : QComplex → ComplexRaw) where
  lower : CauchyData s.lower g
  upper : CauchyData s.upper g

def Square.Regular.contour {s : Square} {g : QComplex → ComplexRaw}
    (h : s.Regular g) : ComplexRaw := ComplexRaw.add h.lower.contour h.upper.contour

theorem Square.Regular.valid {s : Square} {g : QComplex → ComplexRaw}
    (h : s.Regular g) : h.contour.Valid :=
  ComplexRaw.add_valid h.lower.contour_valid h.upper.contour_valid

private theorem raw_add_zero (z : ComplexRaw) (hz : z.Valid) :
    (ComplexRaw.add z (ComplexRaw.ofQComplex zero)).Equiv z := by
  intro n
  apply (ComplexRaw.compareAt_overlap_iff _ _ n n).2
  have ho := ComplexRaw.valid_ordered hz n
  simp only [ComplexRaw.add,ComplexRaw.ofQComplex,QBox.add,QComplex.add,zero,
    QBox.Overlaps,QBox.Ordered,QComplex.le_def] at *
  constructor <;> constructor <;> grind only

theorem Square.Regular.cauchy {s : Square} {g : QComplex → ComplexRaw}
    (h : s.Regular g) : h.contour.Equiv (ComplexRaw.ofQComplex zero) := by
  have he := ComplexRaw.add_equiv h.lower.cauchy h.upper.cauchy
  exact ComplexRaw.equiv_trans h.valid
    (ComplexRaw.add_valid (ComplexRaw.ofQComplex_valid zero) (ComplexRaw.ofQComplex_valid zero))
    (ComplexRaw.ofQComplex_valid zero) he (raw_add_zero _ (ComplexRaw.ofQComplex_valid zero))

/-- Represented values of a supplied simple-pole decomposition. The domain
requires actual separation from the pole, including on contour segments. -/
def simplePoleValue (s : Square) (rho : ComplexRaw) (g : QComplex → ComplexRaw)
    (z : QComplex) (_hz : normSq (sub z s.center) ≠ 0) : ComplexRaw :=
  ComplexRaw.add (ComplexRaw.qcomplexLeftMul (inverse (sub z s.center)) rho) (g z)

/-- A split quadrature: sampled singular pullbacks and sampled regular
triangles, never an evaluator defined to be the predicted residue value. -/
def Square.residueContour (s : Square) (rho : ComplexRaw)
    {g : QComplex → ComplexRaw} (regular : s.Regular g) (tags : SquarePole.Sampling) : ComplexRaw :=
  ComplexRaw.add (ComplexRaw.mul rho (SquarePole.contour s.center s.radius tags)) regular.contour

theorem Square.residueContour_valid (s : Square) (rho : ComplexRaw) (hrho : rho.Valid)
    {g : QComplex → ComplexRaw} (regular : s.Regular g) (tags : SquarePole.Sampling) :
    (s.residueContour rho regular tags).Valid :=
  ComplexRaw.add_valid (ComplexRaw.mul_valid hrho
    (SquarePole.contour_valid s.center s.radius (Rat.ne_of_gt s.positive) tags)) regular.valid

/-- Exact local simple-pole residue identity with arbitrary represented
complex residue. The only analytic input on the regular part is local
first-order approximation data; its contour value is proved, not assumed. -/
theorem Square.residue (s : Square) (rho : ComplexRaw) (hrho : rho.Valid)
    {g : QComplex → ComplexRaw} (regular : s.Regular g) (tags : SquarePole.Sampling) :
    (s.residueContour rho regular tags).Equiv (ComplexRaw.mul rho PDE.CauchyContour.twoPiI) := by
  have hp := ComplexRaw.mul_equiv hrho hrho
    (SquarePole.contour_valid s.center s.radius (Rat.ne_of_gt s.positive) tags)
    PDE.CauchyContour.twoPiI_valid (ComplexRaw.equiv_refl rho hrho)
    (SquarePole.contour_equiv_twoPiI s.center s.radius (Rat.ne_of_gt s.positive) tags)
  have h := ComplexRaw.add_equiv hp regular.cauchy
  have hv := ComplexRaw.mul_valid hrho PDE.CauchyContour.twoPiI_valid
  exact ComplexRaw.equiv_trans (s.residueContour_valid rho hrho regular tags)
    (ComplexRaw.add_valid hv (ComplexRaw.ofQComplex_valid zero)) hv h (raw_add_zero _ hv)

/-- Changing the residue representation and both internal integration
algorithms preserves the value. -/
theorem Square.residue_independent (s : Square) (rho sigma : ComplexRaw)
    (hrho : rho.Valid) (hsigma : sigma.Valid) (he : rho.Equiv sigma)
    {g h : QComplex → ComplexRaw} (rg : s.Regular g) (rh : s.Regular h)
    (tags other : SquarePole.Sampling) :
    (s.residueContour rho rg tags).Equiv (s.residueContour sigma rh other) := by
  have hm := ComplexRaw.mul_equiv hrho hsigma
    PDE.CauchyContour.twoPiI_valid PDE.CauchyContour.twoPiI_valid he
    (ComplexRaw.equiv_refl _ PDE.CauchyContour.twoPiI_valid)
  exact ComplexRaw.equiv_trans (s.residueContour_valid rho hrho rg tags)
    (ComplexRaw.mul_valid hrho PDE.CauchyContour.twoPiI_valid)
    (s.residueContour_valid sigma hsigma rh other) (s.residue rho hrho rg tags)
    (ComplexRaw.equiv_trans (ComplexRaw.mul_valid hrho PDE.CauchyContour.twoPiI_valid)
      (ComplexRaw.mul_valid hsigma PDE.CauchyContour.twoPiI_valid)
      (s.residueContour_valid sigma hsigma rh other) hm
      (ComplexRaw.equiv_symm (s.residue sigma hsigma rh other)))

end ComputableAnalysis.ComplexAnalysis
