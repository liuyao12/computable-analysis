import ComputableAnalysis.RiemannHilbert.CoveredAtlasDivisions

/-! Exact rational cuts of represented parameter segments. A cut is found by
rational division, including the degenerate interval case. Whole-cell covers
restrict to both pieces by the proved affine reparametrization laws; values
of the path and the parameters used inside either piece remain represented. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory UnitInterval

structure RationalParameter where
  val : Rat
  lower : 0 ≤ val
  upper : val ≤ 1

namespace RationalParameter

def point (s : RationalParameter) : Point := rational s.val s.lower s.upper

theorem ext {s t : RationalParameter} (h : s.val=t.val) : s=t := by
  cases s
  cases t
  cases h
  rfl

def zero : RationalParameter := ⟨0, by decide +kernel, by decide +kernel⟩
def one : RationalParameter := ⟨1, by decide +kernel, by decide +kernel⟩

theorem point_order {s t : RationalParameter} (h : s.val ≤ t.val) : s.point.value.Le t.point.value :=
  fun _ _ => h

def relative (s t c : RationalParameter) (hsc : s.val ≤ c.val) (hct : c.val ≤ t.val) : Point :=
  if h : s.val=t.val then UnitInterval.zero else
    rational ((c.val-s.val)/(t.val-s.val))
      (Rat.mul_nonneg (by grind only) (Rat.le_of_lt ((Rat.inv_pos).2 (by grind only))))
      (by
        have hp : 0 < t.val-s.val := by grind only
        have hn : t.val-s.val ≠ 0 := Rat.ne_of_gt hp
        have hl := Rat.mul_le_mul_of_nonneg_right (show c.val-s.val ≤ t.val-s.val by grind only)
          (Rat.le_of_lt ((Rat.inv_pos).2 hp))
        simpa only [Rat.div_def, Rat.mul_inv_cancel _ hn] using hl)

theorem segment_rational (s t : RationalParameter) (v : Rat) (h0 : 0 ≤ v) (h1 : v ≤ 1)
    (c : RationalParameter) (he : s.val+(t.val-s.val)*v=c.val) :
    segment s.point t.point (rational v h0 h1) ≈ c.point := by
  intro k
  apply (RealRaw.compareAt_overlap_iff _ _ k k).2
  rw [segment_compute]
  simp only [point, rational, RealRaw.ofRat, QBox.mulRealInterval, min4, max4, minRat, maxRat2]
  simp only [Rat.le_refl, if_true]
  rw [he]
  exact ⟨Rat.le_refl, Rat.le_refl⟩

theorem relative_value (s t c : RationalParameter) (hsc : s.val ≤ c.val) (hct : c.val ≤ t.val) :
    segment s.point t.point (relative s t c hsc hct) ≈ c.point := by
  unfold relative
  split
  · rename_i h
    have hc : s=c := ext (by grind only)
    subst c
    exact segment_zero s.point t.point
  · rename_i h
    apply segment_rational
    have hn : t.val-s.val ≠ 0 := by grind only
    have hi : (t.val-s.val)*(t.val-s.val)⁻¹=1 := Rat.mul_inv_cancel _ hn
    grind [Rat.div_def]

end RationalParameter

namespace CoveredAtlasDivision
universe u
variable {I : Type u} {n : Nat} {a : CoefficientAtlas I n} {p q : Scalar}
variable (f : ScalarPaths.Path p q) (i : I) (s t c : RationalParameter)
variable (hsc : s.val ≤ c.val) (hct : c.val ≤ t.val)
variable (inside : ∀ u, (a.chart i).domain ((ScalarPaths.subpath f s.point t.point).eval u))

include hsc hct inside

theorem rationalCut_mem : (a.chart i).domain (f.eval c.point) :=
  ((a.chart i).domain_congr (f.eval (segment s.point t.point (RationalParameter.relative s t c hsc hct)))
    (f.eval c.point) (f.congr _ _ (RationalParameter.relative_value s t c hsc hct))).1
    (inside (RationalParameter.relative s t c hsc hct))

theorem rationalCut_first_inside (u : Point) :
    (a.chart i).domain ((ScalarPaths.subpath f s.point c.point).eval u) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f s.point c.point).eval u)
    ((ScalarPaths.subpath f s.point (segment s.point t.point (RationalParameter.relative s t c hsc hct))).eval u)
    (f.congr _ _ (segment_congr (Setoid.refl _) (Setoid.symm (RationalParameter.relative_value s t c hsc hct))
      (Setoid.refl u)))).2
    (first_inside f i s.point t.point (RationalParameter.relative s t c hsc hct) inside u)

theorem rationalCut_second_inside (u : Point) :
    (a.chart i).domain ((ScalarPaths.subpath f c.point t.point).eval u) :=
  ((a.chart i).domain_congr ((ScalarPaths.subpath f c.point t.point).eval u)
    ((ScalarPaths.subpath f (segment s.point t.point (RationalParameter.relative s t c hsc hct)) t.point).eval u)
    (f.congr _ _ (segment_congr (Setoid.symm (RationalParameter.relative_value s t c hsc hct)) (Setoid.refl _)
      (Setoid.refl u)))).2
    (second_inside f i s.point t.point (RationalParameter.relative s t c hsc hct) inside u)

end CoveredAtlasDivision
end ComputableAnalysis.RiemannHilbert
