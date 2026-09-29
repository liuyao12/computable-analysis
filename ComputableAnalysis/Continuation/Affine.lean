import ComputableAnalysis.Continuation.Derivative
import ComputableAnalysis.Continuation.Domain
import ComputableAnalysis.Continuation.Transport
import ComputableAnalysis.HolomorphicExamples

/-! A concrete non-rational client: affine holomorphic germs. Their local
identity theorem is proved from derivative uniqueness and finite algebra;
coefficient equality is not inferred from one value or assumed in a germ. -/
namespace ComputableAnalysis.Continuation
open ComplexRaw FunctionTheory

structure Affine where
  slope : ComplexRaw
  intercept : ComplexRaw
  slope_valid : slope.Valid
  intercept_valid : intercept.Valid

namespace Affine

def chart (f : Affine) : FunctionTheory.Map :=
  affine f.slope f.intercept f.slope_valid f.intercept_valid

def localFunction (f : Affine) (a : Point) : LocalFunction a :=
  ⟨f.chart, affine_holomorphic f.slope f.intercept f.slope_valid f.intercept_valid, True.intro⟩

instance : Setoid Affine where
  r f g := f.slope.Equiv g.slope ∧ f.intercept.Equiv g.intercept
  iseqv := ⟨fun f => ⟨equiv_refl _ f.slope_valid,equiv_refl _ f.intercept_valid⟩,
    fun h => ⟨equiv_symm h.1,equiv_symm h.2⟩,
    fun {f g h} hfg hgh =>
      ⟨equiv_trans f.slope_valid g.slope_valid h.slope_valid hfg.1 hgh.1,
        equiv_trans f.intercept_valid g.intercept_valid h.intercept_valid hfg.2 hgh.2⟩⟩

theorem localFunction_congr {f g : Affine} (h : f ≈ g) (a : Point) :
    f.localFunction a ≈ g.localFunction a := by
  refine ⟨⟨1,by decide⟩, fun z hz _ => ⟨True.intro,True.intro,?_⟩⟩
  exact add_equiv (mul_equiv f.slope_valid g.slope_valid hz hz h.1 (equiv_refl z hz)) h.2

private theorem recover_intercept (f : Affine) (a : Point) :
    (sub (f.chart.eval a.val) (mul f.slope a.val)).Equiv f.intercept := by
  let v : Nat → ComplexRaw := fun n => if n=0 then f.slope else if n=1 then a.val else f.intercept
  have hv : ∀ n, (v n).Valid := by
    intro n; dsimp [v]; split
    · exact f.slope_valid
    · split
      · exact a.property
      · exact f.intercept_valid
  let term : PolynomialExpr := .mul (.var 0) (.var 1)
  exact PolynomialExpr.identity (.add (.add term (.var 2)) (.neg term)) (.var 2) v hv (by
    intro p
    simp only [term,PolynomialExpr.rational,QComplex.add,QComplex.neg,QComplex.mul]
    cases p 2
    simp only [QComplex.mk.injEq]
    constructor <;> grind)

/-- A proved identity theorem for affine charts at arbitrary represented base
points and coefficients: equality on a neighborhood determines both coefficients. -/
theorem coefficients_of_germ {f g : Affine} (a : Point)
    (h : f.localFunction a ≈ g.localFunction a) : f ≈ g := by
  have hs : f.slope.Equiv g.slope := derivative_eq_of_agreeAt
    (g.localFunction a).holomorphic.openDomain
    ((f.localFunction a).holomorphic.atPoint a.val a.property True.intro)
    ((g.localFunction a).holomorphic.atPoint a.val a.property True.intro) h
  have hv := LocalFunction.value_congr h
  have hm := mul_equiv f.slope_valid g.slope_valid a.property a.property hs (equiv_refl _ a.property)
  have hd := FunctionTheory.sub_congr hv hm
  have hfv := sub_valid (f.chart.valid a.val a.property True.intro) (mul_valid f.slope_valid a.property)
  have hgv := sub_valid (g.chart.valid a.val a.property True.intro) (mul_valid g.slope_valid a.property)
  exact ⟨hs, equiv_trans f.intercept_valid hfv g.intercept_valid
    (equiv_symm (f.recover_intercept a))
    (equiv_trans hfv hgv g.intercept_valid hd (g.recover_intercept a))⟩

theorem germ_iff_coefficients (f g : Affine) (a : Point) :
    (f.localFunction a ≈ g.localFunction a) ↔ f ≈ g :=
  ⟨coefficients_of_germ a, fun h => localFunction_congr h a⟩

/-- Moving an affine germ preserves its already uniquely determined
coefficients. This client instantiates every local transport law. -/
def transport (D : Region) : Transport D.Edge D.Face (fun _ => Affine) where
  step := fun _ f => f
  congr := by intro a b e s t h; exact h
  stationary := fun _ _ => Setoid.refl _
  inverse := fun _ _ _ => Setoid.refl _
  triangle := fun _ _ _ _ _ => Setoid.refl _

theorem endpoint_independent (D : Region) (hD : FiniteSimplyConnected D.Edge D.Face)
    {a b : D.Vertex} (p q : Path D.Edge a b) (f : Affine) :
    (((transport D).run p f).localFunction b.val).value.Equiv
      (((transport D).run q f).localFunction b.val).value :=
  LocalFunction.value_congr (localFunction_congr
    ((transport D).path_independent hD p q f) b.val)

end Affine
end ComputableAnalysis.Continuation
