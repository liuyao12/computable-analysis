import ComputableAnalysis.RiemannHilbert.ContourFrameSampler

/-! Representation agreement for the shared sampler, including overlapping
tiles and arbitrary valid names returned by the supplied maps. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

theorem sampleFromTiles_congr (f g : DomainFunctions.Map) (R : QPos)
    (hF : ∀ z, frameDomain R z → f.domain z) (hG : ∀ z, frameDomain R z → g.domain z)
    (he : ∀ z hz, f.eval z (hF z hz) ≈ g.eval z (hG z hz))
    (L : List (Nat × Nat)) (hL : ∀ i ∈ L, squareFrameTileIndex i.1 i.2) (q : QComplex) :
    sampleFromTiles f R hF L hL q ≈ sampleFromTiles g R hG L hL q := by
  induction L with
  | nil => exact equiv_refl _ (ofQComplex_valid _)
  | cons i L ih =>
    by_cases hq : rationalRectangleContains (squareFrameTile R i.1 i.2) q
    · simp only [sampleFromTiles,dif_pos hq]
      exact he _ ⟨i.1,i.2,hL i List.mem_cons_self,rationalRectangle_represented_mem _ q hq⟩
    · simp only [sampleFromTiles,dif_neg hq]
      exact ih (fun i hi => hL i (List.mem_cons_of_mem _ hi))

theorem frameSample_congr (f g : DomainFunctions.Map) (R : QPos)
    (hF : ∀ z, frameDomain R z → f.domain z) (hG : ∀ z, frameDomain R z → g.domain z)
    (he : ∀ z hz, f.eval z (hF z hz) ≈ g.eval z (hG z hz)) (q : QComplex) :
    frameSample f R hF q ≈ frameSample g R hG q :=
  sampleFromTiles_congr f g R hF hG he frameTiles frameTiles_valid q

end ComputableAnalysis.RiemannHilbert.RectangularContour
