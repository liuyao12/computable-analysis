import ComputableAnalysis.RiemannHilbert.ContourFrameGeometry
import ComputableAnalysis.RiemannHilbert.ContourBoundaryVanishing

/-! One executable sampler shared by every tile of a square frame.
Domain evidence is consumed only after a rational membership decision. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions
set_option autoImplicit false

def frameTiles : List (Nat × Nat) :=
  [(0,0),(0,1),(0,2),(0,3),(1,0),(1,3),(2,0),(2,3),(3,0),(3,1),(3,2),(3,3)]

theorem frameTiles_valid : ∀ i ∈ frameTiles, squareFrameTileIndex i.1 i.2 := by
  intro i hi
  simp only [frameTiles,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with h|h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> decide +kernel

theorem frameTiles_complete (j k : Nat) (h : squareFrameTileIndex j k) :
    (j,k) ∈ frameTiles := by
  have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by unfold squareFrameTileIndex at h; omega
  have hk : k=0 ∨ k=1 ∨ k=2 ∨ k=3 := by unfold squareFrameTileIndex at h; omega
  rcases hj with hj|hj|hj|hj <;> rcases hk with hk|hk|hk|hk <;>
    subst j <;> subst k <;> simp_all [frameTiles,squareFrameTileIndex]

def frameDomain (R : QPos) (z : Scalar) : Prop :=
  ∃ j k, squareFrameTileIndex j k ∧ representedRectangleContains (squareFrameTile R j k) z

def sampleFromTiles (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) :
    (L : List (Nat × Nat)) → (∀ i ∈ L, squareFrameTileIndex i.1 i.2) → QComplex → Scalar
  | [], _, _ => ⟨zero,ofQComplex_valid _⟩
  | i::L, hi, q =>
    if h : rationalRectangleContains (squareFrameTile R i.1 i.2) q then
      f.eval (rationalRectangleScalar q) (hdom _
        ⟨i.1,i.2,hi i (List.mem_cons_self),rationalRectangle_represented_mem _ q h⟩)
    else sampleFromTiles f R hdom L (fun j hj => hi j (List.mem_cons_of_mem _ hj)) q

theorem sampleFromTiles_agreement (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (L : List (Nat × Nat))
    (hL : ∀ i ∈ L, squareFrameTileIndex i.1 i.2) (q : QComplex)
    (hq : ∃ i ∈ L, rationalRectangleContains (squareFrameTile R i.1 i.2) q)
    (hd : f.domain (rationalRectangleScalar q)) :
    (sampleFromTiles f R hdom L hL q).val.Equiv (f.eval (rationalRectangleScalar q) hd).val := by
  induction L with
  | nil => obtain ⟨i,hi,_⟩ := hq; exact False.elim (List.not_mem_nil hi)
  | cons i L ih =>
    by_cases h : rationalRectangleContains (squareFrameTile R i.1 i.2) q
    · simp only [sampleFromTiles,dif_pos h]
      exact equiv_refl _ (f.eval (rationalRectangleScalar q) hd).property
    · simp only [sampleFromTiles,dif_neg h]
      apply ih
      obtain ⟨j,hj,hjq⟩ := hq
      rcases List.mem_cons.mp hj with he|ht
      · subst j; exact False.elim (h hjq)
      · exact ⟨j,ht,hjq⟩

def frameSample (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) : QComplex → Scalar :=
  sampleFromTiles f R hdom frameTiles frameTiles_valid

theorem frameSample_agreement (f : DomainFunctions.Map) (R : QPos)
    (hdom : ∀ z, frameDomain R z → f.domain z) (j k : Nat) (hi : squareFrameTileIndex j k)
    (q : QComplex) (hq : rationalRectangleContains (squareFrameTile R j k) q)
    (hd : f.domain (rationalRectangleScalar q)) :
    (frameSample f R hdom q).val.Equiv (f.eval (rationalRectangleScalar q) hd).val :=
  sampleFromTiles_agreement f R hdom frameTiles frameTiles_valid q
    ⟨(j,k),frameTiles_complete j k hi,hq⟩ hd

end ComputableAnalysis.RiemannHilbert.RectangularContour
